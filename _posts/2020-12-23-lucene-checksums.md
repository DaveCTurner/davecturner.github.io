---
layout: post
title:  "Corruption detection in Lucene and Elasticsearch"
date:   2020-12-23
---

100% reliable data storage is [fundamentally
impossible](http://lamport.azurewebsites.net/pubs/buridan.pdf), but we can get
pretty close with layers of protection against something going wrong at the
physical level. Databases are typically agnostic to the specific protections
that any given installation is using. The protections might be in the
[filesystem itself](https://en.wikipedia.org/wiki/ZFS) but it's more usual to
push them down to the lower layers of RAID controllers and drive firmware.
However it is impossible to truly guarantee protection against [silent
corruption](https://en.wikipedia.org/wiki/Data_corruption#Silent) and this
happens often enough that many databases add their own mechanisms for detecting
and correcting those rare cases where the data that they read isn't the data
that they previously wrote.

Apache Lucene has a simple but effective mechanism for detecting corruption
which the lower layers missed: every relevant file in a Lucene index includes a
[CRC32](https://en.wikipedia.org/wiki/Cyclic_redundancy_check) checksum in its
[footer](https://lucene.apache.org/core/8_7_0/core/org/apache/lucene/codecs/CodecUtil.html).
CRC32 is fast to compute and good at detecting the kinds of random corruption
that happen to files on disk. A CRC32 mismatch definitely indicates that
something has gone wrong, although of course a matching checksum doesn't prove
the absence of corruption. A mismatch is reported with an exception like this:

    org.apache.lucene.index.CorruptIndexException:
        checksum failed (hardware problem?) : expected=335fe5fd actual=399b3f10 ...

Elasticsearch, which uses Lucene for most of its interactions with disk, shares
this mechanism for detecting corruption. There are a few places where
Elasticsearch throws its own `CorruptIndexException` with a subtly different
message:

    org.apache.lucene.index.CorruptIndexException:
        checksum failed (hardware problem?) : expected=e95zwd actual=fzexao ...

This is indicating the same issue except the `expected` and `actual` values are
reported in base 36 rather than base 16, because that's how Elasticsearch
tracks these things internally.

Verifying a checksum is expensive since it involves reading every byte of the
file which takes significant effort and might evict more useful data from the
filesystem cache, so systems typically doesn't verify the checksum on a file
very often. This is why you tend only to encounter a `CorruptIndexException`
when something unusual is happening. Users sometimes claim that corruptions are
being _caused by_ merges, or shard movements or snapshots in Elasticsearch, but
this isn't the case. These activities are examples of the rare times where
reading a whole file is necessary, so they're a good opportunity to verify the
checksum at the same time, and this is when the corruption is detected and
reported. It doesn't tell us what actually caused the corruption or when it
happened. It could have been introduced many months earlier.

All the relevant files in a Lucene index are written sequentially from start to
end and then never modified or overwritten. This access pattern is important
because it means the checksum computation is really simple and can happen
on-the-fly as the file is written, and also makes it very unlikely that an
incorrect checksum is due to a userspace bug at the time the file was written.
The [code that computes the
checksum](https://github.com/apache/lucene-solr/blob/2dc63e901c60cda27ef3b744bc554f1481b3b067/lucene/core/src/java/org/apache/lucene/store/OutputStreamIndexOutput.java)
is straightforward and very well-tested, so we can have high confidence that a
checksum mismatch really does indicate that the data that Lucene read is not
the data that it previously wrote.

We do get reports of Elasticsearch detecting these silent corruptions in
practice, which is to be expected since our userbase represents a huge quantity
of data running in environments of sometimes-questionable quality. It's not
always the hardware: often the reports involve a
[nonstandard](http://sbsfaq.com/qnap-fails-to-reveal-data-corruption-bug-that-affects-all-4-bay-and-higher-nas-devices/)
setup which hasn't seen enough real-world use to shake out the bugs. Lucene's
behaviour during a power outage on properly configured storage is
[well-tested](http://blog.mikemccandless.com/2014/04/testing-lucenes-index-durability-after.html)
but many storage systems are not properly configured and may be vulnerable to
[corrupting data on power loss](https://brad.livejournal.com/2116715.html).
[Filesystem](https://bugzilla.redhat.com/show_bug.cgi?id=1390050)
[bugs](https://bugzilla.redhat.com/show_bug.cgi?id=1379568), [kernel
bugs](https://www.elastic.co/blog/canonical-elastic-and-google-team-up-to-prevent-data-corruption-in-linux),
[drive firmware
bugs](https://pcper.com/2009/10/intel-halts-downloads-of-new-x25-m-firmware-due-to-corruption/)
and
[incompatible](https://www.dell.com/community/PowerEdge-HDD-SCSI-RAID/R610-SAS6IR-with-SSD-RAID-1-File-System-Corruption/m-p/4538501#M39288)
RAID controllers are amongst the many other possibilities. The more unusual or
cutting-edge your storage subsystem is the higher the chances of encountering
this sort of bug. But of course it could genuinely be faulty hardware too,
maybe the [RAID controller](https://community.perforce.com/s/article/2410),
maybe the [drive](https://www.backblaze.com/b2/hard-drive-test-data.html)
itself, or maybe even your [RAM](https://en.wikipedia.org/wiki/ECC_memory).
These things do happen.

The trouble with silent corruption is that it's _silent_, it typically doesn't
result in log entries or other evidence of corruption apart from the checksum
mismatch. In cases where the storage is managed by a separate team from the
applications there's usually at least one exchange where the storage team says
it must be an application bug because there's no evidence that anything went
wrong at the storage layer, ignoring of course that a checksum mismatch itself
is pretty convincing evidence that there was a problem with the storage system.

When you hear hoofbeats, [look for horses not
zebras](https://en.wikipedia.org/wiki/Zebra_%28medicine%29): Lucene's mechanism
for writing and checksumming files is simple, sequential and used by everyone,
but there's a lot of complexity and concurrency and variability on the other
side of the syscalls it makes. **It's very very likely that the cause of
corruption is infrastructural and out of the application's control.**

### Technical details

Here are some technical details of how the checksum works and how to verify it
independently. You can generally rely on Lucene getting this right, but
hopefully the transparency is reassuring.

At time of writing, the last few bytes of a Lucene file will look something
like this:

```
...
0000014a: 7265 6446 6965 6c64 7346 6f72 6d61 742e  redFieldsFormat.
0000015a: 6d6f 6465 0a42 4553 545f 5350 4545 4400  mode.BEST_SPEED.
0000016a: c028 93e8 0000 0000 0000 0000 335f e5fd  .(..........3_..
#                                       ^^^^^^^^^ checksum
#                             ^^^^^^^^^ 4 bytes of zeroes (not checksummed)
#                   ^^^^^^^^^ 4 bytes of zeroes (checksummed)
#         ^^^^^^^^^ 4-byte magic number (checksummed)
```

The footer is the last 16 bytes of which the first 12 bytes must be exactly
`c028 93e8 0000 0000 0000 0000` and the last 4 bytes are the CRC32 checksum of
the whole file _except its last 8 bytes_.

There doesn't seem to be a standard tool to compute and display the CRC32
checksum of a file on Linux, although it's a very widely-used checksum
algorithm. The most portable method I know is to run the relevant data through
`gzip` and then extract the checksum from the footer of the resulting
compressed stream, which can be done without needing to install anything
special if you don't mind burning a bunch of unnecessary CPU for the
compression:

```
$ cat _13.si | head -c-8 | gzip --fast -c | tail -c8 | od -tx4 -N4 -An
 399b3f10
```

There are tools to do this computation too, although they're not usually
installed by default, and there's almost certainly a short program in your
language of choice to do the same thing. Reading the expected checksum from the
last 4 bytes is simpler:

```
$ tail -c4 _13.si | od -tx4 -N4 -An --endian=big
 335fe5fd
```

These outputs don't match so the file is corrupt, which was the problem
reported by the example exception shown above. On a file that isn't corrupt we get matching outputs:

```
$ tail -c16 _13.cfs | xxd
00000000: c028 93e8 0000 0000 0000 0000 0064 fc5d  .(...........d.]
$ cat _13.cfs | head -c-8 | gzip --fast -c | tail -c8 | od -tx4 -N4 -An
 0064fc5d
$ tail -c4 _13.cfs | od -tx4 -N4 -An --endian=big
 0064fc5d
```
