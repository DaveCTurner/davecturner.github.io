---
layout: post
title:  "Testing storage for corruption bugs"
date:   2020-12-26
---

If you are suffering from more than your fair share of [silent corruption]({%
post_url 2020-12-23-lucene-checksums %}) then you might have a buggy storage
system. Here's a couple of tools that exercise your storage with workloads that
are simple and transparent whilst also being quite effective at triggering
corruption bugs.

A successful run of either of these tools does not prove the absence of bugs,
of course, nor does it say anything about corruptions that only occur when the
data has been sitting on disk for an extended period of time. However a failure
definitely indicates that your storage is not working as required. It's always
worth running tests like these when commissioning a new system.

## Corruption on power loss

System calls like Linux's `fsync()` are supposed to guarantee that some data
has genuinely been written to durable storage and will still be there even if
power is lost and subsequently restored. Durable writes can be expensive, so
it's pretty common to encounter systems which are configured to ignore
`fsync()` calls which gives the impression of better performance in benchmarks.
Ignoring `fsync()` calls is obviously very dangerous and will lead to data loss
or corruption in a power outage. It's also a very subtle misconfiguration since
you probably can't tell whether `fsync()` is really working or not without a
genuine power outage. In particular if you're testing VMs it's unlikely to be
enough to "power down" the VM and keep the host running: you really need to
abruptly remove power from the host to find bugs of this nature.

The venerable [`diskchecker.pl`
script](https://brad.livejournal.com/2116715.html) is pretty good at shaking
out cases where `fsync()` is not working as it's supposed to.

This script does quite a bit of I/O and involves pulling power cords out of
things while they're running so it's not a great idea to run it on systems
while they're in production.

## Write-time corruption

The excellent [`stress-ng` tool](https://kernel.ubuntu.com/~cking/stress-ng/)
recently merged a
[patch](https://github.com/ColinIanKing/stress-ng/commit/ecaf4f655d38dfd771a9f6a29bb5f1af64c8aa36)
which improves its ability to detect corruption introduced at write time. I
suggest invoking it something like this:

```
$ sudo stress-ng --hdd 32 \
                 --hdd-opts wr-seq,rd-rnd \
                 --hdd-write-size 8k \
                 --hdd-bytes 30g \
                 --temp-path $MOUNT_POINT \
                 --verify
```

Some notes on the options:

`--hdd 32`: This sets the number of concurrent processes writing to disk. I
suggest setting it higher than the number of cores to force some
context-switching which may help surface more bugs.

`--hdd-opts wr-seq,rd-rnd`: This says to write the file sequentially from start
to finish and then perform random reads during verification. This most closely
matches Lucene's access pattern, although Lucene may [use `mmap()` for reads
instead of `read()` and
friends](https://dzone.com/articles/use-lucene’s-mmapdirectory). It's also
reasonable to use `wr-seq,rd-seq`.

`--hdd-write-size 8k`: Lucene writes in 8kB chunks by default.

`--hdd-bytes 30g`: This says how large a file each process should write. The
total size of all the files written must of course not exceed the space on the
filesystem, but should be large enough that the reads cannot all be served from
pagecache. In this example there are 32 processes each writing 30GB of data,
which adds up to about 1TB. You can also try dropping pagecache every now and
then during the test with `echo 3 | sudo tee /proc/sys/vm/drop_caches` .

`--temp-path $MOUNT_POINT`: This says where to create the files used for the
test, which must of course be on the filesystem you suspect to be buggy.

`--verify`: This says to check that the data read is what was written, which is
required to detect cases of silent corruption. Without this option the test
will still go through the motions of reading and writing data but only reports
a failure if any of the I/O actually fails.

This is a pretty aggressive test so it's not a good idea to run it on systems
while they're in production. By default it will run for 24 hours which I think
is reasonable.

Make sure that you're using a new enough version of `stress-ng` too, versions
0.12.0 and older did not test things so thoroughly.
