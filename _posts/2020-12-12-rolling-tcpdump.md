---
layout: post
title:  "Rolling packet captures"
date:   2020-12-12
---

I sometimes have a need to collect a packet capture for an extended period of
time. On a busy host this can generate enough data that it needs some special
handling. In particular it's useful to roll over to a new file every now and
then, and to offload the completed files somewhere else so they don't fill up
the disk.

This week I discovered that `tcpdump` has options `-C`, `-G` and `-z` that let
me do exactly that, rendering obsolete my janky `bash` script that tried to do
the same:

```
    -C size
        The file size (in multiples of 1e6 bytes) at which to roll over.
    -G age
        The file age (in seconds) at which to roll over.
    -z command
        Runs `command <filename>` on completion of a file.
```

The [man page](https://www.tcpdump.org/manpages/tcpdump.1.html) gives more
details including a (somewhat vague) description of how `tcpdump` names files
when using these options. I will be using something like this:

```
sudo tcpdump -G600 -C1000 -zgzip -wcapture-%s.pcap -i eth0 tcp port 12345 ...
#                 adjust these bits according to taste ^^^^^^^^^^^^^^^^^^^^^^^
```

This says to roll over every 10 minutes, and every 1GB, and to run `gzip` to
compress the file on rollover. The first file in every 10-minute period is
named something like `capture-1607780545.pcap`, and if that file hits 1GB then
subsequent files are named `capture-1607780545.pcap1`,
`capture-1607780545.pcap2`, etc. The lack of leading zeroes is a bit of a pain:
the eleventh file in each period is called `capture-1607780545.pcap10` which
tends to sort between `capture-1607780545.pcap1` and
`capture-1607780545.pcap2`. At the end of the ten-minute period it starts over
again at `capture-1607781145.pcap`.

Note that `tcpdump` will spawn `command` each time it rolls over to a new file.
It does not itself limit how many of them are running concurrently, so it's
your responsibility to make sure that the system can keep up with the traffic.
Make sure to give `tcpdump` a suitably restrictive
[filter](https://www.tcpdump.org/manpages/pcap-filter.7.html). If you don't,
you'll hit some [limit](https://github.com/lorin/awesome-limits) or other
eventually, which probably won't go well. If the system is under particularly
heavy load then you can alternatively use `tcpdump -w-` to send the capture to
`stdout` and then pipe it somewhere else that does have the capacity for
further processing. If you do that, make sure to exclude the piped-elsewhere
data from the packets you're capturing.

The `command` is
[executed](https://github.com/the-tcpdump-group/tcpdump/blob/a0e19c0caef95fdcbace674de91e7c181d3bc866/tcpdump.c#L2806)
using `execlp(3)` so it searches your `$PATH` for the executable like a shell,
but you cannot pass any other arguments. Note also that the command above runs
`tcpdump` as `root` which means that `command` runs as `root` too.  The man
page suggests writing a script to do some more advanced processing but you may
not want (or be permitted) to run a more complicated script as `root`. If you'd
rather do most of the work as a different user then you can have `tcpdump` run
`gzip` and then use `inotifywait` to receive a notification each time a
compressed capture file is ready for further action:

```
inotifywait -e delete . -m --format %f \
    | sed -ue '/gz$/d;s/$/.gz/' \
    | xargs -n1 ./done.sh
```

This works because `gzip` deletes the original file once the compressed file is
complete which triggers the notification. The `inotifywait` command writes out
the names of files that are deleted from the current directory, the `sed`
command adds a `.gz` to the end of each filename, and then the `xargs -n1` runs
the named script on each compressed capture file.

The `done.sh` script can do whatever you need, often offloading the data
elsewhere and then removing the original file:

```
#!/bin/bash

echo Processing $1
aws s3 cp $1 s3://mybucket/captures/$HOSTNAME/$1
rm -vf $1
```

Invoking `xargs` like this will process the files in turn, with no parallelism,
so if the `done.sh` script can't keep up with the traffic then a backlog of
compressed capture files might build up. Consider running these captures in
their own filesystem to bound the disk space they can consume, or else adjust
`done.sh` to simply drop the given file with no additional processing if disk
usage is building up.

There's a couple of feedback gotchas here. Firstly, deleting the compressed
file triggers `inotifywait` again, which is why compressed files are skipped by
the `/gz$/d` in the `sed` script. Secondly, if you're sending the captured
traffic back out over the network then there's a risk that `tcpdump` will
capture it all over again. Make sure you set up an appropriate filter in the
original capture to avoid that.
