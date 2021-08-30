---
layout: post
title:  "Tracking down a seven-year-old segfault"
date:   2021-08-30
---

Back in August 2014 a user reported they [couldn't run
Elasticsearch](https://discuss.elastic.co/t/segfault-in-ffi-prep-closure-loc/19227):
it would immediately crash with a segmentation fault. Elasticsearch is almost
entirely written in Java which as a managed language is supposed to protect us
from low-level issues like segmentation faults. The "almost" in the previous
sentence is the problem: Elasticsearch calls out to native code in a few
places, and it was one of these places that was triggering the crash.

Elasticsearch makes its native calls using
[JNA](https://github.com/java-native-access/jna) which is a deeply magical
library that makes it easy for Java code to call into libraries written in C.
There was definitely a suspicion that this was something to do with JNA, but
the investigation fizzled out before it got very far.

Then in May 2016 Github user [**@fxh**](https://github.com/fxh) reported [the
same thing on Github](https://github.com/elastic/elasticsearch/issues/18272).
The investigation got further this time: the issue seemed to manifest only when
SELinux was enabled, and seemed to be related to whether temporary files were
permitted to contain executable code. Forbidding temporary executables is a
security measure: anyone can write to `/tmp` so it's possible to attack a
system by writing a nefarious executable to `/tmp` and then tricking someone
more privileged into running it.

In this context "executable" means more than just programs that you can run
from the command line. Modern processors [distinguish code from
data](https://en.wikipedia.org/wiki/NX_bit) at a very low level, with a flag on
each page of memory that determines whether the data it contains can ever be
interpreted as instructions that the CPU will execute. If `/tmp` is mounted
with the `noexec` option then every page that's associated with a file under
`/tmp` will have the no-execute bit set. This forbids fully-fledged programs
and dynamically-linked libraries and also, crucially, any other kind of
memory-mapped executable page that is backed by a file in `/tmp`.

Some of JNA's deep magic works by dynamically generating a temporary library
(wrapping around the C library) into which the Java code can call. It's
sometimes possible to generate code dynamically in pages that aren't backed by
a file, but for security reasons the system might also proscribe pages from
being both writeable and executable, and obviously we need write access to the
memory in which we're generating the code. The usual solution seems to be to
write the code into a file and then use something like `mmap()` to load it
again into read-only-but-executable pages. In order to do this we need some
temporary space that isn't mounted `noexec`.

However the crash wasn't _just_ caused by having `/tmp` mounted with the
`noexec` option: if you do that then you get a [different
error](https://github.com/elastic/elasticsearch/issues/18272#issuecomment-224140253)
and not a segmentation fault. And anyway you can tell JNA to create its
temporary library in a different location by setting the `java.io.tmpdir` or
`jna.tmpdir` system properties, which is a sensible workaround for when
executables are forbidden in the default temporary directory. This doesn't
always fix the problem.

At this point it became hard to make further progress: there was no
sufficiently well-locked-down SELinux system on which to analyse things further
and it's not a configuration that gets a lot of testing. We verified that the
problem really wasn't in Elasticsearch code itself and
[concluded](https://github.com/elastic/elasticsearch/issues/18272#issuecomment-234687922)
that it must be a problematic and untested interaction between SELinux and JNA
in the hope that a future version of SELinux and/or JNA would fix it.

A few months later user [**@vineet01**](https://github.com/vineet01) reported
that they were having the same problem and that they [fixed
it](https://github.com/elastic/elasticsearch/issues/18272#issuecomment-294321118)
by creating a home directory for the user as which Elasticsearch was running.
They hypothesised that this was because the JVM wanted to create a
usage-tracking file in the home directory. More recently user
[**@cyamal1b4**](https://github.com/cyamal1b4) reported the [same
fix](https://github.com/elastic/elasticsearch/issues/73309) and blamed the same
usage-tracking file, although neither user gave an explanation of how a failure
to write this file might lead to a segmentation fault in JNA-related code.

Over the years many users have reported this same crash. It still definitely
exists on very locked-down systems. It always appears to be related to
temporary executable files and is generally fixed by fiddling with environment
variables/system properties/permissions until the segfault goes away. The
trouble is that the users that have these very locked-down systems are also the
users that can provide the least amount of debugging context, and that struggle
to make changes to permissions or other environmental settings. It's often
quite a long process to find the right combination of settings that fix it, and
all these cases consume much time from many engineers. At least the crash
reliably happens at every startup. It'd be much worse if it were
nondeterministic or took a long time to manifest, but Elasticsearch really
should not be failing with a segmentation fault like this, and we really
shouldn't be spending this much time helping users solve the same issue over
and over again.

Recently I decided it was worth taking another look to see if I could work out
what was at the bottom of it.

## JVM error log analysis

**@fxh** included the JVM error log file in the [original Github
issue](https://github.com/elastic/elasticsearch/issues/18272) which contains a
fantastic amount of detail about the state of the JVM at the time of the crash.
Here's an excerpt of the important bits:

```
#
# A fatal error has been detected by the Java Runtime Environment:
#
#  SIGSEGV (0xb) at pc=0x00007f424226f40a, pid=28216, tid=139922878629632
#
# JRE version: Java(TM) SE Runtime Environment (7.0_75-b13) (build 1.7.0_75-b13)
# Java VM: Java HotSpot(TM) 64-Bit Server VM (24.75-b04 mixed mode linux-amd64 compressed oops)
# Problematic frame:
# C  [jna4948368637624641726.tmp+0x1240a]  ffi_prep_closure_loc+0x1a
#

Registers:
RAX=0x00007f424226f8c2, RBX=0x00007f425579ed48, RCX=0x00007f424c44a7b0, RDX=0x00007f4242264590
RSP=0x00007f425579eae0, RBP=0x00007f425579eae0, RSI=0x00007f424c44a7d0, RDI=0x0000000000000000
R8 =0x00007f425007ae43, R9 =0x0000000000000002, R10=0x00007f425579e870, R11=0x00007f424226f3f0
R12=0x0000000000000000, R13=0x0000000000000008, R14=0x00007f424c44a7b0, R15=0x0000000000000004
RIP=0x00007f424226f40a, EFLAGS=0x0000000000010246, CSGSFS=0x0000000000000033, ERR=0x0000000000000006
TRAPNO=0x000000000000000e

Instructions: (pc=0x00007f424226f40a)
0x00007f424226f3ea:   66 90 66 66 66 90 8b 06 55 41 b9 02 00 00 00 48
0x00007f424226f3fa:   89 e5 ff c8 83 f8 01 77 44 48 8b 05 c6 49 10 00
0x00007f424226f40a:   66 c7 07 49 bb 4c 89 47 0c 66 c7 47 0a 49 ba 48
0x00007f424226f41a:   89 47 02 8b 46 1c 48 89 77 18 48 89 57 20 48 89

Stack: [0x00007f42556a0000,0x00007f42557a1000],  sp=0x00007f425579eae0,  free space=1018k
Native frames: (J=compiled Java code, j=interpreted, Vv=VM code, C=native code)
C  [jna4948368637624641726.tmp+0x1240a]  ffi_prep_closure_loc+0x1a
C  [jna4948368637624641726.tmp+0xd4dd]  Java_com_sun_jna_Native_registerMethod+0x45d
j  com.sun.jna.Native.registerMethod(Ljava/lang/Class;Ljava/lang/String;Ljava/lang/String;[I[J[JIJJLjava/lang/Class;JIZ[Lcom/sun/jna/ToNativeConverter;Lcom/sun/jna/FromNativeConverter;Ljava/lang/String;)J+0
...
j  org.elasticsearch.bootstrap.JNACLibrary.<clinit>()V+45
...
j  org.elasticsearch.bootstrap.JNANatives.definitelyRunningAsRoot()Z+8
```

The header tells us that Elasticsearch received a fatal `SIGSEGV` signal while
executing the instruction at `ffi_prep_closure_loc+0x1a`, i.e. the one which
starts `0x1a` bytes into the function `ffi_prep_closure_loc`. This signal
usually means the program attempted to dereference a pointer that doesn't point
to a valid memory location. The stack trace shows that Elasticsearch was in the
process of executing
[`JNANatives#definitelyRunningAsRoot()`](https://github.com/elastic/elasticsearch/blob/36683a4581a8fc2f108701d92af2e4d527e56d02/server/src/main/java/org/elasticsearch/bootstrap/JNANatives.java#L154-L164)
which looks like this:

```
static boolean definitelyRunningAsRoot() {
    if (Constants.WINDOWS) {
        return false; // don't know
    }
    try {
        return JNACLibrary.geteuid() == 0;
    } catch (UnsatisfiedLinkError e) {
        // this will have already been logged by Kernel32Library, no need to repeat it
        return false;
    }
}
```

This method is ultimately trying to call the C library's `geteuid()` function,
and it's the first time we've touched the `JNACLibrary` class so we're running
the static constructor (`<clinit>`) which is setting up all the JNA magic.

The dump of instruction memory is useful too: the instruction pointer is at
`0x00007f424226f40a` and as mentioned above this is only `0x1a` bytes into
executing `ffi_prep_closure_loc`, which means the function starts at address
`0x00007f424226f3f0` and hence we can disassemble all the instructions in this
function leading up to the one that caused the crash:

```
0:  8b 06                   mov    eax,DWORD PTR [rsi]
2:  55                      push   rbp
3:  41 b9 02 00 00 00       mov    r9d,0x2
9:  48 89 e5                mov    rbp,rsp
c:  ff c8                   dec    eax
e:  83 f8 01                cmp    eax,0x1
11: 77 44                   ja     0x57
13: 48 8b 05 c6 49 10 00    mov    rax,QWORD PTR [rip+0x1049c6]        # 0x1049e0
1a: 66 c7 07 49 bb          mov    WORD PTR [rdi],0xbb49
```

The `SIGSEGV` happened on the last line which is trying to write something to
the address to which register `RDI` points, and the crash dump also tells us
that `RDI` is currently `0x0000000000000000` which is the null pointer and
definitely not a valid address. This function hasn't tried to write to `RDI`
before it gets to the faulting instruction, which means it must have been
expecting the caller to set `RDI` to a valid address.

If a function takes arguments then the caller is responsible for putting them
in appropriate places so that the callee can find them. A [_calling
convention_](https://en.wikipedia.org/wiki/Calling_convention) is an agreement
between caller and callee which defines (amongst other things) where the
arguments to a function are when the function is called. Even on a particular
processor architecture there are [many possible calling
conventions](https://en.wikipedia.org/wiki/X86_calling_conventions) but in
practice on a 64-bit system running Linux `RDI` will contain the first argument
to the function. We can see from the stack dump that the caller is JNA's
`Java_com_sun_jna_Native_registerMethod` function, and [here's how it calls
`ffi_prep_closure_loc`](https://github.com/java-native-access/jna/blob/030411b909d5dfd249b1df09a7f24c44babcae64/native/dispatch.c#L3468-L3469):

```
closure = ffi_closure_alloc(sizeof(ffi_closure), &code);
status = ffi_prep_closure_loc(closure, closure_cif, dispatch_direct, data, code);
```

The first argument is the `closure` which is returned from `ffi_closure_alloc`.
The [docs for this
function](https://github.com/libffi/libffi/blob/ee1263f7d43bd29b15fc72c4d9520a824e8004df/doc/libffi.texi#L809-L813)
say it allocates and returns a chunk of memory and doesn't suggest that it
might return `NULL`, but if we look at [its
source](https://github.com/libffi/libffi/blob/ee1263f7d43bd29b15fc72c4d9520a824e8004df/src/closures.c#L958)
it's clear that it does return `NULL` to indicate various kinds of failure.

Hurrah, we worked it out: the segmentation fault is because JNA isn't checking
for a failure to allocate this closure, which turns out to be a [known
issue](https://github.com/java-native-access/jna/issues/1107) which should be a
[small thing to fix](https://github.com/java-native-access/jna/pull/1378).

## But wait, there's more

Although it's definitely an improvement to throw a Java exception on this
failure instead of a segmentation fault, this doesn't actually solve anything.
Elasticsearch will still fail to start up even with this fix: it'll report a
more descriptive message and shut down more gracefully but still users will
need to fiddle around with permissions and ask for help to get Elasticsearch up
and running. Ideally we need to make `ffi_closure_alloc` succeed or at least to
understand better why it's failing.

> Note that from here on this investigation takes a couple of leaps of faith:
> I've only read the code, I don't have a locked-down system on which to run
> experiments to verify any of this.

There are a number of different implementations of `ffi_closure_alloc`
depending on operating system and selected by `#ifdef` pragmas but they all
ultimately need to allocate some memory into which some machine code can be
written: like JNA, `libffi` does some of its magic with dynamically-generated
executable code.

The allocation mechanism is kinda complicated: there's actually a [whole
separate implementation of `malloc()` and
friends](https://github.com/libffi/libffi/blob/ee1263f7d43bd29b15fc72c4d9520a824e8004df/src/dlmalloc.c)
which relies on `mmap()` to actually acquire memory from the operating system,
but then `mmap()` is
[redefined](https://github.com/libffi/libffi/blob/ee1263f7d43bd29b15fc72c4d9520a824e8004df/src/closures.c#L541-L542)
to call a custom implementation which does its best to allocate _executable_
pages using different techniques until it finds one which succeeds. Fortunately
there are some [helpful comments about how this works on
Linux](https://github.com/libffi/libffi/blob/ee1263f7d43bd29b15fc72c4d9520a824e8004df/src/closures.c#L124-L151):

```
#if !FFI_MMAP_EXEC_WRIT && !FFI_EXEC_TRAMPOLINE_TABLE
# if __linux__ && !defined(__ANDROID__)
/* This macro indicates it may be forbidden to map anonymous memory
   with both write and execute permission.  Code compiled when this
   option is defined will attempt to map such pages once, but if it
   fails, it falls back to creating a temporary file in a writable and
   executable filesystem and mapping pages from it into separate
   locations in the virtual memory space, one location writable and
   another executable.  */
#  define FFI_MMAP_EXEC_WRIT 1
#  define HAVE_MNTENT 1
# endif
...
#if FFI_MMAP_EXEC_WRIT && !defined FFI_MMAP_EXEC_SELINUX
# if defined(__linux__) && !defined(__ANDROID__)
/* When defined to 1 check for SELinux and if SELinux is active,
   don't attempt PROT_EXEC|PROT_WRITE mapping at all, as that
   might cause audit messages.  */
#  define FFI_MMAP_EXEC_SELINUX 1
# endif
#endif
```

That tells us that `libffi` will sometimes create temporary executable files,
and it will always create them when running under SELinux.  It's important to
note that this is completely independent of the fact that JNA creates temporary
executable files: `libffi` is a language-independent library for calling
foreign functions so it doesn't know anything about Java and therefore doesn't
have access to the Java system properties `java.io.tmpdir` and `jna.tmpdir`
which control where JNA does its work. Instead, on Linux `libffi` tries to
create its temporary executable files [in various places in the following order
of
preference](https://github.com/libffi/libffi/blob/ee1263f7d43bd29b15fc72c4d9520a824e8004df/src/closures.c#L702-L707):

- `$LIBFFI_TMPDIR`
- `$TMPDIR`
- `/tmp`
- `/var/tmp`
- `/dev/shm`
- `$HOME`

Elasticsearch doesn't set any of these environment variables specially, so even
if JNA is creating its temporary files somewhere that permits executables it's
entirely possible that `libffi` does not. This also helpfully resolves the
mystery of why giving the `elasticsearch` user a writeable home directory seems
to make the problem go away: when nothing else works, `libffi` will try writing
to `$HOME` which typically does permit executable code as long as it exists.

Finally, this leads us to a proper fix: we don't need to give the
`elasticsearch` user a whole home directory, instead we should be able to [set
`$LIBFFI_TMPDIR`](https://github.com/elastic/elasticsearch/issues/77014) to
point to the same directory that JNA uses.
