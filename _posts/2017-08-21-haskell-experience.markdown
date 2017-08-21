---
layout: post
title:  "Haskell experience report"
date:   2017-08-21 14:02:09 +0000
---

TLDR: [Tracsis is currently hiring](https://www.tracsis.com/careers) so if you
are in the Leeds area and want join a Haskell development team then [get in
touch](mailto:recruitment@tracsis.com).

I've been working as a software developer for [Tracsis
plc](https://www.tracsis.com) since 2010. For a team of ~15 developers we use a
pretty broad selection of technologies and languages of various vintages,
including

* C# for most of our Windows desktop software
* C++ and Fortran for the more mathematical end of things
* Haskell and a bit of Java for webapp back-ends
* Javascript for webapp front-ends
* A lot of Bash, and a few bits of Python and Ruby for gluing it all together

Our web applications are used in planning departments and control rooms in the
rail and bus industries, primarily in the UK but with some overseas users too.
Although it's unlikely that bugs or downtime would directly lead to physical
harm to people or property there's certainly the scope for fairly large
financial losses if things go wrong in the control room, so we have to have a
fairly strong focus on correctness and reliability.

A few years ago I started to investigate Haskell, amongst other things, as an
alternative to using C# and/or Java for our webapp back-ends. I tried writing
some small things in it: first some internal tools and then a few back-end
network services. I quite liked it. Then I tried training some of my peers up
in it and that seemed to go ok too, so we eventually started using it in anger.
Our Haskell codebase is currently ~60kLOC of production code and ~40kLOC of
other code (mainly tests and generated code).

[Michael Snoyman asked for some articles about using Haskell in the real
world](https://www.snoyman.com/blog/2017/04/haskell-success-stories) so here is
mine. Incidentally, [Tracsis is currently
hiring](https://www.tracsis.com/careers) so if you are in the Leeds area and
want to join a Haskell development team then [get in
touch](mailto:recruitment@tracsis.com).

It's hard to declare this sort of thing as an unqualified success, but we
certainly seem to be heading in the right direction. We've shipped a fairly
substantial and complicated product that solves some tricky real-world
problems. We've brought a decent fraction of the team up to speed without any
major issues, and the onboarding process is developing and settling down
nicely.

My gut feeling (i.e. without a controlled experiment) is that there have been
somewhat fewer business-logic bugs than I'd have expected from a similar
project done in C#, and essentially none to do with inconsistent or missing
data (like null-pointer dereferences) and concurrency.

In contrast, I think we're currently moving no faster than if we were still
working in C#, perhaps a little slower, partly because there's some kind of
conservation-of-complexity law that means that fewer bugs costs more thinking
harder up front, and partly because most of the developers started with the
language less than a year ago so we're still accelerating.

This is the team's first major product that runs in a browser, on Linux, and on
the cloud, so it's fair to expect that a substantial fraction of the drag we've
experienced has been unrelated to the change of language. A brief look at our
Slack history shows that we discuss platform issues significantly more than
anything specifically about the language.

As the product matures and accumulates more customers, and as the team gets
more familiar with the platform and language, I expect the acceleration to
continue. In support of this, a couple of articles note that [maintenance
consumes 40%-80% of the cost of
software](https://dl.acm.org/citation.cfm?id=626281) and [maintenance is where
Haskell
shines](https://www.fpcomplete.com/blog/2016/12/software-project-maintenance-is-where-haskell-shines).
I've certainly done some refactorings of bits of logic that would have been
much more daunting without the support of the compiler, the strength of the
type system and the reasoning benefits of immutability.

### Survey results

The rest of this article is based on an informal survey of my peers and I'm
going to try and be as impartial as I can with their answers. The survey
questions were:

* How long have you been using Haskell?
* How long have you been using other programming languages?
* What did you think of Haskell when you first started using it?
* Were there any online resources you found useful when starting out?
* Can you identify any things that helped or hindered the initial phases of
  learning?
* Were there any insights you had where things suddenly became clearer?
* How long did it take before you felt productive with Haskell?
* What do you think are strengths of Haskell for development on a team,
  compared with the other platforms we use?
* Similarly, what are some of Haskell's weaknesses compared with the other
  platforms we use?
* Have you done any tasks where you feel Haskell's features have particularly
  helped/obstructed?
* What kinds of projects would you consider using Haskell for in the future?
  What kinds would you not?
* Anything else you'd like to say?

Five of the team responded, including myself. There were another three
developers working on this product who declined to respond. I'm **D** and the
other four developers are **A**, **B**, **C** and **E** below.

### How long have you been using Haskell?

Two of us (**D**, **B**) first met Haskell at university (5-15 years ago)
although neither of us have used it consistently since then. **D** has been
using it professionally for about 5 years and **B** for around four months.
The other three first met it at Tracsis when starting to contribute to this
project (**E**: three years, **A**: 18 months and **C** 3 months ago).

### How long have you been using other programming languages?

**D**: BBC-BASIC in the 1980s, C/C++/Java/SQL in the 1990s, Perl/PHP/other
scripting stuff in the 2000s, C# since 2009. All sorts of other things along
the way too.

**B**: C++ since 2000. A few years of C# since joining Tracsis too.

**C**: 3½ years of C#.

**A**: 2 years of C# and Javascript plus Lua, Ruby.

**E**: 5 years of C# and some Java before that.

### What did you think of Haskell when you first started using it?

I personally thought it was a bit of a theoretical toy, but to be fair I met it
at university along with a lot of other theoretical toys. **B** was
enthusiastic about it:
> Holy wow, it's basically written maths!

**A**, **C** and **E** all had mixed-to-negative experiences, largely due to
how different it was from what they were expecting. This is typical:
> In a word: bizarre. I had ideas in my head of what 'enterprise programming'
> was at the time and Haskell was not it. I'd never seen anything like it. [...]
> Both Haskell and functional programming in general were completely new to me.
and
> I had none of the concepts available in my head.

It's fair to say that I didn't put a lot of effort into softening any culture
shock, and this was compounded by the fact that they were also leaping from
desktop to web software and from Windows to Linux.

### Were there any online resources you found useful when starting out?

I personally don't remember any in particular, although I did buy the Real
World Haskell book which was useful at the time but is very dated now. I
pointed everyone else at [LYAH](http://learnyouahaskell.com/chapters) which was
good for a basic grounding in syntax and elementary concepts, but generally was
found to take a bit long to get to anything more useful. LYAH plus a task to
accomplish on an existing codebase seemed to work better. Other answers
included

* Google,
* [Hoogle](https://www.haskell.org/hoogle/),
* [r/haskell](https://www.reddit.com/r/haskell/), and
* the [Yesod documentation](https://www.yesodweb.com/).

Also mentioned was that starting from a Yesod scaffold was useful for two
reasons:

* it let you write some logic straight away without thinking about the
  plumbing, and
* if you're so inclined, you can go and look at the behind-the-scenes plumbing
  and learn new things from it.

### Can you identify any things that helped or hindered the initial phases of learning?

The main thing that apparently helped was having other approachable and
knowledgeable Haskellers around ("essential"). Initially, that was me, but
there's definitely a lot of other knowledge-sharing going on around me now.
Also helpful were:

* learning to read every line of compiler errors. The compiler errors aren't as
  bad as C++ (which has a habit of yielding a thousand lines of errors because
of a missing semicolon) but they can still go on for a while and contain a lot
of unfamiliar words and not many actionable suggestions. This is definitely
getting better in later GHC versions.

* GHCi was useful for playing around.

A number of things hindered people:

* LYAH took too long to get to something that established programmers could
  find useful, after covering the basic syntax and type system.

* Unclear or absent documentation.

* Excessive abstraction. It's definitely easier to understand things when the
  types are more specific than perhaps they theoretically could be. Haddocks
are most useful when the types in the docs line up with the types of the
expressions you have in your code.

### Were there any insights you had where things suddenly became clearer?

From my experience of training other developers up, the first big epiphany
occurs when you learn the importance of being able to do basic
typechecking/unification in your head. When working on an established codebase
it actually works quite well to just try plausible-looking changes at random
until you get one that compiles, but this technique is a source of considerable
frustration and mystification. The technique that seems to solve this is to
break an expression down completely, write down all the types from the
Haddocks, then unify all the type variables to calculate the overall type.
After doing this a few times (and explaining type errors similarly) the
importance of being able to do this automatically seems to sink in.

All the different ways you can combine functions (`.`, `$`, `<$>`, `>>=`, etc.)
is a source of considerable confusion. More generally, the unfamiliar syntax
(parenthesis-free function application, switching from infix to prefix calls)
was also a sticking point.

Reading, and understanding, error messages was also mentioned as a minor
epiphany, as was the natural desire to try and find analogues in OO languages
for various concepts that don't map well onto OO.

Two mentioned the "monadic revelation", and specifically described this as the
realisation that there's nothing really special about monads except the `do`
notation.

### How long did it take before you felt productive with Haskell?

**B** and **C**, being relatively new to writing production Haskell, modestly
claim not yet to be fully productive although they are both already working
independently. The rest of us answered in the range 4-6 months.

### What do you think are strengths of Haskell for development on a team, compared with the other platforms we use?

Everyone mentioned the stronger type-safety (vs C#) in some form.

I personally consider sum types (and case splitting) to be incredibly powerful
for the kinds of enterprise applications that we work on. In business there are
frequently things that are best represented as a choice between various
different cases, and it's really hard to express this safely without sum types.
This has definitely caught serious bugs that would have been missed had we been
working in C#. The use of explicit `Maybe` types rather than nullable
references is similarly powerful.

**E** also gave a hat tip to sum types, and the benefits of immutability in
terms of more robust reasoning about your code.

**A** found it easier to start a .NET project than a Haskell one "because
Haskell encourages you to have clearer high-level picture of the final program
before you begin." To be fair, he also admitted that "I suspect my opinion on
that will change over time."

**C** mentioned ease of refactoring but also noted that she hadn't realised
this benefit yet. She's also starting to really like the succinctness of it.

### Similarly, what are some of Haskell's weaknesses compared with the other platforms we use?

Slow compiles and the lack of a professional-grade IDE featured a lot in the
answers to this. Visual Studio plus Resharper is an incredibly productive
environment to work on a decent sized codebase, and the compile-edit-run cycle
in VS is significantly shorter than we have managed to achieve in our Haskell
codebase.

The editors in use include Vim, Notepad++ and Sublime Text, with various
plugins to add IDE-like functionality, but plugins are fiddly to set up and
none come close to the VS experience.

Since our production environment is Linux but our desktops are all
Windows-based there's more friction than if we were using Windows for the whole
stack.

A number of answers mentioned the lack of a debugger. I'm not a fan of
debugging-to-fix-bugs but debugging-to-learn-how-the-program-runs is very
powerful and everyone has had to learn other ways to investigate runtime
behaviour, particularly when Haskell's runtime behaviour is so unlike that of
more imperative languages. This experience could be charitably described as
"character building". The VS integrated profiler and various tools for
inspecting the contents of memory are sorely missed.

**E** mentioned that he found `base` to be restrictively small compared with
C#'s standard library, needing dozens of extra libraries to get anything useful
done. He also mentioned that "the reaction to Haskell is certainly not uniform"
which I think is a euphemism for the fact that it's still seen as quite
daunting to start working on this project.

### Have you done any tasks where you feel Haskell's features have particularly helped/obstructed?

The first big task I did was parsing a really weird file format using
[Parsec](https://hackage.haskell.org/package/parsec) which was mindblowingly
easy to get right; **B** has also had good experiences with parsing things.

I also find it very pleasant to write network services (HTTP or otherwise)
thanks to things like [Yesod](https://www.yesodweb.com/) and
[Servant](https://hackage.haskell.org/package/servant) as well as lower-level
libraries like [conduit](https://hackage.haskell.org/package/conduit).

In contrast I find lazy-by-default to be more and more of an obstruction.
Laziness is occasionally really useful, but most of our code wants things to be
strict, so we've put a bunch of effort into making things explicitly strict and
still things slip through the cracks sometimes.

**A** finds monad transformer stacks to be daunting compared with the ease with
which you can pass state around in C#.

**E** and I both find [STM](https://hackage.haskell.org/package/stm) and
[async](https://hackage.haskell.org/package/async) to be extremely powerful
abstractions for dealing with concurrency and hiding the complexity from other
developers. We have quite a bit of concurrency in this project and it's amazing
how little you have to think about it when working elsewhere in the codebase.

In contrast we've also both found writing quick scripts to involve too much
ceremony with compilation, imports, packages, types etc. We're aware that you
can do [scripting in
Haskell](https://www.fpcomplete.com/blog/2016/11/scripting-in-haskell) but we
haven't found it as slick as advertised. It comes into its own whenever you've
got a program that lasts more than a few hours-to-days, but the payback horizon
is quite distant.

### What kinds of projects would you consider using Haskell for in the future?  What kinds would you not?

I'm sold for most tasks, except Windows desktop apps (unless they were
HTTP-based) and things involving sharing a process with a JVM.

Everyone else said they'd use it for (at least) network services and some of
them mentioned things like
* complicated data processing
* handling failures
* parsing
* CLI applications

Games, desktop applications and quick scripts all got a mention as things that
they'd probably look elsewhere for.

### Anything else you'd like to say?

In their own words.

**A** says:

> Overall I like Haskell and I feel that it opened my eyes to just how
> different languages can be.  I am concerned about the future prospects of the
> language and the programming style. With Haskell being my first 'professional
> language', I feel it's necessary to make sure I'm not limiting myself to
> functional languages for the rest of my career.

**E** says:

> The choice of programming language is somewhat subjective - there are
> probably lots of languages that we could write our products in, with varying
> effort needed for deployment, maintenance and so on. Haskell has some great
> technical points and plenty of flaws, but ultimately we haven't made anything
> that we couldn't in another language.  However for me personally, Haskell is
> a good fit for the way I think about problems and I find it easy to express
> pretty much everything I need to in it. To expand upon the last point, the
> things I want to express can nearly always be expressed using basic data
> types and so on - I rarely touch type level magic. I also don't really know
> much about lenses, I just use them in a rather monkey-see-monkey-do fashion.
> There is an awful lot of other complicated stuff in the world of Haskell that
> I don't understand, but I manage to get by OK and produce software that
> works.

**C** says:

> Any negative points I've made are more a reflection of my own lack of comfort
> with Haskell really.  The more I'm seeing/writing of it, the more I'm
> starting to appreciate it [...] It feels like it's growing increasingly
> popular as a language, but that at the moment we're definitely in the early
> adopters category, and I think that means that there's less support and
> resources available for getting started.  I think initially I may have been
> guilty of thinking "Haskell is hard", where what I really should have been
> thinking is "starting to work on something new, with a new language, new OS,
> new DB, new architecture" is hard!
