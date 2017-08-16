---
layout: post
title:  "Scenes from Paxos"
date:   2016-11-15 19:09:09 +0000
---

Some sketches of things that happen in an implementation of a distributed
consensus algorithm.

# Steady state

Most of the time there's an ongoing conversation that looks like this.

![Steady state]({{ "/assets/2016-11-15/01-most-of-the-time.png" | relative_url }})

Sometimes there's no clients making requests, but the system's conversation
continues.

![Nothing to do]({{ "/assets/2016-11-15/02-nothing-to-do.png" | relative_url }})

# When nodes die

The system continues to run as long as more than half of the nodes are alive.

![A follower dies]({{ "/assets/2016-11-15/04-follower-dies.png" | relative_url }})

This is OK since two of the three nodes are still alive.

![Too many followers die]({{ "/assets/2016-11-15/05-too-many-followers-die.png" | relative_url }})

This is not OK since only one of the three nodes is alive.  In particular, here
the leader can't tell whether the other two nodes are dead or if it's just been
disconnected from them and they're still operating.

Nodes that are disconnected from the leader may attempt to become leader
themselves. However followers should be faithful to their current leader while
they remain connected to it.

![Faithful followers]({{ "/assets/2016-11-15/03-faithful-followers.png" | relative_url }})

When the leader dies...

![Scenes from Paxos]({{ "/assets/2016-11-15/06-when-the-leader-dies.png" | relative_url }})

... clever things happen to make sure that all the nodes carry on agreeing with
each other and nothing is lost in the handover.

[This whole post is available in one image.]({{ "/assets/2016-11-15/scenes-from-paxos.png" | relative_url }})


