---
layout: post
title:  "Dependency matrices"
date:   2016-11-20 19:09:09 +0000
---

For small systems, a simple "boxes and arrows" diagram is often sufficient
to show the structure of dependencies between components.

![Boxes and arrows]({{ "/assets/2016-11-20/01-this-does-not-scale.png" | relative_url }})

This does not scale. For larger systems, it is much better to draw a
_dependency matrix_.

![Dependency matrix]({{ "/assets/2016-11-20/02-do-this-instead.png" | relative_url }})

Each row and column represents a component (in the same order) and the cells
are shaded to show the existence of relationships between them.

# Patterns

A big advantage of this view is that certain kinds of dependency pattern
can be identified by eye. Here are some examples.

![A full column]({{ "/assets/2016-11-20/03-full-column.png" | relative_url }})

A full column indicates a component that depends on everything.

![A full row]({{ "/assets/2016-11-20/04-full-row.png" | relative_url }})

A full row indicates a component on which everything depends.

![A triangular matrix]({{ "/assets/2016-11-20/05-triangular.png" | relative_url }})

A triangular matrix indicates that the system is well-layered, with the order
of the rows and columns indicating the order of the layers.

![Square]({{ "/assets/2016-11-20/06-square.png" | relative_url }})

A filled-in square indicates a dependency cycle. More generally, filled-in
cells above the diagonal indicate layering violations, which might arise due to
dependency cycles.

# Manipulations

There are some natural manipulations that you can do to navigate a dependency
matrix.

![Grouping and combining]({{ "/assets/2016-11-20/07-group-and-combine.png" | relative_url }})

Sometimes it makes sense to group subcomponents together into larger
components, either by highlighting the boundaries (e.g. the blue lines around
the rows and columns for C and D) or even by combining them together.

![Weights]({{ "/assets/2016-11-20/08-add-weights.png" | relative_url }})

Sometimes you can add information about the strengths of the relationships between
components by adding numbers and colours to the cells.

![Reorder rows and columns]({{ "/assets/2016-11-20/09-reorder-rows-and-cols.png" | relative_url }})

Sometimes the components need to be reordered to, e.g., fix layering violations.
It is important that the orders of the rows and columns are kept synchronised.
If the matrix cannot be made triangular by this kind of reordering then it
contains dependency cycles.

# A typical system

![Typical system]({{ "/assets/2016-11-20/10-typical-system.png" | relative_url }})

Typical systems often have dependency structures a little like this. At the top
is an "application" layer which ties all the components together, and at the
bottom is a layer of "utilities" or a "library" that is used by all the
components. In between is a set of cohesive components with heavy
intra-component dependencies but typically only light inter-component
dependencies.

Sometimes it is necessary to have intra-component dependency cycles, but often
inter-component dependency cycles indicate design problems.


[This whole post is available in one image.]({{ "/assets/2016-11-20/dependency-matrices.png" | relative_url }})


