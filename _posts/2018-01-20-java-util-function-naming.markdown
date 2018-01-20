---
layout: post
title:  "The names of Java's functional interfaces"
date:   2018-01-20 19:09:09 +0000
---

Java 8 introduced [lambda
expressions](https://docs.oracle.com/javase/tutorial/java/javaOO/lambdaexpressions.html).
A lambda expression is a very lightweight syntax for an anonymous class that
implements an interface with a single method, a.k.a. a closure, or simply a
function.

There are various situations where you need to know the name of the interface
that you're implementing. Although there's a certain pattern to the names of
the interfaces defined in
[`java.util.function`](https://docs.oracle.com/javase/8/docs/api/java/util/function/package-summary.html),
it's not totally clear to me, and there's a couple of exceptions that break the
uniformity, so this is a note-to-self about the naming convention for future
reference.

## Reference Types

It's simplest to start with functions that take and return instances of
reference types, as this sets up most of the basic pattern:

|               | `void`            | `R`
| `f()`         | `Runnable`        | `Supplier<R>`
| `f(T t)`      | `Consumer<T>`     | `Function<T,R>`
| `f(T t, U u)` | `BiConsumer<T,U>` | `BiFunction<T,U,R>`
{: .java-type-table }

Here, and throughout the rest of this note, the function's return type is shown
in the column headings and each row heading shows the rest of the function's
declaration.

There are two special cases that don't fit so neatly into this table:
`Function<T,T>` is typically spelled `UnaryOperator<T>`, and
`BiFunction<T,T,T>` is spelled `BinaryOperator<T>`.

## All types

The full story is more complicated because we also need support for types like
`double`, `int`, `long` and `boolean` which aren't reference types, and we'd
rather avoid having to box and unbox them when using lambda expressions. Here
is most of the story:

|                | `void`            | `R`                 | `double`                  | `int`                  | `long`                  | `boolean`
| `f()`          | `Runnable`        | `Supplier<R>`       | `DoubleSupplier`          | `IntSupplier`          | `LongSupplier`          | `BooleanSupplier`
| `f(T t)`       | `Consumer<T>`     | `Function<T,R>`     | `ToDoubleFunction<T>`     | `ToIntFunction<T>`     | `ToLongFunction<T>`     | `Predicate<T>`
| `f(T t, U u)`  | `BiConsumer<T,U>` | `BiFunction<T,U,R>` | `ToDoubleBiFunction<T,U>` | `ToIntBiFunction<T,U>` | `ToLongBiFunction<T,U>` | `BiPredicate<T,U>`
| `f(double d)`  | `DoubleConsumer`  | `DoubleFunction<R>` | `DoubleUnaryOperator`     | `DoubleToIntFunction`  | `DoubleToLongFunction`  | `DoublePredicate`
| `f(int i)`     | `IntConsumer`     | `IntFunction<R>`    | `IntToDoubleFunction`     | `IntUnaryOperator`     | `IntToLongFunction`     | `IntPredicate`
| `f(long l)`    | `LongConsumer`    | `LongFunction<R>`   | `LongToDoubleFunction`    | `LongToIntFunction`    | `LongUnaryOperator`     | `LongPredicate`
{: .java-type-table }

## Extras

As well as `UnaryOperator<T>` and `BinaryOperator<T>` there's the following
extras that don't fit into this table:

```
void   f(T       t, double  d) // ObjDoubleConsumer<T>
void   f(T       t, long    l) // ObjLongConsumer<T>
void   f(T       t, int     i) // ObjIntConsumer<T>
double f(double da, double db) // DoubleBinaryOperator
long   f(long   la, long   lb) // LongBinaryOperator
int    f(int    ia, int    ib) // IntBinaryOperator
```


