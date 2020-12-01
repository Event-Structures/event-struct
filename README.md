# Event Structures Formalization

![GitHub Actions][github-actions-badge]

[github-actions-badge]: https://github.com/volodeyka/event-struct/workflows/CI/badge.svg

A library of formalized event structure theory applied to weak-memory models.
Includes notion and theory of execution event structures, labeled transition
system on execution event structures, big-step semantics for simple
register machine, and well-founded relations theory.

## Files in poject
All files include description of its constituents.

### `utilities.v`
Some extra lemmas and tactics to make our work more convenient.
Includes `lia` analouge for ssreflect -- `slia`.
Based on: https://github.com/amahboubi/lia4mathcomp

### `inhtype.v`
Interface for inhabited type

### `wftype.v`
Interface for types with well-founded order

### `ident.v`
Interface for types that can be used as identifiers.
In other words we, require:
1) `ident0` -- first identifier
2) `<` -- well-founded order
3) `fresh : T -> T` -- function that returns fresh identifier

### `relations.v`
Theory of well-founded orders closures

### `rfsfun.v`
Theory of functions on a finite subset of some type `E` that can be extended
on whole type `E` and embedded in fixed relation. 

### `eventstructure.v`
Theory of finite execution event structures

### `transitionsystem.v`
Labeled transition system on execution event structures

### `regmachine.v`
Big-step semantics for simple register machine