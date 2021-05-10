# Mechanized Theory of Event Structures

![GitHub Actions][github-actions-badge]

[github-actions-badge]: https://github.com/event-structures/event-struct/workflows/CI/badge.svg

A Coq library of formalized theory of event structures with applications to concurrency semantics.
Includes a theory of prime event structures and 
operational small-step semantics for their incremental construction.

## Description of Files
All files include a more detailed description of their contents.

##### `utilities.v`
Utility lemmas and tactics. Includes `lia` analogue for ssreflect --
`ssrnatlia`, extracted from https://github.com/amahboubi/lia4mathcomp by Assia
Mahboubi.

##### `inhtype.v`
Interface for inhabited type, that is a type with one distinguished inhabitant. 

##### `wftype.v`
Interface for types with well-founded partial order.

##### `ident.v`
Interface for types that can be used as identifiers.
We require the following properties.
1) `ident0` -- first identifier.
2) `fresh : T -> T` -- function that returns a fresh identifier.
3) `forall x, x < fresh x` -- freshness axiom. 
   We require `<` to be well-founded order.  

##### `relations.v`
Theory of computable transitive closure of well-founded relations.

##### `eventstructure.v`
Theory of finite prime event structures.

##### `transitionsystem.v`
Labeled transition system defined on prime event structures.
The transition relation adds a single event to the event structure.

##### `regmachine.v`
Operational small-step semantics for a simple register machine.
