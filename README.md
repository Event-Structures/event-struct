# Mechanized Theory of Event Structures

![GitHub Actions][github-actions-badge]

[github-actions-badge]: https://github.com/event-structures/event-struct/workflows/CI/badge.svg

A Coq library of formalized theory of event structures with applications to concurrency semantics.
Includes a theory of prime event structures and 
operational small-step semantics for their incremental construction.

## Description of Files

All files include a more detailed description of their contents.

- `common` - common definitions, lemmas, and notations  

    - `utils.v` - miscellaneous 
    - `relalg.v` - variuos additions to relation-algebra package
    - `ssrnatlia.v` - lia analogue for ssreflect
    - `wftype.v` - interface for types with well-founded partial order
    - `inhtype.v` - interface for inhabited type, that is a type with one distinguished inhabitant
    - `ident.v` - interface for types that can be used as identifiers
    - `rel.v` - additional facts about decidable binary relations
    - `monoid.v` - theory of monoids and partial monoids
    - `monad.v` - additional facts about monads
    - `rewriting_system.v` - some bits of the theory of rewrite systems

- `concur` - semantic domains for concurrency

    - `lposet.v` - labelled partially ordered sets
    - `pomset.v` - pomsets languages
    - `prime_eventstruct.v` - prime event structures 
    - `porf_eventstruct.v` - prime event structure built from program-order and reads-from relations
    - `transitionsystem.v` - incremental construction of event structure

- `lang` - syntax and semantics of concurrent languages and systems

    - `regmachine.v` - simple parallel register machine with shared memory
