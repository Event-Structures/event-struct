# Mechanized Theory of Event Structures

![GitHub Actions][github-actions-badge]

[github-actions-badge]: https://github.com/event-structures/event-struct/workflows/CI/badge.svg

A Coq library with the formalized theory of event structures and non-interleaving concurrency.  
Currently includes a theory of the following semantic domains and their relationships:

- labelled transition systems
- pomset languages 
- prime event structures

Also features several applications of the theory. 

- Formalization of several basic consistency models 
  parametrized by the abstract datatype, defined according to the paper 
   ["Causal Consistency: Beyond Memory" by Matthieu Perrin, Achour Mostefaoui, Claude Jard (PPoPP 2016)](https://core.ac.uk/download/pdf/52993336.pdf)

- Incremental construction of prime event structures 
  build from program-order and reads-from relations.

The library is under active development.
Therefore the API is unstable and might be subject to further modifications.

## Description of Files

For a more detailed description, see the documentation in the headers of source files. 

- `common` - common definitions, lemmas, and notations  

    - `utils.v` - miscellaneous 
    - `rel.v` - additional facts about decidable binary relations
    - `relalg.v` - variuos additions to relation-algebra package
    - `order.v` - various additions to porder theory from mathcomp 
    - `wftype.v` - interface for types with well-founded partial order
    - `inhtype.v` - interface for inhabited type, that is a type with one distinguished inhabitant
    - `ident.v` - interface for types that can be used as identifiers
    - `monoid.v` - theory of monoids and partial monoids
    - `rewriting_system.v` - a piece of rewriting systems theory

- `concur` - semantic domains for concurrency

    - `lts.v` - labelled transition systems and (linear) traces
    - `lposet.v` - labelled partially ordered sets
    - `pomset.v` - pomsets as quotient types
    - `pomset_lts.v` - a connection between pomset languages and labelled transition systems
    - `prime_eventstruct.v` - prime event structures 
    - `porf_eventstruct.v` - prime event structure built from program-order and reads-from relations
    - `transitionsystem.v` - incremental construction of event structure

- `lang` - syntax and semantics of concurrent languages and systems

    - `relaxed.v` - relaxed memory models parametrized by an abstract datatype  
    - `sharedmem.v` - shared memory abstract datatype
    - `regmachine.v` - simple parallel register machine with shared memory
