# Experiments with Realizability in Cubical Agda

This repository contains accompanying code for my (upcoming) Bachelor's thesis.

Weak timeline :

Upto November 2023:

- [x] Combinatory Algebras
  - [x] Applicative Structures
  - [x] Feferman structure on an AS
  - [x] Combinatorial completeness
  - [ ] Computation rule for $\lambda*$
  - Combinators
    - [x] Identity, booleans, if-then-else, pairs, projections, B combinator, some Curry numerals
    - [x] Computation rule for pairs 
    - [ ] Fixpoint combinators and primitive recursion combinator
- [x] Category of Assemblies
  - [x] Define assemblies
  - [x] Define the category $\mathsf{Asm}$
  - [x] Cartesian closure and similar structure
    - [x] Binary products
    - [x] Binary coproducts
      - [x] Universal property
    - [x] Equalisers
    - [x] Exponentials
    - [x] Initial and terminal objects
    - [x] Coequalisers (December 2023)

December 2023:

- [ ] $\mathsf{Asm}$ is regular
    - [x] Kernel pairs of morphisms exist
    - [x] Kernel pairs have coequalisers
    - [ ] Regular epics stable under pullback
- [ ] Exact completion
    - [x] Internal equivalence relations of a category
    - [ ] Functional relations
- [ ] Tripos
	- [x] Heyting-valued Predicates
	- [x] $\forall$ and $\exists$ are adjoints
	- [x] Beck-Chevalley condition
	- [ ] Heyting prealgebra structure
	- [ ] Interpret intuitionistic logic

# Code Organisation

- At the highest level, we have combinatory algebra machinery
- Most modules are parameterised by a combinatory algebra `ca : CombinatoryAlgebra A`
- There are modules on the category of assemblies in `Realizability.Assembly`
- Lemmas and stuff relating to the regularity of $\mathsf{Asm}$ is found in `Realizability.Assembly.Regular`
- Tripos modules are to be found in `Realizability.Tripos`

# Writing

There are some notes relating to the project on my [abstract non-sense](https://github.com/rahulc29/abstract-nonsense) repository.

# Build Instructions

You will need Agda >= 2.6.4 and a [custom fork](https://github.com/rahulc29/cubical/tree/rahulc29/realizability) of the Cubical library to build the code.

The custom fork has a few additional definitions in the category theory modules. I will hopefully integrate them into the Cubical library.

