# Goal:

Prove the equivalence of a pair of definitions for **flat modules**.

## Definition 1 (ideal_def):

The definition of a *flat module implemented in Lean is:

Let `R` be a commutative ring, and `M` and `R`-module. The module is *flat* if for all finitely
generated ideals `I` of `R`, the canonical map `I ⊗ M →ₗ M` is injective. 

## Definition 2 (ses_def):

The goal definition is that given in the Stacks project <https://stacks.math.columbia.edu/tag/00HB>:

An `R`-module `M` is called *flat* if when `N₁ →ₗ N₂ →ₗ N₃` is an exact sequence of R-modules, the
induced sequence obtained by tensoring `N₁ ⊗ M →ₗ N₂ ⊗ M →ₗ N₃ ⊗ M` is exact.

## Main Theorem:

The main theorem of this Lean document is that **ideal_def** and **ses_def** are equivalent. 
This has as a consequence the more general [theorem](https://stacks.math.columbia.edu/tag/00HD):

Let `M` be an `R`-module. TFAE:

1. `M` is flat over `R` (according to **ses_def**)
2. For every injection `N →ₗ N'` of `R`-modules, the map `N ⊗ M →ₗ N' ⊗ M` is injective. 
3. For every idea `I` of `R`, the induced map `I ⊗ M →ₗ M` is injective.
4. `M` is flat over `R` in the Lean sense (**ideal_def**)
