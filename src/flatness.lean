/-
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

1. `M` is flat over `R` (according to definition 2)
2. For every injection `N →ₗ N'` of `R`-modules, the map `N ⊗ M →ₗ N' ⊗ M` is injective. 
3. For every idea `I` of `R`, the induced map `I ⊗ M →ₗ M` is injective.
4. `M` is flat over `R` in the Lean sense (d)

## Proof Sketch: 

The proof sketch in the Stacks project goes as follows:

1. **ses_def** implies **ideal_def**. 

    This argument is straightforward, because `I` and `R` fit into the exact sequence 
    `I →ₗ R →ₗ R / I`, and exactness in the middle of `I ⊗ M →ₗ R ⊗ M ≃ₗ M →ₗ (R / I) ⊗ M` 
    implies that the left map is injective.

    New goal: Show **ideal_def** implies **ses_def**

2. Show that in order to prove **ses_def** it is sufficient to prove `_ ⊗ M` preserves injectives.
    
    Given any exact sequence of the form  `N₁ →ₗ N₂ →ₗ N₃`, let `K = ker N₂ →ₗ N₃` 
    and `Q = im N₂ →ₗ N₃`. Then after tensoring with `M` everything fits into a sequence
    `N₁ ⊗ M →ₗ K ⊗ M →ₗ N₂ ⊗ M →ₗ  Q ⊗ M →ₗ N₃ ⊗ M`. Then show that
    
    * The first and third maps are surjective always. 
    * If we show the second and forth maps are injective, then **ses_def** follows. (footnote 1)

    New goal: Given `K →ₗ N` an injective map of `R`-modules, show `K ⊗ M →ₗ N ⊗ M` is injective.

3. Show that in order to prove (2) it is enough to show `_ ⊗ M` preserves injective maps `K →ₗ N`
when `K` is a finite `R`-module. 

    Given an a general `K`, it can be written as a limit of its finite submodules. So in order to
    show that `x : ker (K ⊗ M →ₗ N ⊗ M)` is zero, we can restrict to a finite submodule `K'`
    of `K` that contains `x`.

    New goal: Given `K →ₗ N` an injective map of `R`-modules with `K` finite, show `K ⊗ M →ₗ N ⊗ M`
    is injective.

4. In order to show (3) it suffces to show that `_ ⊗ M` preserves injective maps `K →ₗ N` when both
`K` and `N` are finite `R`-modules.

    Again, `N` can be written as a limit of its finite submodules, which is a directed system
    becuase any two finite submodules are contained in the finite submodule 

    The result then follows by the following [lemma](https://stacks.math.columbia.edu/tag/00D7):
    If `(M i, μ i j)` is a directed system of modules with `M = lim M i` (write `μ i : M i →ₗ M` for
    the associated map) then `x i : M i` maps to zero in `M` via `μ i` if and only if there exists
    a `j ≥ i` such that `μ i j (x i) = 0`. (this lemma also may follow from 
    [something else](https://stacks.math.columbia.edu/tag/00D6))

    New goal: Given `K →ₗ N` an injective map of `R`-modules with `K` and `N` finite, 
    show `K ⊗ M →ₗ N ⊗ M` is injective.

5. In order to show (4) it suffices to show that `_ ⊗ M` preserves injective maps of the form
`L →ₗ ⊕^n R`.

    Because `N` is finite, we can write it as `⊕^n R / L`, and `K = L'/L` for some submodules `L`
    and `L'` of `⊕^n R`. In order to show `K ⊗ M →ₗ N ⊗ M` is injective it suffices to show both
    `L ⊗ M →ₗ ⊕^n M` and `L' ⊗ M →ₗ ⊕^n M` are injective.

    New goal: Given `L →ₗ ⊕^n R` injective, show that `L ⊗ M →ₗ ⊕^n M` is injective. 

6. We now prove (5) by induction on `n`. 

    The `n = 1` case, we are considering submodules `L →ₗ R`, which we can repeat the same argument
    as in (3) to reduce to the case when `L` is a finite submodule (finitely generated ideal), 
    which is precisely **ideal_def**

    For the induction step if we consider the meet of the submodules `L` and `R ⊕ 0^(n-1)` written
    as `L'`, then `L'' = L'/L` is a submodule of `⊕^(n-1) R` and we obtain the diagram

            `L' ⊗ M` -----> `L ⊗ M` -----> `L'' ⊗ M` -----> `0`
              |                 |                |
              |                 |                |
              |                 |                |
              v                 v                v
    `0` ---> `M` ----------> `⊕^n M` -----> `⊕^(n-1) M` ---> `0`

    where the bottom row is obviously exact, the top row is exact as well, and our induction
    hypothesis implies the left and right vertical arrows are injective. Hence the middle arrow
    is injective as well. 

## Todo:

## Progress:

## Where to go from here?:

* Maybe defining `Tor`?

-/
