/-
# Goal: Translate between limits over preorders and diagrams

The ultimate goal is to provide some glue between the two parts of mathlib 

## Preorder side:

```
def module.direct_limit {R : Type u} [ring R] 
                        {ι : Type v} [dec_ι : decidable_eq ι] [preorder ι] 
                        (G : ι → Type w) [Π (i : ι), add_comm_group (G i)] 
                        [Π (i : ι), module R (G i)] (f : Π (i j : ι), i ≤ j → (G i →ₗ[R] G j))
```

## Category side:



## Translations: 
-/
import category_theory.limits.cones