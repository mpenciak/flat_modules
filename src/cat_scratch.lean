import category_theory.limits.cones
import finite_submodules
import category_theory.category.preorder
import algebra.category.Module.monoidal


/-
I should be able to copy some of the below when I eventually get to it
-/
-- universes u v

-- variables (R : Type u) [ring R] (M : Type v) [add_comm_group M] [module R M]
-- [decidable_eq (fin_submodule R M)] -- Need this for `fg_shape` and I'm not sure I can get rid of it

-- -- I don't think this is an actual solution, you don't need this for the lattice of submodules
-- -- noncomputable instance : decidable_eq (fin_submodule R M) := λX Y, classical.dec (X = Y)

-- -- example : preorder.small_category (fin_submodule R M)) ⥤ Module.{v} R := sorry

-- variables {R M}

-- def fg_shape : (fin_submodule R M) ⥤ Module R := { obj := λN, Module.of R N,
--   map := λ _ _ f, Module.of_hom (fin_submodule.le_inclusion $ plift.down $ ulift.down f),
--   map_id' := λ _, by ext; refl,
--   map_comp' := λ _ _ _ _ _, by ext; refl }

/-
In this section I translate between a general direct limit over a directed system into the
corresponding statement in terms of colimits in `Module R`
-/
section categorical_glue

universes u v w u₁

variables {R : Type u} [ring R]
variables {ι : Type v} [decidable_eq ι] [preorder ι]
variables (G : ι → Type w) [Π i, add_comm_group (G i)] [Π i, module R (G i)]
variables (f : Π i j, i ≤ j → G i →ₗ[R] G j) [directed_system G (λ i j h, f i j h)]

#check module.directed_system.map_self f 

def associated_functor : ι ⥤ Module R := { obj := λi, Module.of R (G i),
  map := λi j k, Module.of_hom (f i j k.down.down),
  map_id' :=
  begin
    intro i,
    ext,
    have H := module.directed_system.map_self f i x (by refl), 
    unfold Module.of_hom,
    rw H,
    refl,
  end,
  map_comp' := 
  begin
    intros i j k g h, 
    ext,
    unfold Module.of_hom,
    simp,
    have H := module.directed_system.map_map f g.down.down h.down.down x,
    exact H.symm,
  end }

/-
Show this guy satisfies the universal property! (probably have the lemmas in the direct_limits.lean file)
-/

#check Module.of R (module.direct_limit G f)

end categorical_glue