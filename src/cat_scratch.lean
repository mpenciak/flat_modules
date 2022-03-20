import category_theory.limits.cones
import finite_submodules
import category_theory.category.preorder
import algebra.category.Module.monoidal

section silly_lemma

universes u v

variables {R : Type u} [ring R]
variables {M N P : Type v} [add_comm_group M] [add_comm_group N] [add_comm_group P] 
[module R M] [module R N] [module R P]
variables (f : M →ₗ[R] N) (g : N →ₗ[R] P) 

lemma silly_lemma : Module.of_hom f ≫ Module.of_hom g = Module.of_hom (g ∘ₗ f) := by refl

end silly_lemma
/-
I should be able to copy some of the below when I eventually get to it, but ideally the general result is done first and then I copy it
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

universes u v

variables {R : Type u} [ring R]
variables {ι : Type v} [decidable_eq ι] [preorder ι]
variables (G : ι → Type v) [Π i, add_comm_group (G i)] [Π i, module R (G i)]
variables (f : Π i j, i ≤ j → G i →ₗ[R] G j) [directed_system G (λ i j h, f i j h)]

variables (i j : ι) (k : i ≤ j)

lemma of_f_comp (i j : ι) (hij : i ≤ j) : 
module.direct_limit.of R ι G f j ∘ₗ (f i j hij) = module.direct_limit.of R ι G f i :=
begin
  ext,
  simp only [linear_map.coe_comp, function.comp_app, module.direct_limit.of_f],
end

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

def def1 : category_theory.limits.cocone (associated_functor G f) := { X := Module.of R (module.direct_limit G f),
  ι := { app := λ i, Module.of_hom $ module.direct_limit.of R ι G f i,
  naturality' := begin
    intros i j k,
    dunfold associated_functor,
    rw [silly_lemma, of_f_comp],
    ext,
    refl,
  end } } 

example : category_theory.limits.is_colimit (def1 G f) := { desc := λP, begin
  apply Module.of_hom,
  fapply module.direct_limit.lift,
  intro i,
  exact P.ι.app i,
  intros i j hij x,
  sorry
end,
  fac' := _,
  uniq' := _ }
 
end categorical_glue