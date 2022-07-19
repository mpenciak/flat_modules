/-
# Goal: Translate between limits over preorders and diagrams

The ultimate goal is to provide some glue between the two parts of mathlib that deal with direct
limits: the preorder defined `module.direct_limit` and the category theoretic 
`category_theory.cocone.is_colimit` 

## Preorder side:

```
def module.direct_limit {R : Type u} [ring R] 
                        {ι : Type v} [dec_ι : decidable_eq ι] [preorder ι] 
                        (G : ι → Type w) [Π (i : ι), add_comm_group (G i)] 
                        [Π (i : ι), module R (G i)] (f : Π (i j : ι), i ≤ j → (G i →ₗ[R] G j))
```

## Category side:

```
structure is_colimit (t : cocone F) :=
    (desc  : Π (s : cocone F), t.X ⟶ s.X)
    (fac'  : ∀ (s : cocone F) (j : J), t.ι.app j ≫ desc s = s.ι.app j . obviously)
    (uniq' : ∀ (s : cocone F) (m : t.X ⟶ s.X) (w : ∀ j : J, t.ι.app j ≫ m = s.ι.app j),
             m = desc s . obviously)
```
-/
import category_theory.limits.cones
import finite_submodules
import category_theory.category.preorder
import algebra.category.Module.monoidal
import linear_algebra.tensor_product

/-
For lack of a better name, I've included a few lemmas that helped translate between compositions of
functions interspersed with `Module.of_hom`. These are all simple, but needed for some key rewrites.
-/
section silly_lemmas

universes u v w

variables {R : Type u} [ring R]
variables {M N P : Type v} [add_comm_group M] [add_comm_group N] [add_comm_group P] 
[module R M] [module R N] [module R P]
variables (f : M →ₗ[R] N) (g : N →ₗ[R] P) 

lemma module_hom_ext (x : M) : Module.of_hom g ((Module.of_hom f) x) = g (f x) := by refl

lemma module_hom_comp : Module.of_hom f ≫ Module.of_hom g = Module.of_hom (g ∘ₗ f) := by refl

lemma module_hom_app (x : M) : Module.of_hom g (f x) = g (f x) := by refl

end silly_lemmas

/-
In this section I translate between a general direct limit over a directed system into the
corresponding statement in terms of colimits in `Module R`
-/
section categorical_glue

/-
Note about universes: There's that some tricky stuff that I think is related to the Zulip chat 
conversation about universes and direct limits. You would want `R : Type u`, `ι : Type v`, and 
`G : ι → Type w` to be totally generic, but for our purposes it suffices for `G : ι → Type v` as
we're interested in the `fin_submodule` case. But using some of that `ulift` stuff that's being
talked about, it should be possible to make the results in this section more general. 
-/
universes u v

variables {R : Type u} [ring R]
-- See comment below on `direct_lim_is_colim` about the `is_directed` and `nonempty` assumptions
variables {ι : Type v} [decidable_eq ι] [preorder ι] [is_directed ι (≤)] [nonempty ι] 
variables (G : ι → Type v) [Π i, add_comm_group (G i)] [Π i, module R (G i)]
variables (f : Π i j, i ≤ j → G i →ₗ[R] G j) [directed_system G (λ i j h, f i j h)]

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

def direct_lim_as_cocone : category_theory.limits.cocone (associated_functor G f) := { 
  X := Module.of R (module.direct_limit G f),
  ι := { app := λ i, Module.of_hom $ module.direct_limit.of R ι G f i,
  naturality' := begin
    intros i j k,
    dunfold associated_functor,
    rw [module_hom_comp, of_f_comp],
    ext,
    refl,
    apply_instance, -- Weird behaviour when I added universes
    apply_instance, -- Same here
  end } } 

set_option trace.ext true

/-
The proof here isn't as general as I think it should be, in particular I need to have `nonempty ι`
and `directed_system ι (≤)` instances. 

Also `ext` wants to apply Waaaaaay too many ext lemmas, so I needed to restrict them in both cases.
Actually, I noticed there wasn't an `ext` lemma for `module.direct_limit` similiar to the `ext` 
lemma for cones and cocones. This may be a nice thing to have.

Also `ext` when left unspecified took a really long time on `submodule.linear_map_qext` and 
`direct_sum.linear_map_ext`.
-/
def direct_lim_is_colim : category_theory.limits.is_colimit (direct_lim_as_cocone G f) := { 
  desc := λP, Module.of_hom $ module.direct_limit.lift R ι G f (λi, P.ι.app i) 
          -- Proof the triangle in the cocone commutes
          (λ _ _ hij x, category_theory.congr_hom (P.ι.naturality hij.hom) x),
  fac' := begin
    intros s j,
    dunfold direct_lim_as_cocone,
    ext1,
    simp only [Module.coe_comp, function.comp_app],
    rw [module_hom_ext, module.direct_limit.lift_of]
  end,                                                         
  uniq' :=
  begin
    intros C φ h,
    apply linear_map.ext,
    intro x,
    dunfold direct_lim_as_cocone at h,
    dunfold direct_lim_as_cocone at x,
    have z := module.direct_limit.exists_of x,
    cases z with i hi,
    cases hi with z hz,
    rw ←hz,
    dsimp,
    rw module_hom_app,
    rw module.direct_limit.lift_of,
    specialize h i, 
    exact category_theory.congr_hom h z,
  end,
  }

end categorical_glue