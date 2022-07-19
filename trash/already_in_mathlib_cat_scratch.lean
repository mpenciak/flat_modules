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


/-
The plan for this section is to prove that `lim (G i ⊗ M)` = `(lim G i) ⊗ M`. 
This should be obvious, given the corresponding fact for colimits.

Strictly speaking, I'm not sure the section above is totally necessary. We already have that any 
module is a direct limit of its f.g. submodules, and we know direct limits are colimits so we
should be able to push the whole flat modules argument through in the language of category theory,
but this is a helpful lemma to tie the different approaches together.
-/
section tensor_and_direct_limit

open_locale tensor_product

universes u v w

variables {R : Type u} [comm_ring R]
variables {M : Type v} [add_comm_group M] [module R M]
-- See comment below on `direct_lim_is_colim` about the `is_directed` and `nonempty` assumptions
variables {ι : Type v} [decidable_eq ι] [preorder ι] [is_directed ι (≤)] [nonempty ι] 
variables (G : ι → Type v) [Π i, add_comm_group (G i)] [Π i, module R (G i)]
variables (f : Π i j, i ≤ j → G i →ₗ[R] G j) [directed_system G (λ i j h, f i j h)]

instance tensor_with_const : directed_system (λ (i : ι), G i ⊗[R] M)
    (λ (i j : ι) (h : i ≤ j),
       ((λ (i j : ι) (hij : i ≤ j), id (tensor_product.map (f i j hij) linear_map.id)) i j h)):= 
       { map_self := 
       begin intros i x hi, simp, 
       have H : f i i hi = (linear_map.id : G i →ₗ[R] G i),
       {
        ext x,
        have H2 := directed_system.map_self (λi j hij, f i j hij) i,
        simp at H2,
        have H3 := H2 x,
        rw H3,
        refl,
       },
       rw H,
       simp,   
       end,
  map_map := 
  begin
    intros i j k hij hjk x,
    simp,
    have H : (tensor_product.map (f j k hjk) linear_map.id).comp (tensor_product.map (f i j hij) linear_map.id) = (tensor_product.map (f i k (le_trans hij hjk)) linear_map.id),
    begin
      rw ←tensor_product.map_comp,
      have H2 : (f j k hjk).comp (f i j hij) = (f i k (le_trans hij hjk)),
      begin
        ext y,
        have H3 := directed_system.map_map (λi j hij, f i j hij) hij hjk,
        simp at H3,
        specialize H3 y,
        exact H3,
      end,
      rw H2,
      refl,
    end,
    rw ←H,
    refl,
  end }

#check associated_functor (λ(i : ι), (G i) ⊗[R] M) (λi j hij, begin dsimp, have H := f i j hij, have H2 := @linear_map.id R M _ _ _, exact tensor_product.map (H) H2, end)

#check associated_functor G f

end tensor_and_direct_limit
/-
Next steps: 
* That should be it in terms of administrative stuff before I can start working on flat modules!
-/


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

