import ring_theory.flat
import ring_theory.noetherian
import algebra.direct_limit
import linear_algebra.isomorphisms
import tactic
import category_theory.limits.cones
import finite_submodules
import category_theory.category.preorder
import algebra.category.Module.monoidal
import linear_algebra.tensor_product
import linear_algebra.finsupp
import algebra.group

section basic_properties

universes u v

open function (injective surjective comp_app)

lemma equiv_injective (R : Type u) [ring R] (M N : Type v) [add_comm_group M] [add_comm_group N] [module R M] [module R N]
(f : M →ₗ[R] N) : injective f ↔ ∀x, f x = 0 → x = 0 :=
begin
split,
{
  intros h x hx,
  rw ←map_zero f at hx,
  exact h hx,
},
intro h,
intros x y hxy,
specialize h (x - y),
rw map_sub at h,
rw [sub_eq_zero, sub_eq_zero] at h,
exact h hxy
end

lemma middle_injective (R : Type u) [ring R] 
(M₁ M₂ M₃ : Type v) [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂] [add_comm_group M₃] [module R M₃]
(N₁ N₂ N₃ : Type v) [add_comm_group N₁] [module R N₁] [add_comm_group N₂] [module R N₂] [add_comm_group N₃] [module R N₃]
(f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (f' : N₁ →ₗ[R] N₂) (g' : N₂ →ₗ[R] N₃) 
(k₁ : M₁ →ₗ[R] N₁) (k₂ : M₂ →ₗ[R] N₂)  (k₃ : M₃ →ₗ[R] N₃) (hk₁ : injective k₁) (hk₃ : injective k₃)
(hf : injective f) (hf' : injective f') (hg : surjective g) (hg' : surjective g')
(hfk : k₂ ∘ f = f' ∘ k₁) (hgk : k₃ ∘ g = g' ∘ k₂)
(hex : f.range = g.ker) (hex' : f'.range = g'.ker)
: injective k₂ := 
begin
rw equiv_injective,
intros x hx,
have H1 : (g' ∘ k₂) x = 0 :=by simp only [hx, comp_app, map_zero],
rw ←hgk at H1,
have H2 : g x = 0 := by {rw[←map_zero k₃, comp_app] at H1; rw hk₃ H1},
have H3 : x ∈ g.ker := by simp only [H2, linear_map.mem_ker],
rw ←hex at H3,
rw linear_map.mem_range at H3,
cases H3 with y hy,
rw ←hy at hx,
rw ←comp_app k₂ f y at hx,
rw hfk at hx,
rw comp_app at hx,
rw ←map_zero f' at hx,
have H4 := hf' hx,
rw ←map_zero k₁ at H4,
have H5 := hk₁ H4,
rw H5 at hy,
rw map_zero at hy,
exact hy.symm
end

open linear_map (ltensor)

lemma tensor_right_exact (R : Type) [comm_ring R] (M M' M'' : Type) 
[add_comm_group M] [add_comm_group M'] [add_comm_group M''] [module R M] [module R M'] [module R M'']
(f : M →ₗ[R] M') (g : M' →ₗ[R] M'') (hfg : f.range = g.ker) (hf : injective f) (hg : surjective g)
(N : Type) [add_comm_group N] [module R N]
: surjective (ltensor N g) ∧ (ltensor N f).range = (ltensor N g).ker := 
begin
split,
{
  intro x,
  apply x.induction_on, -- Needed to switch over to simple tensors
  use 0,
  simp,
  intros x y,
  specialize hg y,
  cases hg with z hz,
  use x ⊗ₜ[R] z,
  simp only [hz, linear_map.ltensor_tmul],
  intros y z hy hz,
  cases hy with a ha,
  cases hz with b hb,
  use (a + b),
  simp only [ha, hb, map_add]
},
{
  ext,
  split,
  {
    intro h,
    rw linear_map.mem_range at h,
    cases h with z hz,
    rw linear_map.mem_ker,
    rw ←hz,
    rw ←comp_app (ltensor N g) (ltensor N f) z,
    sorry
    -- have H : (⇑(ltensor N g) ∘ ⇑(ltensor N f)) = ⇑ ((ltensor N g) ∘ (ltensor N f)) := sorry
    -- change ⇑((ltensor N g) ∘ (ltensor N f)) z = 0,
    -- rw ←linear_map.ltensor_comp N g f,
  },
  {
    apply x.induction_on,
    intro h,
    use 0,
    simp,
    intros y z hyz,
    rw linear_map.mem_ker at hyz,
    rw linear_map.mem_range,
    rw linear_map.ltensor_tmul at hyz,
    
    -- intro h,

    -- apply x.induction_on,

  },
}
end

#check linear_map.ltensor_comp 

end basic_properties