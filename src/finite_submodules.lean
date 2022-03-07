import ring_theory.noetherian
import algebra.direct_limit
import tactic

set_option pp.beta true
set_option trace.simplify.rewrite true

/-
Establish some basic properties about the order structure on the type of finitely
generated submodules. Big takeaways are the definition of `fin_submodule`, establishing
a couple instances `semilattice_sup (fin_submodule R M)` and `is_directed (fin_submodule R M) (≤)`
-/
section basic_properties

universes u v

variables (R : Type u) (M : Type v) [ring R] [add_comm_group M] [module R M]

def fin_submodule : Type v := { N : submodule R M // N.fg }

namespace fin_submodule

/-
Not sure I need any of this actually...
-/
-- @[protected, instance] def set_like : set_like (fin_submodule R M) M := { coe := λ⟨N, _⟩, N,
--   coe_injective' := λ ⟨N, hN⟩ ⟨P, hP⟩ hNP, by congr; exact set_like.ext' hNP }

-- variable N : fin_submodule R M

-- lemma add_mem {x y : M} (h₁ : x ∈ N) (h₂ : y ∈ N) : x + y ∈ N :=
-- begin
-- cases N,
-- apply submodule.add_mem, exact h₁, exact h₂,
-- end

-- instance has_add' : has_add N := { add := λx y, ⟨x + y, add_mem R M N (by simp) (by simp)⟩ }

-- instance has_zero' : has_zero N := { zero := begin cases N, exact ⟨0, by apply submodule.zero_mem'⟩ end }

-- instance has_smul' : has_scalar R N := { smul := λr m, ⟨r • m, begin end⟩ }

-- @[instance] def associated_comm_group (N : fin_submodule R M) : add_comm_monoid N := {
--   add_assoc := _,
--   zero_add := _,
--   add_zero := _,
--   nsmul := _,
--   nsmul_zero' := _,
--   nsmul_succ' := _,
--   add_comm := _,
--   ..has_add' R M N,
--   ..has_zero' R M N}

-- @[simp] def associated_submodule (N : fin_submodule R M) : submodule R M := N.1

-- instance module (N : fin_submodule R M) : module R N := { smul := _,
--   one_smul := _,
--   mul_smul := _,
--   smul_add := _,
--   smul_zero := _,
--   add_smul := _,
--   zero_smul := _ }

instance have_sup : has_sup (fin_submodule R M) := 
{ sup := λ⟨N, hN⟩ ⟨P, hP⟩, ⟨N ⊔ P, submodule.fg_sup hN hP⟩ }

instance have_le : has_le (fin_submodule R M) := { le := λ⟨N, _⟩ ⟨P, _⟩, N ≤ P }

instance have_lt : has_lt (fin_submodule R M) := { lt := λ⟨N, _⟩ ⟨P, _⟩, N ≤ P ∧ ¬ P ≤ N }

instance have_partial_order : partial_order (fin_submodule R M) := 
{ le_refl := λ⟨N, _⟩, partial_order.le_refl N,
  le_trans := λ⟨N, _⟩ ⟨O, _⟩ ⟨P, _⟩, partial_order.le_trans N O P,
  lt_iff_le_not_le := 
  begin
    rintros ⟨N, hN⟩ ⟨O, hO⟩,
    split,
    { rintros ⟨h1, h2⟩,
      exact ⟨h1, h2⟩, },
    { rintros ⟨h1, h2⟩,
      exact ⟨h1, h2⟩ },
  end,
  le_antisymm := 
  begin
    rintros ⟨N, hN⟩ ⟨O, hO⟩ h1 h2,
    change N ≤ O  at h1,
    change O ≤ N at h2,
    congr, 
    exact partial_order.le_antisymm N O h1 h2,
  end,
  ..have_le R M,
  ..have_lt R M }

instance have_semilattice_sup : semilattice_sup (fin_submodule R M) := 
{ le_sup_left := 
  begin
    rintros ⟨N, hN⟩ ⟨O, hO⟩,
    exact complete_lattice.le_sup_left N O,
  end,
  le_sup_right := 
  begin
    rintros ⟨N, hN⟩ ⟨O, hO⟩,
    exact complete_lattice.le_sup_right N O,
  end,
  sup_le := 
  begin
    rintros ⟨N, hN⟩ ⟨O, hO⟩ ⟨P, hP⟩ h1 h2,
    change N ≤ P at h1,
    change O ≤ P at h2,
    change N ⊔ O ≤ P,
    rw sup_le_iff,
    exact ⟨h1, h2⟩,
  end,
  .. have_partial_order R M,
  .. have_sup R M }

instance have_directed : is_directed (fin_submodule R M) (≤) := { directed := 
begin
  rintros ⟨N, hN⟩ ⟨P, hP⟩,
  use N ⊔ P,
  exact submodule.fg_sup hN hP,
  split,
  change N ≤ N ⊔ P,
  exact le_sup_left,
  change P ≤ N ⊔ P,
  exact le_sup_right,
end }


-- Might have to worry about this at some point too?
-- instance have_something : nonempty (fin_submodule R M) := _

end fin_submodule
end basic_properties

/-
Goal: Prove some stuff about direct limits more generally. Big takeaways are `equiv_with_top`
which shows a direct limit over an `order_top ι` is linearly equivalent with `G ⊤`, and 
`injective_of_direct_limit` which should be helpful in the main goal
-/
section direct_limits

universes u v w u₁

open submodule
open function (injective)
open module.direct_limit

variables {R : Type u} [ring R]
variables {ι : Type v}
variables [decidable_eq ι] [preorder ι]
variables (G : ι → Type w)
variables [Π i, add_comm_group (G i)] [Π i, module R (G i)]
variables (f : Π i j, i ≤ j → G i →ₗ[R] G j) [directed_system G (λ i j h, f i j h)]

namespace module.direct_limit

def map_to_top [order_top ι] : module.direct_limit G f →ₗ[R] G ⊤ :=
lift R ι G f (λi, f i ⊤ (le_top)) (λi j hij x, module.directed_system.map_map f hij le_top x)

/-
This lemma obviously doesn't work for any non-fg module, but it didn't seem like it was in mathlib
yet so I wrote it (before I realized I couldn't use it lol)
-/
def equiv_with_top [order_top ι] : module.direct_limit G f ≃ₗ[R] G ⊤  := { 
  to_fun := map_to_top G f,
  map_add' := by simp, -- kind of slow
  map_smul' := by simp, -- kind of slow
  inv_fun := of R ι G f ⊤,
  left_inv := 
  begin
    intro x,
    have H := exists_of x,
    cases H with i1 H1,
    cases H1 with y H,
    rw ← H,
    dunfold map_to_top,
    rw [lift_of, of_f],
  end,
  right_inv := 
  begin
    intro x,
    dunfold map_to_top,
    rw lift_of,
    exact module.directed_system.map_self f ⊤ x _, 
  end }

variables {P : Type u} [add_comm_group P] [module R P] (h : Π i j, injective $ f i j) 

def direct_limit_map_component (g : module.direct_limit G f →ₗ[R] P) : Π i, G i →ₗ[R] P := λi, 
{ to_fun := g ∘ (module.direct_limit.of R ι G f i),
  map_add' := by simp, -- kind of slow
  map_smul' := by simp  -- kind of slow}
}

variables [is_directed ι (≤)] [nonempty ι] 

-- TODO: Rewrite this with rcases once I figure out how that works
lemma injective_of_direct_limit (g : module.direct_limit G f →ₗ[R] P)
(h : Π i, injective (direct_limit_map_component G f g i)) : injective g := 
begin
intros x y heq,
have Hx := exists_of x,
cases Hx with ix Hix,
cases Hix with xi Hxi,
have Hy := exists_of y,
cases Hy with iy Hiy,
cases Hiy with yi Hyi,
have H2 := @is_directed.directed ι (≤) _ ix iy,
cases H2 with j Hj,
have Hx : x = of R ι G f j (f ix j (Hj.1) xi) := by simp [Hxi],
have Hy : y = of R ι G f j (f iy j (Hj.2) yi) := by simp [Hyi],
have main_H : direct_limit_map_component G f g j (f ix j (Hj.1) xi) = 
              direct_limit_map_component G f g j (f iy j (Hj.2) yi) :=
  begin
  dunfold direct_limit_map_component,
  dsimp,
  rw Hx at heq,
  rw Hy at heq,
  exact heq
  end,
have main_H2 : (f ix j (Hj.1) xi) = (f iy j (Hj.2) yi) := h j main_H,
simp [Hx, Hy, main_H2],
end

end module.direct_limit
end direct_limits


/-
In this section the goal is to prove any module is linearly equivalent to the direct limit over
the directed system of its finitely generated submodules. 
-/
section module_from_finite_submodules

namespace fin_submodule

open function (injective)

universes u v

variables {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] 
[dec_ι : decidable_eq (fin_submodule R M)] -- Do I need to prove this?


-- Ok I am definitely doing something wrong... All these definitions are like pulling teeth
def associated_inclusion {N P : fin_submodule R M} (h : N ≤ P) : N.1 →ₗ[R] P.1 := 
{ to_fun := λ⟨x, hx⟩, ⟨x, begin clear _x, clear _fun_match, cases N, cases P, 
  change N_val ≤ P_val at h,
  simp [h hx],
  end⟩,
  map_add' := λ⟨x, hx⟩ ⟨y, hy⟩, by refl,
  map_smul' := λr ⟨x, hx⟩, by refl }

def associated_system (N P : fin_submodule R M) : N ≤ P → ↥N.1 →ₗ[R] ↥P.1 := λh, associated_inclusion h

def inclusion_of_comp (N : fin_submodule R M) : N.1 →ₗ[R] M := 
{ to_fun := λx, x,
  map_add' := by simp,
  map_smul' := by simp }

def system_of_inclusions : Π (N : fin_submodule R M), N.1 →ₗ[R] M := λN, inclusion_of_comp N

lemma inc_is_injective {N P : fin_submodule R M} (h : N ≤ P) : injective $ associated_inclusion h :=
begin
rintros ⟨x, hx⟩ ⟨y, hy⟩ heq,
dunfold fin_submodule.associated_inclusion at heq,
dsimp at heq,
congr,
dunfold fin_submodule.associated_inclusion._match_1 at heq,
cases heq,
refl
end





-- variable N : submodule R M

-- #check N.module

#check @associated_system R M _ _ _ 

-- @[instance]def inst1 :Π (N : fin_submodule R M), add_comm_group ↥N := λ⟨N, hN⟩, N.add_comm_group

@[instance]def inst1 : Π (N : fin_submodule R M), add_comm_group ↥N.val := λ⟨N, hN⟩, submodule.add_comm_group N

-- @[instance]def inst2 : Π (N : fin_submodule R M), module R ↥N.val := λ⟨N, hN⟩, submodule.module N

#check @module.direct_limit R _ (fin_submodule R M) _ _ (λN, N.1) _ (λ⟨K, hK⟩, submodule.module K) begin
have H := @associated_system R M _ _ _ ,
sorry,
end

#check @module.direct_limit

end fin_submodule
end module_from_finite_submodules


/-
This is exactly lemma: [10.8.4](https://stacks.math.columbia.edu/tag/00D7)!
-/
#check module.direct_limit.of.zero_exact