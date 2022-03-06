import ring_theory.noetherian
import algebra.direct_limit
import tactic

set_option pp.beta true
set_option trace.simplify.rewrite true

section basic_properties

universes u v

variables (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [module R M]

def fin_submodule  : Type v := { N : submodule R M // N.fg }

namespace fin_submodule

instance have_sup : has_sup (fin_submodule R M) := { sup := λ⟨N, hN⟩ ⟨P, hP⟩, ⟨N ⊔ P, submodule.fg_sup hN hP⟩ }

instance have_le : has_le (fin_submodule R M) := { le := λ⟨N, _⟩ ⟨P, _⟩, N ≤ P }

instance have_lt : has_lt (fin_submodule R M) := { lt := λ⟨N, _⟩ ⟨P, _⟩, N ≤ P ∧ ¬ P ≤ N }

instance am_partial_order : partial_order (fin_submodule R M) := 
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

instance am_semilattice_sup : semilattice_sup (fin_submodule R M) := 
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
  .. am_partial_order R M,
  .. have_sup R M }

end fin_submodule
end basic_properties

section direct_limits

universes u v w u₁

open submodule
open function (injective)

variables {R : Type u} [ring R]
variables {ι : Type v}
variables [decidable_eq ι] [preorder ι]
variables (G : ι → Type w)
variables [Π i, add_comm_group (G i)] [Π i, module R (G i)]
variables (f : Π i j, i ≤ j → G i →ₗ[R] G j) [order_top ι] (h : Π i j, injective $ f i j) [directed_system G (λ i j h, f i j h)]

-- def associated_component (P : Type u₁) [add_comm_group P] [module R P] (p : module.direct_limit G f →ₗ[R] P) (i : ι) : G i →ₗ[R] P := { to_fun := -- λx, ⇑p (module.direct_limit.of R ι G f i x), :((
-- begin
--   intro x,
--   apply ⇑p,
--   exact module.direct_limit.of R ι G f i x,
-- end,
--   map_add' := sorry,
--   map_smul' := sorry }

-- lemma lemma1 (P : Type u₁) [add_comm_group P] [module R P] (p : module.direct_limit G f →ₗ[R] P): ∀ (i : ι), 1 + 1 = 2 := 


/-
In order to prove the important lemma `isomorphism_with_top`, I should establish two smaller
lemmas, which are `lemma1` and `lemma2` above. The first 
-/

open module.direct_limit

def map_to_top [order_top ι] : module.direct_limit G f →ₗ[R] G ⊤ :=
lift R ι G f (λi, f i ⊤ (le_top)) (λi j hij x, module.directed_system.map_map f hij le_top x)

lemma isomorphism_with_top [order_top ι] : module.direct_limit G f ≃ₗ[R] G ⊤  := { 
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

/-
THIS IS EXACTLY LEMMA [10.8.4](https://stacks.math.columbia.edu/tag/00D7)!!!!!
-/
#check module.direct_limit.of.zero_exact
#check module.direct_limit G f

end direct_limits

/-
I think I'm coming to the limits of my ability to work with this purely preorder direct limit stuff
I think the easiest way may be to try to work with cones and category theory instead?
-/