import algebra.module.basic
import algebra.module.linear_map
import ring_theory.flat
import linear_algebra.tensor_product
import algebra.module.submodule_lattice
import tactic
import ring_theory.noetherian

section blah

open_locale tensor_product
open_locale big_operators

set_option pp.beta true
set_option trace.simplify.rewrite true

namespace module
open function (injective)
open linear_map (lsmul)

universes u v

variables (R : Type u) (M N: Type v) 
[comm_ring R] [add_comm_group M] [module R M]
[add_comm_group N] [module R N]
(s : finset M)

variables (P: Type v) [comm_ring R] 
[add_comm_group M] [module R M] 
[add_comm_group N] [module R N] 
[add_comm_group P] [module R P] 
(f : M →ₗ[R] N) [flat R P]

variables (x : M) (h : x ∈ submodule.span R (s : set M)) (h' : ∀ (x : M), x ∈ s → x = 0)

#check linear_map.ker_eq_bot_of_injective
#check submodule.span_induction h h'
#check eq_iff_true_of_subsingleton 
#check @submodule.span_induction R M _ _ _ x s ( = (0 : M)) h 
#check tensor_product.span_tmul_eq_top R M N 
#check submodule.span_induction h h' 

example (x : M) (y : N) (h : x = 0) : x ⊗ₜ[R] y = 0 := by simp [h]


/-
Sub lemma that shows any element of a trivial module is zero
-/
lemma triv_mem_eq_zero (h : subsingleton M) (x : M) : x = 0 := by {rw eq_iff_true_of_subsingleton, trivial}

/-
Sub lemma that is useful in order to show a module is trivial by showing all its elements are 0.
-/
lemma triv_of_all_zero (h : ∀(x : M), x = 0) : subsingleton M := 
begin
apply subsingleton.intro,
intros a b,
rw [h a, h b]
end

#check triv_mem_eq_zero M 

/-
First useful lemma: This lemma proves that if `M` is trivial, then `M ⊗ N` is trivial.
-/
lemma triv_of_triv_tensor (h :subsingleton M) : subsingleton (M ⊗[R] N) := 
begin
apply triv_of_all_zero,
intro x, 
have H : x ∈ submodule.span R {t : M ⊗ N | ∃ (m : M) (n : N), m ⊗ₜ[R] n = t} := by
simp [tensor_product.span_tmul_eq_top R M N],
apply submodule.span_induction H,
{
intros s hs,
have H3 : ∃ (m : M) (n : N), m ⊗ₜ[R] n = s := hs,
cases H3 with m hm,
cases hm with n hn,
rw ← hn,
have H4 : m = 0 := triv_mem_eq_zero M h m,
rw H4,
simp,
},
{
refl,
},
{
intros x y hx hy,
simp [hx, hy],
},
{
intros a x hx,
simp [hx],
},
end

/-
I'M RIGHT HERE:
currently we're working out a good API for finite modules, need to prove each one is a set so we
can talk about set membership for the simp lemma below mem_bot. 

maybe separate out the two parts of the proof below into their own lemmas also... 
-/

variable [decidable_eq M]


def fin_submodule (R : Type u) (M : Type v) [semiring R] [decidable_eq M] [add_comm_monoid M] [module R M] : Type v := { N : submodule R M // N.fg }

/-
You would want something like this to be true, but it's not! Not unless R is Noetherian! But you don't need the whole thing in order to do what I want for direct limits...
-/
def fg_inter_isfalse {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [module R M] {N P : submodule R M} (hN : N.fg) (hP : P.fg) : (N ⊓ P).fg :=
begin
sorry,
end

instance : has_sup (fin_submodule R M) := { sup :=  λ⟨N, hN⟩ ⟨P, hP⟩, ⟨N ⊔ P, submodule.fg_sup hN hP⟩
}

instance : has_le (fin_submodule R M) := { le := λ⟨N, _⟩ ⟨P, _⟩, N ≤ P }

instance : has_lt (fin_submodule R M) := { lt := _ }

#check 

instance : partial_order (fin_submodule R M) := { le := _,
  lt := _,
  le_refl := _,
  le_trans := _,
  lt_iff_le_not_le := _,
  le_antisymm := _ }

instance : semilattice_sup (fin_submodule R M) := { sup := λ⟨N, hN⟩ ⟨P, hP⟩, ⟨N ⊔ P, submodule.fg_sup hN hP⟩,
  le := λ⟨N, _⟩ ⟨P, _⟩, N ≤ P,
  lt := _,
  le_refl := _,
  le_trans := _,
  lt_iff_le_not_le := _,
  le_antisymm := _,
  le_sup_left := _,
  le_sup_right := _,
  sup_le := _ }

/-
COPY THIS ABOVE:
instance : complete_lattice (submodule R M) :=
{ sup          := λ a b, Inf {x | a ≤ x ∧ b ≤ x},
  le_sup_left  := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, ha,
  le_sup_right := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, hb,
  sup_le       := λ a b c h₁ h₂, Inf_le' ⟨h₁, h₂⟩,
  inf          := (⊓),
  le_inf       := λ a b c, set.subset_inter,
  inf_le_left  := λ a b, set.inter_subset_left _ _,
  inf_le_right := λ a b, set.inter_subset_right _ _,
  Sup          := λtt, Inf {t | ∀t'∈tt, t' ≤ t},
  le_Sup       := λ s p hs, le_Inf' $ λ q hq, hq _ hs,
  Sup_le       := λ s p hs, Inf_le' hs,
  Inf          := Inf,
  le_Inf       := λ s a, le_Inf',
  Inf_le       := λ s a, Inf_le',
  ..submodule.order_top,
  ..submodule.order_bot,
  ..set_like.partial_order }
-/

#check set.inter_subset_left
#check submodule.fg_sup
-- instance : set (fin_submodule R M) := _

instance : has_bot (fin_submodule R M) := { bot := 
begin
split,
swap,
exact ⊥,
use { 0 },
simp,
end }

#check (⊥ : fin_submodule R M)

#check @has_bot.bot (fin_submodule R M) _ 

-- @[simp] lemma mem_bot {x : M} : x ∈ (⊥ : fin_submodule R M) ↔ x = 0 := sorry

-- instance : order_bot (fin_submodule R M) := { bot := ⊥,
--   bot_le :=
--   begin
--   intros N x hx,
--   have H : x = 0 :=
--   begin
--   have H2 := @has_bot.bot (fin_submodule R M) _, 
--   end
--   end }

-- instance : has_bot (fin_submodule R M) := { bot :=  }



end module
end blah

/-
Plan for March 2: 
* Prove `lemma2` above (that if `M = 0` then `M ⊗ N = 0`) **** DID IT *****
* State and prove the result about how a module is a direct limit of its finite submodules. 
* State and prove lemma <https://stacks.math.columbia.edu/tag/00D7>
-/

