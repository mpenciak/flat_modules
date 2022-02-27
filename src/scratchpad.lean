import algebra.module.basic
import algebra.module.linear_map
import ring_theory.flat
import tactic

universes u v

namespace module
open function (injective)
open linear_map (lsmul)

open_locale tensor_product

variables (M N P: Type v) (R: Type u) [comm_ring R] 
[add_comm_group M] [module R M] 
[add_comm_group N] [module R N] 
[add_comm_group P] [module R P] 
(f : M →ₗ[R] N) [flat R P]

lemma main_result : injective f → injective (tensor_product.map (@linear_map.id R P _ _ _) f) :=
begin
intro h,
sorry
end

lemma lemma1 (h : ∀(x : M), x = 0) : subsingleton M := 
begin
apply subsingleton.intro,
intros a b,
simp [h a, h b]
end

lemma lemma2 (h :subsingleton M) : subsingleton (M ⊗[R] N) := 
begin
apply subsingleton.intro,
intros x y,
sorry
end

-- Want to define a function which takes an element x of a vectorspace, and a spanning set, and 
-- returns a hypothesis that allows one to rewrite x in terms of said linear combination. 

open_locale big_operators

def test_function (x : M) (s : set M) (h : submodule.span R s = ⊤) 
: ∃(I : finset s), x = ∑ a in I, a := 
begin
have H : x ∈ submodule.span R s := by {rw h, exact submodule.mem_top},
have H2 := @submodule.mem_span_finite_of_mem_span R M _ _ _ s x H,
cases H2 with s' h,
apply exists.intro;
sorry
end

lemma in_span (x : M) (s : finset M) (h : x ∈ submodule.span R (s : set M)) : ∃(coeff : M → R),
x = @finset.sum M M _ s (λm, (coeff m) • m) := 
begin
sorry
end
end module

variable (S : finset ℕ)

-- mem_span_finite_of_mem_span seems important

variables (M : Type v) (R: Type u) [comm_ring R] 
[add_comm_group M] [module R M] (s : set M) (s' : finset s) (a : s)

#check (a : M) 

#check @submodule.mem_span_finite_of_mem_span R M _ _ _ s 
#check @exists.intro s' 

#check @finset.sum M s _ s' 
