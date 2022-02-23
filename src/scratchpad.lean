import algebra.module.basic
import algebra.module.linear_map
import ring_theory.flat


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

end module