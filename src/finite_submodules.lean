import ring_theory.noetherian
import algebra.direct_limit
import linear_algebra.isomorphisms
import tactic

set_option trace.simplify.rewrite true
set_option pp.beta true

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

instance : has_sup (fin_submodule R M) := 
{ sup := λ N P, ⟨↑N ⊔ ↑P, submodule.fg_sup N.prop P.prop⟩ }

instance : partial_order (fin_submodule R M) := 
subtype.partial_order _
 
variables {R M}
def to_submodule (N : fin_submodule R M) : submodule R M := N.val

instance : has_coe (fin_submodule R M) (submodule R M) := ⟨@to_submodule R M _ _ _⟩

@[simp]lemma le_iff_submodule_le {N P : fin_submodule R M} : N ≤ P ↔ N.val ≤ P.val := 
by simp only [subtype.val_eq_coe, subtype.coe_le_coe]

@[simp]lemma coe_sup_eq_sup_coe (N P : fin_submodule R M) : ↑(N ⊔ P) = (N: submodule R M) ⊔ P 
:= by refl

instance : semilattice_sup (fin_submodule R M) := 
{ sup := (⊔),
  le_sup_left := 
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
    simp,
    exact ⟨h1, h2⟩,
  end,
  ..partial_order R M}

instance : is_directed (fin_submodule R M) (≤) := { directed := 
begin
  intros N P,
  existsi N ⊔ P,
  simp,
end }

instance : has_bot (fin_submodule R M) := { bot := ⟨⊥, submodule.fg_bot⟩ }

end fin_submodule
end basic_properties

/-
In this section we define the `map_to_top` which is a map out of a direct limit to its top. The main
results are `equiv_with_top` which shows this map is an equivalence, and `injective_of_direct_limit`
where we show if each component of a map out of the direct limit is injective, then the resulting
map out of the direct limit is injective. (when the connecting maps are themselves all injective)
-/
section direct_limits

universes u v w u₁

variables {R : Type u} [ring R]
variables {ι : Type v} [decidable_eq ι] [preorder ι]
variables (G : ι → Type w) [Π i, add_comm_group (G i)] [Π i, module R (G i)]
variables (f : Π i j, i ≤ j → G i →ₗ[R] G j) [directed_system G (λ i j h, f i j h)]

namespace module.direct_limit

def map_to_top [order_top ι] : module.direct_limit G f →ₗ[R] G ⊤ :=
lift R ι G f (λi, f i ⊤ (le_top)) (λi j hij x, module.directed_system.map_map f hij le_top x)

def equiv_with_top [order_top ι] : module.direct_limit G f ≃ₗ[R] G ⊤  := { 
  to_fun := map_to_top G f,
  map_add' := by simp only [map_add, eq_self_iff_true, forall_const], 
  map_smul' := by simp only [linear_map.map_smulₛₗ, eq_self_iff_true, forall_const], 
  inv_fun := of R ι G f ⊤,
  left_inv := 
  begin
    intro x,
    have H := exists_of x,
    cases H with i₁ H₁,
    cases H₁ with y H₂,
    rw ← H₂,
    unfold map_to_top,
    rw [lift_of, of_f],
  end,
  right_inv := 
  begin
    intro x,
    unfold map_to_top,
    rw lift_of,
    exact module.directed_system.map_self f ⊤ x _, 
  end }

open submodule
open function (injective)
open module.direct_limit
variables {P : Type u} [add_comm_group P] [module R P] (h : Π i j, injective $ f i j) 
variables [is_directed ι (≤)] [nonempty ι] 

def direct_limit_map_component (g : module.direct_limit G f →ₗ[R] P) : Π i, G i →ₗ[R] P 
:= λi, g ∘ₗ (module.direct_limit.of R ι G f i)

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
have Hx : x = of R ι G f j (f ix j (Hj.1) xi) := by simp only [Hxi, of_f],
have Hy : y = of R ι G f j (f iy j (Hj.2) yi) := by simp only [Hyi, of_f],
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
simp only [Hx, Hy, main_H2],
end

end module.direct_limit
end direct_limits

section module_from_finite_submodules

/-
The main result in this section is `equiv_with_module` which shows a module is equivalent to the 
direct limit of its finitely generated submodules. Along the way we develop some helpful simp lemmas
about the subtype of finitely generated submodules, and the main result is a consequence of the two
main lemmas `inc_kernel_eq_bot` and `fg_limit_to_module_surjective`.
-/
namespace fin_submodule

open module (direct_limit)
open module.direct_limit
open function (injective)
open _root_.submodule (span)

universes u v

variables {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] 
[decidable_eq (fin_submodule R M)]

def le_inclusion {N P : fin_submodule R M} (h : N ≤ P) : N.1 →ₗ[R] P.1 := 
submodule.of_le h

def le_system (N P : fin_submodule R M) : N ≤ P → ↥N.1 →ₗ[R] ↥P.1 := λh, le_inclusion h

def module_inclusion (N : fin_submodule R M) : N.1 →ₗ[R] M := 
submodule.subtype N.1

def system_of_inclusions : Π (N : fin_submodule R M), N.1 →ₗ[R] M := λN, module_inclusion N

lemma le_inc_injective {N P : fin_submodule R M} (h : N ≤ P) : injective $ le_inclusion h :=
λ x y heq, subtype.ext $ by injection heq

variables (R) (M)

def fg_limit_to_module : direct_limit (λ (N : fin_submodule R M), N) (le_system) →ₗ[R] M
:= lift R (fin_submodule R M) (λN,N) le_system system_of_inclusions (λ_ _ _ _, by refl) 

variables {M}

def finset_to_fin_submodule : finset M → fin_submodule R M := λs, ⟨span R s, by existsi s; refl⟩

def elt_to_fin_submodule : M → fin_submodule R M := λx, finset_to_fin_submodule R {x}

-- I think having this as a simp lemma breaks things
-- @[simp]lemma in_submodule_span_of_self (x : M) : x ∈ @submodule.span R M _ _ _ { x }  := submodule.mem_span_singleton_self x

@[simp]lemma in_elt_to_fin_submodule (x : M) : x ∈ (elt_to_fin_submodule R x).val:=
begin
rw [elt_to_fin_submodule, finset_to_fin_submodule],
simp only [finset.coe_singleton],
exact submodule.mem_span_singleton_self x
end

@[simp]lemma finset_to_fin_submodule_eq (x : M) : 
(finset_to_fin_submodule R ({ x } : finset M)).val = submodule.span R ({ x } : finset M) 
:= by rw finset_to_fin_submodule

@[simp]lemma mem_span_singleton_self (x : M) : x ∈ (elt_to_fin_submodule R x).val :=
begin
rw[elt_to_fin_submodule, finset_to_fin_submodule],
change x ∈ span R ↑{x},
rw finset.coe_singleton,
exact submodule.mem_span_singleton_self x
end

lemma inc_kernel_eq_bot : linear_map.ker (fg_limit_to_module R M) = ⊥ := 
begin
ext x,
rw [submodule.mem_bot, linear_map.mem_ker],
split,
{ intro h1,
  have H := exists_of x,
  cases H with N hN,
  cases hN with y hy,
  rw ← hy,
  rw [← hy, fg_limit_to_module, lift_of, system_of_inclusions] at h1,
  unfold module_inclusion at h1,
  simp only [submodule.coe_subtype, submodule.coe_eq_zero] at h1,
  rw [h1, map_zero],
  },
{ intro h,
  rw [fg_limit_to_module, h, map_zero]
  }
end

-- TODO: Change this name eventually once I understand why I should or shouldn't have to define this
def weirdmap (x : M) : ↥((elt_to_fin_submodule R x).val) := ⟨x, in_elt_to_fin_submodule R x⟩

lemma fg_limit_to_module_surjective: function.surjective $ fg_limit_to_module R M :=
begin
intro x,
existsi of R (fin_submodule R M) 
             (λ (N : fin_submodule R M), N) (le_system) 
             (elt_to_fin_submodule R x) (weirdmap R x),
rw [fg_limit_to_module, lift_of, system_of_inclusions],
unfold module_inclusion,
simp only [weirdmap, submodule.coe_subtype, submodule.coe_mk]
end

open linear_map (quot_ker_equiv_of_surjective)
open _root_.submodule (quot_equiv_of_eq_bot)

noncomputable def equiv_with_module : direct_limit (λ (N : fin_submodule R M), N) le_system ≃ₗ[R] M 
:= begin
have H1 := quot_ker_equiv_of_surjective (fg_limit_to_module R M) (fg_limit_to_module_surjective R),
have H2 := quot_equiv_of_eq_bot (⊥ : submodule R (direct_limit (λ (N : fin_submodule R M), N) le_system)) (rfl),
rw inc_kernel_eq_bot R at H1,
exact H2.symm.trans H1,
end

end fin_submodule
end module_from_finite_submodules