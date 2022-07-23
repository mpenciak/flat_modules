import enough_injectives.adjunction_Ab
import category_theory.abelian.generator

universes v
variables (R : Ring.{v})

example : category_theory.enough_injectives (Module.{v} R) := infer_instance
#check category_theory.abelian.has_injective_coseparator


/-

Hom(-, Hom(M, X)) <-> Hom ((_ ⊗ M), X)
Hom(-, X) preserves monos, and reflects monos
(X is a cogenerator),

Hom(M, X) is injective iff 
preserves mono iff 
_ ⊗ M preserves mono iff
M is flat

Baer criterion: Suffices to check
Hom(-, Hom(M, X)) preserves monos of the form
I → R
So we only need to check such morphisms for flatness

where X is an injective cogenerator
-/

