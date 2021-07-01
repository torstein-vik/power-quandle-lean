
import eta_injective_pq

import pq_induction_principles

universes u1 u2

section pq_injective

variables {Q1 : Type u1} [power_quandle Q1] {Q2 : Type u2} [power_quandle Q2]

theorem pq_injective_if_L_injective (f : Q1 → Q2) (hf : is_pq_morphism f) (hLf : function.injective (L_of_morph f hf)) (hQ1 : eta_injective Q1) : function.injective f :=
begin
  intros x y hxy,
  apply hQ1,
  apply hLf,
  rw L_of_morph_of,
  rw L_of_morph_of,
  apply congr_arg,
  exact hxy,
end


end pq_injective
