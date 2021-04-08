

import pq_quotient_rel

universes u1 u2 u3

section pq_coeq

variables {Q1 : Type u1} [power_quandle Q1] {Q2 : Type u2} [power_quandle Q2]

variables (f g : Q1 → Q2) (hf : is_pq_morphism f) (hg : is_pq_morphism g)

include hf hg

instance pq_quotient_base_rel_coeq : has_pq_rel Q2 := ⟨λ x y, ∃ q : Q1, x = f q ∧ y = g q⟩

def pq_coeq : Type u2 := @pq_quotient Q2 _ (pq_quotient_base_rel_coeq f g hf hg)

variables {Q3 : Type u3} [power_quandle Q3]

def pq_coeq_lift (a : Q2 → Q3) (ha : is_pq_morphism a) (hae : ∀ q : Q1, a (f q) = a (g q)) : pq_coeq f g hf hg → Q3 
:= pq_quotient_lift a ha begin 
  
end


end pq_coeq
