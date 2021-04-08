
import pq_induction_principles

universe u


section pq_like_direct_coeq

variables {G : Type u} [group G]

variables {i : G →* pq_group G} {hi : ∀ g : G, counit (i g) = g}


inductive coeq_rel 


end pq_like_direct_coeq
