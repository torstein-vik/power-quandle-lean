
import minimal_sub_pq_gen_group

universe u

section pq_like_direct_kernel

variables {G : Type u} [group G]

variables (p : pq_group G →* (counit : pq_group G →* G).ker) (hp : ∀ x : (counit : pq_group G →* G).ker, p x = x)

variables (i : G →* pq_group G) (hi : ∀ g : G, counit (i g) = g) (hpi : ∀ g : G, p (i g) = 1)

def eta_p_ker : set G := λ g, p (of g) = 1






end pq_like_direct_kernel

