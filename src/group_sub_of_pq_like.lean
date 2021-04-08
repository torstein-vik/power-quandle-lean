
import pq_to_group

universes u1 u2

section group_sub_of_pq_like


variables {Q1 : Type u1} {Q2 : Type u2} [power_quandle Q1] [power_quandle Q2]

variables {G : subgroup (pq_group Q1)} {H : subgroup (pq_group Q2)}


def iso_reflected_sub_pq_like (f : G ≃ H) (hf : is_pq_morphism f) : G ≃* H := sorry



end group_sub_of_pq_like
