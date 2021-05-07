
import group_theory.abelianization
import pq_quotient_rel
import group_to_pq

universes u1 u2

section pq_iso_abelianization

variables {G : Type u1} [group G] {H : Type u2} [group H]

@[priority 10]
instance G_has_pq_rel : has_pq_rel G := ⟨λ x y, ∃ z : G, z ▷ x = y⟩


def abelianization_iso : abelianization G ≃ pq_quotient G :=
begin
  fconstructor,
  {
    fapply quotient.lift,
    exact λ g, pq_quotient_of g,
    {
      intros a b hab,
      apply quotient.sound,
      suffices : a⁻¹ * b ≈ 1,
      {
        cases this,
        fconstructor,
        refine pq_general_rel'.custom_rel _,
        unfold has_pq_rel.rel,
        sorry,
      },
      have hab1 : a⁻¹ * b ∈ commutator G := hab,
      unfold commutator at hab1,
      unfold subgroup.normal_closure at hab1,
      
      fapply subgroup.closure_induction,
      sorry,
    },
  },
  {
    fapply pq_quotient_lift,
    {
      intro g,
      exact abelianization.of g,
    },
    {
      split,
      {
        intros a b,
        refl,
      },
      {
        intros a n,
        rw monoid_hom.map_gpow,
      },
    },
    {
      intros x y hxy,
      unfold has_pq_rel.rel at hxy,
      cases hxy with z hz,
      rw ←hz,
      rw rhd_def,
      simp only [monoid_hom.map_mul, eq_self_iff_true, mul_inv_cancel_comm, monoid_hom.map_mul_inv],
    },
  },
  {
    sorry,
  },
  {
    sorry,
  },
end

def pq_iso_abelianization (f : G ≃ H) (hf : is_pq_morphism f) : abelianization G ≃* abelianization H := sorry


end pq_iso_abelianization
