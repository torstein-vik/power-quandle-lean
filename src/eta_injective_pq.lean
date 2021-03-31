
import minimal_sub_pq


universe u

section eta_injective_pq


def eta_injective (Q : Type u) [power_quandle Q] : Prop := function.injective (of : Q → pq_group Q)

variables {Q : Type u} [power_quandle Q]

noncomputable def eta_injective_iso_sub_pq (hQ : eta_injective Q) : Q ≃ gen_group_sub_pq (@of_gen_group_sub_pq Q _) := 
begin
  fapply equiv.of_bijective,
  {
    intro q,
    fconstructor,
    exact of q,
    use q,
  },
  {
    split,
    {
      intros x y hxy,
      apply hQ,
      simp only [subtype.mk_eq_mk] at hxy,
      exact hxy,
    },
    {
      intro x,
      cases x with x hx,
      cases hx with q hq,
      use q,
      simp only [subtype.mk_eq_mk],
      rw hq,
    },
  },
end

theorem eta_injective_iso_sub_pq_is_pq_morphism (hQ : eta_injective Q) : is_pq_morphism (eta_injective_iso_sub_pq hQ) :=
begin
  split,
  {
    intros a b,
    unfold eta_injective_iso_sub_pq,
    simp only [equiv.of_bijective_apply],
    simp_rw ←rhd_of_eq_of_rhd,
    refl,
  },
  {
    intros a n,
    unfold eta_injective_iso_sub_pq,
    simp only [equiv.of_bijective_apply],
    simp_rw of_pow_eq_pow_of,
    refl,
  },
end

end eta_injective_pq
