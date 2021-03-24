
import pq_to_group
import sub_pq

universe u

section subgroup_pq_like

variables {Q : Type u} [power_quandle Q]

def sub_L_pq (H : subgroup (pq_group Q)) : sub_power_quandle Q := { 
  carrier := (λ x, of x ∈ H),
  closed_rhd := begin 
    intros x y hx hy,
    rw set.mem_def at *,
    rw ←rhd_of_eq_of_rhd,
    rw rhd_def,
    refine H.mul_mem _ _,
    refine H.mul_mem _ _,
    assumption,
    assumption,
    refine H.inv_mem _,
    assumption,
  end,
  closed_pow := begin 
    intros x n hx,
    rw set.mem_def at *,
    rw of_pow_eq_pow_of,
    exact subgroup.gpow_mem H hx n,
  end }


def pq_group_sub_L_pq_to_H (H : subgroup (pq_group Q)) : pq_group (sub_L_pq H) →* H :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro x,
    cases x with x hx,
    fconstructor,
    exact of x,
    exact hx,
  },
  {
    split,
    {
      intros a b,
      cases a with a ha,
      cases b with b hb,
      have rhd_subtype_rw : (⟨a, ha⟩▷⟨b, hb⟩ : {x // x ∈ has_coe_t_aux.coe (sub_L_pq H)}) = ⟨a ▷ b, _⟩ := rfl,
      rw rhd_subtype_rw,
      simp only,
      simp_rw ←rhd_of_eq_of_rhd,
      refl,
    },
    {
      intros a n,
      cases a with a ha,
      have pow_subtype_rw : (⟨a, ha⟩ ^ n : {x // x ∈ has_coe_t_aux.coe (sub_L_pq H)}) = ⟨a ^ n, _⟩ := rfl,
      rw pow_subtype_rw,
      simp only,
      simp_rw of_pow_eq_pow_of,
      ext1,
      simp only [subgroup.coe_gpow, subgroup.coe_mk],
    },
  },
end


end subgroup_pq_like
