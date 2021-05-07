
import sub_pq
import pq_induction_principles

universe u

section pq_group_sub_pq

variables {Q : Type u} [power_quandle Q] {Q1 : sub_power_quandle Q}


def pq_group_sub_pq_inclusion : pq_group Q1 →* pq_group Q :=
begin
  fapply L_of_morph,
  {
    intro x,
    cases x with x hx,
    exact x,
  },
  {
    split,
    {
      intros a b,
      cases a with a ha,
      cases b with b hb,
      refl,
    },
    {
      intros a n,
      cases a with a ha,
      refl,
    },
  },
end

variables {G : Type*} [group G]

def pre_pq_group_in_sub_pq (Q1 : sub_power_quandle Q) : pre_pq_group Q → Prop
| pre_pq_group.unit := true
| (pre_pq_group.incl x) := x ∈ Q1.carrier
| (pre_pq_group.mul x y) := pre_pq_group_in_sub_pq x ∧ pre_pq_group_in_sub_pq y
| (pre_pq_group.inv x) := pre_pq_group_in_sub_pq x

def subgroup_of_pq_supergroup (Q1 : sub_power_quandle Q) : subgroup (pq_group Q) := { 
  carrier := λ x, ∃ y : pre_pq_group Q, ⟦y⟧ = x ∧ pre_pq_group_in_sub_pq Q1 y,
  one_mem' := begin 
    use pre_pq_group.unit,
    split,
    refl,
    trivial,
  end,
  mul_mem' := begin 
    intros a b ha hb,
    cases ha with a1 ha1,
    cases hb with b1 hb1,
    cases ha1 with ha1 ha2,
    cases hb1 with hb1 hb2,
    use pre_pq_group.mul a1 b1,
    split,
    rw ←ha1,
    rw ←hb1,
    refl,
    split,
    assumption,
    assumption,
  end,
  inv_mem' := begin 
    intros a ha,
    cases ha with a1 ha1,
    cases ha1 with ha1 ha2,
    use pre_pq_group.inv a1,
    split,
    rw ←ha1,
    refl,
    assumption,
  end}

def iso_subs_forward : pq_group Q1 →* subgroup_of_pq_supergroup Q1 :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro q,
    cases q with q hq,
    fconstructor,
    exact of q,
    unfold subgroup_of_pq_supergroup,
    use pre_pq_group.incl q,
    split,
    refl,
    exact hq,
  },
  {
    split,
    {
      intros a b,
      cases a with a ha,
      cases b with b hb,
      simp only,
      have : (⟨a, ha⟩ ▷ ⟨b, hb⟩ : Q1) = ⟨a ▷ b, _⟩ := rfl,
      rw this,
      simp only,
      simp_rw ←rhd_of_eq_of_rhd,
      refl,
    },
    {
      intros a n,
      cases a with a ha,
      simp only,
      have : (⟨a, ha⟩ ^ n : Q1) = ⟨a ^ n, _⟩ := rfl,
      rw this,
      simp only,
      simp_rw of_pow_eq_pow_of,
      ext1,
      simp only [subgroup.coe_gpow, subtype.coe_mk],
    },
  },
end

theorem iso_subs_forward_bijective : function.bijective (iso_subs_forward : pq_group Q1 → subgroup_of_pq_supergroup Q1) :=
begin
  split,
  {
    refine iso_subs_forward.injective_iff.mpr _,
    intros a ha,
    unfold iso_subs_forward at ha,
  },
  {
    sorry,
  },
end

def iso_subs_backward : subgroup_of_pq_supergroup Q1 →* pq_group Q1 :=
begin
  fconstructor,
  {
    intro q,
    cases q with q hq,
    unfold subgroup_of_pq_supergroup at hq,
    sorry,
  },
  sorry,
  sorry,
end

def iso_subs : pq_group Q1 ≃* subgroup_of_pq_supergroup Q1 := { 
  to_fun := iso_subs_forward,
  inv_fun := _,
  left_inv := _,
  right_inv := _,
  map_mul' := begin 
    intros x y,
    simp only [monoid_hom.map_mul],
  end }

lemma pq_group_sub_pq_inclusion_injective : function.injective (pq_group_sub_pq_inclusion : pq_group Q1 → pq_group Q) :=
begin
  refine pq_group_sub_pq_inclusion.injective_iff.mpr _,
  intros x hx,
  sorry,
  /-
  refine pq_group_list _,
  intros x hxy,
  induction x with y x hx,
  {
    simp only [list.prod_nil, list.map],
  },
  {

  },
  -/
end



end pq_group_sub_pq
