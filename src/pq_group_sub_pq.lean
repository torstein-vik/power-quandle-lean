
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

lemma closure_mem_simple (s : set G) (x : G) (hx : x ∈ s) : x ∈ subgroup.closure s :=
begin
  intros s1 hs1,
  cases hs1 with G1 hG1,
  rw ←hG1,
  simp only [subgroup.mem_coe, set.mem_Inter, set.mem_set_of_eq],
  intro hs,
  apply hs,
  exact hx,
end

def subgroup_of_pq_supergroup (Q1 : sub_power_quandle Q) : subgroup (pq_group Q) := subgroup.closure (λ x, ∃ q : Q, q ∈ Q1.carrier ∧ x = of q)

def iso_subs_forward : pq_group Q1 →* subgroup_of_pq_supergroup Q1 :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro q,
    cases q with q hq,
    fconstructor,
    exact of q,
    unfold subgroup_of_pq_supergroup,
    apply closure_mem_simple,
    rw set.mem_def,
    use q,
    split,
    exact hq,
    refl,
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
