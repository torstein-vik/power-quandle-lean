
import sub_pq
import pq_to_group
import pq_induction_principles

universe u

section pq_group_subgroup

variables {Q : Type u} [power_quandle Q]

variables (Q1 : sub_power_quandle Q)

inductive is_from_sub_pq : pq_group Q → Prop
| incl (x : Q1) : is_from_sub_pq (of ↑x)
| mul (x y : pq_group Q) (hx : is_from_sub_pq x) (hy : is_from_sub_pq y) : is_from_sub_pq (x * y)

lemma one_mem_is_from_sub_pq : is_from_sub_pq Q1 1 :=
begin 
  suffices : is_from_sub_pq Q1 (of ↑(1 : Q1)),
  {
    convert this,
    rw coe_one,
    rw of_one,
  },
  {
    exact is_from_sub_pq.incl 1,
  },
end

def pq_group_subgroup : subgroup (pq_group Q) := { 
  carrier := is_from_sub_pq Q1,
  one_mem' := begin 
    exact one_mem_is_from_sub_pq Q1,
  end,
  mul_mem' := begin 
    exact is_from_sub_pq.mul,
  end,
  inv_mem' := begin 
    intros x hx,
    induction hx with y,
    {
      rw of_inv,
      rw coe_pow,
      apply is_from_sub_pq.incl,
    },
    {
      simp only [mul_inv_rev],
      apply is_from_sub_pq.mul,
      assumption,
      assumption,
    },
  end }

--variables {X : Type*} [power_quandle X]

/-
def pq_group_subgroup_domain (f : Q1 → X) (hf : is_pq_morphism f) : pq_group_subgroup Q1 →* pq_group X :=
begin
  fconstructor,
  {
    intro x,

  },
  sorry,
  sorry,
end
-/

def pq_group_subgroup_inclusion : pq_group Q1 →* pq_group_subgroup Q1 :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro q,
    fconstructor,
    exact (of ↑q),
    apply is_from_sub_pq.incl,
  },
  {
    split,
    {
      intros a b,
      simp_rw ←coe_rhd,
      simp_rw ←rhd_of_eq_of_rhd,
      refl,
    },
    {
      intros a n,
      simp_rw ←coe_pow,
      simp_rw of_pow_eq_pow_of,
      ext1,
      simp only [subgroup.coe_gpow, subtype.coe_mk],
    }
  }
end

theorem pq_group_subgroup_inclusion_bijective : function.bijective (pq_group_subgroup_inclusion Q1) :=
begin
  split,
  {
    refine (pq_group_subgroup_inclusion Q1).injective_iff.mpr _,
    intros a ha,
    sorry,
  },
  {
    intro x,
    cases x with x hx,
    induction hx with y,
    {
      use (of y),
      refl,
    },
    {
      cases hx_ih_hx with a ha,
      cases hx_ih_hy with b hb,
      use a * b,
      simp only [monoid_hom.map_mul],
      rw ha,
      rw hb,
      refl,
    },
  },
end

end pq_group_subgroup
