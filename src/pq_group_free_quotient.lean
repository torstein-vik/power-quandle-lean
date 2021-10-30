
import pq_to_group

import group_theory.free_group
import group_theory.quotient_group

universe u

section pq_group_free_quotient

variables {s : Type u}

inductive pq_group_relation_space_rel : free_group s → Prop
| rhd_rel (a b c : s) : pq_group_relation_space_rel (free_group.of a * free_group.of b * (free_group.of a)⁻¹ * (free_group.of c)⁻¹)
| pow_rel (a b : s) (n : ℤ) : pq_group_relation_space_rel ((free_group.of a) ^ n * (free_group.of b)⁻¹)
| one_closed : pq_group_relation_space_rel 1
| mul_closed (x y : free_group s) (hx : pq_group_relation_space_rel x) (hy : pq_group_relation_space_rel y) : pq_group_relation_space_rel (x * y)
| inv_closed (x : free_group s) (hx : pq_group_relation_space_rel x) : pq_group_relation_space_rel (x⁻¹)
| normal_closed (x y : free_group s) (hx : pq_group_relation_space_rel x) : pq_group_relation_space_rel (y * x * y⁻¹)


def pq_group_relation_space : subgroup (free_group s) := { 
  carrier := pq_group_relation_space_rel,
  one_mem' := pq_group_relation_space_rel.one_closed,
  mul_mem' := pq_group_relation_space_rel.mul_closed,
  inv_mem' := pq_group_relation_space_rel.inv_closed }

instance pq_group_relation_space_is_normal : (@pq_group_relation_space s).normal :=
begin
  fconstructor,
  intros x hx y,
  apply pq_group_relation_space_rel.normal_closed,
  apply hx,
end

lemma free_of_in_pq_group_relation_space (a : s) : free_group.of a ∈ (@pq_group_relation_space s) :=
begin
  suffices : free_group.of a = (free_group.of a * free_group.of a * (free_group.of a)⁻¹ * (free_group.of a)⁻¹) * ((free_group.of a) ^ (2 : ℤ) * (free_group.of a)⁻¹),
  {
    rw this,
    clear this,
    apply subgroup.mul_mem,
    apply pq_group_relation_space_rel.rhd_rel,
    apply pq_group_relation_space_rel.pow_rel,
  },
  group,
end

lemma pq_group_relation_space_is_univ : (@pq_group_relation_space s) = ⊤ :=
begin
  ext1,
  simp only [subgroup.mem_top, iff_true],
  apply free_group.induction_on x;
  clear x,
  {
    apply subgroup.one_mem,
  },
  {
    apply free_of_in_pq_group_relation_space,
  },
  {
    intro x,
    apply subgroup.inv_mem,
  },
  {
    apply subgroup.mul_mem,
  },
end

-- This is not true!!! Everything going forward is useless

variables {R : subgroup (free_group s)} [hR : R.normal]
include hR

instance rel_intersection_is_normal : (R ⊓ pq_group_relation_space).normal :=
begin
  fconstructor,
  intros n hn g,
  cases hn with hn1 hn2,
  split,
  apply hR.conj_mem, assumption,
  apply pq_group_relation_space_is_normal.conj_mem, assumption,
end


def pq_group_free_quotient_iso_rel_intersect_forward : pq_group (quotient_group.quotient R) →* quotient_group.quotient (R ⊓ pq_group_relation_space) :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro x,
    induction x,
    {
      exact quotient_group.mk x,
    },
    {
      simp only [eq_rec_constant],
      apply quotient.sound,
      show x_a⁻¹ * x_b ∈ (R ⊓ pq_group_relation_space),
      have hx : x_a⁻¹ * x_b ∈ R := x_p,
      sorry,
    },
  },
  sorry,
end

def pq_group_free_quotient_iso_rel_intersect : pq_group (quotient_group.quotient R) ≃* quotient_group.quotient (R ⊓ pq_group_relation_space) := { 
  to_fun := sorry,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry,
  map_mul' := sorry }

end pq_group_free_quotient

