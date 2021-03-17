
import pq_to_group

universe u


section pq_group_decidable_eq

variables {Q : Type u} [power_quandle Q] [decidable_eq Q]

lemma of_eq_unit (a : Q) : of a = 1 ↔ a = a ^ (0 : ℤ) :=
begin
  split,
  {
    intro ha,
    sorry,
  },
  {
    intro h,
    rw h,
    rw of_pow_eq_pow_of,
    simp only [gpow_zero],
  },
end

instance pq_group_decidable_eq : decidable_eq (pq_group Q) :=
begin
  intros a b,
  suffices : ∀ a : pq_group Q, decidable (a = 1),
  {
    specialize this (a*b⁻¹),
    refine decidable_of_decidable_of_iff this _,
    split,
    {
      intro h,
      group at *,
      exact h,
    },
    {
      intro h,
      rw h,
      simp only [mul_right_inv],
    },
  },
  clear a b,
  intro a,
  induction a,
  {
    rw quot_mk_helper,
    induction a,
    {
      apply decidable.is_true,
      refl,
    },
    {
      rw ←of_def,
      sorry,
    },
    {
      sorry,
    },
    {
      sorry,
    },
  },
  {
    sorry,
  },
end


instance pq_group_decidable_eq_2 : decidable_eq (pq_group Q) :=
begin
  intro a,
  induction a,
  {
    rw quot_mk_helper,
    induction a,
    {
      --apply decidable.is_true,
      --refl,
      sorry,
    },
    {
      rw ←of_def,
      sorry,      
    },
    {
      sorry,
    },
    {
      sorry,
    },
  },
  {
    sorry,
  },
end

end pq_group_decidable_eq

