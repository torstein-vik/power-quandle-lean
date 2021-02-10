
import pq_to_group

import tactic

universe u

section counit_ker_abelian

variables {G : Type u} [group G]

/-
theorem counit_ker_abelian : ∀ x : ((counit : pq_group G →* G).ker), ∀ y : pq_group G , ↑x * y = y * x :=
begin
  intro x,
  cases x with x hx,
  induction x,
  {
    repeat {simp_rw quot_mk_helper},
    induction x,
    {
      sorry,
    },
    {
      sorry,
    },
    {
      sorry,
    },
    {
      sorry,
    },
    
  },
  {intro y, refl,},
end
-/

lemma rhd_mul : ∀ x y z : G, x ▷ (y * z) = (x ▷ y) * (x ▷ z) :=
begin
  intros x y z,
  repeat {rw rhd_def},
  group,
end

lemma rhd_inv : ∀ x y : G, x ▷ y⁻¹ = (x ▷ y)⁻¹ :=
begin
  intros x y,
  repeat {rw ←gpow_neg_one},
  rw power_quandle.q_pown_right,
end 

lemma rhd_one : ∀ x : G, x ▷ 1 = 1 :=
begin
  intro x,
  have one_eq_one_pow_zero : (1 : G) = (1 : G) ^ (0 : ℤ) := rfl,
  rw one_eq_one_pow_zero,
  rw power_quandle.q_pow0 x (1 : G),
end

lemma of_inv : ∀ x : G, of (x⁻¹) = (of x)⁻¹ :=
begin
  intro x,
  repeat {rw ←gpow_neg_one},
  rw of_pow_eq_pow_of,
end


theorem inner_aut_eq : ∀ x y : pq_group G, x ▷ y = (of (counit x)) ▷ y :=
begin
  intros x,
  induction x,
  {
    rw quot_mk_helper,
    induction x,
    {
      intro y,
      rw ←unit_def,
      apply congr_arg (λ a, a ▷ y),
      rw monoid_hom.map_one,
      rw of_1_eq_unit,
    },
    {
      intro y,
      rw ←of_def,
      rw counit_of,
    },
    {
      intro y,

      rw counit_mul,
      rw ←mul_def,
      
      rw mul_rhd_eq_rhd,
      rw x_ih_b,
      rw x_ih_a,

      rw ←mul_rhd_eq_rhd,
      

      induction y,
      {
        rw quot_mk_helper at *,
        induction y,
        {
          rw ←unit_def,
          repeat {rw rhd_one},
        },
        {
          repeat {rw ←of_def at *},
          rw rhd_def,
          rw rhd_def,
          have halg_rw_1 : ∀ a b c : pq_group G, a*b*c*(a*b)⁻¹ = a*(b*c*b⁻¹)*a⁻¹,
          {
            intros a b c,
            group,
          },
          rw halg_rw_1,
          repeat {rw rhd_eq_conj},
          rw mul_rhd_eq_rhd,
        },
        {
          rw ←mul_def,
          rw rhd_mul,
          rw rhd_mul,
          rw y_ih_a,
          rw y_ih_b,
        },
        {
          rw ←inv_def,
          rw rhd_inv,
          rw y_ih,
          rw rhd_inv,
        },
      },
      {refl,},
      
    },
    {
      /-
      intro y,
      rw ←inv_def,
      have hx := x_ih (⟦x_a⟧⁻¹▷⟦x_a⟧⁻¹▷y),
      rw ←mul_rhd_eq_rhd at hx,
      simp only [mul_right_inv] at hx,
      rw one_rhd at hx,
      rw hx,
      -/
      intro y,
      rw ←inv_def,
      have hx := x_ih (⟦x_a⟧⁻¹▷y),
      rw ←mul_rhd_eq_rhd at hx,
      simp only [mul_right_inv] at hx,
      rw one_rhd at hx,
      --rw hx,
      rw monoid_hom.map_inv,
      rw of_inv,
      rw hx,
      rw ←mul_rhd_eq_rhd ((of _) ⁻¹),
      simp only [mul_left_inv],
      rw ←hx,
      rw one_rhd,
    }
  },
  {intro y, refl,},
end 


end counit_ker_abelian
