
import sub_pq
import group_to_pq

import group_theory.subgroup

universe u

section pq_center


def pq_center (Q : Type u) [power_quandle Q] : sub_power_quandle Q := { 
  carrier := λ x, ∀ y : Q, y ▷ x = x,
  closed_rhd := begin 
    intros x y hx hy z,
    rw power_quandle.rhd_dist,
    rw hx,
    rw hy,
  end,
  closed_pow := begin 
    intros x n hx y,
    rw ←power_quandle.pow_rhd,
    rw hx,
  end,
  closed_one := begin 
    intros x,
    rw power_quandle.rhd_one,
  end }



end pq_center

section pq_center_iso_center

variables {G : Type u} [group G]

def pq_center_iso_center : pq_center G ≃ subgroup.center G := { 
  to_fun := begin 
    intro x,
    cases x with x hx,
    fconstructor,
    exact x,
    intro y,
    specialize hx y,
    rw rhd_def_group at hx,
    rw ←hx,
    simp only [mul_right_inj, inv_mul_cancel_right],
    exact hx,
  end,
  inv_fun := begin 
    intro x,
    cases x with x hx,
    fconstructor,
    exact x,
    intro y,
    specialize hx y,
    rw rhd_def_group,
    rw hx,
    simp only [mul_inv_cancel_right],
  end,
  left_inv := begin 
    intro x,
    cases x with x hx,
    simp only,
  end,
  right_inv := begin 
    intro x,
    cases x with x hx,
    simp only,
  end }


end pq_center_iso_center

/-

section pq_non_center

def pq_non_center (Q : Type u) [power_quandle Q] (hQ : ∀ x y : Q, x ▷ y = y ↔ y ▷ x = x) : sub_power_quandle Q := { 
  carrier := λ x, x = 1 ∨ ¬ (∀ y : Q, y ▷ x = x),
  closed_rhd := begin 
    intros x y hx hy,
    simp only [set.mem_def] at *,
    cases hy,
    {
      left,
      rw hy,
      rw power_quandle.rhd_one,
    },
    {
      right,
      intro hxy,
      apply hy,
      intro z,
      specialize hxy (x ▷ z),
      rw ←power_quandle.rhd_dist at hxy,
      apply rhd_map_is_injective x hxy,
    },
  end,
  closed_pow := begin 
    intros x n hx,
    simp only [set.mem_def] at *,
    cases hx,
    {
      left,
      rw hx,
      rw pq_one_pow,
    },
    {
      by_cases (x^n = 1),
      {
        left,
        exact h,
      },
      {
        right,
        intro hxn,
        apply hx,
        intro z,
        specialize hxn (x^(n - 1) ▷ z),
        rw hQ at hxn,
        
        /-
        simp only [not_forall] at hx,
        cases hx with z hz,
        -/
        /-
        Suppose x^n = y^n and x^n =/= 1. Prove x = y

        Suppose x^n is in the center, and x^n =/= 1. Prove x is.
        x^n ▷ y = y and y ▷ x^n = x^n for all x, y
        y ▷ x = (x^n ▷ y) ▷ (x^n ▷ x)
        x ▷ y = x^n ▷ (x^{1-n} ▷ y) = x^{1-n} ▷ y
        
        Suppose x is not in the center but x^n is.


        Can we use induction on n?

        x^n in center → x in center

        Prove x^{n + 1} in center → x in center

        x^n ▷ x ▷ y = y for all y

        Pick y = z ◁ x
        -/
        
      },
      --right,
      --intro hxn,
      --apply hx,
      --sorry,
    },
  end,
  closed_one := begin 
    left,
    refl,
  end }


end pq_non_center

-/