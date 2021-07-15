
import group_theory.free_group

import sub_pq


universe u

section pq_group_sub_pq_free_rel

variables {Q : Type u} [power_quandle Q] {Q1 : sub_power_quandle Q}


inductive pq_rel : free_group Q → Prop
| incl_conj (x y : Q) (hx : x ∈ (↑Q1 : set Q)) (hy : y ∈ (↑Q1 : set Q)) : pq_rel ((free_group.of x)*(free_group.of y)*(free_group.of x)⁻¹*(free_group.of (x ▷ y))⁻¹)
| incl_pow (x : Q) (hx : x ∈ (↑Q1 : set Q)) (n : ℤ) : pq_rel ((free_group.of x) ^ n * (free_group.of (x ^ n))⁻¹)
| mul (x y : free_group Q) (hx : pq_rel x) (hy : pq_rel y) : pq_rel (x * y)
| inv (x : free_group Q) (hx : pq_rel x) : pq_rel (x⁻¹)
| one : pq_rel 1


def pq_rel_subgroup (Q1 : sub_power_quandle Q) : subgroup (free_group Q) := { 
  carrier := @pq_rel Q _ Q1,
  one_mem' := pq_rel.one,
  mul_mem' := pq_rel.mul,
  inv_mem' := pq_rel.inv }

inductive sub_free_rel : free_group Q → Prop
| incl (x : Q) (hx : x ∈ (↑Q1 : set Q)) : sub_free_rel (free_group.of x)
| mul (x y : free_group Q) (hx : sub_free_rel x) (hy : sub_free_rel y) : sub_free_rel (x * y)
| inv (x : free_group Q) (hx : sub_free_rel x) : sub_free_rel (x⁻¹)
| one : sub_free_rel 1

def sub_free_subgroup (Q1 : sub_power_quandle Q) : subgroup (free_group Q) := { 
  carrier := @sub_free_rel Q _ Q1,
  one_mem' := sub_free_rel.one,
  mul_mem' := sub_free_rel.mul,
  inv_mem' := sub_free_rel.inv }

lemma sub_free_subgroup_of_mem (Q1 : sub_power_quandle Q) (x : Q) : x ∈ (↑Q1 : set Q) ↔ free_group.of x ∈ sub_free_subgroup Q1 :=
begin
  split,
  {
    intro hx,
    apply sub_free_rel.incl x hx,
  },
  {
    generalize hx : free_group.of x = y,
    intro hy,
    induction y,
    {
      induction y,
      {
        clear hy,
        exfalso,
        rw free_group.of at hx,
        have hx1 := free_group.red.exact.mp hx,
        sorry,
      },
      {
        sorry,
      },
    },
    {
      refl,
    },
  },
end

lemma pq_rel_sub_pq (Q1 : sub_power_quandle Q) (Q2 : sub_power_quandle Q) (hQ2 : Q1 ≤ Q2) : pq_rel_subgroup Q1 ≤ pq_rel_subgroup Q2 :=
begin
  intros x hx,
  induction hx,
  {
    apply pq_rel.incl_conj,
    {
      apply hQ2,
      exact hx_hx,
    },
    {
      apply hQ2,
      exact hx_hy, 
    },
  },
  {
    apply pq_rel.incl_pow,
    {
      apply hQ2,
      exact hx_hx,
    },
  },
  {
    exact (pq_rel_subgroup Q2).mul_mem hx_ih_hx hx_ih_hy,
  },
  {
    exact (pq_rel_subgroup Q2).inv_mem hx_ih,
  },
  {
    exact (pq_rel_subgroup Q2).one_mem,
  },
end

lemma pq_rel_sub_sub_free (Q1 : sub_power_quandle Q) : pq_rel_subgroup Q1 ≤ sub_free_subgroup Q1 :=
begin
  intros x hx,
  induction hx,
  {
    apply (sub_free_subgroup Q1).mul_mem,
    apply (sub_free_subgroup Q1).mul_mem,
    apply (sub_free_subgroup Q1).mul_mem,
    apply sub_free_rel.incl, assumption,
    apply sub_free_rel.incl, assumption,
    apply (sub_free_subgroup Q1).inv_mem,
    apply sub_free_rel.incl, assumption,
    apply (sub_free_subgroup Q1).inv_mem,
    apply sub_free_rel.incl,
    exact Q1.closed_rhd hx_x hx_y hx_hx hx_hy,
  },
  {
    apply (sub_free_subgroup Q1).mul_mem,
    apply (sub_free_subgroup Q1).gpow_mem,
    apply sub_free_rel.incl, assumption,
    apply (sub_free_subgroup Q1).inv_mem,
    apply sub_free_rel.incl,
    exact Q1.closed_pow hx_x hx_n hx_hx,
  },
  {
    exact (sub_free_subgroup Q1).mul_mem hx_ih_hx hx_ih_hy,
  },
  {
    exact (sub_free_subgroup Q1).inv_mem hx_ih,
  },
  {
    exact (sub_free_subgroup Q1).one_mem,
  },
end

inductive pq_rel_element (Q1 : sub_power_quandle Q) : Type u
| conj_incl (x y : Q) (hx : x ∈ (↑Q1 : set Q)) (hy : y ∈ (↑Q1 : set Q)) : pq_rel_element
| conj_incl_inv (x y : Q) (hx : x ∈ (↑Q1 : set Q)) (hy : y ∈ (↑Q1 : set Q)) : pq_rel_element
| pow_incl (x : Q) (n : ℤ) (hx : x ∈ (↑Q1 : set Q)) : pq_rel_element
| pow_incl_inv (x : Q) (n : ℤ) (hx : x ∈ (↑Q1 : set Q)) : pq_rel_element

def pq_rel_element_to_free (Q1 : sub_power_quandle Q) : pq_rel_element Q1 → free_group Q
| (pq_rel_element.conj_incl x y hx hy) := (free_group.of x)*(free_group.of y)*(free_group.of x)⁻¹*(free_group.of (x ▷ y))⁻¹
| (pq_rel_element.conj_incl_inv x y hx hy) := (free_group.of (x ▷ y))*(free_group.of x)*(free_group.of y)⁻¹*(free_group.of x)⁻¹
| (pq_rel_element.pow_incl x n hx) := ((free_group.of x) ^ n * (free_group.of (x ^ n))⁻¹)
| (pq_rel_element.pow_incl_inv x n hx) := ((free_group.of (x ^ n)) * (free_group.of x) ^ (-n))

def pq_rel_element_inv (Q1 : sub_power_quandle Q) : pq_rel_element Q1 → pq_rel_element Q1
| (pq_rel_element.conj_incl x y hx hy) := (pq_rel_element.conj_incl_inv x y hx hy)
| (pq_rel_element.conj_incl_inv x y hx hy) := (pq_rel_element.conj_incl x y hx hy)
| (pq_rel_element.pow_incl x n hx) := (pq_rel_element.pow_incl_inv x n hx)
| (pq_rel_element.pow_incl_inv x n hx) := (pq_rel_element.pow_incl x n hx)

theorem pq_rel_element_inv_to_free (Q1 : sub_power_quandle Q) (x : pq_rel_element Q1) : pq_rel_element_to_free Q1 (pq_rel_element_inv Q1 x) = (pq_rel_element_to_free Q1 x)⁻¹ :=
begin
  cases x,
  {
    unfold pq_rel_element_inv,
    unfold pq_rel_element_to_free,
    group,
  },
  {
    unfold pq_rel_element_inv,
    unfold pq_rel_element_to_free,
    group,
  },
  {
    unfold pq_rel_element_inv,
    unfold pq_rel_element_to_free,
    group,
  },
  {
    unfold pq_rel_element_inv,
    unfold pq_rel_element_to_free,
    group,
  },
end

theorem pq_rel_construction (x : free_group Q) (hx : x ∈ pq_rel_subgroup Q1) : ∃ y : list (pq_rel_element Q1), x = list.prod (list.map (pq_rel_element_to_free Q1) y) :=
begin
  induction hx,
  {
    use pq_rel_element.conj_incl hx_x hx_y hx_hx hx_hy :: list.nil,
    simp only [mul_one, list.prod_cons, list.prod_nil, list.map],
    refl,
  },
  {
    use pq_rel_element.pow_incl hx_x hx_n hx_hx :: list.nil,
    simp only [mul_one, list.prod_cons, list.prod_nil, list.map],
    refl,
  },
  {
    cases hx_ih_hx with a ha,
    cases hx_ih_hy with b hb,
    use a ++ b,
    simp only [list.map_append, list.prod_append],
    rw ha,
    rw hb,
  },
  {
    cases hx_ih with a ha,
    use (list.reverse (list.map (pq_rel_element_inv Q1) a)),
    rw ha,
    clear ha,
    simp only [list.map_reverse, list.map_map],
    induction a,
    {
      simp only [inv_eq_one, list.prod_nil, list.map, list.reverse_nil],
    },
    {
      simp only [list.reverse_cons, mul_inv_rev, mul_one, list.prod_append, function.comp_app, list.prod_cons, list.prod_nil, list.map],
      rw pq_rel_element_inv_to_free,
      simp only [mul_left_inj],
      rw a_ih,
    },
  },
  {
    use list.nil,
    simp only [list.prod_nil, list.map],
  },
end

theorem intersection_is_sub_pq_rel : (sub_free_subgroup Q1) ⊓ (pq_rel_subgroup (sub_pq_univ Q)) = (pq_rel_subgroup Q1) :=
begin
  ext1,
  split,
  {
    intro hx,
    rw subgroup.mem_inf at hx,
    cases hx with hx1 hx2,
    have hx3 := pq_rel_construction x hx2,
    cases hx3 with y hy,
    rw hy,
    rw hy at hx1,
    clear hx2,
    clear hy,
    clear x,
    rename hx1 hy,
    induction y,
    {
      simp only [list.prod_nil, list.map],
      exact (pq_rel_subgroup Q1).one_mem,
    },
    {
      simp only [list.prod_cons, list.map],
      simp only [list.prod_cons, list.map] at hy,
      by_cases (pq_rel_element_to_free (sub_pq_univ Q) y_hd ∈ pq_rel_subgroup Q1),
      {
        apply subgroup.mul_mem,
        apply h,
        apply y_ih,
        have alg_rw : (list.map (pq_rel_element_to_free (sub_pq_univ Q)) y_tl).prod = (pq_rel_element_to_free (sub_pq_univ Q) y_hd)⁻¹ * ((pq_rel_element_to_free (sub_pq_univ Q) y_hd) * (list.map (pq_rel_element_to_free (sub_pq_univ Q)) y_tl).prod),
        {
          group,
        },
        rw alg_rw,
        clear alg_rw,
        apply subgroup.mul_mem,
        {
          apply subgroup.inv_mem,
          apply pq_rel_sub_sub_free Q1 h,
        },
        {
          apply hy,
        },
      },
      {
        rename h hy1,
        cases y_hd,
        {
          rename y_hd_x a,
          rename y_hd_y b,
          unfold pq_rel_element_to_free at *,
          induction y_tl,
          {
            simp only [mul_one, list.prod_nil, list.map],
            simp only [mul_one, list.prod_nil, list.map] at hy,
            apply pq_rel.incl_conj,
            {
              suffices : free_group.of a ∈ sub_free_subgroup Q1,
              {
                rw sub_free_subgroup_of_mem,
                assumption,
              },
              sorry,
            },
            {
              sorry,
            },
          },
          {
            sorry,
          },
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
    },
  },
  {
    intro hx,
    rw subgroup.mem_inf,
    split,
    {
      apply pq_rel_sub_sub_free Q1 hx,
    },
    {
      apply pq_rel_sub_pq Q1 (sub_pq_univ Q) (sub_pq_univ_le Q1) hx,
    },
  },
end


end pq_group_sub_pq_free_rel
