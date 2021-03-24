
import pq_to_group
import minimal_sub_pq_gen_group
import group_theory.semidirect_product

universes u1 u2

section pq_like_semidirect_product

variables {Q1 : Type u1} {Q2 : Type u2} [power_quandle Q1] [power_quandle Q2]


variables {φ : pq_group Q2 →* mul_aut (pq_group Q1)}

variables {hφ : ∀ x : Q2, ∀ y : Q1, ∃ z : Q1, ((φ (of x)) (of y)) = of z}

def semidirect_product_gen : set (pq_group Q1 ⋊[φ] pq_group Q2) := λ x, (∃ q : Q1, x = semidirect_product.inl (of q)) ∨ (∃ q : Q2, x = semidirect_product.inr (of q))


def lhs_to_pq_gen_set_semidirect : pq_group Q1 →* pq_group (free_gen_group_sub_pq (@semidirect_product_gen _ _ _ _ φ)) :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro q,
    apply of,
    fconstructor,
    exact semidirect_product.inl (of q),
    apply gen_in_free_group_sub_pq_carrier,
    left,
    use q,
  },
  {
    split,
    {
      intros a b,
      rw rhd_of_eq_of_rhd,
      apply congr_arg,
      ext1,
      simp only [subtype.coe_mk],
      rw ←rhd_of_eq_of_rhd,
      rw rhd_def,
      simp only [monoid_hom.map_mul, monoid_hom.map_mul_inv],
      rw ←rhd_def,
      refl,
    },
    {
      intros a n,
      rw ←of_pow_eq_pow_of,
      apply congr_arg,
      ext1,
      simp only [subtype.coe_mk],
      rw of_pow_eq_pow_of,
      rw monoid_hom.map_gpow,
      refl,
    },
  }
end


def rhs_to_pq_gen_set_semidirect : pq_group Q2 →* pq_group (free_gen_group_sub_pq (@semidirect_product_gen _ _ _ _ φ)) :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro q,
    apply of,
    fconstructor,
    exact semidirect_product.inr (of q),
    apply gen_in_free_group_sub_pq_carrier,
    right,
    use q,
  },
  {
    split,
    {
      intros a b,
      rw rhd_of_eq_of_rhd,
      apply congr_arg,
      ext1,
      simp only [subtype.coe_mk],
      rw ←rhd_of_eq_of_rhd,
      rw rhd_def,
      simp only [monoid_hom.map_mul, monoid_hom.map_mul_inv],
      rw ←rhd_def,
      refl,
    },
    {
      intros a n,
      rw ←of_pow_eq_pow_of,
      apply congr_arg,
      ext1,
      simp only [subtype.coe_mk],
      rw of_pow_eq_pow_of,
      rw monoid_hom.map_gpow,
      refl,
    },
  }
end

variables {G : Type*} [group G]

lemma subtype_rhd_def (a b : G) (gen : set G) {ha : a ∈ (↑(free_gen_group_sub_pq gen) : set G)} {hb : b ∈ (↑(free_gen_group_sub_pq gen) : set G)} : (⟨a, ha⟩ : free_gen_group_sub_pq gen) ▷ ⟨b, hb⟩ = ⟨a ▷ b, sub_power_quandle.closed_rhd (free_gen_group_sub_pq gen) a b ha hb⟩ := 
begin
  refl,
end


lemma rhd_mul : ∀ x y z : G, x ▷ (y * z) = (x ▷ y) * (x ▷ z) :=
begin
  intros x y z,
  repeat {rw rhd_def},
  group,
end

lemma mul_rhd : ∀ x y z : G, (x * y) ▷ z = x ▷ (y ▷ z) :=
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

include hφ

def semidirect_to_pq_gen_set_semidirect : pq_group Q1 ⋊[φ] pq_group Q2 →* pq_group (free_gen_group_sub_pq (@semidirect_product_gen _ _ _ _ φ)) :=
begin
  fapply semidirect_product.lift,
  {
    apply lhs_to_pq_gen_set_semidirect,
  },
  {
    apply rhs_to_pq_gen_set_semidirect,
  },
  {
    intro x,
    ext1 y,
    simp only [mul_equiv.coe_to_monoid_hom, mul_aut.conj_apply, function.comp_app, monoid_hom.coe_comp],
    revert y,
    induction x,
    {
      rw quot_mk_helper,
      induction x,
      {
        intro y,
        rw incl_unit_eq_unit,
        simp only [one_inv, mul_aut.one_apply, mul_one, one_mul, monoid_hom.map_one],
      },
      {
        intro y,
        rw ←of_def,
        rw ←rhd_def,
        unfold rhs_to_pq_gen_set_semidirect,
        rw pq_morph_to_L_morph_adj_comm_of,

        induction y,
        {
          rw quot_mk_helper,
          induction y,
          {
            rw incl_unit_eq_unit,
            simp only [mul_equiv.map_one, monoid_hom.map_one],
            rw rhd_def,
            simp only [mul_one, mul_right_inv],
          },
          {
            rw ←of_def,
            unfold lhs_to_pq_gen_set_semidirect,
            rw pq_morph_to_L_morph_adj_comm_of,
            rw rhd_of_eq_of_rhd,
            rw subtype_rhd_def,
            simp_rw rhd_def,
            cases hφ x y with z hz,
            rw hz,
            rw pq_morph_to_L_morph_adj_comm_of,
            apply congr_arg,
            ext1,
            simp only [subtype.coe_mk],
            rw ←hz,
            rw semidirect_product.inl_aut (of x) (of y),
            simp only [monoid_hom.map_inv],
          },
          {
            rw ←mul_def,
            simp only [monoid_hom.map_mul, mul_equiv.map_mul],
            rw rhd_mul,
            rw y_ih_a,
            rw y_ih_b,
          },
          {
            rw ←inv_def,
            simp only [monoid_hom.map_inv, mul_equiv.map_inv],
            rw rhd_inv,
            rw y_ih,
          },
        },
        {refl,},
      },
      {
        intro y,
        rw ←mul_def,
        rw ←rhd_def,
        simp only [monoid_hom.map_mul, mul_aut.mul_apply],
        rw mul_rhd,
        --rw ←rhd_def at x_ih_a x_ih_b,
        specialize x_ih_b y,
        rw ←rhd_def at x_ih_b,
        rw ←x_ih_b,
        simp_rw ←rhd_def at x_ih_a,
        rw ←x_ih_a,
      },
      {
        intro y,
        specialize x_ih ((φ ⟦x_a⟧⁻¹) y),
        simp only [mul_aut.apply_inv_self, monoid_hom.map_inv] at x_ih,
        rw ←inv_def,
        simp only [inv_inv, monoid_hom.map_inv],
        rw x_ih,
        group,
      },
    },
    {
      intro y,
      refl,
    },
  },
end


def semidirect_product_pq_like : pq_group Q1 ⋊[φ] pq_group Q2 ≃* pq_group (free_gen_group_sub_pq (@semidirect_product_gen _ _ _ _ φ)) := 
{ to_fun := @semidirect_to_pq_gen_set_semidirect _ _ _ _ φ hφ,
  inv_fun := gen_set_counit semidirect_product_gen,
  left_inv := begin
    intro x,
    cases x with x1 x2,
    simp only [semidirect_product.mk_eq_inl_mul_inr, monoid_hom.map_mul],
    unfold semidirect_to_pq_gen_set_semidirect,
    rw semidirect_product.lift_inl,
    rw semidirect_product.lift_inr,
    apply congr_arg2,
    {
      clear x2,
      induction x1,
      {
        rw quot_mk_helper,
        induction x1,
        {
          rw incl_unit_eq_unit,
          simp only [monoid_hom.map_one],
        },
        {
          rw ←of_def,
          refl,
        },
        {
          rw ←mul_def,
          simp only [monoid_hom.map_mul],
          rw x1_ih_a,
          rw x1_ih_b,
        },
        {
          rw ←inv_def,
          simp only [inv_inj, monoid_hom.map_inv], 
          assumption,
        },
      },
      {refl,},
    },
    {
      clear x1,
      induction x2,
      {
        rw quot_mk_helper,
        induction x2,
        {
          rw incl_unit_eq_unit,
          simp only [monoid_hom.map_one],
        },
        {
          rw ←of_def,
          refl,
        },
        {
          rw ←mul_def,
          simp only [monoid_hom.map_mul],
          rw x2_ih_a,
          rw x2_ih_b,
        },
        {
          rw ←inv_def,
          simp only [inv_inj, monoid_hom.map_inv], 
          assumption,
        },
      },
      {refl,},
    },
  end,
  right_inv := begin
    intro x,
    induction x,
    {
      rw quot_mk_helper,
      induction x,
      {
        rw incl_unit_eq_unit,
        simp only [monoid_hom.map_one],
      },
      {
        rw ←of_def,
        unfold gen_set_counit,
        rw pq_morph_to_L_morph_adj_comm_of,
        cases x with x hx,
        simp only,
        induction hx,
        {
          cases hx_hx with hy hy,
          {
            cases hy with y hy,
            simp_rw hy,
            unfold semidirect_to_pq_gen_set_semidirect,
            rw semidirect_product.lift_inl,
            unfold lhs_to_pq_gen_set_semidirect,
            rw pq_morph_to_L_morph_adj_comm_of,
            refl,
          },
          {
            cases hy with y hy,
            simp_rw hy,
            unfold semidirect_to_pq_gen_set_semidirect,
            rw semidirect_product.lift_inr,
            unfold rhs_to_pq_gen_set_semidirect,
            rw pq_morph_to_L_morph_adj_comm_of,
            refl,
          },
        }, 
        {
          simp only [monoid_hom.map_mul, monoid_hom.map_mul_inv],
          simp_rw ←rhd_def,
          rw hx_ih_hx,
          rw hx_ih_hy,
          rw rhd_of_eq_of_rhd,
          apply congr_arg,
          refl,
        },
        {
          rw monoid_hom.map_gpow,
          rw hx_ih,
          rw ←of_pow_eq_pow_of,
          apply congr_arg,
          refl,
        },
      },
      {
        rw ←mul_def,
        simp only [monoid_hom.map_mul],
        rw x_ih_a,
        rw x_ih_b,
      },
      {
        rw ←inv_def,
        simp only [inv_inj, monoid_hom.map_inv],
        assumption,
      },
    },
    {refl,},
  end,
  map_mul' := begin
    intros x y,
    simp only [monoid_hom.map_mul],
  end }


end pq_like_semidirect_product

