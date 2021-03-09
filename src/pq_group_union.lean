
import pq_to_group
import tactic


universes u v

section pq_group_union

variables {Q1 : Type u} {Q2 : Type v} [power_quandle Q1] [power_quandle Q2]

lemma group_prod_pow_nat {G : Type u} {H : Type v} [group G] [group H] (a : G) (b : H) (n : ℕ) : (a, b)^n = (a^n, b^n) :=
begin
  induction n with n hn,
  {refl,},
  repeat {rw pow_succ},
  rw hn,
  simp only [prod.mk_mul_mk],
end

lemma group_prod_pow {G : Type u} {H : Type v} [group G] [group H] (a : G) (b : H) (n : ℤ) : (a, b)^n = (a^n, b^n) :=
begin
  induction n,
  {apply group_prod_pow_nat,},
  repeat {rw gpow_neg_succ_of_nat},
  rw group_prod_pow_nat,
  simp only [prod.inv_mk],
end

def pq_group_oplus_to_prod : pq_group (Q1 ⊕ Q2) →* pq_group Q1 × pq_group Q2 :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro x,
    cases x,
    {
      exact ⟨of x, 1⟩,
    },
    {
      exact ⟨1, of x⟩,
    },
  },
  {
    split,
    {
      intros a b,
      cases a;
      cases b,
      {
        rw rhd_def_union_ll,
        simp only,
        rw ←rhd_of_eq_of_rhd,
        rw rhd_def,
        rw rhd_def,
        simp only [one_inv, mul_one, prod.inv_mk, prod.mk_mul_mk],
      },
      {
        rw rhd_def_union_lr,
        simp only,
        rw rhd_def,
        simp only [one_inv, mul_one, one_mul, prod.inv_mk, mul_right_inv, prod.mk_mul_mk],
      },
      {
        rw rhd_def_union_rl,
        simp only,
        rw rhd_def,
        simp only [one_inv, mul_one, one_mul, prod.inv_mk, mul_right_inv, prod.mk_mul_mk],
      },
      {
        rw rhd_def_union_rr,
        simp only,
        rw ←rhd_of_eq_of_rhd,
        rw rhd_def,
        rw rhd_def,
        simp only [one_inv, mul_one, prod.inv_mk, prod.mk_mul_mk],
      },
    },
    {
      intros a n,
      cases a,
      {
        rw pow_def_union_l,
        simp only,
        rw of_pow_eq_pow_of,
        rw group_prod_pow,
        simp only [one_gpow],
      },
      {
        rw pow_def_union_r,
        simp only,
        rw of_pow_eq_pow_of,
        rw group_prod_pow,
        simp only [one_gpow],
      },
    }
  }
end

def pq_group_left_to_oplus : pq_group Q1 →* pq_group (Q1 ⊕ Q2) :=
begin
  fapply L_of_morph,
  {
    intro x,
    left,
    exact x,
  },
  split,
  {
    intros a b,
    rw rhd_def_union_ll,
  },
  {
    intros a n,
    rw pow_def_union_l,
  },
end

def pq_group_right_to_oplus : pq_group Q2 →* pq_group (Q1 ⊕ Q2) :=
begin
  fapply L_of_morph,
  {
    intro x,
    right,
    exact x,
  },
  split,
  {
    intros a b,
    rw rhd_def_union_rr,
  },
  {
    intros a n,
    rw pow_def_union_r,
  },
end

def pq_group_prod_to_oplus : pq_group Q1 × pq_group Q2 →* pq_group (Q1 ⊕ Q2) :=
begin
  fconstructor,
  {
    intro x,
    cases x with a b,
    let pa := @pq_group_left_to_oplus Q1 Q2 _ _ a,
    let pb := @pq_group_right_to_oplus Q1 Q2 _ _ b,
    exact pa * pb,
  },
  {
    have one_rw : (1 : pq_group Q1 × pq_group Q2) = (1, 1) := rfl,
    rw one_rw,
    simp only [mul_one, monoid_hom.map_one],
  },
  {
    intros x y,
    cases x with x1 x2,
    cases y with y1 y2,
    have prod_rw : ((x1, x2) * (y1, y2) : pq_group Q1 × pq_group Q2) = (x1 * y1, x2 * y2) := rfl,
    rw prod_rw,
    clear prod_rw,
    simp only [monoid_hom.map_mul],
    suffices : pq_group_left_to_oplus y1 * pq_group_right_to_oplus x2 = pq_group_right_to_oplus x2 * pq_group_left_to_oplus y1,
    {
      group,
      rw @mul_assoc _ _ (pq_group_left_to_oplus x1) _ _,
      rw this,
      group,
    },
    clear x1 y2,
    induction y1,
    {
      rw quot_mk_helper,
      induction y1,
      {
        rw incl_unit_eq_unit,
        simp only [mul_one, one_mul, monoid_hom.map_one],
      },
      {
        rw ←of_def,
        have fun_of_rw_l : pq_group_left_to_oplus (of y1) = of ((sum.inl y1) : Q1 ⊕ Q2) := rfl,
        rw fun_of_rw_l,
        induction x2,
        {
          rw quot_mk_helper,
          induction x2,
          {
            rw incl_unit_eq_unit,
            simp only [mul_one, one_mul, monoid_hom.map_one],
          },
          {
            rw ←of_def,
            have fun_of_rw_r : pq_group_right_to_oplus (of x2) = of ((sum.inr x2) : Q1 ⊕ Q2) := rfl,
            rw fun_of_rw_r,
            suffices : (of (sum.inr x2)) * (of (sum.inl y1)) * (of (sum.inr x2))⁻¹ = of (sum.inl y1),
            {
              apply eq.symm,
              rw center_reformulate,
              exact this,
            },
            rw ←rhd_def,
            rw rhd_of_eq_of_rhd,
            apply congr_arg,
            refl,
          },
          {
            rw ←mul_def,
            simp only [monoid_hom.map_mul],
            rw ←mul_assoc,
            rw x2_ih_a,
            rw mul_assoc,
            rw x2_ih_b,
            rw ←mul_assoc,
          },
          {
            rw ←inv_def,
            simp only [monoid_hom.map_inv],
            group,
            rw ←inv_inj,
            group,
            simp only [gpow_one, gpow_neg],
            rw @mul_assoc _ _ (pq_group_right_to_oplus ⟦x2_a⟧)⁻¹ _ _,
            rw x2_ih,
            group,
          },

        },
        {refl,},
        
      },
      {
        rw ←mul_def,
        simp only [monoid_hom.map_mul],
        rw mul_assoc,
        rw y1_ih_b,
        rw ←mul_assoc,
        rw y1_ih_a,
        rw mul_assoc,
      },
      {
        rw ←inv_def,
        simp only [monoid_hom.map_inv],
        group,
        simp only [gpow_one, gpow_neg],
        rw @mul_assoc _ _ (pq_group_left_to_oplus ⟦y1_a⟧)⁻¹ _ _,
        rw ←y1_ih,
        group,
      },
    },
    {refl,},
  },
end

theorem pq_group_union_prod_inv_left : @pq_group_prod_to_oplus Q1 Q2 _ _ ∘ pq_group_oplus_to_prod = id :=
begin
  funext,
  simp only [id.def, function.comp_app],
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
      unfold pq_group_oplus_to_prod,
      rw pq_morph_to_L_morph_adj_comm_of,
      cases x,
      {
        simp only,
        unfold pq_group_prod_to_oplus,
        simp only [mul_one, monoid_hom.coe_mk, monoid_hom.map_one],
        refl,
      },
      {
        simp only,
        unfold pq_group_prod_to_oplus,
        simp only [one_mul, monoid_hom.coe_mk, monoid_hom.map_one],
        refl,
      }
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
end

theorem pq_group_union_prod_inv_right : @pq_group_oplus_to_prod Q1 Q2 _ _ ∘ pq_group_prod_to_oplus = id :=
begin
  funext,
  simp only [id.def, function.comp_app],
  cases x with x1 x2,
  unfold pq_group_prod_to_oplus,
  simp only [monoid_hom.map_mul, monoid_hom.coe_mk],
  suffices : pq_group_oplus_to_prod (pq_group_left_to_oplus x1) = (x1, (1 : pq_group Q2)) ∧ pq_group_oplus_to_prod (pq_group_right_to_oplus x2) = ((1 : pq_group Q1), x2),
  {
    cases this with h1 h2,
    rw h1,
    rw h2,
    simp only [mul_right_eq_self, mul_left_eq_self, prod.mk.inj_iff, eq_self_iff_true, and_self, prod.mk_mul_mk],
  },
  split,
  {
    clear x2,
    induction x1,
    {
      rw quot_mk_helper,
      induction x1,
      {
        rw incl_unit_eq_unit,
        simp only [monoid_hom.map_one],
        refl,
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
        simp only [mul_one, prod.mk_mul_mk],
      },
      {
        rw ←inv_def,
        simp only [monoid_hom.map_inv],
        rw x1_ih,
        simp only [one_inv, prod.inv_mk],
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
        refl,
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
        simp only [mul_one, prod.mk_mul_mk],
      },
      {
        rw ←inv_def,
        simp only [monoid_hom.map_inv],
        rw x2_ih,
        simp only [one_inv, prod.inv_mk],
      },
      
    },
    {refl,},
  },
end

def pq_group_union : pq_group (Q1 ⊕ Q2) ≃* pq_group Q1 × pq_group Q2 := { 
  to_fun := pq_group_oplus_to_prod,
  inv_fun := pq_group_prod_to_oplus,
  left_inv := congr_fun pq_group_union_prod_inv_left,
  right_inv := congr_fun pq_group_union_prod_inv_right,
  map_mul' := is_mul_hom.map_mul _ }

#check pq_group_union

end pq_group_union
