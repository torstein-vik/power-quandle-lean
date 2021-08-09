
/-

Idea: Take (homo_locus_pres G) × G and introduce multiplication:
(x, a) * (y, b) = (x * y * homo_locus_of(a, b), a * b)

Prove it is a group. Then prove it is isomorphic to pq_group G

-/

import pq_group_homo_locus_pres

universes u

section pq_group_homo_locus_pres_prod

@[ext]
structure homo_locus_pres_prod (G : Type u) [group G] := (x : homo_locus_pres G) (a : G)

variables {G : Type u} [group G]

instance homo_locus_pres_prod_is_group : group (homo_locus_pres_prod G) := { 
  mul := λ ⟨x, a⟩ ⟨y, b⟩, ⟨x * y * homo_locus_of(a, b), a * b⟩,
  inv := λ ⟨x, a⟩, ⟨x⁻¹, a⁻¹⟩,
  one := ⟨1, 1⟩,
  mul_assoc := begin 
    rintros ⟨x, a⟩ ⟨y, b⟩ ⟨z, c⟩,
    ext1,
    {
      show (x * y * homo_locus_of (a, b)) * z * homo_locus_of (a * b, c) = x * (y * z * homo_locus_of (b, c)) * homo_locus_of (a, b * c),
      simp only [mul_assoc],
      apply congr_arg,
      apply congr_arg,
      rw ←mul_assoc,
      rw homo_locus_pres_comm,
      rw ←mul_assoc,
      rw homo_locus_assoc a b c,
      rw homo_locus_pres_comm,
      apply congr_arg,
      rw homo_locus_pres_comm,
    },
    {
      show a * b * c = a * (b * c),
      rw mul_assoc,
    },
  end,
  one_mul := begin 
    rintros ⟨x, a⟩,
    ext1,
    {
      show 1 * x * homo_locus_of (1, a) = x,
      rw homo_locus_of_one,
      simp only [mul_one, one_mul],
      exact homo_locus_closed_left_one a,
    },
    {
      show 1 * a = a,
      rw one_mul,
    },
  end,
  mul_one := begin 
    rintros ⟨x, a⟩,
    ext1,
    {
      show x * 1 * homo_locus_of (a, 1) = x,
      rw homo_locus_of_one,
      simp only [mul_one, one_mul],
      exact homo_locus_closed_right_one a,
    },
    {
      show a * 1 = a,
      rw mul_one,
    },
  end,
  mul_left_inv := begin 
    rintros ⟨x, a⟩,
    ext1,
    {
      show x⁻¹ * x * homo_locus_of (a⁻¹, a) = 1,
      rw mul_left_inv,
      rw one_mul,
      apply homo_locus_of_one,
      exact homo_locus_closed_left_inv a,
    },
    {
      show a⁻¹ * a = 1,
      rw mul_left_inv,
    },
  end }

lemma homo_locus_pres_prod_mul_def (x y : homo_locus_pres G) (a b : G) : (⟨x, a⟩ * ⟨y, b⟩ : homo_locus_pres_prod G) = ⟨x * y * homo_locus_of (a, b), a * b⟩ := rfl

lemma homo_locus_pres_prod_inv_def (x : homo_locus_pres G) (a : G) : (⟨x, a⟩⁻¹ : homo_locus_pres_prod G) = ⟨x⁻¹, a⁻¹⟩ := rfl

lemma homo_locus_pres_prod_one_def : (1 : homo_locus_pres_prod G) = ⟨1, 1⟩ := rfl

lemma homo_locus_pres_prod_mul_def_unsplit (x y : homo_locus_pres_prod G) : (x * y : homo_locus_pres_prod G) = ⟨x.x * y.x * homo_locus_of (x.a, y.a), x.a * y.a⟩ := begin 
  cases x,
  cases y,
  refl,
end

lemma homo_locus_pres_prod_inv_def_unsplit (x : homo_locus_pres_prod G) : (x⁻¹ : homo_locus_pres_prod G) = ⟨x.x⁻¹, x.a⁻¹⟩ := begin 
  cases x,
  refl,
end


end pq_group_homo_locus_pres_prod

section pq_group_homo_locus_pres_prod_iso

variables {G : Type u} [group G]

def pq_group_homo_locus_pres_prod_iso_forward : pq_group G →* homo_locus_pres_prod G :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro g,
    exact ⟨1, g⟩,
  },
  {
    split,
    {
      intros a b,
      conv {
        to_rhs,
        rw rhd_def_group,
      },
      simp only [homo_locus_pres_prod_mul_def, homo_locus_pres_prod_inv_def],
      split,
      {
        simp only [one_inv, mul_one, one_mul],
        rw ←homo_locus_of_inv,
        simp only [mul_right_inv],
      },
      {
        refl,
      },
    },
    {
      intros a,
      have for_nat : ∀ n : ℕ, (⟨1, a ^ n⟩ : homo_locus_pres_prod G) = ⟨1, a⟩ ^ n, 
      {
        intros n,
        induction n,
        {
          refl,
        },
        {
          rw pow_succ,
          rw pow_succ,
          rw ←n_ih,
          clear n_ih,
          rw homo_locus_pres_prod_mul_def,
          simp only,
          split,
          {
            simp only [one_mul],
            symmetry,
            apply homo_locus_of_one,
            convert homo_locus_closed_same_power a 1 n_n,
            rw gpow_one, 
          },
          {
            refl,
          },
        },
      },
      intros n,
      induction n,
      {
        simp only [int.of_nat_eq_coe, gpow_coe_nat],
        rw for_nat,
      },
      {
        simp only [gpow_neg_succ_of_nat],
        rw ←for_nat,
        simp only [homo_locus_pres_prod_inv_def],
        split,
        {
          rw one_inv,
        },
        {
          refl,
        },
      },
    },
  },
end

lemma pq_group_homo_locus_pres_prod_iso_forward_of (x : G) : pq_group_homo_locus_pres_prod_iso_forward (of x) = ⟨1, x⟩ := rfl

def pq_group_homo_locus_pres_prod_iso_backward : homo_locus_pres_prod G →* pq_group G := ⟨λ x, (↑(homo_locus_pres_iso_ker_counit_forward x.x) : pq_group G) * (of x.a), begin 
  simp only [homo_locus_pres_prod_one_def, of_one, mul_one, subgroup.coe_one, monoid_hom.map_one],
end, begin 
  rintros ⟨x, a⟩ ⟨y, b⟩,
  simp only [homo_locus_pres_prod_mul_def],
  simp only [monoid_hom.map_mul, subgroup.coe_mul],
  rw homo_locus_pres_iso_ker_counit_forward_homo_locus_of,
  simp only [subgroup.coe_mk],
  simp only [mul_assoc],
  simp only [mul_right_inj, mul_one, mul_left_inv],
  rw ←mul_assoc,
  rw counit_ker_center _ (of a),
  rw ←mul_assoc,
end⟩

lemma pq_group_homo_locus_pres_prod_iso_right_inv_aux (a b c : G) :  pq_group_homo_locus_pres_prod_iso_forward (pq_group_homo_locus_pres_prod_iso_backward {x := homo_locus_of (a, b), a := c}) = {x := homo_locus_of (a, b), a := c} :=
begin
  unfold pq_group_homo_locus_pres_prod_iso_backward,
  simp only [monoid_hom.map_mul, monoid_hom.coe_mk],
  rw homo_locus_pres_iso_ker_counit_forward_homo_locus_of,
  simp only [monoid_hom.map_mul, gpow_zero, monoid_hom.map_mul_inv, subgroup.coe_mk],
  simp only [pq_group_homo_locus_pres_prod_iso_forward_of],
  simp only [homo_locus_pres_prod_mul_def, homo_locus_pres_prod_inv_def],
  split,
  {
    have : homo_locus_of (a * b, (a * b)⁻¹) = 1,
    {
      rw homo_locus_of_one,
      exact homo_locus_closed_right_inv (a * b),
    },
    rw this,
    clear this,
    have : homo_locus_of (a * b * (a * b)⁻¹, c) = 1,
    {
      group,
      rw homo_locus_of_one,
      exact homo_locus_closed_left_one c,
    },
    rw this,
    clear this,
    group,
  },
  {
    group,
  },
end

def pq_group_homo_locus_pres_prod_iso : pq_group G ≃* homo_locus_pres_prod G := { 
  to_fun := pq_group_homo_locus_pres_prod_iso_forward,
  inv_fun := pq_group_homo_locus_pres_prod_iso_backward,
  left_inv := begin 
    apply morphism_equality_comp_elem_id,
    intros g,
    unfold pq_group_homo_locus_pres_prod_iso_forward,
    rw pq_morph_to_L_morph_adj_comm_of,
    unfold pq_group_homo_locus_pres_prod_iso_backward,
    simp only [monoid_hom.coe_mk],
    simp only [one_mul, subgroup.coe_one, monoid_hom.map_one],
  end,
  right_inv := begin 
    intros x,
    cases x with x a,
    induction x,
    {
      rw homo_locus_pres_quot_mk_helper,
      induction x generalizing a,
      {
        rw ←homo_locus_pres_one_def,
        convert pq_group_homo_locus_pres_prod_iso_right_inv_aux 1 1 a;
        {
          rw homo_locus_of_one,
          exact homo_locus_closed_refl 1,
        },
      },
      {
        rw ←homo_locus_of_def (x_x, x_y),
        rw pq_group_homo_locus_pres_prod_iso_right_inv_aux,
      },
      {
        rw ←homo_locus_pres_mul_def,
        have : ({x := ⟦x_x⟧ * ⟦x_y⟧, a := a} : homo_locus_pres_prod G) = {x := ⟦x_x⟧, a := a} * {x := ⟦x_y⟧, a := 1},
        {
          rw homo_locus_pres_prod_mul_def,
          ext1,
          {
            simp only,
            suffices : homo_locus_of (a, 1) = 1,
            {
              rw this,
              rw mul_one,
            },
            rw homo_locus_of_one,
            exact homo_locus_closed_right_one a,
          },
          {
            simp only,
            rw mul_one,
          },
        },
        rw this,
        simp only [monoid_hom.map_mul],
        congr,
        apply x_ih_x,
        apply x_ih_y,
      },
      {
        rw ←homo_locus_pres_inv_def,
        have : ({x := ⟦x_x⟧⁻¹, a := a} : homo_locus_pres_prod G) = {x := ⟦x_x⟧, a := a⁻¹}⁻¹,
        {
          rw homo_locus_pres_prod_inv_def,
          rw inv_inv,
        },
        rw this,
        simp only [inv_inj, monoid_hom.map_inv],
        apply x_ih,
      },
    },
    {refl,},
  end,
  map_mul' := begin 
    intros a b,
    simp only [monoid_hom.map_mul],
  end }

lemma pq_group_homo_locus_pres_prod_iso_left_inv (x : pq_group G) : pq_group_homo_locus_pres_prod_iso_backward(pq_group_homo_locus_pres_prod_iso_forward x) = x :=
begin
  apply pq_group_homo_locus_pres_prod_iso.left_inv,
end

lemma pq_group_homo_locus_pres_prod_iso_right_inv (x : homo_locus_pres_prod G) : pq_group_homo_locus_pres_prod_iso_forward(pq_group_homo_locus_pres_prod_iso_backward x) = x :=
begin
  apply pq_group_homo_locus_pres_prod_iso.right_inv,
end

end pq_group_homo_locus_pres_prod_iso
