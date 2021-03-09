
import group_to_pq

universes u v

/-
section aut_comp

variables {Q : Type u} [power_quandle Q] {H : Type v} [group H]

instance premap_group (f : Q ≃ H) (hf : is_pq_morphism f) : group Q := { 
  mul := λ x y, f.symm (f x * f y),
  mul_assoc := begin
    intros a b c,
    dsimp only,
    apply congr_arg,
    simp only [equiv.apply_symm_apply],
    apply mul_assoc,
  end,
  one := f.symm 1,
  one_mul := begin
    intro a,
    rw ←equiv.symm_apply_apply f a,
    unfold has_mul.mul,
    unfold semigroup.mul,
    apply congr_arg,
    simp only [one_mul, equiv.apply_symm_apply],
  end,
  mul_one := begin
    intro a,
    rw ←equiv.symm_apply_apply f a,
    unfold has_mul.mul,
    unfold semigroup.mul,
    apply congr_arg,
    simp only [mul_one, equiv.apply_symm_apply],
  end,
  inv := λ x, x ^ (-1 : ℤ),
  mul_left_inv := begin
    intro a,
    simp only,
    unfold has_mul.mul,
    unfold semigroup.mul,
    unfold monoid.mul,
    rw hf.2,
    simp only [gpow_one, gpow_neg, mul_left_inv],
    refl,
  end }


theorem iso_as_pq (f : Q ≃ H) (hf : is_pq_morphism f) : @is_pq_morphism Q (@group_is_pq Q (premap_group f hf)) _ _ (id : Q → Q) :=
begin
  split,
  {
    intros a b,
    simp only [id.def],
    unfold has_triangle_right.triangle_right,
    unfold triangle_right_group,
    unfold has_mul.mul,
    unfold semigroup.mul,
    unfold monoid.mul,
    unfold group.mul,
    simp only [equiv.apply_symm_apply],
    unfold has_inv.inv,
    unfold group.inv,
    rw hf.2,
    rw gpow_neg_one,
    rw ←rhd_def (f a) (f b),
    rw ←hf.1,
    simp only [equiv.symm_apply_apply],
  },
  {
    intros a n,
    simp only [id.def],
    rw ←@equiv.apply_eq_iff_eq _ _ f,
    rw hf.2,
    induction n,
    {
      induction n,
      {
        simp only [int.coe_nat_zero, gpow_zero, int.of_nat_eq_coe],
        unfold has_pow.pow,
        simp only [group.gpow_eq_has_pow],
        sorry,
      },
      sorry,
    },
    {
      sorry,
    }
  }
end

end aut_comp
-/

section aut_comp_center

variables {G : Type u} {H : Type v} [group G] [group H]

--local attribute [instance] classical.prop_decidable

noncomputable def fun_center_to_all (f : subgroup.center G ≃ subgroup.center G) (hf : is_pq_morphism f) : G ≃ G := { 
  to_fun := begin
    intro x,
    by_cases (x ∈ subgroup.center G),
    {
      exact (f ⟨x, h⟩),
    },
    {
      exact x,
    },
  end,
  inv_fun := begin
    intro x,
    by_cases (x ∈ subgroup.center G),
    {
      exact (f.symm ⟨x, h⟩),
    },
    {
      exact x,
    },
  end,
  left_inv := begin 
    intro x,
    simp only,
    split_ifs,
    {
      simp only [equiv.symm_apply_apply, subtype.coe_eta, subgroup.coe_mk],
    },
    {
      exfalso,
      simp only at h,
      finish,
    },
    {
      exfalso,
      simp only at h,
      rw dif_pos at h,
      swap,
      exact h_1,
      apply h,
      have center_in_center : ∀ x : subgroup.center G, (↑x) ∈ subgroup.center G,
      {
        intro x,
        cases x with x hx,
        simp only [subtype.coe_mk],
        exact hx,
      },
      apply center_in_center,
    },
    {
      refl,
    },
  end,
  right_inv := begin 
    intro x,
    simp only,
    split_ifs,
    {
      simp only [equiv.apply_symm_apply, subtype.coe_eta, subgroup.coe_mk],
    },
    {
      exfalso,
      simp only at h,
      finish,
    },
    {
      exfalso,
      simp only at h,
      rw dif_pos at h,
      swap,
      exact h_1,
      apply h,
      have center_in_center : ∀ x : subgroup.center G, (↑x) ∈ subgroup.center G,
      {
        intro x,
        cases x with x hx,
        simp only [subtype.coe_mk],
        exact hx,
      },
      apply center_in_center,
    },
    {
      refl,
    },
  end, }

theorem fun_center_to_all_pq_morph (f : subgroup.center G ≃ subgroup.center G) (hf : is_pq_morphism f) : is_pq_morphism (fun_center_to_all f hf) :=
begin
  split,
  {
    intros a b,
    unfold fun_center_to_all,
    simp only [equiv.coe_fn_mk],
    by_cases (b ∈ subgroup.center G),
    {
      rw dif_pos,
      swap,
      {
        suffices : a ▷ b = b,
        rw this,
        exact h,
        rw rhd_def,
        rw ←center_reformulate,
        apply h,
      },
      {
        by_cases h1 : (a ∈ subgroup.center G),
        {
          rw dif_pos,
          swap, exact h1,
          rw dif_pos,
          swap, exact h,
          sorry,
        },
        {
          rw dif_neg,
          swap, exact h1,
          rw dif_pos,
          swap, exact h,
          sorry,
        },
      },
    },
    {
      by_cases h1 : (a ∈ subgroup.center G),
      {
        rw dif_neg,
        swap,
        {
          suffices : a ▷ b = b,
          rw this,
          exact h,
          rw rhd_def,
          rw ←center_reformulate,
          apply eq.symm,
          apply h1,
        },
        rw dif_pos,
        swap, exact h1,
        rw dif_neg,
        swap, exact h,
        sorry,
      },
      {
        rw dif_neg,
        swap,
        {
          intro hc,
          apply h,
          suffices : a ▷ b = b,
          rw ←this,
          exact hc,
          rw ←rack.right_inv a b,
          rw ←rack.right_inv a (a▷(a▷b)◁a),
          apply congr_arg (λ x, x ◁ a),
          rw rack.right_inv,
          rw rhd_def,
          rw ←center_reformulate,
          apply hc,
        },
        rw dif_neg,
        swap, exact h1,
        rw dif_neg,
        swap, exact h,
      },
    },
  },
  {
    sorry,
  }
end

end aut_comp_center

