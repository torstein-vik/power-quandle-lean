
import pq_induction_principles

universe u


section pq_group_equalizer_eta_L_eta

variables {G : Type u} [group G]

lemma of_inj : function.injective (of : G → pq_group G) :=
begin
  intros x y hxy,
  have hxy1 := congr_arg counit hxy,
  simp only [counit_of] at hxy1,
  assumption,
end

lemma of_mul_eq (x y : G) : of (of x * of y) = of (of x) * of (of y) ↔ of x * of y = of (x * y) :=
begin
  split,
  {
    intro hxy,
    have hxy1 := congr_arg (L_of_morph counit (functoriality_group_to_pq counit)) hxy,
    simp only [monoid_hom.map_mul, L_of_morph_of, counit_of] at hxy1,
    symmetry,
    exact hxy1,
  },
  {
    intro hxy,
    have hxy1 := congr_arg (L_of_morph of of_is_pq_morphism) hxy,
    simp only [monoid_hom.map_mul, L_of_morph_of] at hxy1,
    rw hxy,
    rw hxy1,
  },
end

lemma of_mul_eq_three (x y z : G) : of (of x * of y * of z) = of (of x) * of (of y) * of (of z) ↔ of x * of y * of z = of (x * y * z) :=
begin
  split,
  {
    intro hxy,
    have hxy1 := congr_arg (L_of_morph counit (functoriality_group_to_pq counit)) hxy,
    simp only [monoid_hom.map_mul, L_of_morph_of, counit_of] at hxy1,
    symmetry,
    exact hxy1,
  },
  {
    intro hxy,
    have hxy1 := congr_arg (L_of_morph of of_is_pq_morphism) hxy,
    simp only [monoid_hom.map_mul, L_of_morph_of] at hxy1,
    rw hxy,
    rw hxy1,
  },
end

lemma counit_prod_map_of (x : list G) : counit (list.map of x).prod = x.prod :=
begin
  induction x,
  {
    simp only [list.prod_nil, list.map, monoid_hom.map_one],
  },
  {
    simp only [monoid_hom.map_mul, list.prod_cons, list.map, counit_of, x_ih],
  },
end

lemma L_of_prod_map_of (x : list G) : (L_of_morph of of_is_pq_morphism) ((list.map of x).prod) = (list.map (of ∘ of) x).prod :=
begin
  induction x,
  {
    simp only [list.prod_nil, list.map, monoid_hom.map_one],
  },
  {
    simp only [monoid_hom.map_mul, function.comp_app, list.prod_cons, list.map],
    simp only [x_ih, L_of_morph_of],
  },
end

lemma of_mul_eq_list (x : list G) : of ((x.map of).prod) = (x.map (of ∘ of)).prod ↔ of (x.prod) = (x.map of).prod :=
begin
  induction x with g x hx,
  {
    simp only [list.prod_nil, list.map, of_1_eq_unit, eq_self_iff_true],
  },
  {
    simp only [function.comp_app, list.prod_cons, list.map],
    split,
    {
      intro hxg,
      have hxg1 := congr_arg (L_of_morph counit (functoriality_group_to_pq counit)) hxg,
      simp only [monoid_hom.map_mul, L_of_morph_of, counit_of, counit_prod_map_of] at hxg1,
      rw hxg1,
      apply congr_arg,
      clear hxg1,
      clear hxg,
      clear hx,
      induction x,
      {
        simp only [list.prod_nil, list.map, monoid_hom.map_one],
      },
      {
        simp only [monoid_hom.map_mul, function.comp_app, list.prod_cons, list.map],
        simp only [L_of_morph_of, counit_of, x_ih],
      },
    },
    {
      intro hxg,
      have hxg1 := congr_arg (L_of_morph of of_is_pq_morphism) hxg,
      simp only [monoid_hom.map_mul, L_of_morph_of, L_of_prod_map_of] at hxg1,
      rw ←hxg1,
      rw hxg,
    },
  },
end 

theorem eta_eq_L_eta (x : pq_group G) : (of x = L_of_morph of of_is_pq_morphism x) ↔ (∃ y, x = of y) :=
begin
  split,
  {
    revert x,
    refine pq_group_list _,
    intros x hx,
    rw L_of_prod_map_of at hx,
    rw of_mul_eq_list at hx,
    use x.prod,
    symmetry,
    assumption,
    /-
    revert x,
    refine pq_group_word_induction _ _,
    {
      intro h1,
      use 1,
      rw of_1_eq_unit,
      /-
      conv {
        to_rhs,
        congr,
        rw ←gpow_zero (1 : G),
      },
      rw of_pow_eq_pow_of,
      simp only [gpow_zero],
      -/
    },
    {
      intros x y hx hxy,
      simp only [monoid_hom.map_mul, L_of_morph_of] at hxy,
      --have hxy1 := congr_arg (L_of_morph counit (functoriality_group_bundled_to_pq counit)) hxy,
      --simp only [monoid_hom.map_mul, L_of_morph_of, counit_of] at hxy1,
      suffices : of x = (L_of_morph of of_is_pq_morphism) x,
      {
        specialize hx this,
        cases hx with z hz,
        use (y * z),
        rw hz,
        rw ←of_mul_eq,
        simp only [hz, L_of_morph_of] at hxy,
        assumption,
      },
      clear hx,
      revert x,
      refine pq_group_word_induction _ _,
      {
        simp only [forall_prop_of_true, mul_one, monoid_hom.map_one],
        exact of_1_eq_unit,
      },
      {
        intros x g hx hxy,
        simp only [monoid_hom.map_mul, L_of_morph_of] at *,
        sorry,
      },
      /-
      suffices : ∃ z : G, of (of y) * (L_of_morph of of_is_pq_morphism) x = of (of z),
      {
        cases this with z hz,
        use z,
        rw ←hxy at hz,
        apply of_inj,
        assumption,
      },
      sorry,
      -/
    },
    -/
  },
  {
    intro hx,
    cases hx with y hy,
    rw hy,
    rw L_of_morph_of,
  },
end


end pq_group_equalizer_eta_L_eta

