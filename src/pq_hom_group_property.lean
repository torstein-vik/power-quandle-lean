

import pq_induction_principles

universes u1 u2

section pq_hom_group_property

variables {G : Type u1} [group G] {H : Type u2} [group H]


theorem pq_hom_group_property (f : G → H) (hf : is_pq_morphism f) 
: (∀ x y : G, f (x * y) = (f x) * (f y))
↔ (∀ x : pq_group G, counit (L_of_morph f hf x) = f (counit x)) :=
begin
  split,
  {
    intros hf1,
    apply pq_group_word_induction,
    {
      simp only [monoid_hom.map_one],
      specialize hf1 1 1,
      simp only [mul_one] at hf1,
      symmetry,
      apply eq_one_of_left_cancel_mul_self,
      assumption,
    },
    {
      intros x y hx,
      simp only [monoid_hom.map_mul, hf1, counit_of, L_of_morph_of, hx],
    },
  },
  {
    intros hf1 x y,
    specialize hf1 ((of x) * (of y)),
    simp only [monoid_hom.map_mul, L_of_morph_of, counit_of] at hf1,
    symmetry,
    assumption,
  },
end


end pq_hom_group_property

/-

section pq_hom_group_property_dual


variables {Q1 : Type u1} [power_quandle Q1] {Q2 : Type u2} [power_quandle Q2] [inhabited Q2]


lemma L_of_morph_of_eq_of_imp_eq_of (x : pq_group Q2) (hx : of x = L_of_morph of of_is_pq_morphism x) : ∃ y, x = of y :=
begin
  /-
  induction x,
  {
    rw quot_mk_helper at *,
    induction x,
    {
      rw incl_unit_eq_unit at *,
      use (arbitrary Q2) ^ (0 : ℤ),
      rw of_pow_eq_pow_of,
      simp only [gpow_zero],
    },
    {
      rw ←of_def at *,
      use x,
    },
    {
      rw ←mul_def at *,
    },
    {
      rw ←inv_def at *,
      sorry,
    },
  },
  {refl,},
  -/
  
  revert x,
  refine pq_group_word_induction _ _,
  {
    intro hx,
    use (arbitrary Q2) ^ (0 : ℤ),
    rw of_pow_eq_pow_of,
    simp only [gpow_zero],
  },
  {
    intros x y hx hxy,
    simp only [monoid_hom.map_mul, L_of_morph_of] at hxy,
    --have hxy1 := congr_arg counit hxy,
    --simp only [monoid_hom.map_mul, counit_of, mul_right_inj] at hxy1,
    
  },
  
end

theorem pq_hom_group_property_dual' (f : pq_group Q1 →* pq_group Q2)
: (∀ x : Q1, ∃ y : Q2, f (of x) = of y)
↔ (∀ x : pq_group Q1, (L_of_morph (of : Q2 → pq_group Q2) of_is_pq_morphism) (f x)
= (L_of_morph f (functoriality_group_bundled_to_pq f)) ((L_of_morph (of : Q1 → pq_group Q1) of_is_pq_morphism) x))
:=
begin
  split,
  {
    intro hf,
    apply pq_group_word_induction,
    {
      simp only [monoid_hom.map_one],
    },
    {
      intros x y hx,
      specialize hf y,
      cases hf with z hz,
      simp only [monoid_hom.map_mul, hx, L_of_morph_of, mul_left_inj],
      rw hz,
      refl,
    },
  },
  {
    intro hf,
    intro q,
    specialize hf (of q),
    simp only [monoid_hom.map_mul, L_of_morph_of] at hf,
    apply L_of_morph_of_eq_of_imp_eq_of,
    symmetry,
    assumption,
  },
end

theorem pq_hom_group_property_dual (f : pq_group Q1 →* pq_group Q2)
: (∃ g : Q1 → Q2, ∃ hg : is_pq_morphism g, f = L_of_morph g hg)
↔ (∀ x : pq_group Q1, (L_of_morph (of : Q2 → pq_group Q2) of_is_pq_morphism) (f x)
= (L_of_morph f (functoriality_group_bundled_to_pq f)) ((L_of_morph (of : Q1 → pq_group Q1) of_is_pq_morphism) x))
:=
begin
  split,
  {
    intro hf,
    cases hf with g hg,
    cases hg with hgpq hg,
    rw hg,
    apply pq_group_word_induction,
    {
      simp only [monoid_hom.map_one],
    },
    {
      intros x y hx,
      simp only [monoid_hom.map_mul, hx, L_of_morph_of],
    },
  },
  {
    intro hf,
    fconstructor,
    intro q,
    specialize hf (of q),
    simp only [monoid_hom.map_mul, L_of_morph_of] at hf,
  },
end

end pq_hom_group_property_dual

-/
