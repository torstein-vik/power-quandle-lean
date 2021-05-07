
import pq_induction_principles
import minimal_sub_pq_gen_group


universe u

section pq_like_eq_equalizer

variables {G : Type u} [group G] --[inhabited Q]

lemma prod_in_free_gen_list (gen : set G) (x : list (free_gen_group_sub_pq gen)) (hx : of ((x.map of).prod) = (x.map (of ∘ of)).prod) : (x.map coe).prod ∈ (free_gen_group_sub_pq gen : set G) :=
begin
  induction x with g x hx,
  {
    simp only [list.prod_nil, list.map],
    sorry,
  },
  {
    simp only [list.prod_cons, list.map],
    simp only [function.comp_app, list.prod_cons, list.map] at hx,
    have hx1 := congr_arg (L_of_morph (gen_set_counit gen) (functoriality_group_bundled_to_pq (gen_set_counit gen))) hx,
    simp only [monoid_hom.map_mul, L_of_morph_of, gen_set_counit_of] at hx1,
    sorry,
  },
end

theorem eta_eq_L_eta (gen : set G) (x : pq_group (free_gen_group_sub_pq gen)) : (of x = L_of_morph of of_is_pq_morphism x) ↔ (∃ y, x = of y) :=
begin
  split,
  swap,
  {
    intro hx,
    cases hx with y hy,
    rw hy,
    simp only [L_of_morph_of],
  },
  {
    revert x,
    refine pq_group_list _,
    intros x hx,
    fconstructor,
    fconstructor,
    use (x.map (λ x, ↑x)).prod,
    {
      simp only,
      induction x,
      {
        simp only [list.prod_nil, list.map],
        sorry,
      },
      have hx1 := congr_arg (L_of_morph (gen_set_counit gen) (functoriality_group_bundled_to_pq (gen_set_counit gen))) hx,
      simp only [monoid_hom.map_mul, list.prod_cons, list.map, L_of_morph_of, gen_set_counit_of] at hx1,
      simp only [list.prod_cons, list.map],
    },
    {
      sorry,
    },
    /-
    refine pq_group_word_induction _ _,
    {
      intro h1,
      clear h1,
      use (arbitrary Q)^(0 : ℤ),
      simp only [of_pow_eq_pow_of, gpow_zero],
    },
    {
      intros x z hx hxz,
      sorry,
    },
    -/
  },
end

end pq_like_eq_equalizer
