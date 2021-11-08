
import pq_like_equalizer_util

universe u

section pq_like_equalizer

-- Idea: Eq(eta, L(eta)) is normal. Useful for proving injectivity?

variables {Q : Type u} [power_quandle Q]

lemma eta_equalizer_iso_forward_of_L_of (x : pq_group (eta_equalizer Q)) : of (eta_equalizer_iso_forward x) = (L_of_morph of of_is_pq_morphism) (eta_equalizer_iso_forward x) :=
begin 
  revert x,
  refine pq_group_word_induction _ _,
  {
    simp only [monoid_hom.map_one],
    rw of_one,
  },
  {
    intros x y hx,
    simp only [monoid_hom.map_mul],
    rw ←hx,
    rw eta_equalizer_iso_forward_of,
    cases y with y hy,
    simp only,
    unfold eta_equalizer at hy,
    rw set.mem_def at hy,
    sorry,
  },
end

lemma inclusion_counit_of (x : pq_group (eta_equalizer Q)) : pq_group_eta_equalizer_inclusion x = of (counit (pq_group_eta_equalizer_inclusion x)) :=
begin
  rw inclusion_eq_L_of_of_forward,
  rw counit_L_of,
  rw eta_equalizer_iso_forward_of_L_of,
end

lemma pq_group_eta_equalizer_inclusion_injective : function.injective (pq_group_eta_equalizer_inclusion : pq_group (eta_equalizer Q) → pq_group (pq_group Q)) :=
begin
  --intros x y hxy,
  refine pq_group_eta_equalizer_inclusion.injective_iff.mpr _,
  intros x hx,
  --rw inclusion_eq_L_of_of_forward at hx,
  
  revert x,
  refine pq_group_list _,
  {
    intros x hxy,
    have hxy_rw : (L_of_morph of of_is_pq_morphism) (list.prod (list.map (λ z : (eta_equalizer Q), ↑z) x)) = pq_group_eta_equalizer_inclusion (list.map of x).prod,
    {
      clear hxy,
      induction x,
      {
        simp only [list.prod_nil, list.map, monoid_hom.map_one],
      },
      {
        simp only [monoid_hom.map_mul, list.prod_cons, list.map],
        simp only at x_ih,
        rw x_ih,
        congr,
        clear x_ih x_tl,
        cases x_hd with x hx,
        simp only [subtype.coe_mk],
        have hx1 := eta_equalizer_mem_def _ hx,
        rw ←hx1,
        refl,
      },
    },
    rw ←hxy_rw at hxy,
    clear hxy_rw,
    sorry,
    /-
    have hxy1 : (list.map (λ z : (eta_equalizer Q), (of (↑z) : pq_group (pq_group Q))) x).prod = pq_group_eta_equalizer_inclusion (list.map of x).prod,
    {
      clear hxy,
      induction x with a b hb,
      {
        simp only [list.prod_nil, list.map, monoid_hom.map_one],
      },
      {
        simp only [monoid_hom.map_mul, list.prod_cons, list.map],
        rw hb,
        cases a with a ha,
        refl,
      },
    },
    rw ←hxy1 at hxy,
    clear hxy1,
    induction x with y x hx,
    {
      simp only [list.prod_nil, list.map],
    },
    {
      cases y with y hy,
      simp only [list.prod_cons, list.map],
      simp only [list.prod_cons, subtype.coe_mk, list.map] at hxy,
      
      sorry,
    },
    -/
  },
  
end

/-
lemma eta_equalizer_iso_helper (x : pq_group Q) (hx : x ∈ ↑(eta_equalizer Q)) : of (⟨x, hx⟩ : eta_equalizer Q) = (L_of_morph of of_is_pq_morphism) (⟨x, hx⟩ : eta_equalizer Q) :=
begin

end
-/

theorem eta_equalizer_iso_helper_2 (x : pq_group (eta_equalizer Q)) : eta_equalizer_iso_backward (counit (pq_group_eta_equalizer_inclusion x)) = x :=
begin
  revert x,
  refine pq_group_word_induction _ _,
  {
    simp only [monoid_hom.map_one],
  },
  {
    intros x y hx,
    simp only [monoid_hom.map_mul, hx, mul_left_inj],
    clear hx,
    clear x,
    unfold pq_group_eta_equalizer_inclusion,
    rw L_of_morph_of,
    cases y with y hy,
    simp only,
    rw eta_equalizer_mem_def,
    swap, exact hy,
    revert y,
    refine pq_group_word_induction _ _,
    {
      intros h1,
      simp only [monoid_hom.map_one],
      rw ←of_one,
      refl,
    },
    {
      intros x y hx hxy,
      sorry,
    },
  },
end

theorem eta_equalizer_iso_helper (x : eta_equalizer Q) : eta_equalizer_iso_backward (eta_equalizer_iso_forward (of x)) = of x :=
begin
  rw eta_equalizer_iso_forward_of,
  cases x with x hx,
  simp only,
  sorry,
  /-
  revert x,
  refine pq_group_list _,
  intros x hx,
  sorry,
  -/
  /-
  refine pq_group_word_induction _ _,
  {
    intro hx,
    simp only [monoid_hom.map_one],
    rw ←of_one,
    refl,
  },
  {
    intros x y hx hxy,
    simp only [monoid_hom.map_mul],
    rw eta_equalizer_iso_backward_of,
    have hxy1 := eta_equalizer_mem_def _ hxy,
    simp only [monoid_hom.map_mul, L_of_morph_of] at hxy1,

  },
  -/
end

def eta_equalizer_iso : pq_group (eta_equalizer Q) ≃* pq_group Q := { 
  to_fun := eta_equalizer_iso_forward,
  inv_fun := eta_equalizer_iso_backward,
  left_inv := begin 
    refine pq_group_word_induction _ _,
    {
      simp only [monoid_hom.map_one],
    },
    {
      intros x y hx,
      simp only [monoid_hom.map_mul],
      rw hx,
      congr,
      unfold eta_equalizer_iso_forward,
      rw pq_morph_to_L_morph_adj_comm_of,
      cases y with y hy,
      simp only,
      clear hx,
      clear x,
      apply pq_group_eta_equalizer_inclusion_injective,
      rw eta_equalizer_in_sub_pq,
      clear hy,
      revert y,
      refine pq_group_word_induction _ _,
      {
        simp only [monoid_hom.map_one],
      },
      {
        intros x y hx,
        simp only [monoid_hom.map_mul],
        rw hx,
        congr,
      },
    },
  end,
  right_inv := begin 
    exact eta_equalizer_iso_forward_of_backward,
  end,
  map_mul' := begin 
    intros x y,
    simp only [monoid_hom.map_mul],
  end }



end pq_like_equalizer
