
import pq_like_equalizer_util

universe u

section pq_like_equalizer_split

-- Show that Gr Q' ~= ker phi x Gr Q

variables {Q : Type u} [power_quandle Q]

def eq_left_split_fun : (pq_group (eta_equalizer Q)) → (eta_equalizer_iso_forward : pq_group (eta_equalizer Q) →* pq_group Q).ker :=
begin
  intro x,
  fconstructor,
  exact x * ((eta_equalizer_iso_backward) (eta_equalizer_iso_forward x))⁻¹,
  refine eta_equalizer_iso_forward.mem_ker.mpr _,
  simp only [monoid_hom.map_mul, monoid_hom.map_inv],
  rw eta_equalizer_iso_forward_of_backward,
  simp only [mul_right_inv],
end

lemma eq_left_split_fun_def (x : pq_group (eta_equalizer Q)) : x * ((eta_equalizer_iso_backward) (eta_equalizer_iso_forward x))⁻¹  = ↑(eq_left_split_fun x) := rfl

lemma eq_left_split_coe_commutes (x y : pq_group (eta_equalizer Q)) : x * ↑(eq_left_split_fun y) = ↑(eq_left_split_fun y) * x :=
begin
  rw ←eq_left_split_fun_def,
  revert x y,
  refine pq_group_word_induction _ _,
  {
    intros y,
    simp only [mul_one, one_mul],
  },
  {
    intros x a hx y,
    assoc_rw hx,
    rw ←mul_assoc,
    simp only [mul_left_inj],
    clear hx x _inst,
    sorry,
  },
  /-
  rw ←eq_left_split_fun_def,
  revert y x,
  refine pq_group_word_induction _ _,
  {
    intro y,
    simp only [one_inv, mul_one, one_mul, monoid_hom.map_one],
  },
  {
    intros y a hy x,
    simp only [mul_inv_rev, monoid_hom.map_mul],
    assoc_rw hy,
    assoc_rw hy,
    assoc_rw hy,
    clear _inst,
    suffices : x * of a * (eta_equalizer_iso_backward (eta_equalizer_iso_forward (of a)))⁻¹ =  of a * (eta_equalizer_iso_backward (eta_equalizer_iso_forward (of a)))⁻¹ * x,
    assoc_rw this,
    clear hy y,
    rw eta_equalizer_iso_forward_of,
    cases a with a ha,
    simp only,
    revert a,
    refine pq_group_word_induction _ _,
    {
      intro ha,
      simp only [one_inv, mul_one, monoid_hom.map_one],
      suffices : of (⟨1, ha⟩ : eta_equalizer Q) = 1,
      rw this,
      simp only [mul_one, one_mul],
      simp_rw ←of_one,
      congr,
      rw of_one,
    },
    {
      intros z y hz haz,
      simp only [mul_inv_rev, monoid_hom.map_mul],
      rw eta_equalizer_iso_backward_of,
      sorry,
    },
  },
  -/
end

def eq_left_split_hom : (pq_group (pq_group Q)) →* (counit : pq_group (pq_group Q) →* (pq_group Q)).ker :=
begin
  fconstructor,
  exact left_split_fun,
  {
    unfold left_split_fun,
    simp only [one_inv, mul_one, monoid_hom.map_one],
    refl,
  },
  {
    intros a b,
    unfold left_split_fun,
    ext1,
    simp only [mul_inv_rev, monoid_hom.map_mul, subgroup.coe_mul, subtype.coe_mk],
    rw mul_assoc,
    rw ←mul_assoc b, 
    rw left_split_fun_def b,
    rw ←mul_assoc,
    rw left_split_coe_commutes,
    rw left_split_coe_commutes,
    rw mul_assoc,
  },
end


theorem eq_left_split_hom_is_left_split (x : (counit : pq_group (pq_group Q) →* (pq_group Q)).ker) : left_split_hom (↑x) = x :=
begin
  cases x with x hx,
  unfold left_split_hom,
  simp only [monoid_hom.coe_mk, subtype.coe_mk],
  unfold left_split_fun,
  ext1,
  simp only [subtype.coe_mk],
  suffices : counit x = 1,
  rw this,
  simp only [mul_one, monoid_hom.map_one],
  simp only [one_inv, mul_one],
  exact hx,
end


def eq_pq_group_prod_ker_G : pq_group (pq_group Q) ≃* pq_group Q × (counit : pq_group (pq_group Q) →* pq_group Q).ker := { 
  to_fun := λ x, ⟨counit x, left_split_hom x⟩,
  inv_fun := λ a, a.2 * (L_of_morph of of_is_pq_morphism a.1),
  left_inv := begin 
    intro x,
    simp only,
    unfold left_split_hom,
    simp only [monoid_hom.coe_mk],
    unfold left_split_fun,
    simp only [subgroup.coe_mk, inv_mul_cancel_right],
  end,
  right_inv := begin 
    intro x,
    cases x with x1 x2,
    simp only [monoid_hom.map_mul],
    ext1,
    {
      simp only,
      rw counit_L_of,
      simp only [mul_left_eq_self],
      cases x2 with x2 hx2,
      simp only [subtype.coe_mk],
      exact hx2,
    },
    {
      simp only,
      rw left_split_hom_is_left_split,
      simp only [mul_right_eq_self],
      unfold left_split_hom,
      simp only [monoid_hom.coe_mk],
      unfold left_split_fun,
      simp_rw counit_L_of,
      group,
      refl,
    },
  end,
  map_mul' := begin 
    intros x y,
    ext1,
    simp only [monoid_hom.map_mul, prod.mk_mul_mk],
    simp only [monoid_hom.map_mul, prod.mk_mul_mk],
  end }

end pq_like_equalizer_split
