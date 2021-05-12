
import pq_to_group
import counit_ker_abelian


universes u1 u2 u3

section pq_like_split

variables {Q : Type u1} [power_quandle Q]


def counit_L_of (x : pq_group Q) : counit ((L_of_morph of of_is_pq_morphism) x) = x :=
begin
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
      refl,
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

def left_split_fun : (pq_group (pq_group Q)) → (counit : pq_group (pq_group Q) →* (pq_group Q)).ker :=
begin
  intro x,
  fconstructor,
  exact x * ((L_of_morph of of_is_pq_morphism) (counit x))⁻¹,
  refine counit.mem_ker.mpr _,
  simp only [monoid_hom.map_mul, monoid_hom.map_inv],
  rw counit_L_of,
  simp only [mul_right_inv],
end

lemma left_split_fun_def (x : pq_group (pq_group Q)) : x * ((L_of_morph of of_is_pq_morphism) (counit x))⁻¹  = ↑(left_split_fun x) := rfl

lemma left_split_coe_commutes (x y : pq_group (pq_group Q)) : x * ↑(left_split_fun y) = ↑(left_split_fun y) * x :=
begin
  rw counit_ker_center,
end

def left_split_hom : (pq_group (pq_group Q)) →* (counit : pq_group (pq_group Q) →* (pq_group Q)).ker :=
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


theorem left_split_hom_is_left_split (x : (counit : pq_group (pq_group Q) →* (pq_group Q)).ker) : left_split_hom (↑x) = x :=
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


def pq_group_prod_ker_G : pq_group (pq_group Q) ≃* pq_group Q × (counit : pq_group (pq_group Q) →* pq_group Q).ker := { 
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

end pq_like_split

