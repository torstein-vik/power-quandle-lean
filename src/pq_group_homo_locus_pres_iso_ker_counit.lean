
import pq_group_homo_locus_pres_prod

universe u

section pq_group_homo_locus_pres_iso_ker_counit

variables {G : Type u} [group G]

lemma counit_pq_group_homo_locus_pres_prod_iso_backward (x : homo_locus_pres G) (a : G) : counit (pq_group_homo_locus_pres_prod_iso_backward ⟨x, a⟩) = a :=
begin
  unfold pq_group_homo_locus_pres_prod_iso_backward,
  simp only [monoid_hom.coe_mk],
  simp only [counit_of, counit_ker_counit, one_mul, monoid_hom.map_mul],
end

lemma counit_pq_group_homo_locus_pres_prod_iso_backward_unsplit (x : homo_locus_pres_prod G) : counit (pq_group_homo_locus_pres_prod_iso_backward x) = x.a :=
begin
  unfold pq_group_homo_locus_pres_prod_iso_backward,
  simp only [monoid_hom.coe_mk],
  simp only [counit_of, counit_ker_counit, one_mul, monoid_hom.map_mul],
end

lemma a_pq_group_homo_locus_pres_prod_iso_forward (x : pq_group G) : (pq_group_homo_locus_pres_prod_iso_forward x).a = counit x :=
begin
  rw ←pq_group_homo_locus_pres_prod_iso_left_inv x,
  rw counit_pq_group_homo_locus_pres_prod_iso_backward_unsplit,
  rw pq_group_homo_locus_pres_prod_iso_left_inv x,
end

def homo_locus_pres_iso : (counit : pq_group G →* G).ker ≃* homo_locus_pres G := { 
  to_fun := λ x, (pq_group_homo_locus_pres_prod_iso_forward (x.val)).x,
  inv_fun := λ x, ⟨(pq_group_homo_locus_pres_prod_iso_backward ⟨x, 1⟩), begin 
    refine counit.mem_ker.mpr _,
    rw counit_pq_group_homo_locus_pres_prod_iso_backward,
  end⟩,
  left_inv := begin 
    rintros ⟨x, hx⟩,
    simp only,
    ext1,
    simp only [subtype.coe_mk],
    suffices : ({x := (pq_group_homo_locus_pres_prod_iso_forward x).x, a := 1} : homo_locus_pres_prod G) = pq_group_homo_locus_pres_prod_iso_forward x,
    {
      rw this,
      rw pq_group_homo_locus_pres_prod_iso_left_inv,
    },
    ext1,
    {
      refl,
    },
    {
      simp only,
      rw a_pq_group_homo_locus_pres_prod_iso_forward,
      symmetry,
      exact hx,
    },
  end,
  right_inv := begin 
    intros x,
    simp only,
    rw pq_group_homo_locus_pres_prod_iso_right_inv,
  end,
  map_mul' := begin 
    rintros ⟨x, hx⟩ ⟨y, hy⟩,
    show (pq_group_homo_locus_pres_prod_iso_forward (x * y)).x = (pq_group_homo_locus_pres_prod_iso_forward (x)).x * (pq_group_homo_locus_pres_prod_iso_forward (y)).x,
    simp only [monoid_hom.map_mul],
    rw homo_locus_pres_prod_mul_def_unsplit,
    simp only,
    rw a_pq_group_homo_locus_pres_prod_iso_forward,
    rw a_pq_group_homo_locus_pres_prod_iso_forward,
    suffices : homo_locus_of (counit x, counit y) = 1,
    {
      rw this,
      rw mul_one,
    },
    suffices : counit x = 1,
    {
      rw this,
      rw homo_locus_of_one,
      exact homo_locus_closed_left_one (counit y),
    },
    exact hx,
  end }

end pq_group_homo_locus_pres_iso_ker_counit
