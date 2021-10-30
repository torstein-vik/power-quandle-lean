
import counit_ker_abelian
import pq_induction_principles
import group_theory.abelianization

universe u

section commutator_counit_kernel

variables {G : Type u} [group G]

theorem commutator_intersect_counit_kernel_trivial (x y : pq_group G) (hxy : counit (x * y * x⁻¹ * y⁻¹) = 1) : x * y * x⁻¹ * y⁻¹ = 1 :=
begin
  simp only [counit_of, monoid_hom.map_mul, monoid_hom.map_mul_inv] at hxy,
  rw ←rhd_def_group,
  rw inner_aut_eq,
  generalize ha : counit x = a,
  rw ha at hxy,
  clear ha x,
  suffices : of a ▷ y = y,
  {
    rw this,
    simp only [mul_right_inv],
  },
  have hya : a ▷ (counit y) = counit y,
  {
    rw ←rhd_def_group at hxy,
    exact mul_inv_eq_one.mp hxy,
  },
  clear hxy,
  suffices : (of a) ▷ (y * (of (counit y))⁻¹) = y * (of (counit y))⁻¹,
  {
    rw rhd_mul at this,
    suffices this2 : (of a▷(of (counit y))⁻¹) = (of (counit y))⁻¹,
    {
      rw this2 at this,
      simp only [mul_left_inj] at this,
      exact this,
    },
    clear this,
    rw of_inv,
    rw rhd_of_eq_of_rhd,
    apply congr_arg,
    rw ←power_quandle.pow_rhd,
    rw hya,
  },
  suffices : (y * (of (counit y))⁻¹) ▷ (of a) = of a,
  {
    generalize ha1 : of a = a1,
    generalize ha2 : (y * (of (counit y))⁻¹) = a2,
    rw ha1 at this,
    rw ha2 at this,
    clear ha1 ha2 hya a y,
    rw rhd_def_group at *,
    rw ←center_reformulate at *,
    symmetry,
    exact this,
  },
  rw inner_aut_eq,
  simp only [counit_of, mul_right_inv, monoid_hom.map_mul_inv],
  rw of_one,
  rw power_quandle.one_rhd,
end

end commutator_counit_kernel

