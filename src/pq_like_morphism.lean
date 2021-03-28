
import pq_to_group

universes u1 u2

section pq_like_morphism

variables {Q1 : Type u1} {Q2 : Type u2} [power_quandle Q1] [power_quandle Q2]

variables {φ : pq_group Q1 →* pq_group Q2}


theorem comes_from_is_pq_morph (f : Q1 → Q2) 
(hf : ∀ x, φ (of x) = of (f x)) 
(hof : function.injective (of : Q2 → pq_group Q2)) : is_pq_morphism f :=
begin
  split,
  {
    intros a b,
    apply hof,
    rw ←rhd_of_eq_of_rhd,
    repeat {rw ←hf},
    rw ←rhd_of_eq_of_rhd,
    rw rhd_def,
    simp only [monoid_hom.map_mul, monoid_hom.map_mul_inv],
    rw rhd_def,
  },
  {
    intros a n,
    apply hof,
    rw of_pow_eq_pow_of,
    repeat {rw ←hf},
    rw of_pow_eq_pow_of,
    rw monoid_hom.map_gpow,
  },
end

theorem comes_from_pq_morph (f : Q1 → Q2) 
(hf : ∀ x, φ (of x) = of (f x)) 
(hof : function.injective (of : Q2 → pq_group Q2)) : φ = L_of_morph f (comes_from_is_pq_morph f hf hof) :=
begin
  ext1,
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
      rw hf,
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


end pq_like_morphism
