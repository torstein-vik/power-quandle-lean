
import eta_injective_pq

import pq_induction_principles

universes u1 u2

section pq_injective

variables {Q1 : Type u1} [power_quandle Q1] {Q2 : Type u2} [power_quandle Q2]

lemma L_fun_of (f : Q1 → Q2) (hf : is_pq_morphism f) (a : Q1) : (L_of_morph f hf) (of a) = of (f a) :=
begin
  refl,
end

lemma of_inv : ∀ x : Q1, of (x ^ (-1 : ℤ)) = (of x)⁻¹ :=
begin
  intro x,
  repeat {rw ←gpow_neg_one},
  rw of_pow_eq_pow_of,
end

theorem pq_injective_if_L_injective (f : Q1 → Q2) (hf : is_pq_morphism f) (hLf : function.injective (L_of_morph f hf)) (hQ1 : eta_injective Q1) : function.injective f :=
begin
  intros x y hxy,
  apply hQ1,
  apply hLf,
  rw L_fun_of,
  rw L_fun_of,
  apply congr_arg,
  exact hxy,
end

theorem L_injective_if_pq_injective (f : Q1 → Q2) (hf : is_pq_morphism f) 
(hfi : function.injective f) (hQ1 : eta_injective Q1) : function.injective (L_of_morph f hf) :=
begin
  refine (L_of_morph f hf).injective_iff.mpr _,
  refine pq_group_word_induction _ _,
  {
    intro h1,
    refl,
  },
  {
    intros x y hx hxy,
    simp only [monoid_hom.map_mul] at hxy,
    rw L_fun_of at hxy,
    have hxy1 := eq_inv_of_mul_eq_one hxy,
    rw ←inv_inj at hxy1,
    simp only [inv_inv] at hxy1,
    rw ←of_inv at hxy1,
    rw ←hf.2 at hxy1,
    sorry,
  },
end


end pq_injective
