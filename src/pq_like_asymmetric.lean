
import pq_like
import pq_induction_principles


universes u1 u2

section pq_like_asymmetric

variables {Q1 : Type u1} [power_quandle Q1] {Q2 : Type u2} [power_quandle Q2]


def pq_like_homo (f : pq_group Q1 → pq_group Q2) (hf : is_pq_morphism f) : pq_group Q1 →* pq_group Q2 :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    exact f ∘ of,
  },
  {
    exact pq_morphism_comp of f of_is_pq_morphism hf,
  },
end

theorem pq_like_homo_surjective (f : pq_group Q1 ≃ pq_group Q2) (hf : is_pq_morphism f) (hf1 : ∀ x : Q2, ∃ z : Q1, f.symm (of x) = of z) : function.surjective (pq_like_homo f hf) :=
begin
  refine pq_group_word_induction _ _,
  {
    use 1,
    simp only [monoid_hom.map_one],
  },
  {
    intros x y hx,
    cases hx with z hz,
    use (f.symm (of y)) * z,
    simp only [monoid_hom.map_mul, hz],
    specialize hf1 y,
    cases hf1 with a ha,
    rw ha,
    unfold pq_like_homo,
    rw pq_morph_to_L_morph_adj_comm_of,
    simp only [function.comp_app, mul_left_inj],
    rw ←ha,
    simp only [equiv.apply_symm_apply],
  },
end


end pq_like_asymmetric
