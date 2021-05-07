
import pq_induction_principles
import minimal_sub_pq_gen_group

universes u v

section pq_group_equalizer_eta_L_eta_sub_pq

variables {G : Type u} [group G]

def eta_equal {gen : set G} (x : pq_group (free_gen_group_sub_pq gen)) : Prop := of x = (L_of_morph of of_is_pq_morphism) x

def all_eta_equal (gen : set G) : Prop := ∀ x : pq_group (free_gen_group_sub_pq gen), eta_equal x

lemma of_inj : function.injective (of : G → pq_group G) :=
begin
  intros x y hxy,
  have hxy1 := congr_arg counit hxy,
  simp only [counit_of] at hxy1,
  assumption,
end

theorem gen_set_counit_injective (gen : set G) (hgen : all_eta_equal gen) : function.injective (gen_set_counit gen) :=
begin
  refine (gen_set_counit gen).injective_iff.mpr _,
  intros x hx,
  apply of_inj,
  rw of_1_eq_unit,
  unfold all_eta_equal at hgen,
  unfold eta_equal at hgen,
  rw hgen,
  revert x,
  refine pq_group_word_induction _ _,
  {
    intro h1,
    simp only [monoid_hom.map_one],
  },
  {
    intros x y hx hxy,
    simp only [monoid_hom.map_mul, L_of_morph_of],
    rw ←hgen,
    simp only [monoid_hom.map_mul, gen_set_counit_of] at hxy,
  },
  
  /-
  intros x y hxy,
  apply of_inj,
  unfold all_eta_equal at hgen,
  unfold eta_equal at hgen,
  rw hgen,
  rw hgen,
  -/
end


end pq_group_equalizer_eta_L_eta_sub_pq
