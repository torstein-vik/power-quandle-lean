
-- Idea: pq-like is always with a normal sub-power quandle

import sub_pq
import pq_to_group
import pq_induction_principles

universe u

section sub_pq_normal

variables {Q : Type u} [power_quandle Q]

def sub_pq_normal (Q1 : sub_power_quandle Q) : Prop := ∀ x : Q, ∀ y : Q1, x ▷ y ∈ Q1.carrier

variables {Q1 : sub_power_quandle Q}

def normal_rhd (hQ1 : sub_pq_normal Q1) (x : Q) (y : Q1) : Q1 := ⟨x ▷ y, hQ1 x y⟩

lemma normal_rhd_def (hQ1 : sub_pq_normal Q1) (x : Q) (y : Q1) : normal_rhd hQ1 x y = ⟨x ▷ y, hQ1 x y⟩ := rfl

end sub_pq_normal


section sub_pq_normal_pq_injective

variables {Q : Type u} [power_quandle Q]

variables {Q1 : sub_power_quandle Q}

def sub_pq_group_inclusion : pq_group Q1 →* pq_group Q := 
begin
  fapply L_of_morph,
  {
    intro q,
    cases q with q hq,
    exact q,
  },
  {
    split,
    {
      intros a b,
      cases a with a ha,
      cases b with b hb,
      refl,
    },
    {
      intros a n,
      cases a with a ha,
      refl,
    },
  }
end

theorem pq_group_normal (hQ1 : sub_pq_normal Q1) (x : pq_group Q) (y : pq_group Q1) : ∃ z : pq_group Q1, (x ▷ (sub_pq_group_inclusion y)) = sub_pq_group_inclusion z :=
begin
  revert x,
  refine pq_group_word_induction _ _,
  {
    use y,
    rw power_quandle.one_rhd,
  },
  {
    intros x a hxy,
    cases hxy with z1 hz1,
    rw mul_rhd,
    rw hz1,
    clear hz1 x y,
    revert z1,
    refine pq_group_word_induction _ _,
    {
      use 1,
      simp only [monoid_hom.map_one],
      rw power_quandle.rhd_one,
    },
    {
      intros x b hxz1,
      cases hxz1 with y hy,
      simp only [monoid_hom.map_mul],
      rw rhd_mul,
      rw hy,
      have hinclb : sub_pq_group_inclusion (of b) = of (↑b),
      {
        unfold sub_pq_group_inclusion,
        rw L_of_morph_of,
        apply congr_arg,
        cases b with b hb,
        simp only [subtype.coe_mk],
      },
      rw hinclb,
      rw rhd_of_eq_of_rhd,
      use (of (normal_rhd hQ1 a b) * y),
      simp only [monoid_hom.map_mul, mul_left_inj],
      refl,
    },
  },
end

theorem sub_pq_group_inclusion_injective (hQ1 : sub_pq_normal Q1) : function.injective (sub_pq_group_inclusion : pq_group Q1 → pq_group Q) :=
begin
  refine sub_pq_group_inclusion.injective_iff.mpr _,
  intros a ha,
  have h_pq_group_normal_Q1 := pq_group_normal hQ1,
  sorry,
  -- It is injective if Q1 is centerless
end

end sub_pq_normal_pq_injective

