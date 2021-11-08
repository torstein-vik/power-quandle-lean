
-- TODO: Define functor, ie. group morphism to pq morphism and comp

import power_quandle

import algebra.group
import group_theory.quotient_group
import group_theory.order_of_element

universes u v

section group_to_pq

variables {Q : Type u} [group Q]

def rhd_group (x : Q) (y : Q) : Q := x * y * x⁻¹ 

instance group_has_rhd : has_rhd Q := ⟨rhd_group⟩

lemma rhd_def_group : ∀ a b : Q, a ▷ b = a * b * a⁻¹  := begin
  intros a b,
  refl,
end

lemma rhd_mul (x y z : Q) : x ▷ (y * z) = (x ▷ y) * (x ▷ z) :=
begin
  simp only [rhd_def_group, conj_mul],
end

lemma rhd_inv (x y : Q) : x ▷ (y⁻¹) = (x ▷ y)⁻¹ :=
begin
  simp only [rhd_def_group, conj_inv],
end

lemma mul_rhd (a b c : Q) : a * b ▷ c = a ▷ b ▷ c :=
begin
  simp only [rhd_def_group],
  group,
end


lemma center_reformulate (a b : Q) : (a * b = b * a) ↔ (a * b * a⁻¹ = b) :=
begin
    split,
    intro hab, rw hab, group,
    intro hab, rw ←hab, simp, rw hab,
end

lemma center_reformulate_inv (a b : Q) : (a * b⁻¹ = b⁻¹ * a) ↔ (a * b * a⁻¹ = b) :=
begin
    split,
    {
        intro hab,
        refine inv_inj.mp _,
        simp,
        rw hab,
        simp,
    },
    {
        intro hab,
        rw ←hab,
        simp, 
        refine inv_inj.mp _,
        simp,
        exact hab,
    },
end

instance group_is_power_quandle : power_quandle Q := {
  rhd_dist := begin 
    intros a b c,
    simp only [rhd_def_group, conj_mul, conj_inv],
  end,
  rhd_idem := begin 
    intros a,
    simp only [rhd_def_group, mul_inv_cancel_right],
  end,
  pow_one := begin 
    intros a,
    simp only [gpow_one],
  end,
  pow_zero := begin 
    intros a,
    simp only [gpow_zero],
  end,
  pow_comp := begin 
    intros a n m,
    group,
  end,
  rhd_one := begin 
    intros a,
    simp only [rhd_def_group, mul_one, mul_right_inv],
  end,
  one_rhd := begin 
    intros a,
    simp only [rhd_def_group, one_inv, mul_one, one_mul],
  end,
  pow_rhd := begin 
    intros a b,
    have for_nat : ∀ n : ℕ, (a ▷ b) ^ n = a ▷ (b ^ n),
    {
      intro n,
      induction n,
      {
        simp only [rhd_def_group, mul_one, mul_right_inv, pow_zero],
      },
      {
        simp only [pow_succ, n_ih, rhd_mul],
      },
    },
    intro n,
    induction n,
    {
      simp only [for_nat, int.of_nat_eq_coe, gpow_coe_nat],
    },
    {
      simp only [gpow_neg_succ_of_nat, pow_succ, for_nat, rhd_inv],
    },
  end,
  rhd_pow_add := begin 
      intros a b n m,
      simp only [rhd_def_group],
      group,
  end,
  ..group_has_rhd,
  ..group.has_pow }

end group_to_pq

section group_morph_to_pq_morph

variables {G : Type u} [group G] {H : Type v} [group H]


theorem functoriality_group_to_pq (f : G →* H) : is_pq_morphism f :=
begin
  split,
  {
    intros a b,
    simp only [rhd_def_group, monoid_hom.map_mul, eq_self_iff_true, monoid_hom.map_mul_inv, mul_left_inj],
  },
  {
    intros a n,
    simp only [monoid_hom.map_gpow],
  },
end

theorem functoriality_group_iso_to_pq (f : G ≃* H) : is_pq_morphism f :=
begin
  convert functoriality_group_to_pq f.to_monoid_hom,
end

-- composition and identity preservence is trivial

/-
theorem group_to_pq_fullness_almost (f : G → H) (hf : is_pq_morphism f) (hfs : function.surjective f) (hG : ∀ a b : H, (∀ c : H, a ▷ c = b ▷ c) → a = b) : is_group_morphism f :=
begin
    cases hf with hf1pre hf2,
    have hf1 : ∀ a b : G, f(a * b * a⁻¹) = f(a) * f(b) * (f(a))⁻¹,
    {
        intros a b,
        specialize hf1pre a b,
        repeat {rw rhd_group_def at hf1pre},
        exact hf1pre,
    },
    --split,
    {
        intros a b,
        apply hG,
        intro c,
        repeat {rw rhd_group_def},
        have de := hfs c,
        cases de with d hd,
        repeat {rw ←hd},
        simp,
        repeat {rw ←mul_assoc},
        rw ←hf1,
        simp,
        repeat {rw ←mul_assoc},
        have rw_mul_assoc : f (a * b * d * b⁻¹ * a⁻¹) = f a * (f b * f d * (f b)⁻¹) * (f a)⁻¹,
        {
            rw ←hf1,
            rw ←hf1,
            repeat {rw ←mul_assoc},
        },
        rw rw_mul_assoc,
        repeat {rw ←mul_assoc},
    },
    /-split,
    {
        specialize hf2 1 0,
        --rw pow_0_int at hf2,
        --rw pow_0_int at hf2,
        simp at hf2,
        exact hf2,
    },
    {
        intro a,
        specialize hf2 a (-1 : int),
        --rw pow_is_inv,
        --rw pow_is_inv,
        rw ←gpow_neg_one,
        rw ←gpow_neg_one,
        exact hf2,
    },-/
end
-/

end group_morph_to_pq_morph
