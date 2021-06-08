
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

section group_to_pq_properties

variables {G : Type u} [group G]

theorem same_conjugation_yields_diff_by_center' (a b : G) (hab : ∀ x : G, a ▷ x = b ▷ x) : ∃ c, a = b * c ∧ (∀ x : G, c ▷ x = x) :=
begin
    let c := b⁻¹ * a,
    have c_def : c = b⁻¹ * a := rfl,
    use c,
    split,
    {
        rw c_def,
        group,
    },
    {
        intro x,
        rw c_def,
        rw mul_rhd_eq_rhd,
        specialize hab x,
        rw hab,
        rw ←mul_rhd_eq_rhd,
        group,
        rw one_rhd,
        group,
    },
end

lemma same_conjugation_yields_diff_by_center (a b : G) (hab : ∀ x : G, a ▷ x = b ▷ x) : ∃ c, a = b * c ∧ (c ∈ subgroup.center G) :=
begin
    have h := same_conjugation_yields_diff_by_center' a b hab,
    cases h with c hc,
    cases hc with hc1 hc2,
    use c,
    split,
    exact hc1,
    intro x,
    specialize hc2 x,
    rw rhd_group_def at hc2,
    rw ←hc2,
    simp,
    rw hc2,
end


variables {H : Type v} [group H]


lemma pq_morphism_pow_nat (f : G → H) (hf : is_pq_morphism f) (a : G) (n : nat) : f (a ^ n) = (f a) ^ n :=
begin
    cases hf with hf1 hf2,
    rw ←gpow_of_nat,
    rw ←gpow_of_nat,
    rw hf2,
end

lemma pq_morphism_one (f : G → H) (hf : is_pq_morphism f) : f 1 = 1 :=
begin
    cases hf with hf1 hf2,
    rw ←gpow_zero (1 : G),
    rw hf2,
    rw gpow_zero,
end


lemma pq_morph_pres_inv (f : G → H) (hf : is_pq_morphism f) : ∀ g : G, f(g⁻¹) = (f g)⁻¹ :=
begin
    intro g,
    group,
    cases hf with hf1 hf2,
    rw hf2,
    group,
end

--def HmodZH := quotient_group.quotient (subgroup.center H)

def map_to_center_quotient (f : G → H) : G → (quotient_group.quotient (subgroup.center H)) := quotient_group.mk ∘ f


theorem pq_morphism_to_center_quotient_homomorphism (f : G → H) (hf : is_pq_morphism f) (hfs : function.surjective f) : is_group_morphism (map_to_center_quotient f) :=
begin
    intros a b,
    --unfold map_to_center_quotient,
    --simp,
    apply quotient.sound,
    
    have h := same_conjugation_yields_diff_by_center (f(a) * f(b)) (f(a * b)) _,
    {
        cases h with c hc,
        cases hc with hc1 hc2,
        rw hc1,
        intro g,
        group,
        specialize hc2 g,
        rw hc2,
        group,
    },
    {
        cases hf with hf1pre hf2,
        have hf1 : ∀ a b : G, f(a * b * a⁻¹) = f(a) * f(b) * (f(a))⁻¹,
        {
            intros a b,
            specialize hf1pre a b,
            repeat {rw rhd_group_def at hf1pre},
            exact hf1pre,
        },
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
end


def group_morphism_mod_center (f : G → H) (hf : is_pq_morphism f) (hfs : function.surjective f) : G →* (quotient_group.quotient (subgroup.center H)) 
    := ⟨map_to_center_quotient f, begin
        apply group_morphism_one,
        apply pq_morphism_to_center_quotient_homomorphism f hf hfs,
    end, begin
         have hfg := pq_morphism_to_center_quotient_homomorphism f hf hfs,
         apply hfg,
    end⟩



lemma center_reformulate (a b : G) : (a * b = b * a) ↔ (a * b * a⁻¹ = b) :=
begin
    split,
    intro hab, rw hab, group,
    intro hab, rw ←hab, simp, rw hab,
end

lemma center_reformulate_inv (a b : G) : (a * b⁻¹ = b⁻¹ * a) ↔ (a * b * a⁻¹ = b) :=
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


theorem group_morph_ker_eq_center (f : G → H) (hf : is_pq_morphism f) (hfs : function.surjective f) (hfi : function.injective f) : (monoid_hom.ker (group_morphism_mod_center f hf hfs)) = subgroup.center G :=
begin
    ext,
    split,
    {
        intro hx,
        intro g,
        /-unfold monoid_hom.ker at hx,
        simp at hx,
        unfold group_morphism_mod_center at hx,
        simp at hx,
        unfold map_to_center_quotient at hx,
        simp at hx,-/
        rw center_reformulate,
        apply hfi,
        rw ←rhd_group_def,
        rw rhd_preserved_by_morphism f hf,
        rw rhd_group_def,
        have hx2 := @quotient.exact H (quotient_group.left_rel (subgroup.center H)) (f x) (1) hx,
        specialize hx2 (f g),
        simp at hx2,
        rw ←center_reformulate_inv,
        exact hx2,
    },
    {
        intro hx,
        apply quotient.sound,
        intro g,
        simp,
        cases (hfs g) with y hy,
        rw ←hy,
        specialize hx y,
        rw center_reformulate,
        rw ←rhd_group_def,
        rw ←pq_morph_pres_inv f hf,
        rw ←rhd_preserved_by_morphism f hf,
        apply congr_arg,
        rw rhd_group_def,
        refine inv_inj.mp _,
        simp,
        rw hx,
        simp,
    },
end

-- Potensially could be made computable, but probably at little benefit.

noncomputable theorem group_mod_ker_eq_mod_center (f : G → H) (hf : is_pq_morphism f) (hfs : function.surjective f) (hfi : function.injective f) : quotient_group.quotient (monoid_hom.ker (group_morphism_mod_center f hf hfs)) ≃* (quotient_group.quotient (subgroup.center G)) :=
begin
    have subgroup_eq := group_morph_ker_eq_center f hf hfs hfi,
    fapply mul_equiv.of_bijective,
    {
        fapply quotient_group.map, 
        exact monoid_hom.id G,
        rw subgroup_eq,
        tauto,
    },
    split,
    {
        intros a b,
        intro hab,
        --unfold quotient_group.map at *,
        --simp at *,
        --unfold quotient_group.lift at *,
        --simp at *,
        induction a,
        induction b,
        {
            apply quotient.sound,
            rw subgroup_eq,
            have habe := @quotient.exact G (quotient_group.left_rel (subgroup.center G)) _ _ hab,
            assumption,
        },
        {refl,},
        {refl,},
    },
    {
        intro b,
        --unfold quotient_group.map at *,
        --simp at *,
        --unfold quotient_group.lift at *,
        --simp at *,
        induction b,
        {
            use b,
            refl,
        },
        {refl,},
    },
end

noncomputable theorem quot_ker_equiv_quot_center (f : G → H) (hf : is_pq_morphism f) (hfb : function.bijective f) :
    (quotient_group.quotient (group_morphism_mod_center f hf hfb.2).ker) ≃* (quotient_group.quotient (subgroup.center H)) :=
begin
    fapply mul_equiv.of_bijective,
    exact quotient_group.ker_lift (group_morphism_mod_center f hf hfb.2),
    split,
    {
        apply quotient_group.ker_lift_injective,
    },
    {
        intro b,
        induction b,
        {
            have hae := hfb.2 b,
            cases hae with a ha,
            use a,
            simp,
            apply quotient.sound,
            intro g,
            rw ha,
            group,
        },
        {refl,},
    },
end


noncomputable theorem group_mod_center_iso (f : G → H) (hf : is_pq_morphism f) (hfb : function.bijective f) : 
    (quotient_group.quotient (subgroup.center G)) ≃* (quotient_group.quotient (subgroup.center H)) :=
begin
    have e1 := group_mod_ker_eq_mod_center f hf hfb.2 hfb.1,
    have e2 := quot_ker_equiv_quot_center f hf hfb,
    have e3 := e1.symm,
    exact e3.trans e2,
end


noncomputable theorem group_center_equiv (f : G → H) (hf : is_pq_morphism f) (hfb : function.bijective f) : 
    (subgroup.center G) ≃ (subgroup.center H) := 
begin
    fapply equiv.of_bijective,
    {
        intro a,
        --unfold subgroup.center at a,
        --unfold subgroup.center,
        --unfold_coes,
        --unfold_coes at a,
        cases a with b hb,
        fconstructor,
        exact (f b),
        intro g,
        cases (hfb.2 g) with c hc,
        specialize hb c,
        rw center_reformulate,
        rw center_reformulate at hb,
        have hfbc := congr_arg f hb,
        rw ←rhd_group_def at hfbc,
        rw rhd_preserved_by_morphism f hf c b at hfbc,
        rw rhd_group_def at hfbc,
        rw hc at hfbc,
        assumption,
    },
    {
        split,
        {
            intros a b,
            intro hab,
            cases a with c hc,
            cases b with d hd,
            simp,
            simp at hab,
            exact (hfb.1 hab),
        },
        {
            intro a,
            cases a with b hb,
            simp,
            cases (hfb.2 b) with c hc,
            use c,
            {
                intro g,
                specialize hb (f g),
                rw center_reformulate,
                rw center_reformulate at hb,
                apply hfb.1,
                rw ←rhd_group_def,
                rw rhd_preserved_by_morphism f hf g c,
                rw rhd_group_def,
                rw hc,
                assumption,
            },
            simp,
            assumption,
        }
    }
end

/-
noncomputable theorem group_center_iso (f : G → H) (hf : is_pq_morphism f) (hfb : function.bijective f) : 
    (subgroup.center G) ≃* (subgroup.center H) :=
begin
    apply mul_equiv.mk' (group_center_equiv f hf hfb),
    intros x y,
    cases x with x hx,
    cases y with y hy,
    sorry,
end
-/


theorem group_order_bijection [fintype G] [decidable_eq G] [fintype H] [decidable_eq H] 
    (f : G → H) (hf : is_pq_morphism f) (hfb : function.bijective f) : 
    (∀ a : G, order_of a = order_of (f a)) :=
begin
    intro a,
    by_contradiction hc,
    by_cases ho : (order_of a < order_of (f a)),
    {
        have hm : ¬(λ (n : ℕ), ∃ (H_1 : n > 0), f a ^ n = 1) (order_of a),
        {
            apply nat.find_min (exists_pow_eq_one (f a)) ho,
        },
        simp at hm,
        have hoa := nat.find_spec (exists_pow_eq_one a),
        cases hoa with hoa1 hoa2,
        have hmh : 0 < order_of a,
        {
            exact order_of_pos a,
        },
        specialize hm hmh,
        have hmc : f a ^ order_of a = 1,
        {
            rw ←pq_morphism_pow_nat,
            unfold order_of,
            rw hoa2,
            apply pq_morphism_one f,
            exact hf,
            exact hf,
        },
        contradiction,
    },
    {
        have ho2 : (order_of (f a) < order_of a),
        {
            refine lt_of_le_of_ne _ (ne.symm hc),
            exact not_lt.mp ho,
        },
        have hm : ¬(λ (n : ℕ), ∃ (H_1 : n > 0), a ^ n = 1) (order_of (f a)),
        {
            apply nat.find_min (exists_pow_eq_one a) ho2,
        },
        simp at hm,
        have hoa := nat.find_spec (exists_pow_eq_one (f a)),
        cases hoa with hoa1 hoa2,
        have hmh : 0 < order_of (f a),
        {
            exact order_of_pos (f a),
        },
        specialize hm hmh,
        have hmc : a ^ order_of (f a) = 1,
        {
            apply hfb.1,
            rw pq_morphism_pow_nat f hf a _,
            unfold order_of,
            rw hoa2,
            rw pq_morphism_one f,
            exact hf,
        },
        contradiction,
    },
end


end group_to_pq_properties

