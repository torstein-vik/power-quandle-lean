
import quandle
import group_to_pq

import tactic

universe u

section automorphism_power_quandle

-- TODO: Define automorphism power quandle
-- TODO: Define property of morphism Q → Aut(Q)

structure automorphism (Q : Type u) [power_quandle Q] : Type u :=
(f : Q → Q)
(finv : Q → Q)
(hf : is_pq_morphism f)
(hfinv : is_pq_morphism finv)
(hffinv : f ∘ finv = id)
(hfinvf : finv ∘ f = id)

variables {Q : Type u} [power_quandle Q]

def automorphism_inverse (φ : automorphism Q) : automorphism Q := automorphism.mk
(automorphism.finv φ)
(automorphism.f φ)
(automorphism.hfinv φ)
(automorphism.hf φ)
(automorphism.hfinvf φ)
(automorphism.hffinv φ)

def automorphism_comp (φ1 : automorphism Q) (φ2 : automorphism Q) : automorphism Q := automorphism.mk
(automorphism.f φ1 ∘ automorphism.f φ2)
(automorphism.finv φ2 ∘ automorphism.finv φ1)
(begin
    cases φ1,
    cases φ2,
    simp, 
    apply pq_morphism_comp,
    assumption,
    assumption,
end)
(begin
    cases φ1,
    cases φ2,
    simp, 
    apply pq_morphism_comp,
    assumption,
    assumption,
end)
(begin
    cases φ1,
    cases φ2,
    simp,
    have assoc_rw : (φ1_f ∘ φ2_f) ∘ φ2_finv ∘ φ1_finv = φ1_f ∘ (φ2_f ∘ φ2_finv) ∘ φ1_finv,
    {
        repeat {rw function.comp.assoc},
    },
    rw assoc_rw,
    rw φ2_hffinv,
    simp,
    rw φ1_hffinv,
end)
(begin
    cases φ1,
    cases φ2,
    simp,
    have assoc_rw : (φ2_finv ∘ φ1_finv) ∘ φ1_f ∘ φ2_f = φ2_finv ∘ (φ1_finv ∘ φ1_f) ∘ φ2_f,
    {
        repeat {rw function.comp.assoc},
    },
    rw assoc_rw,
    rw φ1_hfinvf,
    simp,
    rw φ2_hfinvf,
end)

def id_automorphism : automorphism Q := automorphism.mk
(id)
(id)
(id_is_pq_morphism)
(id_is_pq_morphism)
(rfl)
(rfl)

lemma automorphism_eq (f1 : automorphism Q) (f2 : automorphism Q) : f1 = f2 ↔ automorphism.f f1 = automorphism.f f2 ∧ automorphism.finv f1 = automorphism.finv f2 :=
begin
    split,
    {
        intro hf,
        split,
        rw hf,
        rw hf,
    },
    {
        intro hf_pre,
        cases hf_pre with hf hfinv,
        induction f1,
        induction f2,
        simp,
        simp at hf,
        simp at hfinv,
        split,
        assumption,
        assumption,
    },
end


instance automorphism_has_mul : has_mul (automorphism Q) := ⟨automorphism_comp⟩

instance automorphism_has_one : has_one (automorphism Q) := ⟨id_automorphism⟩

instance automorphism_has_inv : has_inv (automorphism Q) := ⟨automorphism_inverse⟩

lemma automorphism_f_of_comp (f1 : automorphism Q) (f2 : automorphism Q) : (f1 * f2).f = f1.f ∘ f2.f := rfl
lemma automorphism_finv_of_comp (f1 : automorphism Q) (f2 : automorphism Q) : (f1 * f2).finv = f2.finv ∘ f1.finv := rfl

lemma automorphism_f_of_inverse (f1 : automorphism Q) : f1⁻¹.f = f1.finv := rfl
lemma automorphism_finv_of_inverse (f1 : automorphism Q) : f1⁻¹.finv = f1.f := rfl

lemma automorphism_f_of_id : (id_automorphism : automorphism Q).f = id := rfl
lemma automorphism_finv_of_id : (id_automorphism : automorphism Q).finv = id := rfl

lemma automorphism_comp_assoc : ∀ f1 f2 f3 : automorphism Q, f1 * f2 * f3 = f1 * (f2 * f3) :=
begin
    intros f1 f2 f3,
    refl,
end 

lemma automorphism_one_mul : ∀ f1 : automorphism Q, 1 * f1 = f1 :=
begin
    intro f1,
    cases f1,
    refl,
end

lemma automorphism_mul_one : ∀ f1 : automorphism Q, f1 * 1 = f1 :=
begin
    intro f1,
    cases f1,
    refl,
end

lemma automorphism_mul_left_inv : ∀ f1 : automorphism Q, f1⁻¹ * f1 = 1 :=
begin
    intro f1,
    rw automorphism_eq,
    split,
    {
        rw automorphism_f_of_comp,
        rw automorphism_f_of_inverse,
        rw f1.hfinvf,
        refl,
    },
    {
        rw automorphism_finv_of_comp,
        rw automorphism_finv_of_inverse,
        rw f1.hfinvf,
        refl,
    },
end

instance automorphism_group : group (automorphism Q) := group.mk
(automorphism_comp)
(automorphism_comp_assoc)
(id_automorphism)
(automorphism_one_mul)
(automorphism_mul_one)
(automorphism_inverse)
(automorphism_mul_left_inv)

instance automorphism_power_quandle : power_quandle (automorphism Q) := group_is_pq

end automorphism_power_quandle

section automorphism_power_quandle_morphism

variables {Q : Type u} [power_quandle Q]

def element_automorphism (a : Q) : automorphism Q := automorphism.mk
(λ b, a ▷ b)
(λ b, b ◁ a)
(begin
    split,
    {
        intros x y,
        simp,
        apply rack.right_dist,
    },
    {
        intros x n,
        simp,
        apply eq.symm,
        apply power_quandle.q_pown_right,
    },
end)
(begin
    split,
    {
        intros x y,
        simp,
        repeat {rw power_quandle.q_powneg_left},
        apply rack.right_dist,

    },
    {
        intros x n,
        simp,
        apply eq.symm,
        apply q_pown_left,
    },
end)
(begin
    apply funext,
    intro x,
    simp,
    apply rack.left_inv,
end)
(begin
    apply funext,
    intro x,
    simp,
    apply rack.right_inv,
end)

lemma element_automorphism_f (a : Q) : (element_automorphism a).f = λ b, a ▷ b := rfl
lemma element_automorphism_finv (a : Q) : (element_automorphism a).finv = λ b, b ◁ a := rfl

lemma element_automorphism_is_pq_morphism : is_pq_morphism (element_automorphism : Q → automorphism Q) :=
begin
    split,
    {
        intros a b,
        rw automorphism_eq,
        split,
        {
            rw rhd_def,
            rw automorphism_f_of_comp,
            rw automorphism_f_of_comp,
            rw automorphism_f_of_inverse,
            repeat {rw element_automorphism_f},
            rw element_automorphism_finv,
            apply funext,
            intro x,
            simp,
            rw ←rack.left_inv a x,
            rw ←rack.right_dist,
            rw rack.left_inv,
        },
        {
            rw rhd_def,
            rw automorphism_finv_of_comp,
            rw automorphism_finv_of_comp,
            rw automorphism_finv_of_inverse,
            repeat {rw element_automorphism_finv},
            rw element_automorphism_f,
            apply funext,
            intro x,
            simp,
            rw power_quandle.q_powneg_left,
            rw power_quandle.q_pown_right,
            rw ←rack.left_inv a x,
            rw ←rack.right_dist,
            rw rack.left_inv,
            repeat {rw power_quandle.q_powneg_left},
        },
    },
    {
        intros a n,
        induction n,
        {
            induction n with m hm,
            {
                have id_rw : element_automorphism a ^ int.of_nat 0 = id_automorphism,
                {
                    refl,
                },
                rw id_rw,
                rw automorphism_eq,
                split,
                {
                    rw element_automorphism_f,
                    rw automorphism_f_of_id,
                    apply funext,
                    intro x,
                    simp,
                    rw pow_0_rhd,
                },
                {
                    rw element_automorphism_finv,
                    rw automorphism_finv_of_id,
                    apply funext,
                    intro x,
                    simp,
                    rw lhd_pow_0,
                },
            },
            {
                --rw pow_of_nat,
                simp,
                rw gpow_add_one,
                simp at hm,
                simp,
                rw ←hm,
                rw automorphism_eq,
                split,
                {
                    rw automorphism_f_of_comp,
                    repeat {rw element_automorphism_f},
                    apply funext,
                    intro x,
                    simp,
                    rw ←power_quandle.pow_1 a,
                    rw power_quandle.pow_comp,
                    rw power_quandle.pow_comp,
                    rw power_quandle.q_powadd,
                    simp,
                },
                {
                    rw automorphism_finv_of_comp,
                    repeat {rw element_automorphism_finv},
                    apply funext,
                    intro x,
                    simp,
                    rw ←power_quandle.pow_1 a,
                    rw power_quandle.pow_comp,
                    rw power_quandle.pow_comp,
                    rw q_powadd_left,
                    simp,
                    rw int.add_comm,
                },
            },
        },
        {
            induction n with m hm,
            {
                rw automorphism_eq,
                split,
                {
                    --rw pow_neg_succ_of_nat,
                    --rw pow_1_nat_group,
                    simp,
                    rw automorphism_f_of_inverse,
                    rw element_automorphism_finv,
                    rw element_automorphism_f,
                    apply funext,
                    intro x,
                    rw power_quandle.q_powneg_left,
                    refl,
                },
                {
                    --rw pow_neg_succ_of_nat,
                    --rw pow_1_nat_group,
                    simp,
                    rw automorphism_finv_of_inverse,
                    rw element_automorphism_f,
                    rw element_automorphism_finv,
                    apply funext,
                    intro x,
                    rw power_quandle.q_powneg_left,
                    rw ←power_quandle.pow_1 a,
                    rw power_quandle.pow_comp,
                    rw power_quandle.pow_comp,
                    apply congr_arg (λ y, y ▷ x),
                    apply congr_arg,
                    refl,
                },
            },
            {
                --rw pow_neg_succ_of_nat_succ,
                have ar_rw : -[1+ m.succ] = -[1+ m] - 1 := rfl,
                rw ar_rw,
                rw gpow_sub_one,
                rw ←hm,
                rw automorphism_eq,
                split,
                {
                    rw automorphism_f_of_comp,
                    rw automorphism_f_of_inverse,
                    repeat {rw element_automorphism_f},
                    rw element_automorphism_finv,
                    apply funext,
                    intro x,
                    simp,
                    rw power_quandle.q_powneg_left,
                    rw power_quandle.q_powadd,
                    apply congr_arg (λ y, y ▷ x),
                    apply congr_arg,
                    refl,
                },
                {
                    rw automorphism_finv_of_comp,
                    rw automorphism_finv_of_inverse,
                    repeat {rw element_automorphism_finv},
                    rw element_automorphism_f,
                    apply funext,
                    intro x,
                    simp,
                    rw power_quandle.q_powneg_left,
                    rw power_quandle.q_powneg_left,
                    rw ←power_quandle.pow_1 a,
                    repeat {rw power_quandle.pow_comp},
                    rw power_quandle.q_powadd,
                    apply congr_arg (λ y, y ▷ x),
                    apply congr_arg,
                    ring,
                },
            },
        },
    },
end

end automorphism_power_quandle_morphism

