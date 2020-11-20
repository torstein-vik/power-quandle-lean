
-- Very heavy inspiration from https://github.com/leanprover-community/mathlib/blob/master/src/algebra/quandle.lean

import quandle
import group_to_pq

import algebra.group
import data.zmod.basic

universe u

-- TODO: Define enveloping group of power quandle
-- TODO: Universal property as adjoint to forgetful
-- TOOD: Cylic is sent to Cyclic
-- TODO: Dihedral is sent to Dihedral (x C2)

section pq_group

inductive pre_pq_group (Q : Type u) : Type u
| unit : pre_pq_group
| incl (x : Q) : pre_pq_group
| mul (a b : pre_pq_group) : pre_pq_group
| inv (a : pre_pq_group) : pre_pq_group


open pre_pq_group


inductive pre_pq_group_rel' (Q : Type u) [power_quandle Q] : pre_pq_group Q → pre_pq_group Q → Type u
| refl {a : pre_pq_group Q} : pre_pq_group_rel' a a
| symm {a b : pre_pq_group Q} (hab : pre_pq_group_rel' a b) : pre_pq_group_rel' b a
| trans {a b c : pre_pq_group Q} 
  (hab : pre_pq_group_rel' a b) (hbc : pre_pq_group_rel' b c) : pre_pq_group_rel' a c
| congr_mul {a b a' b' : pre_pq_group Q} 
  (ha : pre_pq_group_rel' a a') (hb : pre_pq_group_rel' b b') : 
  pre_pq_group_rel' (mul a b) (mul a' b') 
| congr_inv {a a' : pre_pq_group Q} (ha : pre_pq_group_rel' a a') : 
  pre_pq_group_rel' (inv a) (inv a')
| assoc (a b c : pre_pq_group Q) : pre_pq_group_rel' (mul (mul a b) c) (mul a (mul b c))
| one_mul (a : pre_pq_group Q) : pre_pq_group_rel' (mul unit a) a
| mul_one (a : pre_pq_group Q) : pre_pq_group_rel' (mul a unit) a
| mul_left_inv (a : pre_pq_group Q) : pre_pq_group_rel' (mul (inv a) a) unit
| rhd_conj (a b : Q) : pre_pq_group_rel' (mul (mul (incl a) (incl b)) (inv (incl a))) (incl (a ▷ b))
| pow_pred (a : Q) (n : int) : pre_pq_group_rel' (incl (a ^ n)) (mul (incl a) (incl (a ^ (n - 1))))
| pow_succ (a : Q) (n : int) : pre_pq_group_rel' (incl (a ^ n)) (mul (incl (a ^ (n + 1))) (inv (incl a)))
| pow_zero (a : Q) : pre_pq_group_rel' (incl (a ^ (0 : int))) unit


inductive pre_pq_group_rel (Q : Type u) [power_quandle Q] : pre_pq_group Q → pre_pq_group Q → Prop
| rel {a b : pre_pq_group Q} (r : pre_pq_group_rel' Q a b) : pre_pq_group_rel a b


variables {Q : Type*} [power_quandle Q]

lemma pre_pq_group_rel'.rel {a b : pre_pq_group Q} : pre_pq_group_rel' Q a b → pre_pq_group_rel Q a b := pre_pq_group_rel.rel


@[refl]
lemma pre_pq_group_rel.refl {a : pre_pq_group Q} : pre_pq_group_rel Q a a := 
pre_pq_group_rel'.rel pre_pq_group_rel'.refl


@[symm]
lemma pre_pq_group_rel.symm {a b : pre_pq_group Q} : pre_pq_group_rel Q a b → pre_pq_group_rel Q b a
| ⟨r⟩ := r.symm.rel


@[trans]
lemma pre_pq_group_rel.trans {a b c : pre_pq_group Q} : 
pre_pq_group_rel Q a b → pre_pq_group_rel Q b c → pre_pq_group_rel Q a c
| ⟨rab⟩ ⟨rbc⟩ := (rab.trans rbc).rel


instance pre_pq_group.setoid (Q : Type*) [power_quandle Q] : setoid (pre_pq_group Q) :=
{
    r := pre_pq_group_rel Q,
    iseqv := begin
        split, apply pre_pq_group_rel.refl,
        split, apply pre_pq_group_rel.symm,
        apply pre_pq_group_rel.trans,
    end
}


def pq_group (Q : Type*) [power_quandle Q] := quotient (pre_pq_group.setoid Q)


instance pq_group_is_group : group (pq_group Q) := 
{ mul := λ a b, quotient.lift_on₂ a b
                  (λ a b, ⟦pre_pq_group.mul a b⟧)
                  (λ a b a' b' ⟨ha⟩ ⟨hb⟩,
                    quotient.sound (pre_pq_group_rel'.congr_mul ha hb).rel),
  one := ⟦unit⟧,
  inv := λ a, quotient.lift_on a
                (λ a, ⟦pre_pq_group.inv a⟧)
                (λ a a' ⟨ha⟩,
                  quotient.sound (pre_pq_group_rel'.congr_inv ha).rel),
  mul_assoc := λ a b c,
    quotient.induction_on₃ a b c (λ a b c, quotient.sound (pre_pq_group_rel'.assoc a b c).rel),
  one_mul := λ a,
    quotient.induction_on a (λ a, quotient.sound (pre_pq_group_rel'.one_mul a).rel),
  mul_one := λ a,
    quotient.induction_on a (λ a, quotient.sound (pre_pq_group_rel'.mul_one a).rel),
  mul_left_inv := λ a,
    quotient.induction_on a (λ a, quotient.sound (pre_pq_group_rel'.mul_left_inv a).rel) }


def of (a : Q) : pq_group Q := ⟦incl a⟧


lemma of_def (a : Q) : of a = ⟦incl a⟧ := rfl


lemma mul_def (a b : pre_pq_group Q) : (⟦a⟧ * ⟦b⟧ : pq_group Q) = ⟦mul a b⟧ := rfl

lemma inv_def (a : pre_pq_group Q) : (⟦a⟧⁻¹ : pq_group Q) = ⟦inv a⟧ := rfl


lemma rhd_eq_conj : ∀ a b : Q, of a * of b * (of a)⁻¹ = of (a ▷ b) :=
begin
    intros a b,
    repeat {rw of_def},
    rw inv_def,
    repeat {rw mul_def},
    apply quotient.sound,
    exact (pre_pq_group_rel'.rhd_conj a b).rel
end


lemma pow_eq_mul_pow_pred : ∀ a : Q, ∀ n : int, of (a ^ n) = of a * of (a ^ (n - 1)) :=
begin
    intros a n,
    apply quotient.sound,
    exact (pre_pq_group_rel'.pow_pred a n).rel
end


lemma pow_eq_pow_succ_mul_inv : ∀ a : Q, ∀ n : int, of (a ^ n) = of (a ^ (n + 1)) * (of a)⁻¹ :=
begin
    intros a n,
    apply quotient.sound,
    exact (pre_pq_group_rel'.pow_succ a n).rel
end


lemma pow_zero_eq_unit : ∀ a : Q, of (a ^ (0 : int)) = 1 :=
begin
    intro a,
    apply quotient.sound,
    exact (pre_pq_group_rel'.pow_zero a).rel
end 


lemma of_pow_eq_pow_of : ∀ a : Q, ∀ n : int, of (a ^ n) = (of a) ^ n :=
begin
    intros a n,
    induction n,
    {
        induction n with m hm,
        {
            simp,
            apply pow_zero_eq_unit,
        },
        {
            simp,
            rw pow_eq_mul_pow_pred,
            ring,
            simp at hm,
            rw hm,
            refl,
        },
    },
    {
        induction n with m hm,
        {
            rw pow_eq_pow_succ_mul_inv,
            have ar_rw : -[1+ 0] + 1 = 0 := rfl,
            rw ar_rw,
            --simp,
            rw pow_zero_eq_unit,
            simp,
        },
        {
            rw pow_eq_pow_succ_mul_inv,
            have ar_rw : -[1+ m.succ] + 1 = -[1+ m] := rfl,
            rw ar_rw,
            rw hm,
            refine inv_inj.mp _,
            simp,
            refl,
        },
    },
end



end pq_group


section group_to_to_group_comonad 

open pre_pq_group

variables {G : Type*} [group G]

def counit_pre : pre_pq_group G → G
| unit := (1 : G)
| (incl a) := a
| (mul a b) := (counit_pre a) * (counit_pre b)
| (inv a) := (counit_pre a)⁻¹

def counit_fun : pq_group G → G := λ x, quotient.lift_on x (counit_pre) (begin
    intros a b,
    intro hab,
    induction hab with c d habr,
    clear x,
    clear a,
    clear b,
    induction habr,
    {
        refl,
    },
    {
        apply eq.symm,
        assumption,
    },
    {
        apply eq.trans habr_ih_hab habr_ih_hbc,
    },
    {
        unfold counit_pre,
        apply congr_arg2,
        assumption,
        assumption,
    },
    {
        unfold counit_pre,
        apply congr_arg,
        assumption,
    },
    {
        unfold counit_pre,
        apply mul_assoc,
    },
    {
        unfold counit_pre,
        apply one_mul,
    },
    {
        unfold counit_pre,
        apply mul_one,
    },
    {
        unfold counit_pre,
        apply mul_left_inv,
    },
    {
        unfold counit_pre,
        apply rhd_def,
    },
    {
        unfold counit_pre,
        group,
    },
    {
        unfold counit_pre,
        group,
    },
    {
        unfold counit_pre,
        group,
    },
end)


def counit : pq_group G →* G := ⟨counit_fun, begin
    refl,
end, begin
    intros x y,
    induction x,
    induction y,
    {
        refl,
    },
    {refl,},
    {refl,},
end⟩


lemma counit_surjective : function.surjective (counit : pq_group G → G) :=
begin
    intro b,
    use ⟦incl b⟧,
    refl,
end 


lemma counit_of (a : G) : counit (of a) = a := rfl


end group_to_to_group_comonad



section cyclic_pq_group


structure cyclic (n : nat) :=
(val : zmod n)

variables {n : nat}

def cyclic_mul : cyclic n → cyclic n → cyclic n
| ⟨a⟩ ⟨b⟩ := ⟨a + b⟩

def cyclic_inv : cyclic n → cyclic n
| ⟨a⟩ := ⟨-a⟩

instance cyclic_has_mul : has_mul (cyclic n) := ⟨cyclic_mul⟩

instance cyclic_has_neg : has_inv (cyclic n) := ⟨cyclic_inv⟩ 

instance cyclic_has_one : has_one (cyclic n) := ⟨⟨0⟩⟩


lemma cyclic_mul_def (a b : zmod n) : (⟨a⟩ * ⟨b⟩ : cyclic n) = ⟨a + b⟩ := rfl

lemma cyclic_inv_def (a : zmod n) : (⟨a⟩⁻¹ : cyclic n) = ⟨-a⟩ := rfl

lemma cyclic_one_def : (1 : cyclic n) = ⟨0⟩ := rfl


instance cyclic_group : group (cyclic n) :=
{
    mul_assoc := begin
        rintros ⟨a⟩ ⟨b⟩ ⟨c⟩,
        repeat {rw cyclic_mul_def},
        apply congr_arg,
        apply add_assoc,
    end,
    one_mul := begin
        rintro ⟨a⟩,
        rw cyclic_one_def,
        rw cyclic_mul_def,
        apply congr_arg,
        apply zero_add,
    end,
    mul_one := begin
        rintro ⟨a⟩,
        rw cyclic_one_def,
        rw cyclic_mul_def,
        apply congr_arg,
        apply add_zero,
    end,
    mul_left_inv := begin
        rintro ⟨a⟩,
        rw cyclic_inv_def,
        rw cyclic_mul_def,
        rw cyclic_one_def,
        apply congr_arg,
        apply add_left_neg,
    end,
    ..cyclic_has_mul,
    ..cyclic_has_neg,
    ..cyclic_has_one,
}

def generator : (cyclic n) := ⟨1⟩ 

lemma cyclic_as_power (x : cyclic n) : ∃ k : int, x = generator^k :=
begin
    induction x,
    use (zmod.val_min_abs x),
    --simp at *,
    have gen_pow : ∀ k : int, (⟨k⟩ : cyclic n) = generator ^ k,
    {
        intro k,
        induction k,
        {
            induction k with l hl,
            {
                refl,
            },
            {
                simp at *,
                rw gpow_add_one,
                simp,
                rw ←hl,
                refl,
            },
        },
        {
            induction k with l hl,
            {
                simp,
                refl,
            },
            {
                simp at *,
                rw pow_succ,
                simp,
                rw ←hl,
                apply congr_arg,
                ring,
            },
        },
    },
    have h := gen_pow (x.val_min_abs),
    simp at h,
    assumption,
end


lemma cyclic_counit_form : function.surjective (of : (cyclic n) → pq_group (cyclic n)) :=
begin
    intro x,
    induction x,
    {
        induction x,
        {
            use 1,
            apply quotient.sound,
            fconstructor,
            apply pre_pq_group_rel'.pow_zero,
            exact 1,
        },
        {
            use x,
            refl,
        },
        {
            cases x_ih_a with a ha,
            cases x_ih_b with b hb,
            use (a * b),
            --apply quotient.sound,
            have ha2 := cyclic_as_power a,
            have hb2 := cyclic_as_power b,
            cases ha2 with k hk,
            cases hb2 with l hl,
            rw hk,
            rw hl,
            rw ←gpow_add,
            rw of_pow_eq_pow_of,
            have hr : quot.mk setoid.r (x_a.mul x_b) = ((quot.mk setoid.r x_a) * (quot.mk setoid.r x_b) : pq_group (cyclic n)),
            {
                refl,
            },
            rw hr,
            rw ←ha,
            rw ←hb,
            rw hk,
            rw hl,
            rw of_pow_eq_pow_of,
            rw of_pow_eq_pow_of,
            rw ←gpow_add,
        },
        {
            cases x_ih with y hy,
            use (y ^ (-1 : int)),
            rw of_pow_eq_pow_of,
            rw hy,
            simp,
            refl,
        },
    },
    {refl,},
end


theorem cyclic_counit_bijective : function.bijective (counit : pq_group (cyclic n) → cyclic n) :=
begin
    split,
    {
        intros x y,
        intro hxy,
        have hx := cyclic_counit_form x,
        have hy := cyclic_counit_form y,
        cases hx with xx hxx,
        cases hy with yy hyy,
        rw ←hxx at *,
        rw ←hyy at *,
        apply congr_arg,
        repeat {rw counit_of at hxy},
        assumption,
    },
    {
        apply counit_surjective,
    }
end


noncomputable theorem comonad_cyclic_iso : pq_group (cyclic n) ≃* cyclic n :=
begin
    fapply mul_equiv.of_bijective,
    exact counit,
    exact cyclic_counit_bijective,
end


end cyclic_pq_group

