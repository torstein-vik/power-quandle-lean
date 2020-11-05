
-- Very heavy inspiration from https://github.com/leanprover-community/mathlib/blob/master/src/algebra/quandle.lean

import quandle

import algebra.group

universe u

-- TODO: Define enveloping group of power quandle
-- TODO: Universal property as adjoint to forgetful
-- TOOD: Cylic is sent to Cyclic
-- TODO: Dihedral is sent to Dihedral (x C2)

section pre_pq_group

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
            simp,
            apply pow_zero_eq_unit,
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



end pre_pq_group