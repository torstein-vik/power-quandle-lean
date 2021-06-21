
-- Very heavy inspiration from https://github.com/leanprover-community/mathlib/blob/master/src/algebra/quandle.lean

import power_quandle
import group_to_pq


universes u v

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

lemma unit_def : (1 : pq_group Q) = ⟦unit⟧ := rfl

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

lemma rhd_of_eq_of_rhd : ∀ a b : Q, of a ▷ of b = of (a ▷ b) :=
begin
    intros a b,
    rw rhd_def_group,
    rw rhd_eq_conj,
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

lemma of_one : of (1 : Q) = 1 :=
begin
    rw ←pow_zero_eq_unit (1 : Q),
    apply congr_arg,
    rw power_quandle.pow_zero,
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

lemma of_inv (a : Q) : (of a)⁻¹ = of (a ^ (-1 : ℤ)) :=
begin
    rw of_pow_eq_pow_of,
    simp only [gpow_one, gpow_neg],
end

variables {QG : Type u} {QH : Type v} [power_quandle QG] [power_quandle QH]

lemma of_is_pq_morphism : is_pq_morphism (of : QH → pq_group QH) :=
begin
  split,
  {
    intros a b,
    rw rhd_of_eq_of_rhd,
  },
  {
    intros a n,
    rw of_pow_eq_pow_of,
  },
end

end pq_group


section pq_group_functor

variables {Q1 : Type u} [power_quandle Q1] {Q2 : Type v} [power_quandle Q2]

open pre_pq_group

lemma quot_mk_helper (a : pre_pq_group Q1) : quot.mk setoid.r a = ⟦a⟧ := rfl

lemma incl_unit_eq_unit : (⟦unit⟧ : pq_group Q1) = (1 : pq_group Q1) := 
begin
    refl,
end

def L_of_morph_aux (f : Q1 → Q2) (hf : is_pq_morphism f) : pre_pq_group Q1 → pre_pq_group Q2
| unit := unit
| (incl a) := incl (f a)
| (mul a b) := mul (L_of_morph_aux a) (L_of_morph_aux b)
| (inv a) := inv (L_of_morph_aux a)

def L_of_morph_fun (f : Q1 → Q2) (hf : is_pq_morphism f) : pq_group Q1 → pq_group Q2 := λ x, quotient.lift_on x (λ y, ⟦L_of_morph_aux f hf y⟧) (begin
    intros a b hab,
    induction hab with c d habr,
    clear a b,
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
        unfold L_of_morph_aux,
        repeat {rw ←mul_def},
        simp only at *,
        apply congr_arg2,
        assumption,
        assumption,
    },
    {
        simp only at *,
        unfold L_of_morph_aux,
        repeat {rw ←inv_def},
        apply congr_arg,
        assumption,
    },
    {
        simp only at *,
        unfold L_of_morph_aux,
        repeat {rw ←mul_def},
        apply mul_assoc,
    },
    {
        simp only at *,
        unfold L_of_morph_aux,
        repeat {rw ←mul_def},
        apply one_mul,
    },
    {
        simp only at *,
        unfold L_of_morph_aux,
        repeat {rw ←mul_def},
        apply mul_one,
    },
    {
        simp only at *,
        unfold L_of_morph_aux,
        repeat {rw ←mul_def},
        repeat {rw ←inv_def},
        apply mul_left_inv,
    },
    {
        simp only at *,
        unfold L_of_morph_aux,
        rw hf.1,
        apply quotient.sound,
        fconstructor,
        apply pre_pq_group_rel'.rhd_conj,
    },
    {
        simp only at *,
        unfold L_of_morph_aux,
        repeat {rw hf.2},
        apply quotient.sound,
        fconstructor,
        apply pre_pq_group_rel'.pow_pred,
    },
    {
        simp only at *,
        unfold L_of_morph_aux,
        repeat {rw hf.2},
        apply quotient.sound,
        fconstructor,
        apply pre_pq_group_rel'.pow_succ,
    },
    {
        simp only at *,
        unfold L_of_morph_aux,
        rw hf.2,
        apply quotient.sound,
        fconstructor,
        apply pre_pq_group_rel'.pow_zero,
    },
end)

def L_of_morph (f : Q1 → Q2) (hf : is_pq_morphism f) : pq_group Q1 →* pq_group Q2 := ⟨L_of_morph_fun f hf,
begin
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

theorem L_of_morph_of (f : Q1 → Q2) (hf : is_pq_morphism f) (x : Q1) : (L_of_morph f hf) (of x) = of (f x) := rfl 


def L_of_morph_iso (f : Q1 ≃ Q2) (hf : is_pq_morphism f.to_fun) : pq_group Q1 ≃* pq_group Q2 :=
begin
    fconstructor,
    {
        exact L_of_morph f.to_fun hf
    },
    {
        refine L_of_morph f.inv_fun _,
        split,
        {
            intros a b,
            rw ←f.right_inv a,
            rw ←f.right_inv b,
            rw f.left_inv,
            rw f.left_inv,
            rw ←hf.1,
            rw f.left_inv,
        },
        {
            intros a n,
            rw ←f.right_inv a,
            rw ←hf.2,
            rw f.left_inv,
            rw f.left_inv,
        },
    },
    {
        intro x,
        induction x,
        {
            unfold L_of_morph,
            simp only [monoid_hom.coe_mk],
            unfold L_of_morph_fun,
            simp only [quotient.lift_on_beta],
            induction x,
            {
                refl,
            },
            {
                unfold L_of_morph_aux,
                rw f.left_inv,
                refl,
            },
            {
                unfold L_of_morph_aux,
                rw ←mul_def,
                rw x_ih_a,
                rw x_ih_b,
                refl,
            },
            {
                unfold L_of_morph_aux,
                rw ←inv_def,
                rw x_ih,
                refl,
            },
        },
        {refl,},
    },
    {
        intro x,
        induction x,
        {
            unfold L_of_morph,
            simp only [monoid_hom.coe_mk],
            unfold L_of_morph_fun,
            simp only [quotient.lift_on_beta],
            induction x,
            {
                refl,
            },
            {
                unfold L_of_morph_aux,
                rw f.right_inv,
                refl,
            },
            {
                unfold L_of_morph_aux,
                rw ←mul_def,
                rw x_ih_a,
                rw x_ih_b,
                refl,
            },
            {
                unfold L_of_morph_aux,
                rw ←inv_def,
                rw x_ih,
                refl,
            },
        },
        {refl,},
    },
    {
        intros x y,
        exact is_mul_hom.map_mul ⇑(L_of_morph f.to_fun hf) x y,
    },
end 


end pq_group_functor


section group_to_to_group_comonad 

open pre_pq_group

variables {G : Type*} [group G]

variables {Q : Type*} [power_quandle Q]

def pq_morph_to_L_morph_adj_pre (f : Q → G) (hf : is_pq_morphism f) : pre_pq_group Q → G
| unit := (1 : G)
| (incl a) := f(a)
| (mul a b) := (pq_morph_to_L_morph_adj_pre a) * (pq_morph_to_L_morph_adj_pre b)
| (inv a) := (pq_morph_to_L_morph_adj_pre a)⁻¹ 

def pq_morph_to_L_morph_adj_fun (f : Q → G) (hf : is_pq_morphism f) : pq_group Q → G := λ x, quotient.lift_on x (pq_morph_to_L_morph_adj_pre f hf) (begin 
    cases hf with hf1 hf2,
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
        unfold pq_morph_to_L_morph_adj_pre,
        apply congr_arg2,
        assumption,
        assumption,
    },
    {
        unfold pq_morph_to_L_morph_adj_pre,
        apply congr_arg,
        assumption,
    },
    {
        unfold pq_morph_to_L_morph_adj_pre,
        apply mul_assoc,
    },
    {
        unfold pq_morph_to_L_morph_adj_pre,
        apply one_mul,
    },
    {
        unfold pq_morph_to_L_morph_adj_pre,
        apply mul_one,
    },
    {
        unfold pq_morph_to_L_morph_adj_pre,
        apply mul_left_inv,
    },
    {
        unfold pq_morph_to_L_morph_adj_pre,
        rw hf1,
        apply rhd_def_group,
    },
    {
        unfold pq_morph_to_L_morph_adj_pre,
        repeat {rw hf2},
        group,
    },
    {
        unfold pq_morph_to_L_morph_adj_pre,
        repeat {rw hf2},
        group,
    },
    {
        unfold pq_morph_to_L_morph_adj_pre,
        repeat {rw hf2},
        group,
    },
end)


def pq_morph_to_L_morph_adj (f : Q → G) (hf : is_pq_morphism f) : pq_group Q →* G := ⟨pq_morph_to_L_morph_adj_fun f hf, begin
    refl,
end, begin
    intros a b,
    induction a,
    induction b,
    {
        refl,
    },
    {refl,},
    {refl,},
end⟩

lemma pq_morph_to_L_morph_adj_comm_of (f : Q → G) (hf : is_pq_morphism f) (a : Q) : pq_morph_to_L_morph_adj f hf (of a) = f a :=
begin
    refl,
end

/-

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
-/

def counit : pq_group G →* G := pq_morph_to_L_morph_adj id id_is_pq_morphism

lemma counit_surjective : function.surjective (counit : pq_group G → G) :=
begin
    intro b,
    use ⟦incl b⟧,
    refl,
end 


lemma counit_of (a : G) : counit (of a) = a := rfl


lemma counit_unit : (counit ⟦(unit : pre_pq_group G)⟧) = 1 := rfl
lemma counit_incl (a : G) : counit (⟦incl a⟧) = a := rfl
lemma counit_mul (a b : pre_pq_group G) : counit ⟦mul a b⟧ = counit ⟦a⟧ * counit ⟦b⟧ := rfl
lemma counit_inv (a : pre_pq_group G) : counit ⟦inv a⟧ = (counit ⟦a⟧)⁻¹ := rfl


lemma unit_eq_incl_1 : ⟦unit⟧ = (of 1 : pq_group G) :=
begin
    rw ←gpow_zero (1 : G),
    rw pow_zero_eq_unit (1 : G),
    refl,
end

lemma of_1_eq_unit : (of 1 : pq_group G) = 1 := 
begin
    rw ←unit_eq_incl_1,
    refl,
end


lemma pq_group_commute (a b : G) (hab : commute a b) : commute (of a) (of b) :=
begin
    have arhdb : a ▷ b = b,
    {
        rw rhd_def_group,
        rw ←center_reformulate,
        exact hab,
    },
    unfold commute,
    unfold semiconj_by,
    rw center_reformulate,
    rw rhd_eq_conj,
    rw arhdb,
end

end group_to_to_group_comonad

