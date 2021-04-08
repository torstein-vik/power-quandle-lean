

import pq_induce_lhd

universes u u1 u2

section pq_quotient_rel


class has_pq_rel (Q : Type u) := (rel : Q → Q → Prop)

variables {Q : Type u} [power_quandle Q] [has_pq_rel Q]

inductive pq_general_rel' : Q → Q → Type u
| refl {x : Q} : pq_general_rel' x x
| symm {x y : Q} (hxy : pq_general_rel' x y) : pq_general_rel' y x
| trans {x y z : Q} (hxy : pq_general_rel' x y) (hyz : pq_general_rel' y z) : pq_general_rel' x z
| congr_rhd {x y x' y' : Q} (hx : pq_general_rel' x x') (hy : pq_general_rel' y y') : pq_general_rel' (x ▷ y) (x' ▷ y')
| congr_pow {x x' : Q} {n : ℤ} (hx : pq_general_rel' x x') : pq_general_rel' (x ^ n) (x' ^ n)
| custom_rel {x y : Q} (hxy : has_pq_rel.rel x y) : pq_general_rel' x y


inductive pq_general_rel : Q → Q → Prop
| rel' {x y : Q} (hxy : pq_general_rel' x y) : pq_general_rel x y



instance pq_general_rel_setoid : setoid Q := { 
  r := pq_general_rel,
  iseqv := begin 
    split,
    {
      intro x,
      exact pq_general_rel.rel' (pq_general_rel'.refl),
    },
    split,
    {
      rintros x y hxy,
      cases hxy with _ _ hxy,
      exact pq_general_rel.rel' (pq_general_rel'.symm hxy),
    },
    {
      intros x y z hxy hyz,
      cases hxy with _ _ hxy,
      cases hyz with _ _ hyz,
      refine pq_general_rel.rel' _,
      exact pq_general_rel'.trans hxy hyz,
    },
  end }


def pq_quotient (Q : Type u) [power_quandle Q] [has_pq_rel Q] : Type u := quotient (@pq_general_rel_setoid Q _ _)

instance pq_quotient_rhd : has_triangle_right (pq_quotient Q) := ⟨quotient.lift₂ (λ x y : Q, (⟦x ▷ y⟧ : pq_quotient Q)) begin 
  intros a b c d hac hbd,
  simp only [quotient.eq],
  cases hac,
  cases hbd,
  fconstructor,
  refine pq_general_rel'.congr_rhd _ _,
  assumption,
  assumption,
end⟩

instance pq_quotient_pow : has_pow (pq_quotient Q) ℤ := ⟨λ x n, quotient.lift_on x (λ x : Q, (⟦x ^ n⟧ : pq_quotient Q)) begin 
  intros a b hab,
  cases hab,
  simp only [quotient.eq],
  fconstructor,
  exact pq_general_rel'.congr_pow hab_hxy,
end⟩

lemma quot_mk_helper_pq_quotient (a : Q) : quot.mk setoid.r a = ⟦a⟧ := rfl

lemma pq_quotient_rhd_def (a b : Q) : (⟦a⟧ ▷ ⟦b⟧ : pq_quotient Q) = ⟦a ▷ b⟧ := rfl

lemma pq_quotient_pow_def (a : Q) (n : ℤ) : (⟦a⟧ ^ n : pq_quotient Q) = ⟦a ^ n⟧ := rfl

instance pq_quotient_is_pq : power_quandle (pq_quotient Q) :=
begin
  apply induce_lhd,
  {
    intros a b c,
    induction a,
    induction b,
    induction c,
    {
      simp only [quot_mk_helper_pq_quotient, pq_quotient_rhd_def],
      apply congr_arg,
      apply rack.right_dist,
    },
    repeat {refl,},
  },
  {
    intros a,
    induction a,
    {
      simp only [quot_mk_helper_pq_quotient, pq_quotient_rhd_def],
      apply congr_arg,
      apply quandle.self_idem_right,
    },
    {refl,},
  },
  {
    intros a,
    induction a,
    {
      simp only [quot_mk_helper_pq_quotient, pq_quotient_pow_def],
      apply congr_arg,
      apply power_quandle.pow_1,
    },
    {refl,},
  },
  {
    intros a n m,
    induction a,
    {
      simp only [quot_mk_helper_pq_quotient, pq_quotient_pow_def],
      apply congr_arg,
      apply power_quandle.pow_comp,
    },
    {refl,},
  },
  {
    intros a b,
    induction a,
    induction b,
    {
      simp only [quot_mk_helper_pq_quotient, pq_quotient_rhd_def, pq_quotient_pow_def],
      apply congr_arg,
      apply power_quandle.q_pow0,
    },
    repeat {refl,},
  },
  {
    intros a b,
    induction a,
    induction b,
    {
      simp only [quot_mk_helper_pq_quotient, pq_quotient_rhd_def, pq_quotient_pow_def],
      apply congr_arg,
      exact pow_0_rhd a b,
    },
    repeat {refl,},
  },
  {
    intros a,
    induction a,
    {
      simp only [quot_mk_helper_pq_quotient, pq_quotient_rhd_def, pq_quotient_pow_def],
      apply congr_arg,
      exact pow_neg_one_rhd_self a,
    },
    {refl,},
  },
  {
    intros a b n,
    induction a,
    induction b,
    {
      simp only [quot_mk_helper_pq_quotient, pq_quotient_rhd_def, pq_quotient_pow_def],
      apply congr_arg,
      exact power_quandle.q_pown_right a b n,
    },
    repeat {refl,},
  },
  {
    intros a b n m,
    induction a,
    induction b,
    {
      simp only [quot_mk_helper_pq_quotient, pq_quotient_rhd_def, pq_quotient_pow_def],
      apply congr_arg,
      exact power_quandle.q_powadd a b n m,
    },
    repeat {refl,},
  },
end


variables {Q1 : Type u1} [power_quandle Q1]

def pq_quotient_lift (f : Q → Q1) (hf : is_pq_morphism f) (hfq : ∀ q1 q2 : Q, has_pq_rel.rel q1 q2 → f q1 = f q2) : pq_quotient Q → Q1 := quotient.lift (λ x, f x) begin
  intros a b hab,
  simp only,
  induction hab,
  induction hab_hxy,
  {
    refl,
  },
  {
    symmetry,
    assumption,
  },
  {
    transitivity,
    assumption,
    assumption,
  },
  {
    simp only [hf.1],
    apply congr_arg2,
    assumption,
    assumption,
  },
  {
    simp only [hf.2, hab_hxy_ih],
  },
  {
    apply hfq,
    assumption,
  },
end


theorem pq_quotient_lift_is_pq_morphism (f : Q → Q1) (hf : is_pq_morphism f) (hfq : ∀ q1 q2 : Q, has_pq_rel.rel q1 q2 → f q1 = f q2) : is_pq_morphism (pq_quotient_lift f hf hfq) :=
begin
  split,
  {
    intros a b,
    induction a,
    induction b,
    {
      simp only [quot_mk_helper_pq_quotient, pq_quotient_rhd_def],
      unfold pq_quotient_lift,
      simp only [quotient.lift_beta],
      rw hf.1,
    },
    {refl,},
    {refl,},
  },
  {
    intros a n,
    induction a,
    {
      simp only [quot_mk_helper_pq_quotient, pq_quotient_pow_def],
      unfold pq_quotient_lift,
      simp only [quotient.lift_beta],
      rw hf.2,
    },
    {refl,},
  },
end


end pq_quotient_rel
