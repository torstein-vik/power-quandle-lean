
import pq_induce_lhd

universe u

section pre_free_pq

inductive pre_free_pq (S : Type u) : Type u
| incl (x : S) : pre_free_pq
| rhd (x y : pre_free_pq) : pre_free_pq
| pow (x : pre_free_pq) (n : ℤ) : pre_free_pq

open pre_free_pq

inductive pre_free_pq_rel' (S : Type u) : pre_free_pq S → pre_free_pq S → Type u
| refl {x : pre_free_pq S} : pre_free_pq_rel' x x
| symm {a b : pre_free_pq S} (hab : pre_free_pq_rel' a b) : pre_free_pq_rel' b a
| trans {a b c : pre_free_pq S} 
  (hab : pre_free_pq_rel' a b) (hbc : pre_free_pq_rel' b c) : pre_free_pq_rel' a c
| congr_rhd {a b a' b' : pre_free_pq S} 
  (ha : pre_free_pq_rel' a a') (hb : pre_free_pq_rel' b b') : 
  pre_free_pq_rel' (rhd a b) (rhd a' b') 
| congr_pow {a a' : pre_free_pq S} {n : ℤ} (ha : pre_free_pq_rel' a a') : 
  pre_free_pq_rel' (pow a n) (pow a' n)
| right_dist (a b c : pre_free_pq S) : pre_free_pq_rel' (rhd a (rhd b c)) (rhd (rhd a b) (rhd a c))
| self_idem_right (a : pre_free_pq S) : pre_free_pq_rel' (rhd a a) (a)
| pow_one (a : pre_free_pq S) : pre_free_pq_rel' (pow a (1 : ℤ)) (a)
| pow_comp (a : pre_free_pq S) (n m : ℤ) : pre_free_pq_rel' (pow (pow a n) m) (pow a (n * m))
| rhd_pow_zero (a b : pre_free_pq S) : pre_free_pq_rel' (rhd a (pow b (0 : ℤ))) (pow b (0 : ℤ))
| pow_zero_rhd (a b : pre_free_pq S) : pre_free_pq_rel' (rhd (pow a (0 : ℤ)) b) (b)
| pow_neg_one_rhd (a : pre_free_pq S) : pre_free_pq_rel' (rhd (pow a (-1 : ℤ)) a) (a)
| rhd_pow (a b : pre_free_pq S) (n : ℤ) : pre_free_pq_rel' (pow (rhd a b) n) (rhd a (pow b n))
| rhd_pow_add (a b : pre_free_pq S) (n m : ℤ) : pre_free_pq_rel' (rhd (pow a n) (rhd (pow a m) b)) (rhd (pow a (n + m)) b)


inductive pre_free_pq_rel (S : Type u) : pre_free_pq S → pre_free_pq S → Prop
| rel {a b : pre_free_pq S} (r : pre_free_pq_rel' S a b) : pre_free_pq_rel a b

variables {S : Type*}

lemma pre_free_pq_rel'.rel {a b : pre_free_pq S} : pre_free_pq_rel' S a b → pre_free_pq_rel S a b := pre_free_pq_rel.rel

@[refl]
lemma pre_free_pq_rel.refl {a : pre_free_pq S} : pre_free_pq_rel S a a := 
pre_free_pq_rel'.rel pre_free_pq_rel'.refl


@[symm]
lemma pre_free_pq_rel.symm {a b : pre_free_pq S} : pre_free_pq_rel S a b → pre_free_pq_rel S b a
| ⟨r⟩ := r.symm.rel


@[trans]
lemma pre_free_pq_rel.trans {a b c : pre_free_pq S} : 
pre_free_pq_rel S a b → pre_free_pq_rel S b c → pre_free_pq_rel S a c
| ⟨rab⟩ ⟨rbc⟩ := (rab.trans rbc).rel


instance pre_free_pq.setoid (S : Type*) : setoid (pre_free_pq S) :=
{
    r := pre_free_pq_rel S,
    iseqv := begin
        split, apply pre_free_pq_rel.refl,
        split, apply pre_free_pq_rel.symm,
        apply pre_free_pq_rel.trans,
    end
}

def free_pq (S : Type*) := quotient (pre_free_pq.setoid S)


instance free_pq_rhd : has_triangle_right (free_pq S) := ⟨λ a b, quotient.lift_on₂ a b (λ a b, ⟦rhd a b⟧) begin 
  intros a1 b1 a2 b2,
  intros ha hb,
  cases ha,
  cases hb,
  apply quotient.sound,
  exact (pre_free_pq_rel'.congr_rhd ha_r hb_r).rel,
end⟩

instance free_pq_pow : has_pow (free_pq S) ℤ := ⟨λ a n, quotient.lift_on a (λ a, ⟦pow a n⟧) begin 
  intros a b hab,
  cases hab,
  apply quotient.sound,
  exact (pre_free_pq_rel'.congr_pow hab_r).rel,
end⟩

instance free_pq_is_pq : power_quandle (free_pq S) := 
begin
  apply induce_lhd,
  exact (λ a b c, quotient.induction_on₃ a b c (λ a b c, quotient.sound (pre_free_pq_rel'.right_dist a b c).rel)),
  exact (λ a, quotient.induction_on a (λ a, quotient.sound (pre_free_pq_rel'.self_idem_right a).rel)),
  exact (λ a, quotient.induction_on a (λ a, quotient.sound (pre_free_pq_rel'.pow_one a).rel)),
  exact (λ a n m, quotient.induction_on a (λ a, quotient.sound (pre_free_pq_rel'.pow_comp a n m).rel)),
  exact (λ a b, quotient.induction_on₂ a b (λ a b, quotient.sound (pre_free_pq_rel'.rhd_pow_zero a b).rel)),
  exact (λ a b, quotient.induction_on₂ a b (λ a b, quotient.sound (pre_free_pq_rel'.pow_zero_rhd a b).rel)),
  exact (λ a, quotient.induction_on a (λ a, quotient.sound (pre_free_pq_rel'.pow_neg_one_rhd a).rel)),
  exact (λ a b n, quotient.induction_on₂ a b (λ a b, quotient.sound (pre_free_pq_rel'.rhd_pow a b n).rel)),
  exact (λ a b n m, quotient.induction_on₂ a b (λ a b, quotient.sound (pre_free_pq_rel'.rhd_pow_add a b n m).rel)),
end


def free_pq_of (s : S) : free_pq S := ⟦incl s⟧

lemma free_pq_of_def (s : S) : free_pq_of s = ⟦incl s⟧ := rfl

lemma free_pq_rhd_def (x y : pre_free_pq S) : ⟦rhd x y⟧ = (⟦x⟧ ▷ ⟦y⟧ : free_pq S) := rfl

lemma free_pq_pow_def (x : pre_free_pq S) (n : ℤ) : ⟦pow x n⟧ = (⟦x⟧ ^ n : free_pq S) := rfl


lemma quot_mk_helper_free_pq (a : pre_free_pq S) : quot.mk setoid.r a = ⟦a⟧ := rfl


variables {Q : Type*} [power_quandle Q]

def free_pq_adjoint_pre (f : S → Q) : pre_free_pq S → Q :=
begin
  intro x,
  induction x,
  {
    exact f x,
  },
  {
    exact x_ih_x ▷ x_ih_y,
  },
  {
    exact x_ih ^ x_n,
  },
end

lemma free_pq_adjoint_pre_of (f : S → Q) (x : S) : free_pq_adjoint_pre f (incl x) = f x := rfl

lemma free_pq_adjoint_pre_rhd (f : S → Q) (x y : pre_free_pq S) : free_pq_adjoint_pre f (x.rhd y) = free_pq_adjoint_pre f x ▷ free_pq_adjoint_pre f y := rfl

lemma free_pq_adjoint_pre_pow (f : S → Q) (x : pre_free_pq S) (n : ℤ) : free_pq_adjoint_pre f (x.pow n) = (free_pq_adjoint_pre f x) ^ n := rfl


def free_pq_adjoint (f : S → Q) : free_pq S → Q :=
begin
  intro x,
  induction x,
  {
    exact free_pq_adjoint_pre f x,
  },
  {
    simp only [eq_rec_constant],
    induction x_p,
    induction x_p_r,
    {
      refl,
    },
    {
      apply eq.symm,
      assumption,
    },
    {
      apply eq.trans,
      assumption,
      assumption,
    },
    {
      rw free_pq_adjoint_pre_rhd,
      rw free_pq_adjoint_pre_rhd,
      rw x_p_r_ih_ha,
      rw x_p_r_ih_hb,
    },
    {
      rw free_pq_adjoint_pre_pow,
      rw free_pq_adjoint_pre_pow,
      rw x_p_r_ih,
    },
    {
      repeat {rw free_pq_adjoint_pre_rhd},
      apply rack.right_dist,
    },
    {
      repeat {rw free_pq_adjoint_pre_rhd},
      apply quandle.self_idem_right,
    },
    {
      repeat {rw free_pq_adjoint_pre_pow},
      apply power_quandle.pow_1,
    },
    {
      repeat {rw free_pq_adjoint_pre_pow},
      apply power_quandle.pow_comp,
    },
    {
      repeat {rw free_pq_adjoint_pre_rhd},
      repeat {rw free_pq_adjoint_pre_pow},
      apply power_quandle.q_pow0,
    },
    {
      repeat {rw free_pq_adjoint_pre_rhd},
      repeat {rw free_pq_adjoint_pre_pow},
      apply pow_0_rhd,
    },
    {
      repeat {rw free_pq_adjoint_pre_rhd},
      repeat {rw free_pq_adjoint_pre_pow},
      apply pow_neg_one_rhd_self,
    },
    {
      repeat {rw free_pq_adjoint_pre_rhd},
      repeat {rw free_pq_adjoint_pre_pow},
      repeat {rw free_pq_adjoint_pre_rhd},
      apply power_quandle.q_pown_right,
    },
    {
      repeat {rw free_pq_adjoint_pre_rhd},
      repeat {rw free_pq_adjoint_pre_pow},
      apply power_quandle.q_powadd,
    },
  },
end

lemma free_pq_adjoint_is_pq_morphism {f : S → Q} : is_pq_morphism (free_pq_adjoint f : free_pq S → Q) :=
begin
  split,
  {
    intros a b,
    induction a,
    induction b,
    {
      refl,
    },
    {refl,},
    {refl,},
  },
  {
    intros a n,
    induction a,
    {
      refl,
    },
    {refl,},
  },
end

lemma free_pq_adjoint_comm_of {f : S → Q} (x : S) : free_pq_adjoint f (free_pq_of x) = f x := rfl


end pre_free_pq

