
import abelian_power_quandle

universes u v

section abelianization_pq

inductive pre_abelianization_pq (Q : Type u) [power_quandle Q] : Type u
| incl (x : Q) : pre_abelianization_pq
| add (x y : pre_abelianization_pq) : pre_abelianization_pq 
| neg (x : pre_abelianization_pq) : pre_abelianization_pq
| zero : pre_abelianization_pq
| pow (x : pre_abelianization_pq) (n : ℤ) : pre_abelianization_pq

open pre_abelianization_pq

inductive pre_abelianization_pq_rel' (Q : Type u) [power_quandle Q] : pre_abelianization_pq Q → pre_abelianization_pq Q → Type u
| refl {x : pre_abelianization_pq Q} : pre_abelianization_pq_rel' x x
| symm {x y : pre_abelianization_pq Q} (hxy : pre_abelianization_pq_rel' x y) : pre_abelianization_pq_rel' y x
| trans {x y z : pre_abelianization_pq Q} (hxy : pre_abelianization_pq_rel' x y) (hyz : pre_abelianization_pq_rel' y z) : pre_abelianization_pq_rel' x z
| congr_add {x1 x2 y1 y2 : pre_abelianization_pq Q} (hx : pre_abelianization_pq_rel' x1 x2) (hy : pre_abelianization_pq_rel' y1 y2) : pre_abelianization_pq_rel' (add x1 y1) (add x2 y2)
| congr_neg {x1 x2 : pre_abelianization_pq Q} (hx : pre_abelianization_pq_rel' x1 x2) : pre_abelianization_pq_rel' (neg x1) (neg x2)
| congr_pow {x1 x2 : pre_abelianization_pq Q} {n : ℤ} (hx : pre_abelianization_pq_rel' x1 x2) : pre_abelianization_pq_rel' (pow x1 n) (pow x2 n)
| add_assoc (x y z : pre_abelianization_pq Q) : pre_abelianization_pq_rel' (add (add x y) z) (add x (add y z))
| add_comm (x y : pre_abelianization_pq Q) : pre_abelianization_pq_rel' (add x y) (add y x)
| zero_right (x : pre_abelianization_pq Q) :
pre_abelianization_pq_rel' (add x zero) (x)
| neg_add_right (x : pre_abelianization_pq Q) :
pre_abelianization_pq_rel' (add x (neg x)) (zero)
| pow_one (x : pre_abelianization_pq Q) : pre_abelianization_pq_rel' (pow x (1 : ℤ)) (x)
| pow_exp_zero (x : pre_abelianization_pq Q) : pre_abelianization_pq_rel' (pow x (0 : ℤ)) (incl 1)
| pow_comp (x : pre_abelianization_pq Q) (n m : ℤ) : pre_abelianization_pq_rel' (pow (pow x n) m) (pow x (n * m))
| pow_add (x y : pre_abelianization_pq Q) (n : ℤ) : pre_abelianization_pq_rel' (add (pow x n) (pow y n)) (pow (add x y) n)
| pow_neg (x : pre_abelianization_pq Q) (n : ℤ) : pre_abelianization_pq_rel' (neg (pow x n)) (pow (neg x) n)
| pow_zero (n : ℤ) : pre_abelianization_pq_rel' (pow zero n) (zero) 
| rhd_incl (x y : Q) : pre_abelianization_pq_rel' (incl (x ▷ y)) (incl y) 
| pow_incl (x : Q) (n : ℤ) : pre_abelianization_pq_rel' (incl (x ^ n)) (pow (incl x) n)

inductive pre_abelianization_pq_rel (Q : Type u) [power_quandle Q] : pre_abelianization_pq Q → pre_abelianization_pq Q → Prop
| rel {x y : pre_abelianization_pq Q} (hxy : pre_abelianization_pq_rel' Q x y) : pre_abelianization_pq_rel x y

variables {Q : Type u} [power_quandle Q]

lemma pre_abelianization_pq_rel'.rel {a b : pre_abelianization_pq Q} : pre_abelianization_pq_rel' Q a b → pre_abelianization_pq_rel Q a b := pre_abelianization_pq_rel.rel


@[refl]
lemma pre_abelianization_pq_rel.refl {a : pre_abelianization_pq Q} : pre_abelianization_pq_rel Q a a := 
pre_abelianization_pq_rel'.rel pre_abelianization_pq_rel'.refl


@[symm]
lemma pre_abelianization_pq_rel.symm {a b : pre_abelianization_pq Q} : pre_abelianization_pq_rel Q a b → pre_abelianization_pq_rel Q b a
| ⟨r⟩ := r.symm.rel


@[trans]
lemma pre_abelianization_pq_rel.trans {a b c : pre_abelianization_pq Q} : 
pre_abelianization_pq_rel Q a b → pre_abelianization_pq_rel Q b c → pre_abelianization_pq_rel Q a c
| ⟨rab⟩ ⟨rbc⟩ := (rab.trans rbc).rel


instance pre_abelianization_pq.setoid (Q : Type*) [power_quandle Q] : setoid (pre_abelianization_pq Q) :=
{
    r := pre_abelianization_pq_rel Q,
    iseqv := begin
        split, apply pre_abelianization_pq_rel.refl,
        split, apply pre_abelianization_pq_rel.symm,
        apply pre_abelianization_pq_rel.trans,
    end
}

def abelianization_pq (Q : Type u) [power_quandle Q] : Type u := quotient (pre_abelianization_pq.setoid Q)

instance abelianization_pq_has_add : has_add (abelianization_pq Q) := ⟨λ a b, quotient.lift_on₂ a b (λ a b, ⟦add a b⟧) (begin 
  intros a b c d hac hbd,
  cases hac with hac,
  cases hbd with hbc,
  apply quotient.sound,
  fconstructor,
  apply pre_abelianization_pq_rel'.congr_add,
  assumption,
  assumption,
end)⟩

instance abelianization_pq_has_neg : has_neg (abelianization_pq Q) := ⟨λ a, quotient.lift_on a (λ a, ⟦neg a⟧) (begin 
  intros a b hab,
  cases hab with hab,
  apply quotient.sound,
  fconstructor,
  apply pre_abelianization_pq_rel'.congr_neg,
  assumption,
end)⟩

instance abelianization_pq_has_zero : has_zero (abelianization_pq Q) := ⟨⟦zero⟧⟩

instance abelianizaiton_pq_has_rhd : has_rhd (abelianization_pq Q) :=
⟨λ a b, b⟩

instance abelianization_pq_has_pow : has_pow (abelianization_pq Q) ℤ :=
⟨λ a n, quotient.lift_on a (λ a, ⟦pow a n⟧) (begin 
  intros a b hab,
  cases hab with hab,
  apply quotient.sound,
  fconstructor,
  apply pre_abelianization_pq_rel'.congr_pow,
  assumption,
end)⟩

instance abelianization_pq_has_one : has_one (abelianization_pq Q) := ⟨⟦incl 1⟧⟩

lemma abelianization_pq_add_def (x y : pre_abelianization_pq Q) : (⟦x⟧ + ⟦y⟧ : abelianization_pq Q) = ⟦add x y⟧ := rfl

lemma abelianization_pq_neg_def (x : pre_abelianization_pq Q) : (-⟦x⟧ : abelianization_pq Q) = ⟦neg x⟧ := rfl

lemma abelianization_pq_zero_def : (0 : abelianization_pq Q) = ⟦zero⟧ := rfl

lemma abelianization_pq_rhd_def (x y : abelianization_pq Q) : x ▷ y = y := rfl

lemma abelianization_pq_pow_def (x : pre_abelianization_pq Q) (n : ℤ) : (⟦x⟧ ^ n : abelianization_pq Q) = ⟦pow x n⟧ := rfl

lemma abelianization_pq_one_def : (1 : abelianization_pq Q) = ⟦incl 1⟧ := rfl

lemma quot_mk_helper_abelianization (x : pre_abelianization_pq Q) : quot.mk setoid.r x = ⟦x⟧ := rfl

def apq_of : Q → abelianization_pq Q := λ q, ⟦incl q⟧

lemma apq_of_def (q : Q) : apq_of (q) = ⟦incl q⟧ := rfl

lemma apq_of_rhd (a b : Q) : apq_of (a ▷ b) = (apq_of a) ▷ (apq_of b) :=
begin
  simp only [apq_of_def],
  apply quotient.sound,
  fconstructor,
  exact pre_abelianization_pq_rel'.rhd_incl a b,
end

lemma apq_of_pow (a : Q) (n : ℤ) : apq_of (a ^ n) = (apq_of a) ^ n :=
begin
  simp only [apq_of_def],
  apply quotient.sound,
  fconstructor,
  exact pre_abelianization_pq_rel'.pow_incl a n,
end

instance abelianization_pq_is_pq : power_quandle (abelianization_pq Q) := { 
  rhd_dist := begin 
    intros,
    simp only [abelianization_pq_rhd_def],
  end,
  rhd_idem := begin 
    intros,
    simp only [abelianization_pq_rhd_def],
  end,
  pow_one := begin 
    intro a,
    induction a,
    {
      simp only [quot_mk_helper_abelianization],
      simp only [abelianization_pq_pow_def],
      apply quotient.sound,
      fconstructor,
      exact pre_abelianization_pq_rel'.pow_one a,
    },
    {refl,},
  end,
  pow_zero := begin 
    intro a,
    induction a,
    {
      simp only [quot_mk_helper_abelianization],
      simp only [abelianization_pq_pow_def],
      apply quotient.sound,
      fconstructor,
      exact pre_abelianization_pq_rel'.pow_exp_zero a,
    },
    {refl,},
  end,
  pow_comp := begin
    intros a n m,
    induction a,
    {
      simp only [quot_mk_helper_abelianization],
      simp only [abelianization_pq_pow_def],
      apply quotient.sound,
      fconstructor,
      exact pre_abelianization_pq_rel'.pow_comp a n m,
    },
    {refl,},
  end,
  rhd_one := begin 
    intros, 
    simp only [abelianization_pq_rhd_def],
  end,
  one_rhd := begin 
    intros, 
    simp only [abelianization_pq_rhd_def],
  end,
  pow_rhd := begin 
    intros, 
    simp only [abelianization_pq_rhd_def],
  end,
  rhd_pow_add := begin 
    intros, 
    simp only [abelianization_pq_rhd_def],
  end }

instance abelianization_pq_is_apq : abelian_power_quandle (abelianization_pq Q) := { 
  apq_unit_is_morphism := begin 
    split,
    {
      intros a b,
      simp only [abelianization_pq_rhd_def],
    },
    {
      intros a n,
      symmetry,
      apply quotient.sound,
      fconstructor,
      exact pre_abelianization_pq_rel'.pow_zero n,
    }
  end,
  apq_inverse_is_morphism := begin 
    split,
    {
      intros a b,
      simp only [abelianization_pq_rhd_def],
    },
    {
      intros a n,
      simp only,
      induction a,
      {
        rw quot_mk_helper_abelianization,
        apply quotient.sound,
        fconstructor,
        exact pre_abelianization_pq_rel'.pow_neg a n,
      },
      {refl,},
    },
  end,
  apq_addition_is_morphism := begin 
    split,
    {
      intros a b,
      cases a with a1 a2,
      cases b with b1 b2,
      simp only [rhd_def_prod],
      simp only [abelianization_pq_rhd_def],
    },
    {
      intros a n,
      cases a with a1 a2,
      simp only [pow_def_prod],
      induction a1,
      induction a2,
      {
        simp only [quot_mk_helper_abelianization],
        apply quotient.sound,
        fconstructor,
        exact pre_abelianization_pq_rel'.pow_add a1 a2 n,
      },
      {refl,},
      {refl,},
    },
  end,
  apq_addition_assoc := begin 
    intros a b c,
    induction a,
    induction b,
    induction c,
    {
      simp only [quot_mk_helper_abelianization],
      symmetry,
      apply quotient.sound,
      fconstructor,
      exact pre_abelianization_pq_rel'.add_assoc a b c,
    },
    {refl,},
    {refl,},
    {refl,},
  end,
  apq_addition_comm := begin 
    intros a b,
    induction a,
    induction b,
    {
      simp only [quot_mk_helper_abelianization],
      apply quotient.sound,
      fconstructor,
      exact pre_abelianization_pq_rel'.add_comm a b,
    },
    {refl,},
    {refl,},
  end,
  apq_addition_zero_right := begin 
    intros a,
    induction a,
    {
      simp only [quot_mk_helper_abelianization],
      apply quotient.sound,
      fconstructor,
      exact pre_abelianization_pq_rel'.zero_right a,
    },
    {refl,},
  end,
  apq_addition_zero_left := begin 
    intros a,
    induction a,
    {
      simp only [quot_mk_helper_abelianization],
      apply quotient.sound,
      fconstructor,
      refine pre_abelianization_pq_rel'.trans _ _,
      exact a.add zero,
      apply pre_abelianization_pq_rel'.add_comm,
      exact pre_abelianization_pq_rel'.zero_right a,
    },
    {refl,},
  end,
  apq_inverse_addition_right := begin 
    intros a,
    induction a,
    {
      simp only [quot_mk_helper_abelianization],
      apply quotient.sound,
      fconstructor,
      exact pre_abelianization_pq_rel'.neg_add_right a,
    },
    {refl,},
  end,
  apq_inverse_addition_left := begin 
    intros a,
    induction a,
    {
      simp only [quot_mk_helper_abelianization],
      apply quotient.sound,
      fconstructor,
      refine pre_abelianization_pq_rel'.trans _ _,
      exact add (a) (neg a),
      exact pre_abelianization_pq_rel'.add_comm (neg a) a,
      exact pre_abelianization_pq_rel'.neg_add_right a,
    },
    {refl,},
  end }

lemma apq_of_is_pq_morphism : is_pq_morphism (apq_of : Q → abelianization_pq Q) :=
begin
  split,
  exact apq_of_rhd,
  exact apq_of_pow,
end

end abelianization_pq

section abelianization_pq_functor

variables {Q1 : Type u} [power_quandle Q1] 
variables {Q2 : Type v} [power_quandle Q2] 

open pre_abelianization_pq

def abelianization_pq_functor_pre (f : Q1 → Q2) (hf : is_pq_morphism f) : pre_abelianization_pq Q1 → pre_abelianization_pq Q2
| (incl x) := incl (f x)
| (add x y) := add (abelianization_pq_functor_pre x) (abelianization_pq_functor_pre y) 
| (neg x)  := neg (abelianization_pq_functor_pre x)
| zero := zero
| (pow x n) := pow (abelianization_pq_functor_pre x) n


def abelianization_pq_functor (f : Q1 → Q2) (hf : is_pq_morphism f) : abelianization_pq Q1 → abelianization_pq Q2 := quotient.lift (λ x, ⟦abelianization_pq_functor_pre f hf x⟧) (begin 
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
    simp only [abelianization_pq_functor_pre, ←abelianization_pq_add_def],
    congr,
    assumption,
    assumption,
  },
  {
    simp only [abelianization_pq_functor_pre, ←abelianization_pq_neg_def],
    congr,
    assumption,
  },
  {
    simp only [abelianization_pq_functor_pre, ←abelianization_pq_pow_def],
    congr,
    assumption,
  },
  {
    simp only [abelianization_pq_functor_pre, ←abelianization_pq_add_def],
    rw abelian_power_quandle.apq_addition_assoc,
  },
  {
    simp only [abelianization_pq_functor_pre, ←abelianization_pq_add_def],
    rw abelian_power_quandle.apq_addition_comm,
  },
  {
    simp only [abelianization_pq_functor_pre, ←abelianization_pq_add_def, ←abelianization_pq_zero_def],
    rw abelian_power_quandle.apq_addition_zero_right,
  },
  {
    simp only [abelianization_pq_functor_pre, ←abelianization_pq_add_def, ←abelianization_pq_zero_def, ←abelianization_pq_neg_def],
    rw abelian_power_quandle.apq_inverse_addition_right,
  },
  {
    simp only [abelianization_pq_functor_pre, ←abelianization_pq_pow_def],
    rw power_quandle.pow_one,
  },
  {
    simp only [abelianization_pq_functor_pre, ←abelianization_pq_pow_def],
    rw one_preserved_by_morphism f hf,
    rw ←abelianization_pq_one_def,
    rw power_quandle.pow_zero,
  },
  {
    simp only [abelianization_pq_functor_pre, ←abelianization_pq_pow_def],
    rw power_quandle.pow_comp,
  },
  {
    simp only [abelianization_pq_functor_pre, ←abelianization_pq_pow_def, ←abelianization_pq_add_def],
    rw pow_dist_add,
  },
  {
    simp only [abelianization_pq_functor_pre, ←abelianization_pq_pow_def, ←abelianization_pq_neg_def],
    rw apq_neg_pow,
    
  },
  {
    simp only [abelianization_pq_functor_pre, ←abelianization_pq_pow_def, ←abelianization_pq_zero_def],
    rw apq_zero_pow,
  },
  {
    simp only [abelianization_pq_functor_pre, ←apq_of_def],
    rw hf.1,
    rw apq_of_rhd,
    rw abelianization_pq_rhd_def,
  },
  {
    simp only [abelianization_pq_functor_pre, ←abelianization_pq_pow_def, ←apq_of_def],
    rw hf.2,
    rw apq_of_pow,
  },
end)

theorem abelianization_pq_functor_is_apq_morphism (f : Q1 → Q2) (hf : is_pq_morphism f) : is_apq_morphism (abelianization_pq_functor f hf) :=
begin
  split,
  {
    intros a b,
    induction a,
    induction b,
    refl,
    refl,
    refl,
  },
  {
    intros a n,
    induction a,
    refl,
    refl,
  },
end

end abelianization_pq_functor

section abelianization_pq_adjoint


variables {Q : Type u} [power_quandle Q] 
variables {A : Type v} [abelian_power_quandle A]


end abelianization_pq_adjoint
