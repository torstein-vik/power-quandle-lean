
import tactic

-- TODO: Define pq for union, which is coproduct (?). Also universal property.

universes u v w

class has_rhd (α : Type u) := (rhd : α → α → α)
class has_lhd (α : Type u) := (lhd : α → α → α)

reserve infixr `▷` :70
reserve infixr `◁` :70

infixr ▷ := has_rhd.rhd
infixr ◁ := has_lhd.lhd

/-
class rack (R : Type u) extends has_lhd R, has_rhd R := 
(rhd_dist : ∀ a b c : R, a ▷ (b ▷ c) = (a ▷ b) ▷ (a ▷ c))
(lhd_dist : ∀ a b c : R, (c ◁ b) ◁ a = (c ◁ a) ◁ (b ◁ a))
(lhd_rhd : ∀ a b : R, (a ▷ b) ◁ a = b)
(rhd_lhd : ∀ a b : R, a ▷ (b ◁ a) = b)

class quandle (Q : Type u) extends rack Q := 
(rhd_idem : ∀ a : Q, a ▷ a = a)
(lhd_idem : ∀ a : Q, a ◁ a = a)
-/

class power_quandle (Q : Type u) extends has_rhd Q, has_pow Q int, has_one Q :=
(rhd_dist : ∀ a b c : Q, a ▷ (b ▷ c) = (a ▷ b) ▷ (a ▷ c))
(rhd_idem : ∀ a : Q, a ▷ a = a)
(pow_one : ∀ a : Q, pow a 1 = a)
(pow_zero : ∀ a : Q, pow a 0 = 1 )
(pow_comp : ∀ a : Q, ∀ n m : int, (a^n)^m = a^(n * m))
(rhd_one : ∀ a : Q, a ▷ 1 = 1)
(one_rhd : ∀ a : Q, 1 ▷ a = a)
(pow_rhd : ∀ a b : Q, ∀ n : int, (a ▷ b)^n = a ▷ (b^n))
(rhd_pow_add : ∀ a b : Q, ∀ n m : int, (pow a n) ▷ ((pow a m) ▷ b) = (a^(n + m) ▷ b))

section power_quandle

variables {Q : Type u} [power_quandle Q]

instance pq_has_lhd : has_lhd Q := ⟨λ x y, y ^ (-1 : ℤ) ▷ x⟩

lemma lhd_rhd_pow : ∀ a b : Q, a ◁ b = b ^ (-1 : ℤ) ▷ a :=
begin
    intros a b,
    refl,
end

lemma lhd_dist : ∀ a b c : Q, (c ◁ b) ◁ a = (c ◁ a) ◁ (b ◁ a) :=
begin
    intros a b c,
    repeat {rw lhd_rhd_pow},
    rw power_quandle.pow_rhd,
    rw power_quandle.rhd_dist,
end

lemma lhd_rhd : ∀ a b : Q, (a ▷ b) ◁ a = b :=
begin
    intros a b,
    rw lhd_rhd_pow,
    rw ←power_quandle.pow_one a,
    rw power_quandle.pow_comp,
    rw power_quandle.rhd_pow_add,
    simp only [mul_one, mul_neg_eq_neg_mul_symm, add_left_neg],
    rw power_quandle.pow_zero,
    rw power_quandle.one_rhd,
end

lemma rhd_lhd : ∀ a b : Q, a ▷ (b ◁ a) = b :=
begin
    intros a b,
    rw lhd_rhd_pow,
    rw ←power_quandle.pow_one a,
    rw power_quandle.pow_comp,
    rw power_quandle.rhd_pow_add,
    simp only [mul_one, mul_neg_eq_neg_mul_symm, add_right_neg],
    rw power_quandle.pow_zero,
    rw power_quandle.one_rhd,
end

lemma lhd_idem : ∀ a : Q, a ◁ a = a :=
begin
    intros a,
    conv {
        to_rhs,
        rw ←lhd_rhd a a,
    },
    apply congr_arg (λ b, b ◁ a),
    rw power_quandle.rhd_idem,
end 

lemma lhd_pow : ∀ a b : Q, ∀ n : int, (b ◁ a)^n = (b^n) ◁ a :=
begin
    intros a b n,
    rw lhd_rhd_pow,
    rw power_quandle.pow_rhd,
    rw lhd_rhd_pow,
end

lemma rhd_lhd_pow : ∀ a b : Q, a ▷ b = b ◁ (a ^ (-1 : int)) :=
begin
    intros a b,
    rw lhd_rhd_pow,
    rw power_quandle.pow_comp,
    simp,
    rw power_quandle.pow_one,
end

lemma lhd_pow_add : ∀ a b : Q, ∀ n m : int, (b ◁ (a ^ m)) ◁ (a ^ n) = (b ◁ a^(n + m)) :=
begin
    intros a b n m,
    repeat {rw lhd_rhd_pow},
    repeat {rw power_quandle.pow_comp},
    rw power_quandle.rhd_pow_add,
    simp,
    rw int.add_comm,
end

lemma pq_one_pow : ∀ n : int, (1 : Q) ^ n = 1 :=
begin
    intro n,
    rw ←power_quandle.pow_zero (1 : Q),
    rw power_quandle.pow_comp,
    simp only [zero_mul],
end

lemma lhd_one : ∀ a : Q, a ◁ 1 = a :=
begin
    intro a,
    rw lhd_rhd_pow,
    rw pq_one_pow,
    rw power_quandle.one_rhd,
end  

lemma one_lhd : ∀ a : Q, 1 ◁ a = 1 :=
begin
    intro a,
    rw lhd_rhd_pow,
    rw power_quandle.rhd_one,
end  

lemma a_rhd_an : ∀ a : Q, ∀ n : int, a ▷ a ^ n = a ^ n :=
begin
    intros a n,
    rw ←power_quandle.pow_rhd,
    rw power_quandle.rhd_idem,
end

lemma pow_neg_one_rhd_self : ∀ a : Q , a ^ (-1 : ℤ) ▷ a = a :=
begin
    intro a,
    rw ←lhd_rhd_pow,
    exact lhd_idem a,
end

lemma a_inv_rhd_an : ∀ a : Q, ∀ n : int, a ^ (-1 : int) ▷ a ^ n = a ^ n :=
begin
    intros a n,
    rw ←power_quandle.pow_rhd,
    rw pow_neg_one_rhd_self,
end

lemma an_rhd_am_nat : ∀ a : Q, ∀ n : nat, ∀ m : int, a ^ (n : int) ▷ a ^ m = a ^ m := 
begin
    intros a n m,
    induction n with l hl,
    {
        have int_zero : ↑0 = (0 : int),
        {
            refl,
        },
        rw int_zero,
        rw power_quandle.pow_zero,
        rw power_quandle.one_rhd,
    },
    {
        rw nat.succ_eq_add_one,
        rw ←int.of_nat_eq_coe,
        rw int.of_nat_add l 1,
        rw ←power_quandle.rhd_pow_add,
        have int_one : int.of_nat 1 = (1 : int),
        {
            refl,
        },
        rw int_one,
        rw power_quandle.pow_one,
        rw a_rhd_an,
        assumption,
    },
end

lemma an_rhd_am : ∀ a : Q, ∀ n m : int, a ^ n ▷ a ^ m = a ^ m := 
begin
    intros a n m,
    induction n with n1 n2,
    {
        exact (an_rhd_am_nat a n1 m),
    },
    {
        induction n2 with l hl,
        {
            exact a_inv_rhd_an a m,
        },
        {
            rw int.neg_succ_of_nat_coe,
            rw ←int.of_nat_eq_coe,
            rw int.of_nat_add,
            simp,
            rw int.add_comm (-1) (-1 + -↑l),
            rw ←power_quandle.rhd_pow_add,
            rw a_inv_rhd_an a m,
            rw int.neg_succ_of_nat_coe at hl,
            simp at hl,
            assumption,
        },
    },
end

end power_quandle



section power_quandle_morphism

variables {Q1 : Type u} [power_quandle Q1] {Q2 : Type v} [power_quandle Q2] {Q3 : Type w} [power_quandle Q3]

def is_pq_morphism (f : Q1 → Q2) : Prop := 
(∀ a b : Q1, f(a ▷ b) = f(a) ▷ f(b)) ∧ 
(∀ a : Q1, ∀ n : int, f(a ^ n) = f(a) ^ n)

lemma lhd_preserved_by_morphism (f : Q1 → Q2) (hf : is_pq_morphism f) : ∀ a b : Q1, f(a ◁ b) = f(a) ◁ f(b) :=
begin
    intros a b,
    rw lhd_rhd_pow,
    cases hf with hf1 hf2,
    rw hf1,
    rw hf2,
    rw ←lhd_rhd_pow,
end

lemma rhd_preserved_by_morphism (f : Q1 → Q2) (hf : is_pq_morphism f) : ∀ a b : Q1, f(a ▷ b) = f(a) ▷ f(b) :=
begin
    intros a b,
    cases hf with hf1 hf2,
    rw hf1,
end

lemma pow_preserved_by_morphism (f : Q1 → Q2) (hf : is_pq_morphism f) : ∀ a : Q1, ∀ n : ℤ, f(a ^ n) = (f a) ^ n :=
begin
    intros a n,
    cases hf with hf1 hf2,
    rw hf2,
end

lemma one_preserved_by_morphism (f : Q1 → Q2) (hf : is_pq_morphism f) : f 1 = 1 :=
begin
    rw ←power_quandle.pow_zero (1 : Q1),
    cases hf with hf1 hf2,
    rw hf2,
    rw power_quandle.pow_zero,
end

lemma id_is_pq_morphism : is_pq_morphism (id : Q1 → Q1) :=
begin
    split,
    {
        intros a b,
        simp,
    },
    {
        intros a n,
        simp,
    },
end

lemma pq_morphism_comp (f : Q1 → Q2) (g : Q2 → Q3) (hf : is_pq_morphism f) (hg : is_pq_morphism g) : is_pq_morphism (g ∘ f) :=
begin
    cases hf with hf1 hf2,
    cases hg with hg1 hg2,
    split,
    {
        intros a b,
        simp,
        rw hf1,
        rw hg1,
    },
    {
        intros a n,
        simp,
        rw hf2,
        rw hg2,
    },
end

variables {Q4 : Type u} [power_quandle Q4]

-- This is ever-so-slightly pointless but with this we are completely sure that we are dealing with a category.
lemma pq_morphism_assoc (f : Q1 → Q2) (g : Q2 → Q3) (h : Q3 → Q4) (hf : is_pq_morphism f) (hg : is_pq_morphism g) (hh : is_pq_morphism h) : h ∘ (g ∘ f) = (h ∘ g) ∘ f :=
begin
    refl,
end


lemma pq_iso_inv_is_pq_morphism (f : Q1 ≃ Q2) (hf : is_pq_morphism f) : is_pq_morphism (f.symm) :=
begin
  split,
  {
      intros a b,
      rw ←f.apply_symm_apply a,
      rw ←f.apply_symm_apply b,
      rw f.symm_apply_apply,
      rw f.symm_apply_apply,
      rw ←hf.1,
      rw f.symm_apply_apply,
  },
  {
      intros a n,
      rw ←f.apply_symm_apply a,
      rw ←hf.2,
      rw f.symm_apply_apply,
      rw f.symm_apply_apply,
  },
end

end power_quandle_morphism



section power_quandle_product

variables {Q1 : Type u} [power_quandle Q1] {Q2 : Type v} [power_quandle Q2]

def rhd_product (x : Q1 × Q2) (y : Q1 × Q2) : (Q1 × Q2) := (x.1 ▷ y.1, x.2 ▷ y.2) 

instance product_has_rhd : has_rhd (Q1 × Q2) := has_rhd.mk rhd_product

lemma rhd_def_prod (a b : Q1 × Q2) : a ▷ b = (a.1 ▷ b.1, a.2 ▷ b.2) := rfl

/-
lemma right_dist_product : ∀ a b c : Q1 × Q2, a ▷ (b ▷ c) = (a ▷ b) ▷ (a ▷ c) :=
begin
   intros a b c, 
   repeat {rw rhd_def_prod},
   repeat {rw ←rack.rhd_dist},
end


lemma left_dist_product : ∀ a b c : Q1 × Q2, (c ◁ b) ◁ a = (c ◁ a) ◁ (b ◁ a) :=
begin
   intros a b c, 
   repeat {rw lhd_def_prod},
   repeat {rw ←rack.lhd_dist},
end


lemma right_inv_product : ∀ a b : Q1 × Q2, (a ▷ b) ◁ a = b :=
begin
    intros a b,
    rw rhd_def_prod,
    rw lhd_def_prod,
    simp,
    repeat {rw rack.right_inv},
    simp,
end


lemma left_inv_product : ∀ a b : Q1 × Q2, a ▷ (b ◁ a) = b :=
begin
    intros a b,
    rw rhd_def_prod,
    rw lhd_def_prod,
    simp,
    repeat {rw rack.left_inv},
    simp,
end



instance product_rack : rack (Q1 × Q2) := rack.mk
(right_dist_product)
(left_dist_product)
(right_inv_product)
(left_inv_product)



lemma self_idem_right_prod : ∀ a : Q1 × Q2, a ▷ a = a :=
begin
    intro a,
    rw rhd_def_prod,
    repeat {rw quandle.self_idem_right},
    simp,
end


lemma self_idem_left_prod : ∀ a : Q1 × Q2, a ◁ a = a :=
begin
    intro a,
    rw lhd_def_prod,
    repeat {rw quandle.self_idem_left},
    simp,
end



instance product_quandle : quandle (Q1 × Q2) := quandle.mk
(self_idem_right_prod)
(self_idem_left_prod)



def pq_pow_prod (a : Q1 × Q2) (n : int) : (Q1 × Q2) := (a.1 ^ n, a.2 ^ n)

@[priority std.priority.default-1]
instance product_pq_has_pow : has_pow (Q1 × Q2) int := ⟨pq_pow_prod⟩

lemma pow_def_prod (a : Q1 × Q2) (n : int) : a ^ n = (a.1 ^ n, a.2 ^ n) := rfl



lemma pow_1_prod : ∀ a : Q1 × Q2, a ^ (1 : int) = a :=
begin
    intro a,
    rw pow_def_prod,
    repeat {rw power_quandle.pow_1},
    simp,
end


lemma pow_comp_prod : ∀ a : Q1 × Q2, ∀ n m : int, (a^n)^m = a^(n * m) :=
begin
    intros a n m,
    repeat {rw pow_def_prod},
    --simp,
    repeat {rw power_quandle.pow_comp},
end


lemma q_pow0_prod : ∀ a b : Q1 × Q2, a ▷ (b ^ (0 : int)) = (b ^ (0 : int)) :=
begin
    intros a b,
    repeat {rw pow_def_prod},
    rw rhd_def_prod,
    --simp,
    repeat {rw power_quandle.q_pow0},
end


lemma q_pown_right_prod : ∀ a b : Q1 × Q2, ∀ n : int, (a ▷ b)^n = a ▷ (b^n) :=
begin
    intros a b n,
    repeat {rw pow_def_prod},
    repeat {rw rhd_def_prod},
    --simp,
    repeat {rw power_quandle.q_pown_right},
end


lemma q_pown_left_prod : ∀ a b : Q1 × Q2, ∀ n : int, (b ◁ a)^n = (b^n) ◁ a :=
begin
    intros a b n,
    repeat {rw pow_def_prod},
    repeat {rw lhd_def_prod},
    --simp,
    repeat {rw q_pown_left},
end


lemma q_powneg_right_prod : ∀ a b : Q1 × Q2, a ▷ b = b ◁ (a ^ (-1 : int)) :=
begin
    intros a b,
    rw rhd_def_prod,
    rw lhd_def_prod,
    repeat {rw pow_def_prod},
    --simp,
    repeat {rw q_powneg_right},
end


lemma q_powneg_left_prod : ∀ a b : Q1 × Q2, b ◁ a = (a ^ (-1 : int)) ▷ b :=
begin
    intros a b,
    rw rhd_def_prod,
    rw lhd_def_prod,
    repeat {rw pow_def_prod},
    --simp,
    repeat {rw power_quandle.q_powneg_left},
end


lemma q_powadd_prod : ∀ a b : Q1 × Q2, ∀ n m : int, (pow a n) ▷ ((pow a m) ▷ b) = (a^(n + m) ▷ b) :=
begin
    intros a b n m,
    repeat {rw rhd_def_prod},
    repeat {rw pow_def_prod},
    --simp,
    repeat {rw power_quandle.q_powadd},
end



instance power_quandle_prod : power_quandle (Q1 × Q2) := power_quandle.mk
(pow_1_prod)
(pow_comp_prod)
(q_pow0_prod)
(q_pown_right_prod)
--(q_pown_left_prod)
--(q_powneg_right_prod)
(q_powneg_left_prod)
(q_powadd_prod)

-/


def pq_pow_prod (a : Q1 × Q2) (n : int) : (Q1 × Q2) := (a.1 ^ n, a.2 ^ n)

@[priority std.priority.default-1]
instance product_pq_has_pow : has_pow (Q1 × Q2) int := ⟨pq_pow_prod⟩

lemma pow_def_prod (a : Q1 × Q2) (n : int) : a ^ n = (a.1 ^ n, a.2 ^ n) := rfl


instance : power_quandle (Q1 × Q2) := { 
  rhd_dist := begin 
    intros a b c,
    simp only [rhd_def_prod, prod.mk.inj_iff],
    split;
    rw power_quandle.rhd_dist,
  end,
  rhd_idem := begin 
    rintros ⟨a1, a2⟩,
    simp only [rhd_def_prod, prod.mk.inj_iff],
    split;
    rw power_quandle.rhd_idem,
  end,
  pow_one := begin 
    rintros ⟨a1, a2⟩,
    simp only [pow_def_prod, prod.mk.inj_iff],
    split;
    rw power_quandle.pow_one,
  end,
  pow_zero := begin
    rintros ⟨a1, a2⟩,
    simp only [pow_def_prod, prod.mk_eq_one],
    split;
    rw power_quandle.pow_zero,
  end,
  pow_comp := begin 
    rintros ⟨a1, a2⟩ n m,
    simp only [pow_def_prod, prod.mk.inj_iff],
    split;
    rw power_quandle.pow_comp,
  end,
  rhd_one := begin 
    rintros ⟨a1, a2⟩,
    simp only [rhd_def_prod, prod.snd_one, prod.mk_eq_one, prod.fst_one],
    split;
    rw power_quandle.rhd_one,
  end,
  one_rhd :=  begin 
    rintros ⟨a1, a2⟩,
    simp only [rhd_def_prod, prod.mk.inj_iff, prod.snd_one, prod.fst_one],
    split;
    rw power_quandle.one_rhd,
  end,
  pow_rhd := begin 
    rintros ⟨a1, a2⟩ ⟨b1, b2⟩ n,
    simp only [rhd_def_prod, pow_def_prod, prod.mk.inj_iff],
    split;
    rw power_quandle.pow_rhd,
  end,
  rhd_pow_add := begin
    rintros ⟨a1, a2⟩ ⟨b1, b2⟩ n m,
    simp only [rhd_def_prod, pow_def_prod, prod.mk.inj_iff], 
    split;
    rw power_quandle.rhd_pow_add,
  end,
  ..product_has_rhd,
  ..product_pq_has_pow,
  ..prod.has_one }


-- Universal property of product

def pi1 (a : Q1 × Q2) : Q1 := a.1
def pi2 (a : Q1 × Q2) : Q2 := a.2

lemma pi1_def (a : Q1 × Q2) : pi1 a = a.1 := rfl
lemma pi2_def (a : Q1 × Q2) : pi2 a = a.2 := rfl

lemma pi1_morph : is_pq_morphism (pi1 : (Q1 × Q2) → Q1) := 
begin
    split,
    {
        intros a b,
        repeat {rw pi1_def},
        rw rhd_def_prod,
    },
    {
        intros a n,
        repeat {rw pi1_def},
        rw pow_def_prod,
    },
end


lemma pi2_morph : is_pq_morphism (pi2 : (Q1 × Q2) → Q2) :=
begin
    split,
    {
        intros a b,
        repeat {rw pi2_def},
        rw rhd_def_prod,
    },
    {
        intros a n,
        repeat {rw pi2_def},
        rw pow_def_prod,
    },
end

variables {Y : Type u} [power_quandle Y]

theorem prod_universal_prop (f₁ : Y → Q1) (f₂ : Y → Q2) (hf₁ : is_pq_morphism f₁) (hf₂ : is_pq_morphism f₂) : 
        ∃ f : (Y → Q1 × Q2), (is_pq_morphism f) ∧ (pi1 ∘ f = f₁) ∧ (pi2 ∘ f = f₂) :=
begin
    cases hf₁ with hf₁a hf₁b,
    cases hf₂ with hf₂a hf₂b,
    let f := λ a : Y, (f₁ a, f₂ a),
    have f_def : ∀ a, f(a) = (f₁ a, f₂ a),
    {
        intro a,
        refl,
    },
    existsi f,
    split,
    {
        split,
        {
            intros a b,
            repeat {rw f_def},
            rw rhd_def_prod,
            --simp,
            repeat {rw hf₁a},
            repeat {rw hf₂a},
        },
        {
            intros a n,
            repeat {rw f_def},
            rw pow_def_prod,
            --simp,
            repeat {rw hf₁b},
            repeat {rw hf₂b},
        },
    },
    split,
    {refl,},
    {refl,},
end

end power_quandle_product

section terminal_power_quandle

def rhd_terminal (x : unit) (y : unit) : unit := unit.star 

instance terminal_has_rhd : has_rhd unit := has_rhd.mk rhd_terminal

lemma rhd_def_term (a b : unit) : a ▷ b = unit.star := rfl

lemma unit_eq : ∀ a b : unit, a = b :=
begin
    intros a b,
    induction a,
    induction b,
    refl,
end

/-
instance terminal_rack : rack unit := rack.mk
(begin intros, apply unit_eq end)
(begin intros, apply unit_eq end)
(begin intros, apply unit_eq end)
(begin intros, apply unit_eq end)

instance terminal_quandle : quandle unit := quandle.mk
(begin intros, apply unit_eq end)
(begin intros, apply unit_eq end)
-/

def terminal_pq_pow (a : unit) (n : int) : unit := unit.star

instance terminal_pow : has_pow unit int := has_pow.mk (terminal_pq_pow)

lemma pow_def_term (a : unit) (n : int) : a ^ n = unit.star := rfl

instance terminal_has_one : has_one unit := ⟨unit.star⟩

lemma terminal_one_def (a : unit) : (1 : unit) = a := begin
    apply unit_eq,
end

instance terminal_power_quandle : power_quandle unit := { 
  rhd_dist := begin intros, apply unit_eq, end ,
  rhd_idem := begin intros, apply unit_eq, end,
  pow_one := begin intros, apply unit_eq, end,
  pow_zero := begin intros, apply unit_eq, end,
  pow_comp := begin intros, apply unit_eq, end,
  rhd_one := begin intros, apply unit_eq, end,
  one_rhd := begin intros, apply unit_eq, end,
  pow_rhd := begin intros, apply unit_eq, end,
  rhd_pow_add := begin intros, apply unit_eq, end,
  ..terminal_pow,
  ..terminal_has_rhd,
  ..terminal_has_one, }


-- Universal propery as terminal object

variables {Q : Type u} [power_quandle Q]

def terminal_morphism (a : Q) : unit := unit.star

lemma terminal_morphism_is_morphism : is_pq_morphism (terminal_morphism : (Q → unit)) :=
begin
    split,
    {
        intros a b,
        refl,
    },
    {
        intros a n,
        refl,
    },
end

theorem terminal_pq_is_terminal (f : Q → unit) (hf : is_pq_morphism f) : f = terminal_morphism :=
begin
    apply funext,
    intro a,
    apply unit_eq,
end

end terminal_power_quandle


section initial_power_quandle


-- Proof that it is intial in the category of power quandles


variables {Q : Type u} [power_quandle Q]

def initial_morphism (a : unit) : Q := 1

lemma initial_morphism_def (a : unit) : initial_morphism a = (1 : Q) := rfl

lemma initial_morphism_is_morphism : is_pq_morphism (initial_morphism : (unit → Q)) :=
begin
    split,
    {
        intros a b,
        simp only [initial_morphism_def, power_quandle.rhd_one],
    },
    {
        intros a n,
        simp only [initial_morphism_def, pq_one_pow],
    },
end

theorem initial_pq_is_initial (f : unit → Q) (hf : is_pq_morphism f) : f = initial_morphism :=
begin
    apply funext,
    intro a,
    induction a,
    rw initial_morphism_def,
    rw ←terminal_one_def punit.star,
    rw one_preserved_by_morphism f hf,
end

end initial_power_quandle





