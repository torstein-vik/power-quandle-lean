
import tactic

-- TODO: Define pq for union, which is coproduct (?). Also universal property.

universes u v w

class has_triangle_right (α : Type u) := (triangle_right : α → α → α)
class has_triangle_left (α : Type u) := (triangle_left : α → α → α)

reserve infixr `▷` :70
reserve infixr `◁` :70

infixr ▷ := has_triangle_right.triangle_right
infixr ◁ := has_triangle_left.triangle_left

class rack (R : Type u) extends has_triangle_left R, has_triangle_right R := 
(right_dist : ∀ a b c : R, a ▷ (b ▷ c) = (a ▷ b) ▷ (a ▷ c))
(left_dist : ∀ a b c : R, (c ◁ b) ◁ a = (c ◁ a) ◁ (b ◁ a))
(right_inv : ∀ a b : R, (a ▷ b) ◁ a = b)
(left_inv : ∀ a b : R, a ▷ (b ◁ a) = b)

class quandle (Q : Type u) extends rack Q := 
(self_idem_right : ∀ a : Q, a ▷ a = a)
(self_idem_left : ∀ a : Q, a ◁ a = a)

class power_quandle (Q : Type u) extends quandle Q, has_pow Q int :=
(pow_1 : ∀ a : Q, pow a 1 = a)
(pow_comp : ∀ a : Q, ∀ n m : int, (a^n)^m = a^(n * m))
(q_pow0 : ∀ a b : Q, a ▷ (pow b 0) = pow b 0)
(q_pown_right : ∀ a b : Q, ∀ n : int, (a ▷ b)^n = a ▷ (b^n))
--(q_pown_left : ∀ a b : Q, ∀ n : int, (b ◁ a)^n = (b^n) ◁ a)
--(q_powneg_right : ∀ a b : Q, a ▷ b = b ◁ (pow a (-1)))
(q_powneg_left : ∀ a b : Q, b ◁ a = (pow a (-1)) ▷ b)
(q_powadd : ∀ a b : Q, ∀ n m : int, (pow a n) ▷ ((pow a m) ▷ b) = (a^(n + m) ▷ b))

section power_quandle

variables {Q : Type u} [power_quandle Q]

theorem q_pown_left : ∀ a b : Q, ∀ n : int, (b ◁ a)^n = (b^n) ◁ a :=
begin
    intros a b n,
    rw power_quandle.q_powneg_left,
    rw power_quandle.q_pown_right,
    rw ←power_quandle.q_powneg_left,
end

theorem q_powneg_right : ∀ a b : Q, a ▷ b = b ◁ (a ^ (-1 : int)) :=
begin
    intros a b,
    rw power_quandle.q_powneg_left,
    rw power_quandle.pow_comp,
    simp,
    rw power_quandle.pow_1,
end

theorem q_powadd_left : ∀ a b : Q, ∀ n m : int, (b ◁ (a ^ m)) ◁ (a ^ n) = (b ◁ a^(n + m)) :=
begin
    intros a b n m,
    repeat {rw power_quandle.q_powneg_left},
    repeat {rw power_quandle.pow_comp},
    rw power_quandle.q_powadd,
    simp,
    rw int.add_comm,
end

lemma pow_0_rhd : ∀ a b : Q, a ^ (0 : int) ▷ b = b :=
begin
    intros a b,
    rw ←rack.left_inv a b,
    rw ←power_quandle.pow_1 a,
    rw power_quandle.pow_comp,
    rw power_quandle.q_powadd,
    simp,
end

lemma lhd_pow_0 : ∀ a b : Q, b ◁ a ^ (0 : int) = b :=
begin
    intros a b,
    rw power_quandle.q_powneg_left,
    rw power_quandle.pow_comp,
    simp,
    rw pow_0_rhd,
end

lemma a_rhd_an : ∀ a : Q, ∀ n : int, a ▷ a ^ n = a ^ n :=
begin
    intros a n,
    rw ←power_quandle.q_pown_right,
    rw quandle.self_idem_right,
end

lemma pow_neg_one_rhd_self : ∀ a : Q , a ^ (-1 : ℤ) ▷ a = a :=
begin
    intro a,
    rw ←power_quandle.q_powneg_left,
    exact quandle.self_idem_left a,
end

lemma a_inv_rhd_an : ∀ a : Q, ∀ n : int, a ^ (-1 : int) ▷ a ^ n = a ^ n :=
begin
    intros a n,
    rw q_powneg_right,
    rw power_quandle.pow_comp,
    simp,
    rw power_quandle.pow_1,
    rw ←q_pown_left,
    rw quandle.self_idem_left,
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
        rw pow_0_rhd,
    },
    {
        rw nat.succ_eq_add_one,
        rw ←int.of_nat_eq_coe,
        rw int.of_nat_add l 1,
        rw ←power_quandle.q_powadd,
        have int_one : int.of_nat 1 = (1 : int),
        {
            refl,
        },
        rw int_one,
        rw power_quandle.pow_1,
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
            rw ←power_quandle.q_powadd,
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
    rw power_quandle.q_powneg_left,
    cases hf with hf1 hf2,
    rw hf1,
    rw hf2,
    rw ←power_quandle.q_powneg_left,
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

def triangle_right_product (x : Q1 × Q2) (y : Q1 × Q2) : (Q1 × Q2) := (x.1 ▷ y.1, x.2 ▷ y.2) 
def triangle_left_product (x : Q1 × Q2) (y : Q1 × Q2) : (Q1 × Q2) := (x.1 ◁ y.1, x.2 ◁ y.2) 

instance product_has_triangle_right : has_triangle_right (Q1 × Q2) := has_triangle_right.mk triangle_right_product
instance product_has_triangle_left : has_triangle_left (Q1 × Q2) := has_triangle_left.mk triangle_left_product

lemma rhd_def_prod (a b : Q1 × Q2) : a ▷ b = (a.1 ▷ b.1, a.2 ▷ b.2) := rfl
lemma lhd_def_prod (a b : Q1 × Q2) : a ◁ b = (a.1 ◁ b.1, a.2 ◁ b.2) := rfl

lemma right_dist_product : ∀ a b c : Q1 × Q2, a ▷ (b ▷ c) = (a ▷ b) ▷ (a ▷ c) :=
begin
   intros a b c, 
   repeat {rw rhd_def_prod},
   repeat {rw ←rack.right_dist},
end


lemma left_dist_product : ∀ a b c : Q1 × Q2, (c ◁ b) ◁ a = (c ◁ a) ◁ (b ◁ a) :=
begin
   intros a b c, 
   repeat {rw lhd_def_prod},
   repeat {rw ←rack.left_dist},
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

def triangle_right_terminal (x : unit) (y : unit) : unit := unit.star 
def triangle_left_terminal (x : unit) (y : unit) : unit := unit.star

instance terminal_has_triangle_right : has_triangle_right unit := has_triangle_right.mk triangle_right_terminal
instance terminal_has_triangle_left : has_triangle_left unit := has_triangle_left.mk triangle_left_terminal

lemma rhd_def_term (a b : unit) : a ▷ b = unit.star := rfl
lemma lhd_def_term (a b : unit) : a ◁ b = unit.star := rfl

lemma unit_eq : ∀ a b : unit, a = b :=
begin
    intros a b,
    induction a,
    induction b,
    refl,
end

instance terminal_rack : rack unit := rack.mk
(begin intros, apply unit_eq end)
(begin intros, apply unit_eq end)
(begin intros, apply unit_eq end)
(begin intros, apply unit_eq end)

instance terminal_quandle : quandle unit := quandle.mk
(begin intros, apply unit_eq end)
(begin intros, apply unit_eq end)

def terminal_pq_pow (a : unit) (n : int) : unit := unit.star

instance terminal_pow : has_pow unit int := has_pow.mk (terminal_pq_pow)

lemma pow_def_term (a : unit) (n : int) : a ^ n = unit.star := rfl

instance terminal_power_quandle : power_quandle unit := power_quandle.mk
(begin intros, apply unit_eq end)
(begin intros, apply unit_eq end)
(begin intros, apply unit_eq end)
(begin intros, apply unit_eq end)
--(begin intros, repeat {rw pow_def_term}, repeat {rw lhd_def_term} end)
--(begin intros, repeat {rw lhd_def_term}, rw all_are_star end)
(begin intros, apply unit_eq end)
(begin intros, apply unit_eq end)


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

section power_quandle_union

variables {Q1 : Type u} [power_quandle Q1] {Q2 : Type v} [power_quandle Q2]

def triangle_right_union : (Q1 ⊕ Q2) → (Q1 ⊕ Q2) → (Q1 ⊕ Q2)
| (sum.inl x) (sum.inl y) := sum.inl (x ▷ y)
| (sum.inl x) (sum.inr y) := sum.inr y
| (sum.inr x) (sum.inl y) := sum.inl y
| (sum.inr x) (sum.inr y) := sum.inr (x ▷ y)

def triangle_left_union : (Q1 ⊕ Q2) → (Q1 ⊕ Q2) → (Q1 ⊕ Q2)
| (sum.inl x) (sum.inl y) := sum.inl (x ◁ y)
| (sum.inl x) (sum.inr y) := sum.inl x
| (sum.inr x) (sum.inl y) := sum.inr x
| (sum.inr x) (sum.inr y) := sum.inr (x ◁ y)

instance union_has_triangle_right : has_triangle_right (Q1 ⊕ Q2) := has_triangle_right.mk triangle_right_union
instance union_has_triangle_left : has_triangle_left (Q1 ⊕ Q2) := has_triangle_left.mk triangle_left_union

@[simp] lemma rhd_def_union_ll (a b : Q1) : (sum.inl a : Q1 ⊕ Q2) ▷ (sum.inl b) = sum.inl (a ▷ b) := rfl
@[simp] lemma rhd_def_union_rr (a b : Q2) : (sum.inr a : Q1 ⊕ Q2) ▷ (sum.inr b) = sum.inr (a ▷ b) := rfl
@[simp] lemma rhd_def_union_lr (a : Q1) (b : Q2) : (sum.inl a) ▷ (sum.inr b) = sum.inr (b) := rfl
@[simp] lemma rhd_def_union_rl (a : Q2) (b : Q1) : (sum.inr a) ▷ (sum.inl b) = sum.inl (b) := rfl

@[simp] lemma lhd_def_union_ll (a b : Q1) : (sum.inl a : Q1 ⊕ Q2) ◁ (sum.inl b) = sum.inl (a ◁ b) := rfl
@[simp] lemma lhd_def_union_rr (a b : Q2) : (sum.inr a : Q1 ⊕ Q2) ◁ (sum.inr b) = sum.inr (a ◁ b) := rfl
@[simp] lemma lhd_def_union_lr (a : Q1) (b : Q2) : (sum.inl a) ◁ (sum.inr b) = sum.inl (a) := rfl
@[simp] lemma lhd_def_union_rl (a : Q2) (b : Q1) : (sum.inr a) ◁ (sum.inl b) = sum.inr (a) := rfl

def pq_pow_union : (Q1 ⊕ Q2) → int → (Q1 ⊕ Q2)
| (sum.inl a) n := sum.inl (a ^ n)
| (sum.inr a) n := sum.inr (a ^ n)

instance union_pq_has_pow : has_pow (Q1 ⊕ Q2) int := ⟨pq_pow_union⟩

@[simp] lemma pow_def_union_l (a : Q1) (n : int) : (sum.inl a : Q1 ⊕ Q2) ^ n = sum.inl (a ^ n) := rfl
@[simp] lemma pow_def_union_r (a : Q2) (n : int) : (sum.inr a : Q1 ⊕ Q2) ^ n = sum.inr (a ^ n) := rfl


lemma pow_1_union : ∀ a : Q1 ⊕ Q2, a ^ (1 : int) = a :=
begin
    intro a,
    induction a with a1 a2,
    {
        simp,
        rw power_quandle.pow_1,
    },
    {
        simp,
        rw power_quandle.pow_1,
    },
end


lemma pow_comp_union : ∀ a : Q1 ⊕ Q2, ∀ n m : int, (a^n)^m = a^(n * m) :=
begin
    intros a n m,
    induction a with a1 a2,
    {
        simp,
        rw power_quandle.pow_comp,
    },
    {
        simp,
        rw power_quandle.pow_comp,
    },
end


lemma q_pow0_union : ∀ a b : Q1 ⊕ Q2, a ▷ (b ^ (0 : int)) = b ^ (0 : int) :=
begin
    intros a b,
    induction a with a1 a2,
    {
        induction b with b1 b2,
        {
            simp,
            rw power_quandle.q_pow0,
        },
        {
            simp,
        },
    },
    {
        induction b with b1 b2,
        {
            simp,
        },
        {
            simp,
            rw power_quandle.q_pow0,
        },
    },
end


lemma q_pown_right_union : ∀ a b : Q1 ⊕ Q2, ∀ n : int, (a ▷ b)^n = a ▷ (b^n) :=
begin
    intros a b n,
    induction a with a1 a2,
    {
        induction b with b1 b2,
        {
            simp,
            rw power_quandle.q_pown_right,
        },
        {
            simp,
        },
    },
    {
        induction b with b1 b2,
        {
            simp,
        },
        {
            simp,
            rw power_quandle.q_pown_right,
        },
    },
end

lemma q_powneg_left_union : ∀ a b : Q1 ⊕ Q2, b ◁ a = (a ^ (-1 : int)) ▷ b :=
begin
    intros a b,
    induction a with a1 a2,
    {
        induction b with b1 b2,
        {
            simp,
            rw power_quandle.q_powneg_left,
        },
        {
            simp,
        },
    },
    {
        induction b with b1 b2,
        {
            simp,
        },
        {
            simp,
            rw power_quandle.q_powneg_left,
        },
    },
end


lemma q_powadd_union : ∀ a b : Q1 ⊕ Q2, ∀ n m : int, (pow a n) ▷ ((pow a m) ▷ b) = (a^(n + m) ▷ b) :=
begin
    intros a b n m,
    induction a with a1 a2,
    {
        induction b with b1 b2,
        {
            simp,
            rw power_quandle.q_powadd,
        },
        {
            simp,
        },
    },
    {
        induction b with b1 b2,
        {
            simp,
        },
        {
            simp,
            rw power_quandle.q_powadd,
        },
    },
end


lemma right_dist_union : ∀ a b c : Q1 ⊕ Q2, a ▷ (b ▷ c) = (a ▷ b) ▷ (a ▷ c) :=
begin
    intros a b c,
    induction a with a1 a2,
    {
        induction b with b1 b2,
        {
            induction c with c1 c2,
            {
                simp,
                rw rack.right_dist,
            },
            {
                simp,
            },
        },
        {
            induction c with c1 c2,
            {
                simp,
            },
            {
                simp,
            },
        },
    },
    {
        induction b with b1 b2,
        {
            induction c with c1 c2,
            {
                simp,
            },
            {
                simp,
            },
        },
        {
            induction c with c1 c2,
            {
                simp,
            },
            {
                simp,
                rw rack.right_dist,
            },
        },
    },
end


lemma left_dist_union : ∀ a b c : Q1 ⊕ Q2, (c ◁ b) ◁ a = (c ◁ a) ◁ (b ◁ a) :=
begin
    intros a b c,
    repeat {rw q_powneg_left_union},
    rw q_pown_right_union,
    apply right_dist_union,
end


lemma right_inv_union : ∀ a b : Q1 ⊕ Q2, (a ▷ b) ◁ a = b :=
begin
    intros a b,
    induction a with a1 a2,
    {
        induction b with b1 b2,
        {
            simp,
            rw rack.right_inv,
        },
        {
            simp,
        },
    },
    {
        induction b with b1 b2,
        {
            simp,
        },
        {
            simp,
            rw rack.right_inv,
        },
    },
end


lemma left_inv_union : ∀ a b : Q1 ⊕ Q2, a ▷ (b ◁ a) = b :=
begin
    intros a b,
    rw q_powneg_left_union,
    have right_inv_aux := right_inv_union (a ^ (-1 : int)) b,
    rw q_powneg_left_union at right_inv_aux,
    rw pow_comp_union at right_inv_aux,
    simp at right_inv_aux,
    rw pow_1_union at right_inv_aux,
    exact right_inv_aux,
end


instance union_rack : rack (Q1 ⊕ Q2) := rack.mk
(right_dist_union)
(left_dist_union)
(right_inv_union)
(left_inv_union)


lemma self_idem_right_union : ∀ a : Q1 ⊕ Q2, a ▷ a = a :=
begin
    intro a,
    induction a with a1 a2,
    {
        simp,
        rw quandle.self_idem_right,
    },
    {
        simp,
        rw quandle.self_idem_right,
    },
end


lemma self_idem_left_union : ∀ a : Q1 ⊕ Q2, a ◁ a = a :=
begin
    intro a,
    induction a with a1 a2,
    {
        simp,
        rw quandle.self_idem_left,
    },
    {
        simp,
        rw quandle.self_idem_left,
    },
end


instance union_quandle : quandle (Q1 ⊕ Q2) := quandle.mk
(self_idem_right_union)
(self_idem_left_union)


instance union_power_quandle : power_quandle (Q1 ⊕ Q2) := power_quandle.mk
(pow_1_union)
(pow_comp_union)
(q_pow0_union)
(q_pown_right_union)
(q_powneg_left_union)
(q_powadd_union)




end power_quandle_union

section initial_power_quandle


def triangle_right_initial : empty → empty → empty := λ a, id
def triangle_left_initial : empty → empty → empty := λ a _, a

instance initial_has_triangle_right : has_triangle_right empty := has_triangle_right.mk triangle_right_initial
instance initial_has_triangle_left : has_triangle_left empty := has_triangle_left.mk triangle_left_initial

lemma rhd_def_init (a : empty) (b : empty) : a ▷ b = b := rfl
lemma lhd_def_init (a : empty) (b : empty) : b ◁ a = b := rfl

instance initial_rack : rack empty := rack.mk
(begin intros, trivial, end)
(begin intros, trivial, end)
(begin intros, trivial, end)
(begin intros, trivial, end)

instance initial_quandle : quandle empty := quandle.mk
(begin intros, trivial, end)
(begin intros, trivial, end)

def initial_pq_pow (a : empty) (n : int) : empty := a

instance initial_pow : has_pow empty int := has_pow.mk (initial_pq_pow)

instance initial_power_quandle : power_quandle empty := power_quandle.mk
(begin intros, trivial, end)
(begin intros, trivial, end)
(begin intros, trivial, end)
(begin intros, trivial, end)
(begin intros, trivial, end)
(begin intros, trivial, end)

-- Proof that it is intial in the category of power quandles


variables {Q : Type u} [power_quandle Q]

def initial_morphism (a : empty) : Q := begin
    induction a,
end

lemma initial_morphism_is_morphism : is_pq_morphism (initial_morphism : (empty → Q)) :=
begin
    split,
    {
        intros a b,
        induction a,
    },
    {
        intros a n,
        induction a,
    },
end

theorem initial_pq_is_initial (f : empty → Q) (hf : is_pq_morphism f) : f = initial_morphism :=
begin
    apply funext,
    intro a,
    induction a,
end

end initial_power_quandle



