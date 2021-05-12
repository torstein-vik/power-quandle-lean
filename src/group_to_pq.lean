
-- TODO: Define functor, ie. group morphism to pq morphism and comp

import power_quandle

import algebra.group
import group_theory.quotient_group
import group_theory.order_of_element

universes u v

section group_to_pq

variables {Q : Type u} [group Q]

def triangle_right_group (x : Q) (y : Q) : Q := x * y * x⁻¹ 
def triangle_left_group (y : Q) (x : Q) : Q := x⁻¹ * y * x

instance group_to_pq_has_triangle_right : has_triangle_right Q := has_triangle_right.mk triangle_right_group

instance group_to_pq_has_triangle_left : has_triangle_left Q := has_triangle_left.mk triangle_left_group

lemma rhd_def : ∀ a b : Q, a ▷ b = a * b * a⁻¹  := begin
    intros a b,
    refl,
end

lemma right_dist_group : ∀ a b c : Q, a ▷ (b ▷ c) = (a ▷ b) ▷ (a ▷ c) := begin
    intros a b c,
    repeat {rw rhd_def},
    simp,
    repeat {rw mul_assoc},
    repeat {rw ← mul_assoc}, 
end

lemma q_inv_left_to_right : ∀ a b : Q, b ◁ a = a⁻¹ ▷ b := begin 
    intros a b,
    rw rhd_def,
    simp,
    refl,
end

lemma inv_q_right : ∀ a b : Q, (a ▷ b)⁻¹ = a ▷ b⁻¹ := begin
    intros a b,
    rw rhd_def,
    rw rhd_def,
    simp,
end

lemma left_dist_group : ∀ a b c : Q, (c ◁ b) ◁ a = (c ◁ a) ◁ (b ◁ a) := begin
    intros a b c,
    repeat {rw q_inv_left_to_right},
    have r_ass := right_dist_group a⁻¹ b⁻¹ c,
    rw inv_q_right,
    exact r_ass,
end

lemma right_inv_group : ∀ a b : Q, (a ▷ b) ◁ a = b := begin 
    intros a b,
    rw q_inv_left_to_right,
    repeat {rw rhd_def},
    repeat {rw ←mul_assoc},
    simp,
end

lemma left_inv_group : ∀ a b : Q, a ▷ (b ◁ a) = b := begin
    intros a b,
    rw q_inv_left_to_right,
    repeat {rw rhd_def},
    repeat {rw ←mul_assoc},
    simp,
end

instance group_to_pq_rack : rack Q := rack.mk
(right_dist_group)
(left_dist_group)
(right_inv_group)
(left_inv_group)

lemma self_idem_right_group : ∀ a : Q, a ▷ a = a := begin
    intro a,
    rw rhd_def,
    rw mul_assoc,
    simp,
end

lemma self_idem_left_group : ∀ a : Q, a ◁ a = a := begin
    intro a,
    rw q_inv_left_to_right,
    rw rhd_def,
    simp,
end

instance group_to_pq_quandle : quandle Q := ⟨self_idem_right_group, self_idem_left_group⟩

/-
def pq_pow_nat : Q -> nat -> Q
| q 0 := 1
| q (nat.succ n) := q * pq_pow_nat q n

instance group_to_pq_has_pow_nat : has_pow Q nat := ⟨pq_pow_nat⟩

def pq_pow : Q -> int -> Q
| q (int.of_nat n) := pq_pow_nat q n
| q (int.neg_succ_of_nat n) := (pq_pow_nat q (nat.succ n))⁻¹ 

instance group_to_pq_has_pow : has_pow Q int := ⟨pq_pow⟩

lemma pq_pow_0 : ∀ a : Q, pow a 0 = 1 := begin
    intro a,
    refl,
end

lemma pow_neg : ∀ a : Q, ∀ n : nat, pow a (int.neg_of_nat n) = (a^n)⁻¹ := 
begin 
    intros a n,
    induction n with m hm,
    {
        rw int.neg_of_nat,
        rw pq_pow_0,
        simp,
        refl,
    },
    {
        refl,
    }
end

lemma pow_neg_succ_of_nat : ∀ a : Q, ∀ n : nat, a ^ (int.neg_succ_of_nat n) = (a^(nat.succ n))⁻¹ := 
begin 
    intros a n,
    refl,
end

lemma pow_1_group : ∀ a : Q, pow a (1 : int) = a :=
begin 
    intro a,
    have hp : pow a (1 : int) = a * pow a (0 : int),
    refl,
    rw hp,
    have hp2 : pow a (0 : int) = 1,
    refl,
    rw hp2,
    simp,
end

lemma pow_1_nat_group : ∀ a : Q, pow a (1 : nat) = a :=
begin 
    intro a,
    have hp : pow a (1 : nat) = a * pow a (0 : nat),
    refl,
    rw hp,
    have hp2 : pow a (0 : nat) = 1,
    refl,
    rw hp2,
    simp,
end

lemma pow_0 : ∀ a : Q, a ^ 0 = 1 :=
begin
    intro a,
    refl,
end

lemma pow_0_int : ∀ a : Q, a ^ (0 : int) = 1 :=
begin
    intro a,
    refl,
end

lemma pow_succ_group : ∀ a : Q, ∀ n : nat, a ^ (nat.succ n) = a * a ^ n :=
begin
    intros a b,
    refl,
end

lemma pow_int_to_nat : ∀ a : Q, ∀ n : nat, a ^ (int.of_nat n) = a ^ n :=
begin
    intros a n,
    refl,
end

lemma pow_neg_succ_of_nat_succ : ∀ a : Q, ∀ n : nat, a ^ (int.neg_succ_of_nat (nat.succ n)) = a ^ (int.neg_succ_of_nat n) * a⁻¹ := 
begin 
    intros a n,
    rw pow_neg_succ_of_nat,
    rw pow_succ_group,
    simp,
    refl,
end

lemma pow_mult_nat : ∀ a : Q, ∀ n m : nat, a^n * a^m = a^(n + m) :=
begin
    intros a n m,
    induction n with l hl,
    {
        rw pow_0,
        simp,
    },
    {
        rw nat.succ_add,
        have pow_def : ∀ k, a ^ (nat.succ k) = a * a ^ k,
        {
            intro k,
            refl,
        },
        rw pow_def l,
        rw pow_def (l + m),
        rw mul_assoc,
        rw hl,
    }
end

lemma pow_mult_nat_int : ∀ a : Q, ∀ n : nat, ∀ m : int, a^n * a^m = a^((n : int) + m) :=
begin
    intros a n m,
    induction m with l1 l2,
    {
        have pow_def : ∀ b : Q, ∀ k : nat, b ^ (int.of_nat k) = b ^ k,
        {
            intros b k,
            refl,
        },
        rw pow_def,
        have sum_rw : (↑n + int.of_nat l1) = int.of_nat (n + l1),
        {
            refl,
        },
        rw sum_rw,
        rw pow_def,
        rw pow_mult_nat,
    },
    {
        
        have an_rw : ∀ d : int, ∀ h : d = (↑n + int.neg_succ_of_nat l2), a ^ n = a ^ (d) * a ^ (nat.succ l2),
        {
            intros d hd,
            induction d with d1 d2,
            {
                have pow_def : ∀ b : Q, ∀ k : nat, b ^ (int.of_nat k) = b ^ k,
                {
                    intros b k,
                    refl,
                },
                rw pow_def,
                rw pow_mult_nat,
                have d1_eq : n = d1 + nat.succ l2,
                {
                    rw ←int.of_nat_eq_of_nat_iff,
                    rw int.of_nat_add,
                    rw hd,
                    have sum_eq_zero : -[1+ l2] + int.of_nat (nat.succ l2) = 0,
                    {
                        rw ←int.neg_of_nat_of_succ,
                        ring,
                    },
                    rw add_assoc,
                    rw sum_eq_zero,
                    refl,
                },
                rw d1_eq,
            },
            {
                have pow_def : ∀ b : Q, b ^ (int.neg_succ_of_nat d2) = (b ^ (nat.succ d2))⁻¹,
                {
                    intro b, 
                    refl,
                },
                rw pow_def,
                have other_side : a ^ nat.succ d2 * a ^ n = a ^ nat.succ l2,
                {
                    rw pow_mult_nat,
                    have l2_eq : nat.succ d2 + n = nat.succ l2,
                    {
                        rw ←int.of_nat_eq_of_nat_iff,
                        rw int.of_nat_add,
                        have n_eq : int.of_nat n = -[1+ d2] + 1 + l2,
                        {
                            rw hd,
                            have sum_eq_zero : -[1+ l2] + (1 + ↑l2) = 0,
                            {
                                rw int.neg_succ_of_nat_coe,
                                rw ←int.of_nat_eq_coe,
                                rw int.of_nat_add,
                                rw int.of_nat_eq_coe,
                                ring,
                            },
                            rw add_assoc,
                            rw add_assoc,
                            rw sum_eq_zero,
                            simp,
                        },
                        rw n_eq,
                        repeat {rw ←add_assoc},
                        have sum_eq_zero : int.of_nat (nat.succ d2) + -[1+ d2] = 0,
                        {
                            rw ←int.neg_of_nat_of_succ,
                            ring,
                        },
                        rw sum_eq_zero,
                        simp,
                        rw add_comm,
                    },
                    rw l2_eq,
                },
                rw ←other_side,
                simp,
            },
        },
        rw an_rw (↑n + -[1+ l2]),
        {
            rw ←int.neg_of_nat_of_succ,
            have pow_def : a ^ -int.of_nat (nat.succ l2) = (a ^ (nat.succ l2))⁻¹,
            {
                refl,
            },
            rw pow_def,
            rw mul_assoc,
            simp,
        },
        {
            rw add_comm,
        },
    },
end

lemma pow_mult : ∀ a : Q, ∀ n m : int, a^n * a^m = a^(n + m) :=
begin
    intros a n m,
    induction n with n1 n2,
    {
        have pow_def : ∀ b : Q, ∀ k : nat, b ^ (int.of_nat k) = b ^ k,
        {
            intros b k,
            refl,
        },
        rw pow_def,
        rw pow_mult_nat_int,
        refl,
    },
    {
        have pow_def : ∀ b : Q, b ^ (int.neg_succ_of_nat n2) = (b ^ (nat.succ n2))⁻¹,
        {
            intro b, 
            refl,
        },
        rw pow_def,
        have other_side : a ^ m = a ^ nat.succ n2 * a ^ (-[1+ n2] + m),
        {
            rw pow_mult_nat_int,
            apply congr_arg,
            rw int.neg_succ_of_nat_coe,
            ring,
        },
        rw other_side,
        simp,
    },
end

lemma pow_comp_nat : ∀ a : Q, ∀ n m : nat, (a^n)^m = a^(n * m) :=
begin 
    intros a n m,
    induction m with k hk,
    {
        simp,
        refl,
    },
    {
        have hs1 : (a^n)^(nat.succ k) = a^n * (a^n)^k,
        {refl},
        rw hs1,
        have hs2 : a ^ (n * nat.succ k) = a ^ (n + n * k),
        {
            rw nat.mul_succ,
            rw nat.add_comm,
        },
        rw hs2,
        rw ←pow_mult_nat a n (n * k),
        rw hk,
    },
end

lemma pow_comp_nat_int : ∀ a : Q, ∀ n : nat, ∀ m : int, (a^n)^m = a^(m * n) :=
begin
    intros a n m,
    induction m with l1 l2,
    {
        have pow_def : ∀ b : Q, ∀ k : nat, b ^ (int.of_nat k) = b ^ k,
        {
            intros b k,
            refl,
        },
        rw pow_def,
        rw pow_comp_nat,
        have to_nat_mul : int.of_nat l1 * n = int.of_nat (l1 * n),
        {
            refl,
        },
        rw to_nat_mul,
        rw pow_def,
        rw nat.mul_comm,
    },
    {
        have pow_def : ∀ b : Q, b ^ (int.neg_succ_of_nat l2) = (b ^ (nat.succ l2))⁻¹,
        {
            intro b, 
            refl,
        },
        rw pow_def (a^n),
        have prod_rw : (int.neg_succ_of_nat l2 * n) = int.neg_of_nat (nat.succ l2 * n),
        {
            refl,
        },
        rw prod_rw,
        rw pow_neg,
        rw pow_comp_nat,
        rw nat.mul_comm,
    }
end

lemma pow_is_inv : ∀ a : Q, a⁻¹ = a ^ (-1 : int) :=
begin
    intro a,
    have pow_rw : a ^ (-1 : int) = a ^ (int.neg_succ_of_nat 0),
    {
        refl,
    },
    rw pow_rw,
    have pow_rw_2 : a ^ (int.neg_succ_of_nat 0) = (a ^ (1 : int))⁻¹,
    {
        refl,
    },
    rw pow_rw_2,
    rw pow_1_group a,
end

lemma mul_pow_is_pow_mul_nat : ∀ a : Q, ∀ n : nat, a * a ^ n = a ^ n * a :=
begin
    intros a n,
    induction n with m hm,
    {
        rw pow_0,
        simp,
    },
    {
        rw pow_succ_group,
        rw mul_assoc,
        rw hm,
    },
end

lemma pow_inv_comm_group_nat : ∀ a : Q, ∀ n : nat, a⁻¹ ^ n = (a ^ n)⁻¹ :=
begin
    intros a n,
    induction n with l hl,
    {
        rw pow_0,
        rw pow_0,
        simp,
    },
    {
        rw pow_succ_group,
        rw pow_succ_group,
        simp,
        rw ←hl,
        rw mul_pow_is_pow_mul_nat,
    },
end

lemma pow_inv_comm_group : ∀ a : Q, ∀ k : int, a⁻¹ ^ k = (a^k)⁻¹ :=
begin
    intros a k,
    induction k with k1 k2,
    {
        have pow_def : ∀ b : Q, ∀ k : nat, b ^ (int.of_nat k) = b ^ k,
        {
            intros b k,
            refl,
        },
        rw pow_def,
        rw pow_def,
        rw pow_inv_comm_group_nat,
    },
    {
        have pow_def : ∀ b : Q, ∀ k : nat, b ^ (int.neg_succ_of_nat k) = (b ^ nat.succ k)⁻¹,
        {
            intros b k,
            refl,
        },
        rw pow_def,
        rw pow_def,
        rw pow_inv_comm_group_nat,
    },
end

lemma pow_neg_is_pow_inv_nat : ∀ a : Q, ∀ n : nat, a ^ (-n : int) = (a ^ n)⁻¹ :=
begin
    intros a n,
    rw neg_eq_neg_one_mul,
    rw ←pow_comp_nat_int,
    rw pow_is_inv,
end

lemma pow_neg_is_pow_inv : ∀ a : Q, ∀ n : int, a ^ (-n) = (a ^ n)⁻¹ :=
begin
    intros a n,
    induction n with l1 l2,
    {
        have pow_def : ∀ b : Q, ∀ k : nat, b ^ (int.of_nat k) = b ^ k,
        {
            intros b k,
            refl,
        },
        rw pow_def,
        have coe_def : int.of_nat l1 = (l1 : int),
        {
            refl,
        },
        rw coe_def,
        rw pow_neg_is_pow_inv_nat,
    },
    {
        have pow_def : ∀ b : Q, b ^ (int.neg_succ_of_nat l2) = (b ^ (nat.succ l2))⁻¹,
        {
            intro b, 
            refl,
        },
        rw pow_def,
        simp,
        have neg_neg_is_pos : - (int.neg_succ_of_nat l2) = int.of_nat (nat.succ l2),
        {
            refl,
        },
        rw neg_neg_is_pos,
        refl,
    },
end

lemma pow_comp_group : ∀ a : Q, ∀ n m : int, (a^n)^m = a^(n * m) :=
begin
    intros a n m,
    induction n with l1 l2,
    {
        have pow_def : ∀ b : Q, ∀ k : nat, b ^ (int.of_nat k) = b ^ k,
        {
            intros b k,
            refl,
        },
        rw pow_def,
        rw pow_comp_nat_int,
        rw int.mul_comm,
        refl,
    },
    {
        have pow_def : ∀ b : Q, b ^ (int.neg_succ_of_nat l2) = (b ^ (nat.succ l2))⁻¹,
        {
            intro b, 
            refl,
        },
        rw pow_def,
        have prod_rw : (int.neg_succ_of_nat l2 * m) = -(nat.succ l2 * m),
        {
            have neg_rw : int.neg_succ_of_nat l2 = - (nat.succ l2),
            {
                refl,
            },
            rw neg_rw,
            rw neg_mul_eq_neg_mul_symm,
        },
        rw prod_rw,
        rw pow_inv_comm_group,
        rw pow_neg_is_pow_inv,
        rw pow_comp_nat_int,
        rw int.mul_comm,
    },
    
end

-/

lemma q_pow0_group : ∀ a b : Q, a ▷ (pow b 0) = pow b 0 :=
begin
    intros a b,
    rw rhd_def,
    --rw pow_0,
    simp,
end

lemma q_pown_right_nat : ∀ a b : Q, ∀ n : nat, (a ▷ b)^n = a ▷ (b^n) :=
begin
    intros a b n,
    rw rhd_def,
    rw rhd_def,

    induction n with m hm,
    {
        --rw pow_0,
        --rw pow_0,
        simp,
    },
    {
        --rw pow_succ_group,
        --rw pow_succ_group,
        rw pow_succ,
        rw pow_succ,
        rw hm,
        repeat {rw ←mul_assoc},
        simp,
    },
end

lemma q_pown_right_group : ∀ a b : Q, ∀ n : int, (a ▷ b)^n = a ▷ (b^n) :=
begin
    intros a b n,
    induction n with l1 l2,
    {
        have pow_def : ∀ b : Q, ∀ k : nat, b ^ (int.of_nat k) = b ^ k,
        {
            intros b k,
            refl,
        },
        rw pow_def,
        rw pow_def,
        rw q_pown_right_nat,
    },
    {
        have pow_def : ∀ b : Q, b ^ (int.neg_succ_of_nat l2) = (b ^ (nat.succ l2))⁻¹,
        {
            intro b, 
            refl,
        },
        rw pow_def,
        rw pow_def,
        rw q_pown_right_nat,
        rw inv_q_right,
    },
end

/-
lemma q_pown_left : ∀ a b : Q, ∀ n : int, (b ◁ a)^n = (b^n) ◁ a :=
begin
    intros a b n,
    rw q_inv_left_to_right,
    rw q_inv_left_to_right,
    rw q_pown_right,
end


lemma q_powneg_right : ∀ a b : Q, a ▷ b = b ◁ (pow a (-1 : int)) := 
begin
    intros a b,
    rw q_inv_left_to_right,
    rw ←pow_is_inv,
    simp,
end


lemma q_powneg_left : ∀ a b : Q, b ◁ a = (pow a (-1 : int)) ▷ b := 
begin
    intros a b,
    rw q_powneg_right,
    rw ←pow_is_inv,
    rw ←pow_is_inv,
    simp,
end
-/

lemma q_powneg_left_group : ∀ a b : Q, b ◁ a = (pow a (-1 : int)) ▷ b := 
begin
    intros a b,
    rw q_inv_left_to_right,
    rw gpow_neg_one,
end

lemma q_powadd_group : ∀ a b : Q, ∀ n m : int, (pow a n) ▷ ((pow a m) ▷ b) = (a^(n + m) ▷ b) :=
begin
    intros a b n m,
    repeat {rw rhd_def},
    rw gpow_add,
    --rw ←pow_mult,
    simp,
    repeat {rw ←mul_assoc},
end

instance group_is_pq : power_quandle Q := power_quandle.mk
(gpow_one)--(pow_1_group)
(begin intros, apply eq.symm, apply gpow_mul end)--(pow_comp_group)
(q_pow0_group)
(q_pown_right_group)
--(q_pown_left)
--(q_powneg_right)
(q_powneg_left_group)
(q_powadd_group)


end group_to_pq

section group_morph_to_pq_morph

variables {G : Type u} [group G] {H : Type v} [group H]

def is_group_morphism (f : G → H) : Prop := (∀ a b : G, f(a * b) = f(a) * f(b))

lemma group_morphism_one (f : G → H) (hf : is_group_morphism f) : f (1) = 1 :=
begin
    have calculation := calc 1 = f(1) * (f 1)⁻¹           : by group
                        ...    = f(1 * 1) * (f 1)⁻¹       : by group
                        ...    = f(1) * f(1) * (f 1)⁻¹    : by rw hf
                        ...    = f(1) * (f(1) * (f 1)⁻¹)  : by group
                        ...    = f(1) * 1               : by group
                        ...    = f(1)                   : by group,
    
    apply eq.symm,
    exact calculation,
end

lemma group_morphism_inv (f : G → H) (hf : is_group_morphism f) : ∀ a : G, f(a⁻¹) = (f a)⁻¹ :=
begin
    intro a,

    have calculation := calc f(a⁻¹) = f(a⁻¹) * 1              : by group
                        ...        = f(a⁻¹) * (f(a) * (f a)⁻¹) : by group
                        ...        = f(a⁻¹) * f(a) * (f a)⁻¹   : by group
                        ...        = f(a⁻¹ * a) * (f a)⁻¹      : by rw hf
                        ...        = f(1) * (f a)⁻¹           : by group
                        ...        = 1 * (f a)⁻¹              : by rw group_morphism_one f hf
                        ...        = (f a)⁻¹                  : by group,
    exact calculation,
end



theorem functoriality_group_to_pq (f : G → H) (hf : is_group_morphism f) : is_pq_morphism f :=
begin
    split,
    {
        intros a b,
        rw rhd_def,
        rw rhd_def,
        rw hf,
        rw hf,
        rw ←group_morphism_inv f hf,
    },
    {
        intro a,
        have preservence_nat : ∀ m : nat, f(a ^ m) = f(a) ^ m,
        {
            intro m,
            induction m with l hl,
            {
                --rw pow_0,
                --rw pow_0,
                simp,
                exact group_morphism_one f hf,
            },
            {
                rw pow_succ,
                rw pow_succ,
                rw hf,
                apply congr_arg,
                exact hl,
            },
        },
        intro n,
        induction n with l1 l2,
        {
            have pow_def_g : ∀ b : G, ∀ k : nat, b ^ (int.of_nat k) = b ^ k,
            {
                intros b k,
                refl,
            },
            rw pow_def_g,
            have pow_def_h : ∀ b : H, ∀ k : nat, b ^ (int.of_nat k) = b ^ k,
            {
                intros b k,
                refl,
            },
            rw pow_def_h,
            rw preservence_nat,
        },
        {
            have pow_def_g : ∀ b : G, b ^ (int.neg_succ_of_nat l2) = (b ^ (nat.succ l2))⁻¹,
            {
                intro b, 
                refl,
            },
            rw pow_def_g,
            have pow_def_h : ∀ b : H, b ^ (int.neg_succ_of_nat l2) = (b ^ (nat.succ l2))⁻¹,
            {
                intro b, 
                refl,
            },
            rw pow_def_h,
            rw group_morphism_inv f hf,
            apply congr_arg,
            rw preservence_nat,
        },
    },
end

theorem functoriality_group_bundled_to_pq (f : G →* H) : is_pq_morphism f :=
begin
    apply functoriality_group_to_pq,
    intros a b,
    simp only [monoid_hom.map_mul],
end

theorem functoriality_group_iso_to_pq (f : G ≃* H) : is_pq_morphism f :=
begin
    apply functoriality_group_to_pq,
    intros a b,
    simp only [mul_equiv.map_mul],
end

-- composition and identity preservence is trivial

theorem group_to_pq_fullness_almost (f : G → H) (hf : is_pq_morphism f) (hfs : function.surjective f) (hG : ∀ a b : H, (∀ c : H, a ▷ c = b ▷ c) → a = b) : is_group_morphism f :=
begin
    cases hf with hf1pre hf2,
    have hf1 : ∀ a b : G, f(a * b * a⁻¹) = f(a) * f(b) * (f(a))⁻¹,
    {
        intros a b,
        specialize hf1pre a b,
        repeat {rw rhd_def at hf1pre},
        exact hf1pre,
    },
    --split,
    {
        intros a b,
        apply hG,
        intro c,
        repeat {rw rhd_def},
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


end group_morph_to_pq_morph

section group_to_pq_properties

variables {G : Type u} [group G]

lemma mul_rhd_eq_rhd (a b c : G) : a * b ▷ c = a ▷ b ▷ c :=
begin
    repeat {rw rhd_def},
    group,
end

lemma one_rhd (a : G) : 1 ▷ a = a :=
begin
    rw rhd_def,
    group,
end

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
    rw rhd_def at hc2,
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
            repeat {rw rhd_def at hf1pre},
            exact hf1pre,
        },
        intro c,
        repeat {rw rhd_def},
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
        rw ←rhd_def,
        rw rhd_preserved_by_morphism f hf,
        rw rhd_def,
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
        rw ←rhd_def,
        rw ←pq_morph_pres_inv f hf,
        rw ←rhd_preserved_by_morphism f hf,
        apply congr_arg,
        rw rhd_def,
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
        rw ←rhd_def at hfbc,
        rw rhd_preserved_by_morphism f hf c b at hfbc,
        rw rhd_def at hfbc,
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
                rw ←rhd_def,
                rw rhd_preserved_by_morphism f hf g c,
                rw rhd_def,
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

