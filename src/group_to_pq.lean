
-- TODO: Define functor, ie. group morphism to pq morphism and comp

import quandle

import algebra.group

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

lemma q_pow0_group : ∀ a b : Q, a ▷ (pow b 0) = pow b 0 :=
begin
    intros a b,
    rw rhd_def,
    rw pow_0,
    simp,
end

lemma q_pown_right_nat : ∀ a b : Q, ∀ n : nat, (a ▷ b)^n = a ▷ (b^n) :=
begin
    intros a b n,
    rw rhd_def,
    rw rhd_def,

    induction n with m hm,
    {
        rw pow_0,
        rw pow_0,
        simp,
    },
    {
        rw pow_succ_group,
        rw pow_succ_group,
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
    rw pow_is_inv,
end

lemma q_powadd_group : ∀ a b : Q, ∀ n m : int, (pow a n) ▷ ((pow a m) ▷ b) = (a^(n + m) ▷ b) :=
begin
    intros a b n m,
    repeat {rw rhd_def},
    rw ←pow_mult,
    simp,
    repeat {rw ←mul_assoc},
end

instance group_is_pq : power_quandle Q := power_quandle.mk
(pow_1_group)
(pow_comp_group)
(q_pow0_group)
(q_pown_right_group)
--(q_pown_left)
--(q_powneg_right)
(q_powneg_left_group)
(q_powadd_group)


end group_to_pq

section group_morph_to_pq_morph

variables {G : Type u} [group G] {H : Type v} [group H]

def is_group_morphism (f : G → H) : Prop := (∀ a b : G, f(a * b) = f(a) * f(b)) ∧ (f(1) = 1) ∧ (∀ a : G, f(a⁻¹) = (f a)⁻¹)

theorem functoriality_group_to_pq (f : G → H) (hf : is_group_morphism f) : is_pq_morphism f :=
begin
    cases hf with hf1 hfr,
    cases hfr with hf2 hf3,
    split,
    {
        intros a b,
        rw rhd_def,
        rw rhd_def,
        rw hf1,
        rw hf1,
        rw hf3,
    },
    {
        intro a,
        have preservence_nat : ∀ m : nat, f(a ^ m) = f(a) ^ m,
        {
            intro m,
            induction m with l hl,
            {
                rw pow_0,
                rw pow_0,
                exact hf2,
            },
            {
                rw pow_succ_group,
                rw pow_succ_group,
                rw hf1,
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
            rw hf3,
            apply congr_arg,
            rw preservence_nat,
        },
    },
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
    split,
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
    split,
    {
        specialize hf2 1 0,
        rw pow_0_int at hf2,
        rw pow_0_int at hf2,
        exact hf2,
    },
    {
        intro a,
        specialize hf2 a (-1 : int),
        rw pow_is_inv,
        rw pow_is_inv,
        exact hf2,
    },
end


end group_morph_to_pq_morph

