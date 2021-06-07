
import power_quandle

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

