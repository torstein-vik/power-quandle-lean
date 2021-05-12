
import power_quandle

universe u

section pq_induce_lhd

variables {Q : Type u}

def induce_lhd 
[hQpow : has_pow Q ℤ]
[hQrhd : has_triangle_right Q]
(right_dist : ∀ a b c : Q, a ▷ (b ▷ c) = (a ▷ b) ▷ (a ▷ c))
(self_idem_right : ∀ a : Q, a ▷ a = a)
(pow_1 : ∀ a : Q, a ^ (1 : ℤ) = a)
(pow_comp : ∀ a : Q, ∀ n m : int, (a^n)^m = a^(n * m))
(q_pow0 : ∀ a b : Q, a ▷ (b ^ (0 : ℤ)) = b ^ (0 : ℤ))
(pow_zero_rhd : ∀ a b : Q, (a ^ (0 : ℤ)) ▷ b = b)
(pow_neg_one_rhd : ∀ a : Q, (a ^ (-1 : ℤ)) ▷ a = a)
(q_pown_right : ∀ a b : Q, ∀ n : int, (a ▷ b)^n = a ▷ (b^n))
(q_powadd : ∀ a b : Q, ∀ n m : int, (pow a n) ▷ ((pow a m) ▷ b) = (a^(n + m) ▷ b))
: power_quandle Q := { 
  triangle_left := λ y x, (x ^ (-1 : ℤ)) ▷ y,
  right_dist := right_dist,
  left_dist := begin 
    intros a b c,
    unfold has_triangle_left.triangle_left,
    rw q_pown_right,
    apply right_dist,
  end,
  right_inv := begin 
    intros a b,
    unfold has_triangle_left.triangle_left,
    rw ←pow_1 a,
    rw pow_comp,
    rw q_powadd,
    norm_num,
    rw pow_zero_rhd,
  end,
  left_inv := begin 
    intros a b,
    unfold has_triangle_left.triangle_left,
    rw ←pow_1 a,
    rw pow_comp,
    rw q_powadd,
    norm_num,
    rw pow_zero_rhd,
  end,
  self_idem_right := self_idem_right,
  self_idem_left := begin 
    intros a,
    unfold has_triangle_left.triangle_left,
    rw pow_neg_one_rhd,
  end,
  pow_1 := pow_1,
  pow_comp := pow_comp,
  q_pow0 := q_pow0,
  q_pown_right := q_pown_right,
  q_powneg_left := begin 
    intros a b,
    refl,
  end,
  q_powadd := q_powadd,
  ..hQpow,
  ..hQrhd,
}

end pq_induce_lhd
