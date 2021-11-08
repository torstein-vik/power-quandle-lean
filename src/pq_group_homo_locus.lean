
import pq_to_group

universe u

section pq_group_homo_locus

variables {G : Type u} [group G]

def homo_locus (a : G × G) := (of a.1) * (of a.2) = of (a.1 * a.2)

lemma homo_locus_def (a : G × G) : homo_locus a ↔ (of a.1) * (of a.2) = of (a.1 * a.2) := by refl

lemma homo_locus_triple_as_doubles (a b c : G) (hab : homo_locus (a, b)) (habc : homo_locus (a * b, c)) : (of a * of b * of c = of (a * b * c)) :=
begin
  simp only [homo_locus_def] at *,
  rw hab,
  rw habc,
end

-- This is experimentally untrue
/-
lemma homo_locus_closed_rhd (a b : G × G) (ha : homo_locus a) (hb : homo_locus b) : homo_locus (a ▷ b) :=
begin
  rw homo_locus_def at *,
  cases a with a1 a2,
  cases b with b1 b2,
  simp only at *,
  rw rhd_def_group,
  simp only [prod.inv_mk, prod.mk_mul_mk],
  rw ←rhd_def_group,
  rw ←rhd_def_group,
  rw ←rhd_of_eq_of_rhd,
  rw ←rhd_of_eq_of_rhd,
  rw rhd_def_group,
  rw rhd_def_group,
  sorry,
end
-/

-- This is experimentally untrue
-- For an analytical arguement, consider (1, a) * (b, 1) would give any (a, b)
/-
lemma homo_locus_closed_mul (a b : G × G) (ha : homo_locus a) (hb : homo_locus b) : homo_locus (a * b) :=
begin
  rw homo_locus_def at *,
  cases a with a1 a2,
  cases b with b1 b2,
  simp only [prod.mk_mul_mk] at *,
  sorry,
end
-/

lemma nat_pow_prod (a b : G) (n : ℕ) : ((a, b) : G × G) ^ n = (a ^ n, b ^ n) :=
begin
  induction n,
  {
    refl,
  },
  {
    rw pow_succ,
    rw n_ih,
    refl,
  },
end

lemma gpow_prod (a b : G) (n : ℤ) : ((a, b) : G × G) ^ n = (a ^ n, b ^ n) :=
begin
  induction n,
  {
    simp only [int.of_nat_eq_coe, gpow_coe_nat] at *,
    apply nat_pow_prod,
  },
  {
    simp only [gpow_neg_succ_of_nat],
    rw nat_pow_prod,
    refl,
  },
end

lemma homo_locus_closed_same_power (a : G) (n m : ℤ) : homo_locus (a ^ n, a ^ m) :=
begin
  rw homo_locus_def,
  simp only,
  rw ←gpow_add,
  simp only [of_pow_eq_pow_of],
  rw gpow_add,
end

lemma homo_locus_closed_refl (a : G) : homo_locus (a, a) :=
begin
  convert homo_locus_closed_same_power a 1 1,
  rw gpow_one,
  rw gpow_one,
end

lemma homo_locus_closed_left_one (a : G) : homo_locus (1, a) :=
begin
  convert homo_locus_closed_same_power a 0 1,
  rw gpow_one,
end

lemma homo_locus_closed_right_one (a : G) : homo_locus (a, 1) :=
begin
  convert homo_locus_closed_same_power a 1 0,
  rw gpow_one,
end

lemma homo_locus_closed_left_inv (a : G) : homo_locus (a⁻¹, a) :=
begin
  convert homo_locus_closed_same_power a (-1) 1,
  rw pow_one,
  rw gpow_one,
end

lemma homo_locus_closed_right_inv (a : G) : homo_locus (a, a⁻¹) :=
begin
  convert homo_locus_closed_same_power a 1 (-1),
  rw gpow_one,
  rw pow_one,
end


lemma homo_locus_closed_symm (a b : G) (ha : homo_locus (a, b)) : homo_locus (b, a) :=
begin
  rw homo_locus_def at *,
  simp only at *,
  suffices : of b * of a * of b * (of b)⁻¹ = of (b * a),
  simp only [mul_inv_cancel_right] at this,
  exact this,
  assoc_rw ha,
  clear _inst,
  rw ←rhd_def_group,
  rw rhd_of_eq_of_rhd,
  rw rhd_def_group,
  rw mul_assoc,
  simp only [mul_inv_cancel_right],
end

-- This is false by experiment, in power-quandle-computation
/-
lemma homo_locus_closed_invert_right (a b : G) (hab : homo_locus (a, b)) : homo_locus (a, b⁻¹) :=
begin
  have hab1 := homo_locus_closed_symm _ _ hab,
  rw homo_locus_def at *,
  simp only at *,
  sorry,
end
-/

lemma homo_locus_closed_rhd_left (a b c : G) (hab : homo_locus (a, b)) : homo_locus (c ▷ a, c ▷ b) :=
begin
  rw homo_locus_def at *,
  simp only at *,
  rw ←rhd_mul,
  simp only [←rhd_of_eq_of_rhd],
  rw ←rhd_mul,
  rw hab,
end

lemma homo_locus_closed_commutator (a b : G) : homo_locus (a, b ▷ a⁻¹) ↔ homo_locus (a ▷ b, b⁻¹) :=
begin
  simp only [homo_locus],
  rw ←rhd_of_eq_of_rhd,
  rw inv_of,
  rw rhd_def_group,
  rw rhd_def_group,
  rw ←mul_assoc,
  rw ←mul_assoc,
  rw ←rhd_def_group,
  rw ←inv_of,
  rw rhd_of_eq_of_rhd,
  suffices : of (a * (b * a⁻¹ * b⁻¹)) = of ((a▷b) * b⁻¹),
  {
    rw this,
  },
  rw rhd_def_group,
  apply congr_arg,
  group,
end

lemma homo_locus_closed_shift_left (a b : G) : homo_locus (a, b) ↔ homo_locus (a * b, a⁻¹) :=
begin
  simp only [homo_locus_def],
  split,
  {
    intro hab,
    rw ←hab,
    rw ←rhd_def_group,
    rw ←rhd_of_eq_of_rhd,
    rw rhd_def_group,
    rw inv_of,
  },
  {
    intro hab,
    rw ←rhd_def_group at hab,
    rw ←rhd_of_eq_of_rhd at hab,
    rw rhd_def_group at hab,
    rw inv_of at hab,
    simp only [mul_left_inj] at hab,
    symmetry,
    exact hab,
  },
end 


lemma homo_locus_closed_shift_right (a b : G) : homo_locus (a, b) ↔ homo_locus (a * b, b⁻¹) :=
begin
  simp only [homo_locus_def],
  split,
  {
    intro hab,
    rw ←hab,
    simp only [inv_of, mul_inv_cancel_right],
  },
  {
    intro hab,
    simp only [inv_of, mul_inv_cancel_right] at hab,
    rw ←hab,
    simp only [inv_mul_cancel_right],
  },
end

lemma homo_locus_closed_double_inverse (a b : G) : homo_locus (a*b, a⁻¹) ↔ homo_locus (a*b, b⁻¹) :=
begin
  rw ←homo_locus_closed_shift_right,
  rw ←homo_locus_closed_shift_left,
end

lemma homo_locus_closed_second_shift (a b : G) (hab : homo_locus (a, b)) : homo_locus (a, (a * b)⁻¹) :=
begin
  let c := a * b,
  let d := b⁻¹,
  have a_def : a = c * d,
  {
    simp only [mul_inv_cancel_right],
  },
  have b_def : b = d⁻¹,
  {
    simp only [inv_inv],
  },
  simp only [a_def, b_def] at *,
  revert hab,
  generalize : c = e,
  generalize : d = f,
  clear a_def b_def c d a b,
  intro hab,
  convert (homo_locus_closed_double_inverse e f).mpr hab,
  simp only [mul_inv_cancel_right],
end

-- Transitivity is trivially untrue, as (a, 1) and (1, b) would always yield (a, b) for any a b
/-
lemma homo_locus_closed_trans (a b c : G) (hab : homo_locus (a, b)) (hbc : homo_locus (b, c)) : homo_locus (a, c) :=
begin
  rw homo_locus_def at *,
  simp only at *,
  suffices : of a * of b * (of b)⁻¹ * of c = of (a * c),
  simp only [mul_inv_cancel_right] at this,
  exact this,
  rw hab,
  rw ←inv_of,
  sorry,
end
-/

lemma homo_locus_closed_trans_alt_right (a b c : G) (hab : homo_locus (a, b)) (hbc : homo_locus (b, c)) (habc : homo_locus (a * b, c)) : homo_locus (a, b * c) :=
begin
  rw homo_locus_def at *,
  simp only at *,
  rw ←mul_assoc,
  rw ←habc,
  rw ←hab,
  rw ←hbc,
  rw mul_assoc,
end

lemma homo_locus_closed_trans_alt_left (a b c : G) (hab : homo_locus (a, b)) (hbc : homo_locus (b, c)) (habc : homo_locus (a, b * c)) : homo_locus (a * b, c) :=
begin
  rw homo_locus_def at *,
  simp only at *,
  rw ←mul_assoc at habc,
  rw ←habc,
  rw ←hab,
  rw ←hbc,
  rw mul_assoc,
end

lemma homo_locus_closed_inv (a : G × G) (ha : homo_locus a) : homo_locus (a⁻¹) :=
begin
  have ha1 := homo_locus_closed_symm _ _ ha,
  rw homo_locus_def at *,
  cases a with a1 a2,
  simp only [prod.inv_mk],
  simp only at *,
  rw ←mul_inv_rev,
  simp only [inv_of],
  rw ←ha1,
  rw mul_inv_rev,
end

-- Not true without comm by experiment
lemma homo_locus_closed_pow_comm (a : G × G) (n : ℤ) (ha : homo_locus a) (ha1 : commute a.1 a.2) : homo_locus (a ^ n) :=
begin
  rw homo_locus_def at *,
  cases a with a1 a2,
  rw gpow_prod,
  simp only at *,
  rw of_pow_eq_pow_of,
  rw of_pow_eq_pow_of,
  rw ←commute.mul_gpow,
  rw ha,
  rw ←of_pow_eq_pow_of,
  rw commute.mul_gpow,
  exact ha1,
  apply pq_group_commute,
  exact ha1,
end

end pq_group_homo_locus
