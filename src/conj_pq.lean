
-- Define Cc Q as the power quandle of the "conjugacy classes" of Q. 

import power_quandle

universe u

section conj_pq

variables {Q : Type u} [power_quandle Q]

--structure conj_pq_wrapper (Q : Type u) [power_quandle Q] := (a : Q)

/-
inductive pq_is_conj : Q → Q → Prop
| refl (a : Q) : pq_is_conj a a
| symm (a b : Q) (hab : pq_is_conj a b) : pq_is_conj b a
| rhd (a b c : Q) (hbc : pq_is_conj b c) : pq_is_conj (a ▷ b) c

lemma pq_is_conj_refl (a : Q) : pq_is_conj a a := pq_is_conj.refl a

lemma pq_is_conj_symm (a b : Q) (hab : pq_is_conj a b) : pq_is_conj b a := pq_is_conj.symm a b hab

lemma pq_is_conj_trans (a b c : Q) (hab : pq_is_conj a b) (hbc : pq_is_conj b c) : pq_is_conj a c :=
begin
  suffices : 
  induction hab,
end
-/

def pq_is_conj : Q → Q → Prop := λ x y, ∃ z : list Q, y = list.foldl (λ a b, b ▷ a) x z

lemma pq_is_conj_refl (a : Q) : pq_is_conj a a :=
begin
  use list.nil,
  refl,
end

lemma pq_is_conj_symm (a b : Q) (hab : pq_is_conj a b) : pq_is_conj b a :=
begin
  cases hab with x hx,
  use (list.map (λ y, y ^ (-1 : ℤ)) x).reverse,
  rw hx,
  clear hx,
  induction x generalizing a,
  {
    refl,
  },
  {
    simp only [list.reverse_cons, list.foldl_append, list.foldl, list.map],
    rw ←x_ih (x_hd ▷ a),
    rw ←power_quandle.pow_one x_hd,
    rw power_quandle.pow_comp,
    norm_num,
    rw power_quandle.rhd_pow_add,
    norm_num,
    rw power_quandle.pow_zero,
    rw power_quandle.one_rhd,
  },
end

lemma pq_is_conj_trans (a b c : Q) (hab : pq_is_conj a b) (hbc : pq_is_conj b c) : pq_is_conj a c :=
begin
  cases hab with x hx,
  cases hbc with y hy,
  use x ++ y,
  simp only [list.foldl_append],
  rw ←hx,
  exact hy,
end

lemma pq_is_conj_rhd_congr (a b a' b' : Q) (hab : pq_is_conj a b) (hab' : pq_is_conj a' b') : pq_is_conj (a ▷ a') (b ▷ b') :=
begin
  cases hab' with y hy,
  use ([a ^ (-1 : ℤ)] ++ y ++ [b]),
  simp only [list.foldl_append, list.foldl],
  rw hy,
  congr,
  rw ←power_quandle.pow_one a,
  rw power_quandle.pow_comp,
  norm_num,
  rw power_quandle.rhd_pow_add,
  norm_num,
  rw power_quandle.pow_zero,
  rw power_quandle.one_rhd,
end

lemma pq_is_conj_pow_congr (a b : Q) (n : ℤ) (hab : pq_is_conj a b) : pq_is_conj (a ^ n) (b ^ n) :=
begin
  cases hab with x hx,
  use x,
  rw hx,
  clear hx,
  induction x generalizing a,
  {
    refl,
  },
  {
    simp only [list.foldl],
    rw x_ih (x_hd ▷ a),
    congr,
    rw power_quandle.pow_rhd,
  },
end

instance pq_is_conj_setoid : setoid Q := ⟨pq_is_conj, begin 
  split,
  apply pq_is_conj_refl,
  split,
  apply pq_is_conj_symm,
  apply pq_is_conj_trans,
end⟩

def conj_pq (Q : Type u) [power_quandle Q] : Type u := @quotient Q (pq_is_conj_setoid)

instance conj_pq_has_rhd : has_rhd (conj_pq Q) := ⟨λ x y, quotient.lift_on₂ x y (λ a b, ⟦a ▷ b⟧) begin 
  intros a b c d hab hcd,
  apply quotient.sound,
  apply pq_is_conj_rhd_congr,
  assumption,
  assumption,
end⟩

instance conj_pq_has_pow : has_pow (conj_pq Q) (ℤ) := ⟨λ x n, quotient.lift_on x (λ a, ⟦a ^ n⟧) begin 
  intros a b hab,
  apply quotient.sound,
  apply pq_is_conj_pow_congr,
  assumption,
end⟩

instance conj_pq_has_one : has_one (conj_pq Q) := ⟨(⟦1⟧ : conj_pq Q)⟩

lemma conj_pq_rhd_def (a b : Q) : (⟦a⟧ ▷ ⟦b⟧ : conj_pq Q) = ⟦a ▷ b⟧ := rfl

lemma conj_pq_pow_def (a : Q) (n : ℤ) : (⟦a⟧ ^ n : conj_pq Q) = ⟦a ^ n⟧ := rfl 

lemma conj_pq_one_def : (1 : conj_pq Q) = ⟦1⟧ := rfl

lemma quot_mk_helper_conj_pq (a : Q) : quot.mk setoid.r a = ⟦a⟧ := rfl

lemma pq_is_conj_refl_helper (a b : Q) (hab : a = b) : ⟦a⟧ = ⟦b⟧ := 
begin
  congr,
  assumption,
end

instance conj_pq_is_pq : power_quandle (conj_pq Q) := { 
  rhd_dist := begin
    rintros ⟨a⟩ ⟨b⟩ ⟨c⟩,
    simp only [quot_mk_helper_conj_pq],
    simp only [conj_pq_rhd_def, conj_pq_pow_def, conj_pq_one_def],
    apply pq_is_conj_refl_helper,
    exact power_quandle.rhd_dist a b c,
  end,
  rhd_idem := begin
    rintros ⟨a⟩,
    simp only [quot_mk_helper_conj_pq],
    simp only [conj_pq_rhd_def, conj_pq_pow_def, conj_pq_one_def],
    apply pq_is_conj_refl_helper,
    exact power_quandle.rhd_idem a,
  end,
  pow_one := begin
    rintros ⟨a⟩,
    simp only [quot_mk_helper_conj_pq],
    simp only [conj_pq_rhd_def, conj_pq_pow_def, conj_pq_one_def],
    apply pq_is_conj_refl_helper,
    exact power_quandle.pow_one a,
  end,
  pow_zero := begin
    rintros ⟨a⟩,
    simp only [quot_mk_helper_conj_pq],
    simp only [conj_pq_rhd_def, conj_pq_pow_def, conj_pq_one_def],
    apply pq_is_conj_refl_helper,
    exact power_quandle.pow_zero a,
  end,
  pow_comp := begin
    rintros ⟨a⟩ n m,
    simp only [quot_mk_helper_conj_pq],
    simp only [conj_pq_rhd_def, conj_pq_pow_def, conj_pq_one_def],
    apply pq_is_conj_refl_helper,
    exact power_quandle.pow_comp a n m,
  end,
  rhd_one := begin
    rintros ⟨a⟩,
    simp only [quot_mk_helper_conj_pq],
    simp only [conj_pq_rhd_def, conj_pq_pow_def, conj_pq_one_def],
    apply pq_is_conj_refl_helper,
    exact power_quandle.rhd_one a,
  end,
  one_rhd := begin
    rintros ⟨a⟩,
    simp only [quot_mk_helper_conj_pq],
    simp only [conj_pq_rhd_def, conj_pq_pow_def, conj_pq_one_def],
    apply pq_is_conj_refl_helper,
    exact power_quandle.one_rhd a,
  end,
  pow_rhd := begin
    rintros ⟨a⟩ ⟨b⟩ n,
    simp only [quot_mk_helper_conj_pq],
    simp only [conj_pq_rhd_def, conj_pq_pow_def, conj_pq_one_def],
    apply pq_is_conj_refl_helper,
    exact power_quandle.pow_rhd a b n,
  end,
  rhd_pow_add := begin
    rintros ⟨a⟩ ⟨b⟩ n m,
    simp only [quot_mk_helper_conj_pq],
    simp only [conj_pq_rhd_def, conj_pq_pow_def, conj_pq_one_def],
    apply pq_is_conj_refl_helper,
    exact power_quandle.rhd_pow_add a b n m,
  end,
  ..conj_pq_has_rhd,
  ..conj_pq_has_pow,
  ..conj_pq_has_one }

end conj_pq