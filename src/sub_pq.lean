
import power_quandle

universe u

section sub_power_quandle


structure sub_power_quandle (Q : Type u) [power_quandle Q] := 
(carrier : set Q)
(closed_rhd : ∀ x y : Q, x ∈ carrier → y ∈ carrier → (x ▷ y) ∈ carrier)
(closed_pow : ∀ x : Q, ∀ n : ℤ, x ∈ carrier → x ^ n ∈ carrier)
(closed_one : (1 : Q) ∈ carrier)


variables {Q : Type u} [power_quandle Q]

instance spq_coe_carrier : has_coe (sub_power_quandle Q) (set Q) := ⟨λ spq, spq.carrier⟩

lemma spq_coe_is_carrier (Q1 : sub_power_quandle Q) : ↑Q1 = Q1.carrier := rfl

variables {Q1 : sub_power_quandle Q}

def spq_rhd : Q1 → Q1 → Q1 := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x ▷ y, Q1.closed_rhd x y hx hy⟩

def spq_pow : Q1 → ℤ → Q1 := λ ⟨x, hx⟩ n, ⟨x ^ n, Q1.closed_pow x n hx⟩

def spq_one : Q1 := ⟨1, Q1.closed_one⟩

instance sub_power_quandle_has_rhd : has_rhd Q1 := ⟨spq_rhd⟩

instance sub_power_quandle_has_pow : has_pow Q1 ℤ := ⟨spq_pow⟩

instance sub_power_quandle_has_one : has_one Q1 := ⟨spq_one⟩

lemma spq_rhd_def (a b : Q) (ha : a ∈ Q1.carrier) (hb : b ∈ Q1.carrier) : (⟨a, ha⟩ ▷ ⟨b, hb⟩ : Q1) = ⟨a ▷ b, (Q1.closed_rhd a b ha hb)⟩ := rfl 

lemma spq_pow_def (a : Q) (n : ℤ) (ha : a ∈ Q1.carrier) : (⟨a, ha⟩ ^ n : Q1) = ⟨a ^ n, (Q1.closed_pow a n ha)⟩ := rfl 

lemma spq_one_def : (1 : Q1) = ⟨1, Q1.closed_one⟩ := rfl

lemma coe_rhd (a b : Q1) : (↑a : Q) ▷ (↑b) = ↑(a ▷ b) := 
begin
  cases a with a ha,
  cases b with b hb,
  refl,
end

lemma coe_pow (a : Q1) (n : ℤ) : (↑a : Q) ^ n = ↑(a ^ n) := 
begin
  cases a with a ha,
  refl,
end

lemma coe_one : (↑(1 : Q1) : Q) = 1 := rfl

instance sub_power_quandle_is_pq : power_quandle Q1 := { 
  rhd_dist := begin 
    rintros ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩,
    simp only [spq_rhd_def, subtype.mk_eq_mk],
    apply power_quandle.rhd_dist,
  end,
  rhd_idem := begin 
    rintros ⟨a, ha⟩,
    simp only [spq_rhd_def, subtype.mk_eq_mk],
    apply power_quandle.rhd_idem,
  end,
  pow_one := begin 
    rintros ⟨a, ha⟩,
    simp only [spq_pow_def, subtype.mk_eq_mk],
    apply power_quandle.pow_one,
  end,
  pow_zero := begin 
    rintros ⟨a, ha⟩,
    simp only [spq_pow_def, spq_one_def, subtype.mk_eq_mk],
    apply power_quandle.pow_zero,
  end,
  pow_comp := begin 
    rintros ⟨a, ha⟩ n m,
    simp only [spq_pow_def, subtype.mk_eq_mk],
    apply power_quandle.pow_comp,
  end,
  rhd_one := begin 
    rintros ⟨a, ha⟩,
    simp only [spq_rhd_def, spq_one_def, subtype.mk_eq_mk],
    apply power_quandle.rhd_one,
  end,
  one_rhd := begin 
    rintros ⟨a, ha⟩,
    simp only [spq_rhd_def, spq_one_def, subtype.mk_eq_mk],
    apply power_quandle.one_rhd,
  end,
  pow_rhd := begin 
    rintros ⟨a, ha⟩ ⟨b, hb⟩ n,
    simp only [spq_rhd_def, spq_pow_def, subtype.mk_eq_mk],
    apply power_quandle.pow_rhd,
  end,
  rhd_pow_add := begin 
    rintros ⟨a, ha⟩ ⟨b, hb⟩ n m,
    simp only [spq_rhd_def, spq_pow_def, subtype.mk_eq_mk],
    apply power_quandle.rhd_pow_add,
  end,
  ..sub_power_quandle_has_rhd,
  ..sub_power_quandle_has_pow,
  ..sub_power_quandle_has_one }



end sub_power_quandle
