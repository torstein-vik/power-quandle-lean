
import pq_induce_lhd

universe u

section sub_power_quandle


structure sub_power_quandle (Q : Type u) [power_quandle Q] := 
(carrier : set Q)
(closed_rhd : ∀ x y : Q, x ∈ carrier → y ∈ carrier → (x ▷ y) ∈ carrier)
(closed_pow : ∀ x : Q, ∀ n : ℤ, x ∈ carrier → x ^ n ∈ carrier)


variables {Q : Type u} [power_quandle Q]

instance spq_coe_carrier : has_coe (sub_power_quandle Q) (set Q) := ⟨λ spq, spq.carrier⟩

variables {Q1 : sub_power_quandle Q}

def spq_rhd : Q1 → Q1 → Q1 := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x ▷ y, Q1.closed_rhd x y hx hy⟩

def spq_pow : Q1 → ℤ → Q1 := λ ⟨x, hx⟩ n, ⟨x ^ n, Q1.closed_pow x n hx⟩

instance sub_power_quandle_has_rhd : has_triangle_right Q1 := ⟨spq_rhd⟩

instance sub_power_quandle_has_pow : has_pow Q1 ℤ := ⟨spq_pow⟩

lemma spq_rhd_def (a b : Q) (ha : a ∈ Q1.carrier) (hb : b ∈ Q1.carrier) : (⟨a, ha⟩ ▷ ⟨b, hb⟩ : Q1) = ⟨a ▷ b, (Q1.closed_rhd a b ha hb)⟩ := rfl 

lemma spq_pow_def (a : Q) (n : ℤ) (ha : a ∈ Q1.carrier) : (⟨a, ha⟩ ^ n : Q1) = ⟨a ^ n, (Q1.closed_pow a n ha)⟩ := rfl 


instance sub_power_quandle_is_pq : power_quandle Q1 :=
begin
  apply induce_lhd,
  {
    intros a b c,
    ext1,
    cases a with a ha,
    cases b with b hb,
    cases c with c hc,
    repeat {rw spq_rhd_def},
    simp only [subtype.coe_mk],
    exact rack.right_dist a b c,
  },
  {
    intros a,
    ext1,
    cases a with a ha,
    repeat {rw spq_rhd_def},
    simp only [subtype.coe_mk],
    exact quandle.self_idem_right a,
  },
  {
    intros a,
    ext1,
    cases a with a ha,
    rw spq_pow_def,
    simp only [subtype.coe_mk],
    exact power_quandle.pow_1 a,
  },
  {
    intros a n m,
    ext1,
    cases a with a ha,
    repeat {rw spq_pow_def},
    simp only [subtype.coe_mk],
    exact power_quandle.pow_comp a n m,
  },
  {
    intros a b,
    ext1,
    cases a with a ha,
    cases b with b hb,
    repeat {rw spq_pow_def},
    repeat {rw spq_rhd_def},
    simp only [subtype.coe_mk],
    exact power_quandle.q_pow0 a b,
  },
  {
    intros a b,
    ext1,
    cases a with a ha,
    cases b with b hb,
    repeat {rw spq_pow_def},
    repeat {rw spq_rhd_def},
    simp only [subtype.coe_mk],
    exact pow_0_rhd a b,
  },
  {
    intros a,
    ext1,
    cases a with a ha,
    repeat {rw spq_pow_def},
    repeat {rw spq_rhd_def},
    simp only [subtype.coe_mk],
    rw ←power_quandle.q_powneg_left,
    exact quandle.self_idem_left a,
  },
  {
    intros a b n,
    ext1,
    cases a with a ha,
    cases b with b hb,
    repeat {rw spq_pow_def},
    repeat {rw spq_rhd_def},
    repeat {rw spq_pow_def},
    simp only [subtype.coe_mk],
    exact power_quandle.q_pown_right a b n,
  },
  {
    intros a b n m,
    ext1,
    cases a with a ha,
    cases b with b hb,
    repeat {rw spq_pow_def},
    repeat {rw spq_rhd_def},
    repeat {rw spq_pow_def},
    simp only [subtype.coe_mk],
    exact power_quandle.q_powadd a b n m,
  },
end



end sub_power_quandle
