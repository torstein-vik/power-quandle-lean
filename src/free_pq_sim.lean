
-- Dually-generated sub-pqs: 
-- a, b -> a ▷ b ▷ a ▷ a
-- Seems to be (free_group {a, b}) ▷ ({a, b})^n


import free_pq
import group_theory.free_group

universe u

section free_pq_test

variables {s : Type u}

inductive free_pq_sim (s : Type u)
| one : free_pq_sim
| elem (conj : free_group s) (x : s) (n : ℤ) (hn : n ≠ 0) : free_pq_sim

instance free_pq_sim_has_one : has_one (free_pq_sim s) := ⟨free_pq_sim.one⟩

def free_pq_sim_pow : free_pq_sim s → ℤ → free_pq_sim s
| (free_pq_sim.one) n := free_pq_sim.one
| (free_pq_sim.elem (conj : free_group s) (x : s) (n : ℤ) (hn : n ≠ 0)) k := free_pq_sim.elem conj x (n * k) (begin 
  sorry,
end)


instance free_pq_sim_has_pow : has_pow (free_pq_sim s) := ⟨free_pq_sim_pow⟩

def free_pq_to_free_pq_sim : free_pq s → free_pq_sim s

def free_pq_sim_to_free_pq : free_pq_sim s → free_pq s
| free_pq_sim.one := 1
| (free_pq_sim.elem (conj : free_group s) (x : s) (n : ℤ) (hn : n ≠ 0)) := begin 
  induction conj,
  {
    revert conj,
    fapply list.foldr,
    {
      intros conj core,
      exact ((free_pq_of conj.1) ^ (( if (conj.2) then -1 else 1) : ℤ)) ▷ core,
    },
    {
      exact (free_pq_of x) ^ n,
    },
  },
  {
    simp only [eq_rec_constant],
    induction conj_p,
    simp only [list.foldr, list.foldr_append],
    congr,
    cases conj_p_b,
    {
      simp only [if_true, bool.coe_sort_ff, bool.coe_sort_tt, bool.bnot_false, if_false],
      rw power_quandle.rhd_pow_add,
      norm_num,
      rw power_quandle.pow_zero,
      rw power_quandle.one_rhd,
    },
    {
      simp only [if_true, bool.coe_sort_ff, bool.coe_sort_tt, if_false, bool.bnot_true],
      rw power_quandle.rhd_pow_add,
      norm_num,
      rw power_quandle.pow_zero,
      rw power_quandle.one_rhd,
    },
  },
end

def free_pq_sim_is_sim : free_pq s ≃ free_pq_sim s := { 
  to_fun := sorry,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }

end free_pq_test

