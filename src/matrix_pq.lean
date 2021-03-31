
import data.zmod.basic
import pq_induce_lhd


universe u

section matrix_pq

structure matrix_pq_prop {α : Type u} [has_pow α ℤ] (rhd : α → α → ℤ) :=
(pow_one : ∀ a : α, a ^ (1 : ℤ) = a)
(pow_comp : ∀ a : α, ∀ n m : ℤ, (a ^ n) ^ m = a ^ (n * m))
(rhd_pow : ∀ a b : α, ∀ n : ℤ, rhd a (b ^ n) = rhd a b)
(pow_zero_rhd : ∀ a b : α, rhd (a ^ (0 : ℤ)) b = 1)
(rhd_self : ∀ a : α, rhd a a = 1)
(rhd_self_pow_neg_one : ∀ a : α, rhd (a ^ (-1 : ℤ)) a = 1)

structure matrix_pq {α : Type u} [has_pow α ℤ] (rhd : α → α → ℤ) (hα : matrix_pq_prop rhd) :=  (val : α)

variables {α : Type u} [has_pow α ℤ] {rhd : α → α → ℤ} {hα : matrix_pq_prop rhd}

instance matrix_pq_has_pow : has_pow (matrix_pq rhd hα) ℤ := ⟨λ x n, ⟨x.val ^ n⟩⟩

lemma matrix_pq_pow_def (x : matrix_pq rhd hα) (n : ℤ) : x ^ n = ⟨x.val ^ n⟩ := rfl

def matrix_pq_rhd (a b : matrix_pq rhd hα) : matrix_pq rhd hα := b ^ (rhd a.val b.val)

instance matrix_pq_has_rhd : has_triangle_right (matrix_pq rhd hα) := ⟨matrix_pq_rhd⟩

lemma matrix_pq_rhd_def (a b : matrix_pq rhd hα) : a ▷ b = b ^ (rhd a.val b.val) := rfl

instance matrix_pq_power_quandle : power_quandle (matrix_pq rhd hα) :=
begin
  apply induce_lhd,
  {
    rintros ⟨a⟩ ⟨b⟩ ⟨c⟩,
    simp only [matrix_pq_pow_def, matrix_pq_rhd_def],
    repeat {rw hα.pow_comp},
    apply congr_arg,
    repeat {rw hα.rhd_pow},
    rw mul_comm,
    apply congr_arg,
    sorry,
  },
  {
    rintro ⟨a⟩,
    simp only [matrix_pq_pow_def, matrix_pq_rhd_def],
    rw hα.rhd_self,
    rw hα.pow_one,
  },
  {
    rintro ⟨a⟩,
    simp only [matrix_pq_pow_def, matrix_pq_rhd_def],
    rw hα.pow_one,
  },
  {
    rintros ⟨a⟩ n m,
    simp only [matrix_pq_pow_def, matrix_pq_rhd_def],
    rw hα.pow_comp,
  },
  {
    rintros ⟨a⟩ ⟨b⟩,
    simp only [matrix_pq_pow_def, matrix_pq_rhd_def],
    rw hα.rhd_pow,
    rw hα.pow_comp,
    apply congr_arg,
    simp only [zero_mul],
  },
  {
    rintros ⟨a⟩ ⟨b⟩,
    simp only [matrix_pq_pow_def, matrix_pq_rhd_def],
    rw hα.pow_zero_rhd,
    rw hα.pow_one,
  },
  {
    rintros ⟨a⟩,
    simp only [matrix_pq_pow_def, matrix_pq_rhd_def],
    rw hα.rhd_self_pow_neg_one,
    rw hα.pow_one,
  },
  {
    rintros ⟨a⟩ ⟨b⟩ n,
    simp only [matrix_pq_pow_def, matrix_pq_rhd_def],
    simp only [hα.pow_comp],
    apply congr_arg,
    rw hα.rhd_pow,
    rw mul_comm,
  },
  {
    rintros ⟨a⟩ ⟨b⟩ n m,
    simp only [matrix_pq_pow_def, matrix_pq_rhd_def],
    simp only [hα.pow_comp, hα.rhd_pow],
    apply congr_arg,
    sorry,
  },
end


end matrix_pq
