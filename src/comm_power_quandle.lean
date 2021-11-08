
import pq_induction_principles

universe u

section comm_power_quandle

class comm_power_quandle (Q : Type u) extends power_quandle Q :=
(rhd_comm : ∀ a b : Q, a ▷ b = b)

variables {G : Type u} [comm_group G]

instance comm_power_quandle_comm_group : comm_power_quandle G := {
  rhd_comm := begin 
    intros a b,
    simp only [rhd_def_group, mul_comm, inv_mul_cancel_left],
  end }

variables {Q : Type u} [comm_power_quandle Q]

instance pq_group_comm_pq : comm_group (pq_group Q) := { 
  mul_comm := begin 
    intros a b,
    revert b,
    refine pq_group_of_mul_induction _ _,
    {
      rename a x,
      intros a,
      revert x,
      refine pq_group_of_mul_induction _ _,
      {
        intros b,
        rw center_reformulate,
        rw ←rhd_def_group,
        rw rhd_of_eq_of_rhd,
        congr,
        rw comm_power_quandle.rhd_comm,
      },
      {
        intros x y hx hy,
        rw mul_assoc,
        rw hy,
        rw ←mul_assoc,
        rw hx,
        rw ←mul_assoc,
      },
    },
    {
      intros x y hx hy,
      rw mul_assoc,
      rw ←hy,
      rw ←mul_assoc,
      rw ←mul_assoc,
      rw ←hx,
    },
  end,
  ..pq_group_is_group }

end comm_power_quandle

