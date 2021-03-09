
import .pq_to_group
import algebra.big_operators.basic
import data.finset.basic
import data.finset.pi

universe u

section abelian_pq_group

open_locale big_operators

variables {G : Type u} [comm_group G] [fintype G]

instance fintype_subgroup : fintype (subgroup G) := sorry

instance pq_comm_group : comm_group (pq_group G) := {
    mul_comm := begin
        intros a b,
        induction a,
        {
            rw quot_mk_helper,
            induction a,
            {
                rw incl_unit_eq_unit,
                simp,
            },
            {
                induction b,
                {
                    rw quot_mk_helper,
                    induction b,
                    {
                        rw incl_unit_eq_unit,
                        simp,
                    },
                    {
                        repeat {rw ←of_def},
                        apply pq_group_commute,
                        apply mul_comm,
                    },
                    {
                        rw ←mul_def,
                        rw mul_assoc,
                        rw ←b_ih_b,
                        rw ←mul_assoc,
                        rw b_ih_a,
                        rw mul_assoc,
                    },
                    {
                        rw ←inv_def,
                        apply commute.inv_right,
                        exact b_ih,
                    }
                },
                {refl,},
            },
            {
                rw ←mul_def,
                rw mul_assoc,
                rw a_ih_b,
                rw ←mul_assoc,
                rw a_ih_a,
                rw mul_assoc,
            },
            {
                rw ←inv_def,
                apply commute.inv_left,
                exact a_ih,
            },
        },
        {refl,},
    end,
    ..pq_group_is_group
}


noncomputable def max_cyclic_sub : finset (subgroup G) := {x ∈ finset.univ | is_cyclic x ∧ ¬ ∃ y : subgroup G, x ≤ y ∧ is_cyclic y}

local notation `MCS` := @max_cyclic_sub G _ _

def Hpre := Π (a : (↑MCS : set (subgroup G))), (a : subgroup G)

local notation `H` := @Hpre G _ _

instance H_is_group : comm_group H := sorry

noncomputable def f_H_to_pq (f : H) : pq_group G := ∏ x in (finset.univ), of (f x)


theorem pq_group_iso_H : pq_group G ≃* H := sorry


end abelian_pq_group
