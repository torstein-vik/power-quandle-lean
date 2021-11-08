
import pq_like_equalizer_util

universe u

section pq_like_equalizer_rel_induction

variables {Q : Type u} [power_quandle Q]

theorem eta_equalizer_inclusion_injective : function.injective (pq_group_eta_equalizer_inclusion : pq_group (eta_equalizer Q) → pq_group (pq_group Q)) :=
begin
  refine pq_group_eta_equalizer_inclusion.injective_iff.mpr _,
  intros a ha,
  induction a,
  {
    rw quot_mk_helper at *,
    unfold pq_group_eta_equalizer_inclusion at ha,
    unfold L_of_morph at ha,
    simp only [monoid_hom.coe_mk] at ha,
    unfold L_of_morph_fun at ha,
    simp only [quotient.lift_on_beta] at ha,
    have ha1 := quotient.exact ha,
    clear ha,
    rename ha1 ha,
    cases ha,
    sorry,
  },
  {refl},
end

end pq_like_equalizer_rel_induction
