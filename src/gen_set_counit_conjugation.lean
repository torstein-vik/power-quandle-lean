
import minimal_sub_pq_gen_group

universe u

section gen_set_counit_conjugation

variables {G : Type u} [group G]



theorem gen_set_counit_conjugation (gen : set G) (a b : pq_group (free_gen_group_sub_pq gen)) : a ▷ b = (of (gen_set_counit gen a)) ▷ b :=
begin
  sorry,
end




end gen_set_counit_conjugation
