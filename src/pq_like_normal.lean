
import minimal_sub_pq
import sub_pq_normal

universe u

section pq_like_normal

variables {Q : Type u} [power_quandle Q]

theorem pq_like_normal : sub_pq_normal (gen_group_sub_pq (@of_gen_group_sub_pq Q _)) :=
begin
  intros x y,
  cases y with y hy,
  simp only [subtype.coe_mk],
  cases hy with z hz,
  rw hz,
  rw set.mem_def,
  unfold gen_group_sub_pq,
  simp only,
  unfold of_gen_group_sub_pq,
  simp only,
  unfold of_gen,
  sorry,
  --use ((counit x) ▷ z : Q),

end


end pq_like_normal
