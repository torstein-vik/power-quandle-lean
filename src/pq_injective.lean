
import eta_injective_pq

universes u1 u2

section pq_injective

variables {Q1 : Type u1} [power_quandle Q1] {Q2 : Type u2} [power_quandle Q2]

lemma L_fun_of (f : Q1 → Q2) (hf : is_pq_morphism f) (a : Q1) : (L_of_morph f hf) (of a) = of (f a) :=
begin
  refl,
end

theorem pq_injective_if_L_injective (f : Q1 → Q2) (hf : is_pq_morphism f) (hLf : function.injective (L_of_morph f hf)) (hQ1 : eta_injective Q1) : function.injective f :=
begin
  intros x y hxy,
  apply hQ1,
  apply hLf,
  rw L_fun_of,
  rw L_fun_of,
  apply congr_arg,
  exact hxy,
end

theorem L_injective_if_pq_injective (f : Q1 → Q2) (hf : is_pq_morphism f) (hfi : function.injective f) (hQ1 : eta_injective Q1) : function.injective (L_of_morph f hf) :=
begin
  refine (L_of_morph f hf).injective_iff.mpr _,
  intros a ha,
  sorry,
end


end pq_injective
