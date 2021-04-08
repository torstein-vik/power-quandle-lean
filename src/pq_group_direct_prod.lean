
import minimal_sub_pq_gen_group
import pq_induction_principles


universe u

section pq_group_direct_prod

variables {G : Type u} [group G]

variables (f : pq_group G ≃* G × (counit : pq_group G →* G).ker)



def pq_group_inclusion : G →* pq_group G := (f.symm.to_monoid_hom).comp (monoid_hom.inl G (counit : pq_group G →* G).ker)

def pq_group_projection : pq_group G →* G := (monoid_hom.fst G (counit : pq_group G →* G).ker).comp (f.to_monoid_hom)

def inclusion_preimage_of : set G := set.preimage (pq_group_inclusion f) (@of_gen G _)

variables (hf : (counit : pq_group G →* G) = (monoid_hom.fst G (counit : pq_group G →* G).ker).comp (f.to_monoid_hom))

include hf

def pq_group_direct_pq_like : G ≃* pq_group (free_gen_group_sub_pq (inclusion_preimage_of f)) := { 
  to_fun := begin
    
    
  end,
  inv_fun := gen_set_counit (inclusion_preimage_of f),
  left_inv := begin 
    sorry,
  end,
  right_inv := begin 
    sorry,
  end,
  map_mul' := _ }


--variables (hf : (counit : pq_group G →* G) = (monoid_hom.fst G (counit : pq_group G →* G).ker).comp (f.to_monoid_hom))

--include hf


/-
def pq_group_direct_pq_like_to_fun : pq_group G →* pq_group (free_gen_group_sub_pq (inclusion_preimage_of f)) :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro g,
    apply of,
    fconstructor,
    exact pq_group_projection f (of g),
    apply gen_in_free_group_sub_pq_carrier,
    unfold inclusion_preimage_of,
    simp only [set.mem_preimage],
    sorry,
  },
  sorry,
end

def pq_group_direct_pq_like_to_aux (x : pq_group G) (g : G) (hx : x = pq_group_inclusion f g) : pq_group (free_gen_group_sub_pq (inclusion_preimage_of f)) :=
begin
  

  induction x,
  {
    rw quot_mk_helper at *,
    induction h : x,
  },
  {
    sorry,
  },
end
-/


/-
theorem inclusion_preimage_of_generates : group_generated_by (inclusion_preimage_of f) :=
begin
  intro x,
  let y := pq_group_inclusion f x,
  have hx : x = pq_group_projection f y,
  {
    simp only [y, pq_group_inclusion, pq_group_projection],
    simp only [mul_equiv.apply_symm_apply, monoid_hom.coe_fst, mul_equiv.coe_to_monoid_hom, function.comp_app, monoid_hom.inl_apply,
  monoid_hom.coe_comp],
  },
  rw hx,
  generalize : y = e,
  revert e,
  apply pq_group_word_induction,
  {
    simp only [monoid_hom.map_one],
    exact generated_by.unit,
  },
  {
    intros a b ha,
    simp only [monoid_hom.map_mul],
    refine generated_by.mul ((pq_group_projection f) (of b)) ((pq_group_projection f) a) _ ha,
    refine generated_by.incl ((pq_group_projection f) (of b)) _,
    unfold inclusion_preimage_of,
    simp only [set.mem_preimage],
    simp only [pq_group_inclusion, pq_group_projection],
    
  },
end
-/
/-
def inclusion_preimage_of_pq : sub_power_quandle G := { 
  carrier := inclusion_preimage_of f,
  closed_rhd := begin 
    intros x y hx hy,
    unfold inclusion_preimage_of at *,
    simp only [set.mem_preimage] at *,
    rw rhd_def,
    simp only [monoid_hom.map_mul, monoid_hom.map_mul_inv],
    rw ←rhd_def,
    refine of_gen_group_sub_pq.closed_rhd _ _ _ _,
    assumption,
    assumption,
  end,
  closed_pow := begin 
    intros x n hx,
    unfold inclusion_preimage_of at *,
    simp only [set.mem_preimage] at *,
    rw monoid_hom.map_gpow,
    refine of_gen_group_sub_pq.closed_pow _ _ _,
    assumption,
  end }
-/

end pq_group_direct_prod
