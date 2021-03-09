
import pq_to_group
import counit_ker_abelian


universes u1 u2 u3

section pq_like

variables {QG : Type u1} {QH : Type u2} [power_quandle QG] [power_quandle QH]
--variables {G : Type u} {H : Type v} [group G] [group H]

--variables {hG : G ≃* pq_group QG} {hH : H ≃* pq_group QH}

--include QG QH hG hH

lemma of_is_pq_morphism : is_pq_morphism (of : QH → pq_group QH) :=
begin
  split,
  {
    intros a b,
    rw rhd_of_eq_of_rhd,
  },
  {
    intros a n,
    rw of_pow_eq_pow_of,
  },
end

def pq_like_morphism (f : pq_group QG ≃ pq_group QH) (hf : is_pq_morphism f) : pq_group QG →* pq_group QH :=
begin
  fconstructor,
  {
    let L_of := L_of_morph (of : QG → pq_group QG) of_is_pq_morphism,
    let L_f := L_of_morph f hf,
    exact (counit ∘ L_f ∘ L_of),
  },
  {
    simp only [function.comp_app, mul_equiv.map_one, monoid_hom.map_one],
  },
  {
    simp only [forall_const, monoid_hom.map_mul, eq_self_iff_true, function.comp_app, mul_equiv.map_mul],
  },
end


lemma L_fun_of_2 (f : QG → QH) (hf : is_pq_morphism f) (a : QG) : (L_of_morph f hf) (of a) = of (f a) :=
begin
  refl,
end



lemma pq_like_morphism_is_f_on_of (f : pq_group QG ≃ pq_group QH) (hf : is_pq_morphism f) (x : QG) : (f : pq_group QG → pq_group QH) (of x) = (pq_like_morphism f hf) (of x) :=
begin
  unfold pq_like_morphism,
  simp only [function.comp_app, monoid_hom.coe_mk],
  rw L_fun_of_2,
  rw L_fun_of_2,
  rw counit_of,
end

variables {QK : Type u3} [power_quandle QK]

lemma pq_like_morphism_functoriality_pre (f : pq_group QG ≃ pq_group QH) (hf : is_pq_morphism f) (g : pq_group QH ≃ pq_group QK) (hg : is_pq_morphism g) (hfg : is_pq_morphism (f.trans g)) : 
  (pq_like_morphism g hg) ∘ (pq_like_morphism f hf) = (pq_like_morphism (f.trans g) hfg) :=
begin
  funext,
  simp only [function.comp_app],
  induction x,
  {
    rw quot_mk_helper,
    induction x,
    {
      sorry,
    },
    {
      rw ←of_def,
      rw ←pq_like_morphism_is_f_on_of,
      rw ←pq_like_morphism_is_f_on_of,
      
      sorry,
    },
    {
      rw ←mul_def,
      simp only [monoid_hom.map_mul],
      rw x_ih_a,
      rw x_ih_b,
    },
    {
      sorry,
    },
  },
  {refl,},
end

--lemma pq_like_morphism 

lemma pq_like_morphism_inv_on_of (f : pq_group QG ≃ pq_group QH) (hf : is_pq_morphism f) (x : QG) : f.symm (pq_like_morphism f hf (of x)) = of x :=
begin
  unfold pq_like_morphism,
  simp only [function.comp_app, monoid_hom.coe_mk],
  rw L_fun_of_2,
  rw L_fun_of_2,
  rw counit_of,
  simp only [equiv.symm_apply_apply],
end

/-
theorem pq_like_morphism_kernel (f : pq_group QG ≃ pq_group QH) (hf : is_pq_morphism f) (x : pq_group QG) (hx : pq_like_morphism f hf x = 1) : x = 1 :=
begin
  induction x,
  {
    rw quot_mk_helper at *,
    induction x,
    {
      sorry,
    },
    {
      sorry,
    },
    {
      sorry,
    },
    {
      sorry,
    },
  },
  {refl,},
end
-/


theorem pq_like_morphism_surjective (f : pq_group QG ≃ pq_group QH) (hf : is_pq_morphism f) : function.surjective (pq_like_morphism f hf) :=
begin
  intro x,
  induction x,
  {
    rw quot_mk_helper,
    induction x,
    {
      sorry,
    },
    {
      rw ←of_def,
      use (f.symm (of x)),
      sorry
    },
    {
      sorry,
    },
    {
      sorry,
    },
  },
  {refl,},
end


theorem pq_like_morphism_inv (f : pq_group QG ≃ pq_group QH) (hf1 : is_pq_morphism f) (hf2 : is_pq_morphism f.symm) : (pq_like_morphism f hf1) ∘ (pq_like_morphism f.symm hf2) = id :=
begin
  funext,
  simp only [id.def, function.comp_app],
  induction x,
  {
    rw quot_mk_helper,
    induction x,
    {
      rw incl_unit_eq_unit,
      simp only [monoid_hom.map_one],
    },
    {
      rw ←of_def,
      rw ←pq_like_morphism_is_f_on_of f.symm hf2 x,
      --unfold pq_like_morphism,
      --simp only [function.comp_app, monoid_hom.coe_mk],
      --rw L_fun_of,
      --rw L_fun_of,
      --rw counit_of,
      sorry,
    },
    {
      rw ←mul_def,
      simp only [monoid_hom.map_mul],
      rw x_ih_a,
      rw x_ih_b,
    },
    {
      rw ←inv_def,
      simp only [inv_inj, monoid_hom.map_inv],
      assumption,
    },
  },
  {refl,},
end



end pq_like


section pq_like_split

variables {Q : Type u1} [power_quandle Q]


def counit_L_of (x : pq_group Q) : counit ((L_of_morph of of_is_pq_morphism) x) = x :=
begin
  induction x,
  {
    rw quot_mk_helper,
    induction x,
    {
      rw incl_unit_eq_unit,
      simp only [monoid_hom.map_one],
    },
    {
      rw ←of_def,
      refl,
    },
    {
      rw ←mul_def,
      simp only [monoid_hom.map_mul],
      rw x_ih_a,
      rw x_ih_b,
    },
    {
      rw ←inv_def,
      simp only [inv_inj, monoid_hom.map_inv],
      assumption,
    },
  },
  {refl,},
end

def left_split_fun : (pq_group (pq_group Q)) → (counit : pq_group (pq_group Q) →* (pq_group Q)).ker :=
begin
  intro x,
  fconstructor,
  exact x * ((L_of_morph of of_is_pq_morphism) (counit x))⁻¹,
  refine counit.mem_ker.mpr _,
  simp only [monoid_hom.map_mul, monoid_hom.map_inv],
  rw counit_L_of,
  simp only [mul_right_inv],
end

lemma left_split_fun_def (x : pq_group (pq_group Q)) : x * ((L_of_morph of of_is_pq_morphism) (counit x))⁻¹  = ↑(left_split_fun x) := rfl

lemma left_split_coe_commutes (x y : pq_group (pq_group Q)) : x * ↑(left_split_fun y) = ↑(left_split_fun y) * x :=
begin
  rw counit_ker_center,
end

def left_split_hom : (pq_group (pq_group Q)) →* (counit : pq_group (pq_group Q) →* (pq_group Q)).ker :=
begin
  fconstructor,
  exact left_split_fun,
  {
    unfold left_split_fun,
    simp only [one_inv, mul_one, monoid_hom.map_one],
    refl,
  },
  {
    intros a b,
    unfold left_split_fun,
    ext1,
    simp only [mul_inv_rev, monoid_hom.map_mul, subgroup.coe_mul, subtype.coe_mk],
    rw mul_assoc,
    rw ←mul_assoc b, 
    rw left_split_fun_def b,
    rw ←mul_assoc,
    rw left_split_coe_commutes,
    rw left_split_coe_commutes,
    rw mul_assoc,
  },
end


theorem left_split_hom_is_left_split (x : (counit : pq_group (pq_group Q) →* (pq_group Q)).ker) : left_split_hom (↑x) = x :=
begin
  cases x with x hx,
  unfold left_split_hom,
  simp only [monoid_hom.coe_mk, subtype.coe_mk],
  unfold left_split_fun,
  ext1,
  simp only [subtype.coe_mk],
  suffices : counit x = 1,
  rw this,
  simp only [mul_one, monoid_hom.map_one],
  simp only [one_inv, mul_one],
  exact hx,
end


end pq_like_split

