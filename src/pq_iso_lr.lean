
import pq_to_group

universe u


section lr_direct_prod


variables {G : Type u} [group G]


/-
def lr_to_ker : pq_group G →* (counit : pq_group G → G).ker :=
begin
  sorry,
end
-/

/-
def lr_iso_direct_prod : pq_group G ≃* G × counit.ker :=
begin
  fapply mul_equiv.of_bijective,
end
-/

end lr_direct_prod



section L_iso_of



variables {G H : Type u} [group G] [group H]

lemma L_fun_of (f : G → H) (hf : is_pq_morphism f) (a : G) : (L_of_morph f hf) (of a) = of (f a) :=
begin
  refl,
end

lemma L_iso_of (f : G ≃ H) (hf : is_pq_morphism f) (a : G) : (L_of_morph_iso f hf) (of a) = of (f a) :=
begin
  refl,
end

lemma pq_iso_inv_is_pq_morphism (f : G ≃ H) (hf : is_pq_morphism (f.to_fun)) : is_pq_morphism (f.inv_fun) :=
begin
  split,
  {
      intros a b,
      rw ←f.right_inv a,
      rw ←f.right_inv b,
      rw f.left_inv,
      rw f.left_inv,
      rw ←hf.1,
      rw f.left_inv,
  },
  {
      intros a n,
      rw ←f.right_inv a,
      rw ←hf.2,
      rw f.left_inv,
      rw f.left_inv,
  },
end


lemma pq_iso_eq_one_iff (f : G ≃ H) (hf : is_pq_morphism f) (a : G) (ha : f a = 1) : a = 1 :=
begin
  rw ←equiv.left_inv f a,
  unfold_coes at ha,
  rw ha,
  have hf1 := pq_iso_inv_is_pq_morphism f hf,
  exact pq_morphism_one f.inv_fun hf1,
end

theorem mem_ker_equiv (f : G ≃ H) (hf : is_pq_morphism f) (a : pq_group G) : counit a = 1 ↔ counit (L_of_morph_iso f hf a) = 1 :=
begin
  induction a,
  {
    rw quot_mk_helper,
    induction a,
    {
      rw ←unit_def,
      rw mul_equiv.map_one,
      split,
      intro h, refl,
      intro h, refl,
    },
    {
      rw ←of_def,
      rw counit_of,
      split,
      {
        intro ha,
        rw ha,
        rw of_1_eq_unit,
        rw mul_equiv.map_one,
        refl,
      },
      {
        intro ha,
        rw L_iso_of f hf a at ha,
        rw counit_of (f a) at ha,
        apply pq_iso_eq_one_iff f hf,
        assumption,
      }
    },
    {
      sorry,
    },
    {
      rw ←inv_def,
      rw monoid_hom.map_inv,
      rw inv_eq_one,
      rw mul_equiv.map_inv,
      rw monoid_hom.map_inv,
      rw inv_eq_one,
      exact a_ih,
    },
  },
  {refl,},
end

-- Silly attempt
theorem mem_ker_equiv'' (f : G ≃ H) (hf : is_pq_morphism f) (a : pq_group G) : counit a = 1 ↔ counit (L_of_morph_iso f hf a) = 1 :=
begin
  induction a,
  {
    rw quot_mk_helper,
    split,
    {
      intro ha,
      induction a,
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
    {
      sorry,
    },
  },
  {refl,},
end


theorem mem_ker_equiv' (f : G ≃ H) (hf : is_pq_morphism f) (a : pq_group G) : f (counit a) = counit (L_of_morph_iso f hf a) :=
begin
  induction a,
  {
    rw quot_mk_helper,
    induction a,
    {
      rw ←unit_def,
      rw mul_equiv.map_one,
      sorry,
    },
    {
      rw ←of_def,
      rw counit_of,
      rw L_iso_of f hf a,
      rw counit_of (f a),
    },
    {
      
    },
    {
      rw ←inv_def,
      rw monoid_hom.map_inv,
      rw mul_equiv.map_inv,
      rw monoid_hom.map_inv,
      rw ←a_ih,
      apply pq_morph_pres_inv f hf,
    },
  },
  {refl,},
end

theorem mem_ker_equiv_inv (f : G ≃ H) (hf : is_pq_morphism f) (a : pq_group H) : counit a = 1 ↔ counit ((L_of_morph_iso f hf).inv_fun a) = 1 :=
begin
  rw ←(L_of_morph_iso f hf).right_inv a,
  rw (L_of_morph_iso f hf).left_inv,
  rw mem_ker_equiv f hf,
  refl,
end

theorem counit_ker_iso (f : G ≃ H) (hf : is_pq_morphism f) : (counit : pq_group G →* G).ker ≃* (counit : pq_group H →* H).ker :=
begin
  let Lf := L_of_morph_iso f hf,
  fconstructor,
  {
    rintro ⟨x, hx⟩,
    fconstructor,
    exact Lf x,
    {
      refine counit.mem_ker.mpr _,
      have hx1 := counit.mem_ker.mp (hx),
      rw ←mem_ker_equiv f hf x,
      assumption,
    },
  },
  {
    rintro ⟨x, hx⟩,
    fconstructor,
    exact Lf.inv_fun x,
    {
      refine counit.mem_ker.mpr _,
      have hx1 := counit.mem_ker.mp (hx),
      rw ←mem_ker_equiv_inv f hf x,
      assumption,
    }
  },
  {
    rintro ⟨x, hx⟩,
    simp only [subtype.mk_eq_mk],
    unfold_coes,
    rw mul_equiv.left_inv,
  },
  {
    rintro ⟨x, hx⟩,
    simp only [subtype.mk_eq_mk],
    unfold_coes,
    rw mul_equiv.right_inv,
  },
  {
    intros x y,
    cases x with x hx,
    cases y with y hy,
    simp only,
    sorry,

  },
end


/-
begin
  refine mul_equiv.of_bijective _ _,
  {
    fconstructor,
    {
      rintro ⟨x, hx⟩,
      fconstructor,
      exact L_of_morph f hf x,
      {
        
      },
    },
    {
      refl,
    },
    {
      intros x y,
      sorry,
    },
  },
  {
    simp only [monoid_hom.coe_mk],
    split,
    {
      intros x y hxy,
      cases x with x hx,
      cases y with y hy,
      simp only [subtype.mk_eq_mk] at *,
      apply (L_of_morph_iso f hf hfb).1 hxy,
    },
    {
      intros x,
      cases x with x hx,
      sorry,
    },
  }
end
-/


end L_iso_of
