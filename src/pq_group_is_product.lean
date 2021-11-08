

-- Idea: use computation given isomorphism with A × G to obtain pq-like perhaps

import pq_group_homo_locus_pres_iso_ker_counit

universe u

section pq_group_is_product

variables {G : Type u} [group G]

def pq_group_iso_prod_to_homo_locus_lang (G_iso : pq_group G ≃* (counit : pq_group G →* G).ker × G) : homo_locus_pres_prod G ≃* (homo_locus_pres G) × G :=
begin
  refine mul_equiv.trans pq_group_homo_locus_pres_prod_iso.symm _,
  refine mul_equiv.trans G_iso _,
  have counit_ker_iso : (counit : pq_group G →* G).ker ≃* homo_locus_pres G := homo_locus_pres_iso,
  refine { 
    to_fun := λ x, (counit_ker_iso x.1, x.2),
    inv_fun := λ x, (counit_ker_iso.symm x.1, x.2),
    left_inv := _,
    right_inv := _,
    map_mul' := _, 
  },
  {
    intros x,
    simp only,
    rw mul_equiv.symm_apply_apply,
    simp only [prod.mk.eta],
  },
  {
    intros x,
    simp only,
    rw mul_equiv.apply_symm_apply,
    simp only [prod.mk.eta],
  },
  {
    intros x y,
    simp only [prod.snd_mul, prod.fst_mul, mul_equiv.map_mul, prod.mk_mul_mk],
  },
end

def pq_group_iso_prod_pres_embed (iso : homo_locus_pres_prod G ≃* (homo_locus_pres G) × G) : G →* homo_locus_pres G := ⟨λ x, (iso.symm (1, x)).x, begin 
  have : ((1, 1) : ((homo_locus_pres G) × G)) = 1 := rfl,
  rw this,
  simp only [mul_equiv.map_one],
  refl,
end, begin 
  intros x y,
  have : ((1, x * y) : ((homo_locus_pres G) × G)) = (1, x) * (1, y),
  {
    sorry,
  },
  rw this,
  simp only [mul_equiv.map_mul],
  rw homo_locus_pres_prod_mul_def_unsplit,
  simp only [mul_right_eq_self],
end⟩

end pq_group_is_product
