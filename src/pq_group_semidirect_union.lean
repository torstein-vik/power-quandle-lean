
import pq_to_group
import automorphism
import group_theory.semidirect_product

universes u1 u2


section semidirect_union

variables {Q1 : Type u1} {Q2 : Type u2} [power_quandle Q1] [power_quandle Q2]

variables (φ : Q2 → automorphism Q1) (hφ : is_pq_morphism φ)

inductive semidirect_union (Q1 : Type u1) (Q2 : Type u2) [power_quandle Q1] [power_quandle Q2] (φ : Q2 → automorphism Q1) (hφ : is_pq_morphism φ) : Type (max u1 u2)
| inl (x : Q1) : semidirect_union
| inr (x : Q2) : semidirect_union

open semidirect_union

def semidirect_union_rhd : semidirect_union Q1 Q2 φ hφ → semidirect_union Q1 Q2 φ hφ → semidirect_union Q1 Q2 φ hφ
| (inl x) (inl y) := inl (x ▷ y)
| (inl x) (inr y) := inr y
| (inr x) (inr y) := inr (x ▷ y)
| (inr x) (inl y) := inl ((φ x).f y)

instance semidirect_union_has_rhd : has_triangle_right (semidirect_union Q1 Q2 φ hφ) := ⟨semidirect_union_rhd φ hφ⟩

def semidirect_union_pow : semidirect_union Q1 Q2 φ hφ → ℤ → semidirect_union Q1 Q2 φ hφ
| (inl x) n := inl (x ^ n)
| (inr x) n := inr (x ^ n)

instance semidirect_union_has_pow : has_pow (semidirect_union Q1 Q2 φ hφ) ℤ := ⟨semidirect_union_pow φ hφ⟩

def semidirect_union_lhd : semidirect_union Q1 Q2 φ hφ → semidirect_union Q1 Q2 φ hφ → semidirect_union Q1 Q2 φ hφ := λ x y, (x ^ (-1 : ℤ)) ▷ y

instance semidirect_union_has_lhd : has_triangle_left (semidirect_union Q1 Q2 φ hφ) := ⟨semidirect_union_lhd φ hφ⟩

@[simp] lemma rhd_def_semidirect_union_ll (a b : Q1) : (inl a : semidirect_union Q1 Q2 φ hφ) ▷ (inl b) = inl (a ▷ b) := rfl
@[simp] lemma rhd_def_semidirect_union_rr (a b : Q2) : (inr a : semidirect_union Q1 Q2 φ hφ) ▷ (inr b) = inr (a ▷ b) := rfl
@[simp] lemma rhd_def_semidirect_union_lr (a : Q1) (b : Q2) : (inl a : semidirect_union Q1 Q2 φ hφ) ▷ (inr b) = inr (b) := rfl
@[simp] lemma rhd_def_semidirect_union_rl (a : Q2) (b : Q1) : (inr a : semidirect_union Q1 Q2 φ hφ) ▷ (inl b) = inl ((φ a).f b) := rfl

instance semidirect_union_pq : power_quandle (semidirect_union Q1 Q2 φ hφ) := { 
  right_dist := sorry,
  left_dist := sorry,
  right_inv := sorry,
  left_inv := sorry,
  self_idem_right := sorry,
  self_idem_left := sorry,
  pow_1 := sorry,
  pow_comp := sorry,
  q_pow0 := sorry,
  q_pown_right := sorry,
  q_powneg_left := sorry,
  q_powadd := sorry ,
  ..semidirect_union_has_rhd,
  ..semidirect_union_has_lhd,
  ..semidirect_union_has_pow,}

end semidirect_union



section pq_group_semidirect_union


variables {Q1 : Type u1} {Q2 : Type u2} [power_quandle Q1] [power_quandle Q2]

variables (φ : Q2 → automorphism (Q1)) (hφ : is_pq_morphism φ)

def L_of_action (φ : Q2 → automorphism (Q1)) (hφ : is_pq_morphism φ) : pq_group Q2 →* mul_aut (pq_group Q1) :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro x,
    let φx := φ x,
    let φx' : Q1 ≃ Q1 := { 
      to_fun := φx.f,
      inv_fun := φx.finv,
      left_inv := begin
        apply congr_fun,
        exact φx.hfinvf,
      end,
      right_inv := begin
        apply congr_fun,
        exact φx.hffinv, 
      end, 
    },
    refine L_of_morph_iso φx' _,
    exact φx.hf,
  },
  {
    simp only,
    split,
    {
      intros a b,
      simp only,
      rw rhd_def,
      --ext1,
      --simp only [mul_aut.mul_apply],
      rw hφ.1,
      rw rhd_def,
      simp_rw automorphism_f_of_comp,
      simp_rw automorphism_f_of_inverse,
      simp_rw automorphism_finv_of_comp,
      simp_rw automorphism_finv_of_inverse,
      sorry,

    },
    {
      sorry,
    },
  },
end


def pq_group_oplus_to_prod : pq_group (semidirect_union Q1 Q2 φ hφ) →* pq_group Q1 ⋊[L_of_action φ hφ] pq_group Q2 :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro x,
    cases x,
    {
      exact ⟨of x, 1⟩,
    },
    {
      exact ⟨1, of x⟩,
    },
  },
  {
    split,
    {
      intros a b,
      cases a;
      cases b,
      {
        rw rhd_def_semidirect_union_ll,
        simp only,
        rw ←rhd_of_eq_of_rhd,
        rw rhd_def,
        rw rhd_def,
        simp only [semidirect_product.mk_eq_inl_mul_inr, mul_one, monoid_hom.map_mul, eq_self_iff_true, monoid_hom.map_mul_inv,
  mul_left_inj, semidirect_product.inl_inj, monoid_hom.map_one],
      },
      {
        rw rhd_def_semidirect_union_lr,
        simp only,
        rw rhd_def,
        simp only [semidirect_product.mk_eq_inl_mul_inr, mul_one, one_mul, monoid_hom.map_one],
        
      },
      {
        rw rhd_def_union_rl,
        simp only,
        rw rhd_def,
        simp only [one_inv, mul_one, one_mul, prod.inv_mk, mul_right_inv, prod.mk_mul_mk],
      },
      {
        rw rhd_def_union_rr,
        simp only,
        rw ←rhd_of_eq_of_rhd,
        rw rhd_def,
        rw rhd_def,
        simp only [one_inv, mul_one, prod.inv_mk, prod.mk_mul_mk],
      },
    },
    {
      intros a n,
      cases a,
      {
        rw pow_def_union_l,
        simp only,
        rw of_pow_eq_pow_of,
        rw group_prod_pow,
        simp only [one_gpow],
      },
      {
        rw pow_def_union_r,
        simp only,
        rw of_pow_eq_pow_of,
        rw group_prod_pow,
        simp only [one_gpow],
      },
    }
  }
end


def pq_group_semidirect_union : pq_group (semidirect_union Q1 Q2 φ hφ) ≃* pq_group Q1 ⋊[L_of_action φ hφ] pq_group Q2 := { 
  to_fun := sorry,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry,
  map_mul' := sorry }


end pq_group_semidirect_union


