
import pq_to_group

import tactic

universes u v

section counit_ker_abelian

variables {G : Type u} [group G]


lemma of_inv_group : ∀ x : G, of (x⁻¹) = (of x)⁻¹ :=
begin
  intro x,
  repeat {rw ←gpow_neg_one},
  rw of_pow_eq_pow_of,
end

theorem inner_aut_eq : ∀ x y : pq_group G, x ▷ y = (of (counit x)) ▷ y :=
begin
  intros x,
  induction x,
  {
    rw quot_mk_helper,
    induction x,
    {
      intro y,
      rw ←unit_def,
      apply congr_arg (λ a, a ▷ y),
      rw monoid_hom.map_one,
      rw of_1_eq_unit,
    },
    {
      intro y,
      rw ←of_def,
      rw counit_of,
    },
    {
      intro y,

      rw counit_mul,
      rw ←mul_def,
      
      rw mul_rhd,
      rw x_ih_b,
      rw x_ih_a,

      rw ←mul_rhd,
      

      induction y,
      {
        rw quot_mk_helper at *,
        induction y,
        {
          rw ←unit_def,
          repeat {rw power_quandle.rhd_one},
        },
        {
          repeat {rw ←of_def at *},
          rw rhd_def_group,
          rw rhd_def_group,
          have halg_rw_1 : ∀ a b c : pq_group G, a*b*c*(a*b)⁻¹ = a*(b*c*b⁻¹)*a⁻¹,
          {
            intros a b c,
            group,
          },
          rw halg_rw_1,
          repeat {rw rhd_eq_conj},
          rw mul_rhd,
        },
        {
          rw ←mul_def,
          rw rhd_mul,
          rw rhd_mul,
          rw y_ih_a,
          rw y_ih_b,
        },
        {
          rw ←inv_def,
          rw rhd_inv,
          rw y_ih,
          rw rhd_inv,
        },
      },
      {refl,},
      
    },
    {
      /-
      intro y,
      rw ←inv_def,
      have hx := x_ih (⟦x_a⟧⁻¹▷⟦x_a⟧⁻¹▷y),
      rw ←mul_rhd_eq_rhd at hx,
      simp only [mul_right_inv] at hx,
      rw one_rhd at hx,
      rw hx,
      -/
      intro y,
      rw ←inv_def,
      have hx := x_ih (⟦x_a⟧⁻¹▷y),
      rw ←mul_rhd at hx,
      simp only [mul_right_inv] at hx,
      rw power_quandle.one_rhd at hx,
      --rw hx,
      rw monoid_hom.map_inv,
      rw of_inv_group,
      rw hx,
      rw ←mul_rhd ((of _) ⁻¹),
      simp only [mul_left_inv],
      rw ←hx,
      rw power_quandle.one_rhd,
    }
  },
  {intro y, refl,},
end 


theorem counit_ker_center : ∀ a : ((counit : pq_group G →* G).ker), ∀ b : pq_group G, ↑a * b = b * a := 
begin
  intros a b,
  cases a with a ha,
  simp only [subtype.coe_mk],
  rw center_reformulate,
  rw ←rhd_def_group,
  rw inner_aut_eq,
  have ha1 : counit a = 1 := ha,
  rw ha1,
  rw of_1_eq_unit,
  rw power_quandle.one_rhd,
end

theorem counit_ker_sub_center : ((counit : pq_group G →* G).ker) ≤ subgroup.center (pq_group G) :=
begin
  intros x hx,
  intro y,
  apply eq.symm,
  apply counit_ker_center ⟨x, hx⟩ y,
end

theorem counit_ker_abelian : ∀ a b : ((counit : pq_group G →* G).ker), a * b = b * a :=
begin
  intros a b,
  cases b with b hb,
  ext1,
  simp only [subgroup.coe_mul, subtype.coe_mk],
  apply counit_ker_center,
end

lemma counit_ker_rhd : ∀ a b : ((counit : pq_group G →* G).ker), a ▷ b = b :=
begin 
  intros a b,
  rw rhd_def_group,
  rw counit_ker_abelian,
  group,
end

lemma counit_ker_abelian_counit (a b : pq_group G) (ha : counit a = 1) : a * b = b * a :=
begin
  suffices : ↑(⟨a, ha⟩ : (counit : pq_group G →* G).ker) * b = b * a,
  simp only [subtype.coe_mk] at this,
  exact this,
  rw counit_ker_center,
  refl,
end

lemma counit_ker_rhd_left_counit (a b : pq_group G) (ha : counit a = 1) : a ▷ b = b :=
begin
  rw rhd_def_group,
  rw counit_ker_abelian_counit a,
  simp only [mul_inv_cancel_right],
  exact ha,
end

lemma counit_ker_rhd_right_counit (a b : pq_group G) (ha : counit a = 1) : b ▷ a = a :=
begin
  rw rhd_def_group,
  rw mul_assoc,
  rw counit_ker_abelian_counit a,
  simp only [mul_inv_cancel_left],
  exact ha,
end

/-
instance counit_ker_comm : comm_group ((counit : pq_group G →* G).ker) := {
  mul_comm := begin
    exact counit_ker_abelian,
  end ,
  ..
}
-/

end counit_ker_abelian


section phi_ker

variables {G : Type u} [group G]

/-
@[ext]
structure deg (G : Type u) [group G] := (g : G)

instance degen_pq_G : power_quandle (deg G) := { 
  triangle_left := λ x y, x,
  triangle_right := λ x y, y,
  right_dist := begin intros a b c, refl, end,
  left_dist := begin intros a b c, refl, end,
  right_inv := begin intros a b, refl, end,
  left_inv := begin intros a b, refl, end,
  self_idem_right := begin intro a, refl, end,
  self_idem_left := begin intro a, refl, end,
  pow := λ x n, ⟨x.g ^ n⟩,
  pow_1 := begin intro a, cases a, ext, simp only [gpow_one], end,
  pow_comp := begin intros a n m, cases a, ext, simp only, exact power_quandle.pow_comp a n m, end,
  q_pow0 := begin intros a b, refl, end,
  q_pown_right := begin intros a b n, refl, end,
  q_powneg_left := begin intros a b, refl, end,
  q_powadd := begin intros a b n m, refl, end }

lemma deg_rhd_def : ∀ a b : (deg G), a ▷ b = b :=
begin
  intros a b,
  refl,
end

lemma deg_pow_def : ∀ a : (deg G), ∀ n : ℤ, a ^ n = ⟨a.g ^ n⟩ :=
begin
  intros a n,
  refl,
end
-/
notation `kerc` G := (counit : pq_group G →* G).ker


def φ' : G × G → kerc G := λ ⟨x, y⟩, ⟨of x * of y * (of (x*y))⁻¹, begin 
  refine counit.mem_ker.mpr _,
  repeat {rw monoid_hom.map_mul},
  rw monoid_hom.map_inv,
  repeat {rw counit_of},
  group,
end⟩ 


theorem φ'_is_cocycle : ∀ g h k : G, φ'(g, h) * φ'(g * h, k) = φ'(g, h * k) * φ'(h ,k) :=
begin
  intros g h k,
  rw counit_ker_abelian (φ' (g, h * k))  (φ' (h, k)),
  unfold φ',
  ext1,
  simp only [subgroup.coe_mul, subgroup.coe_mk],
  have alg_rw : of h * of k * (of (h * k))⁻¹ * (of g * of (h * k) * (of (g * (h * k)))⁻¹) = (of h * (of k * ((of (h * k))⁻¹ * of g * ((of (h * k))⁻¹)⁻¹) * (of k)⁻¹) * (of h)⁻¹ * of h * of k) * (of (g * (h * k)))⁻¹,
  {
    group,
  },
  rw alg_rw,
  clear alg_rw,
  rw ←rhd_def_group,
  rw ←rhd_def_group,
  rw ←rhd_def_group,
  rw ←mul_assoc g h k,
  group,
  rw ←of_pow_eq_pow_of,
  repeat {rw rhd_of_eq_of_rhd},
  repeat {rw rhd_def_group},
  group,
end
 

end phi_ker


section center_LR_morph

variables {G : Type u} [group G]



def center_LR_morph_fun : subgroup.center (pq_group G) → subgroup.center (G) :=
begin
  intro x,
  cases x with x hx,
  fconstructor,
  exact counit x,
  intro y,
  specialize hx (of y),
  have hx1 := congr_arg counit hx,
  repeat {rw monoid_hom.map_mul at hx1},
  repeat {rw counit_of at hx1},
  exact hx1,
end


def center_LR_morph : subgroup.center (pq_group G) →* subgroup.center (G) := ⟨center_LR_morph_fun, begin
  have one_rw : (1 : subgroup.center (pq_group G)) = ⟨1, _⟩ := rfl,
  rw one_rw,
  unfold center_LR_morph_fun,
  ext1,
  simp only [subgroup.coe_one, subtype.coe_mk, monoid_hom.map_one],
end, begin 
  intros x y,
  cases x with x hx,
  cases y with y hy,
  have prod_rw : (⟨x, hx⟩ * ⟨y, hy⟩ : subgroup.center (pq_group G)) = ⟨x * y, _⟩ := rfl,
  rw prod_rw,
  unfold center_LR_morph_fun,
  ext1,
  simp only [monoid_hom.map_mul, subgroup.coe_mul, subtype.coe_mk],
end⟩


noncomputable theorem counit_ker_iso_center_LR_morph_ker : (counit : pq_group G →* G).ker ≃* (center_LR_morph : subgroup.center (pq_group G) →* subgroup.center (G) ).ker := 
begin
  fapply mul_equiv.of_bijective,
  fconstructor,
  {
    intro x,
    cases x with x hx,
    fconstructor,
    fconstructor,
    exact x,

    apply counit_ker_sub_center,
    exact hx,
    ext1,
    exact hx,
  },
  {
    refl,
  },
  {
    intros x y,
    cases x with x hx,
    cases y with y hy,
    ext1,
    ext1,
    have prod_rw : (⟨x, hx⟩ * ⟨y, hy⟩ : ((counit : pq_group G →* G).ker)) = ⟨x * y, _⟩ := rfl,
    rw prod_rw,
    simp only [subgroup.coe_mul, subtype.coe_mk],
  },
  {
    split,
    {
      simp only [monoid_hom.coe_mk],
      intros x y,
      cases x with x hx,
      cases y with y hy,
      simp only [imp_self, subtype.mk_eq_mk],
    },
    {
      simp only [monoid_hom.coe_mk],
      intro x,
      cases x with x hx,
      cases x with x hx1,
      fconstructor,
      fconstructor,
      exact x,
      {
        have hx2 : center_LR_morph ⟨x, _⟩ = 1 := hx,
        injections_and_clear,
        exact h_1,
      },
      refl,
    },
  }
end

end center_LR_morph
