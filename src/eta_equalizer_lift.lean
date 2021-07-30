
import pq_like_equalizer

universe u

section eta_equalizer_lift

variables {Q : Type u} [power_quandle Q]

def eta1 : pq_group Q →* pq_group (pq_group Q) := L_of_morph of of_is_pq_morphism
def eta2 : pq_group (pq_group Q) →* pq_group (pq_group (pq_group Q)) := L_of_morph eta1 (functoriality_group_to_pq eta1)
def eta3 : pq_group (pq_group Q) →* pq_group (pq_group (pq_group Q)) := L_of_morph of of_is_pq_morphism

def lifted_eta_equalizer (Q : Type u) [power_quandle Q] : subgroup (pq_group (pq_group Q)) := { 
  carrier := λ x, eta3 x = eta2 x,
  one_mem' := begin 
    rw set.mem_def,
    simp only [monoid_hom.map_one],
  end,
  mul_mem' := begin 
    intros a b ha hb,
    rw set.mem_def at *,
    simp only [monoid_hom.map_mul, ha, hb],
  end,
  inv_mem' := begin 
    intros x hx,
    rw set.mem_def at *,
    simp only [inv_inj, monoid_hom.map_inv, hx],
  end }

lemma lifted_eta_equalizer_mem_def (x : pq_group (pq_group Q)) (hx : x ∈ lifted_eta_equalizer Q) : eta3 x = eta2 x := hx 
lemma lifted_eta_equalizer_mem_iff (x : pq_group (pq_group Q)) : (x ∈ lifted_eta_equalizer Q) ↔ (eta3 x = eta2 x) := by refl

lemma of_of_in_lifted_eta_equalizer (x : Q) : (of (of x)) ∈ lifted_eta_equalizer Q :=
begin
  rw lifted_eta_equalizer_mem_iff,
  simp only [eta2, eta3, eta1, L_of_morph_of],
end

def eta_equalizer_lift_iso_backward : pq_group (eta_equalizer Q) →* lifted_eta_equalizer Q :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro x,
    cases x with x hx,
    fconstructor,
    exact of x,
    show (of x) ∈ lifted_eta_equalizer Q,
    rw lifted_eta_equalizer_mem_iff,
    simp only [eta2, eta3, L_of_morph_of],
    congr,
    exact hx,
  },
  {
    split,
    {
      intros a b,
      cases a with a ha,
      cases b with b hb,
      simp only,
      have subtype_rw : (⟨a, ha⟩ ▷ ⟨b, hb⟩ : eta_equalizer Q) = ⟨a ▷ b, _⟩ := rfl,
      rw subtype_rw,
      simp only,
      simp_rw ←rhd_of_eq_of_rhd,
      refl,
    },
    {
      intros a n,
      cases a with a ha,
      simp only,
      have subtype_rw : (⟨a, ha⟩ ^ n : eta_equalizer Q) = ⟨a ^ n, _⟩ := rfl,
      rw subtype_rw,
      simp only,
      simp_rw of_pow_eq_pow_of,
      ext1,
      simp only [subgroup.coe_gpow, subtype.coe_mk],
    },
  },
end

theorem eta_equalizer_lift_iso_backward_bijective : function.bijective (eta_equalizer_lift_iso_backward : pq_group (eta_equalizer Q) → lifted_eta_equalizer Q) :=
begin
  split,
  {
    refine eta_equalizer_lift_iso_backward.injective_iff.mpr _,
    intros a ha,
    sorry,
  },
  {
    intros x,
    cases x with x hx,
    revert x,
    refine pq_group_word_induction _ _,
    {
      intros h1,
      use 1,
      refl,
    },
    {
      intros x y hx hxy,
      revert y,
      refine pq_group_word_induction _ _,
      {
        intros h1x,
        simp only [one_mul, of_one] at h1x,
        specialize hx h1x,
        cases hx with z hz,
        use z,
        rw hz,
        simp only [of_one, one_mul],
      },
      {
        intros a b hax habx,
        have : of a * x ∈ lifted_eta_equalizer Q,
        {
          have habx1 := lifted_eta_equalizer_mem_def _ habx,
          simp only [eta1, eta2, eta3, L_of_morph_of, monoid_hom.map_mul] at habx1,
          rw lifted_eta_equalizer_mem_iff,
          simp only [eta1, eta2, eta3, L_of_morph_of, monoid_hom.map_mul],
          sorry,
        },
        specialize hax this,
        cases hax with z hz,
        suffices : ∃ y1 : pq_group (eta_equalizer Q), eta_equalizer_lift_iso_backward y1 = ⟨of y, _⟩,
        {
          cases this with y1 hy1,
          use y1 * z,
          simp only [monoid_hom.map_mul, hz, hy1],
          refl,
        },
        {
          sorry,
        },
        {
          -- For next time: we need to go deeper. Do induction on y.
        },

      },
    },
  },
end

def eta_equalizer_lift_iso : lifted_eta_equalizer Q ≃* pq_group (eta_equalizer Q) := { 
  to_fun := _,
  inv_fun := _,
  left_inv := _,
  right_inv := _,
  map_mul' := _ }


end eta_equalizer_lift