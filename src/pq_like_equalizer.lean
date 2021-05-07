
import pq_induction_principles
import minimal_sub_pq_gen_group


universe u

section pq_like_equalizer


variables {Q : Type u} [power_quandle Q]

def eta_equalizer (Q : Type u) [power_quandle Q] : sub_power_quandle (pq_group Q) := { 
  carrier := λ x, of x = (L_of_morph of of_is_pq_morphism) x,
  closed_rhd := begin 
    intros x y hx hy,
    rw set.mem_def at *,
    rw ←rhd_of_eq_of_rhd,
    rw rhd_def x y,
    simp only [monoid_hom.map_mul, monoid_hom.map_mul_inv],
    rw ←rhd_def,
    apply congr_arg2,
    assumption,
    assumption,
  end,
  closed_pow := begin 
    intros x n hx,
    rw set.mem_def at *,
    rw of_pow_eq_pow_of,
    rw monoid_hom.map_gpow,
    rw hx,
  end }


def eta_equalizer_iso_forward : pq_group (eta_equalizer Q) →* pq_group Q :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro x,
    cases x with x hx,
    exact x,
  },
  {
    split,
    {
      intros a b,
      cases a with a ha,
      cases b with b hb,
      simp only,
      have subtype_rhd : (⟨a, ha⟩ ▷ ⟨b, hb⟩ : eta_equalizer Q) = ⟨a ▷ b, _⟩ := rfl,
      rw subtype_rhd,
    },
    {
      intros a n,
      cases a with a ha,
      simp only,
      have subtype_pow : (⟨a, ha⟩ ^ n : eta_equalizer Q) = ⟨a ^ n, _⟩ := rfl,
      rw subtype_pow,
    },
  },
end

def eta_equalizer_iso_backward : pq_group Q →* pq_group (eta_equalizer Q) :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro q,
    apply of,
    fconstructor,
    exact (of q),
    fconstructor,
  },
  {
    split,
    {
      intros a b,
      rw rhd_of_eq_of_rhd,
      apply congr_arg,
      simp_rw ←rhd_of_eq_of_rhd,
      refl,
    },
    {
      intros a n,
      rw ←of_pow_eq_pow_of,
      apply congr_arg,
      simp_rw of_pow_eq_pow_of,
      refl,
    },
  },
end

def pq_group_eta_equalizer_inclusion : pq_group (eta_equalizer Q) →* pq_group (pq_group Q) :=
begin
  fapply L_of_morph,
  {
    intro x,
    cases x with x hx,
    exact x,
  },
  {
    split,
    {
      intros a b,
      cases a with a ha,
      cases b with b hb,
      refl,
    },
    {
      intros a n,
      cases a with a ha,
      refl,
    },
  },
end

lemma eta_equalizer_in_sub_pq (x : pq_group Q) (hx : x ∈ (eta_equalizer Q : set (pq_group Q))) 
: pq_group_eta_equalizer_inclusion (of ⟨x, hx⟩ : pq_group (eta_equalizer Q)) = (L_of_morph of of_is_pq_morphism) (x) :=
begin
  rw spq_coe_is_carrier at hx,
  unfold eta_equalizer at hx,
  simp only at hx,
  rw set.mem_def at hx,
  rw ←hx,
  refl,
end

lemma inclusion_eq_L_of_of_forward (x : pq_group (eta_equalizer Q)) : pq_group_eta_equalizer_inclusion x = (L_of_morph of of_is_pq_morphism) (eta_equalizer_iso_forward x) :=
begin
  revert x,
  refine pq_group_word_induction _ _,
  {
    simp only [monoid_hom.map_one],
  },
  {
    intros x y hx,
    simp only [monoid_hom.map_mul, hx],
    congr,
    cases y with y hy,
    rw eta_equalizer_in_sub_pq,
    congr,
  },
end


lemma pq_group_eta_equalizer_inclusion_injective : function.injective (pq_group_eta_equalizer_inclusion : pq_group (eta_equalizer Q) → pq_group (pq_group Q)) :=
begin
  --intros x y hxy,
  refine pq_group_eta_equalizer_inclusion.injective_iff.mpr _,
  intros x hx,
  --rw inclusion_eq_L_of_of_forward at hx,
  
  revert x,
  refine pq_group_list _,
  {
    intros x hxy,
    have hxy1 : (list.map (λ z : (eta_equalizer Q), (of (↑z) : pq_group (pq_group Q))) x).prod = pq_group_eta_equalizer_inclusion (list.map of x).prod,
    {
      clear hxy,
      induction x with a b hb,
      {
        simp only [list.prod_nil, list.map, monoid_hom.map_one],
      },
      {
        simp only [monoid_hom.map_mul, list.prod_cons, list.map],
        rw hb,
        cases a with a ha,
        refl,
      },
    },
    rw ←hxy1 at hxy,
    clear hxy1,
    induction x with y x hx,
    {
      simp only [list.prod_nil, list.map],
    },
    {
      cases y with y hy,
      simp only [list.prod_cons, list.map],
      simp only [list.prod_cons, subtype.coe_mk, list.map] at hxy,
      
      sorry,
    },
  },
  
end

def eta_equalizer_iso : pq_group (eta_equalizer Q) ≃* pq_group Q := { 
  to_fun := eta_equalizer_iso_forward,
  inv_fun := eta_equalizer_iso_backward,
  left_inv := begin 
    refine pq_group_word_induction _ _,
    {
      simp only [monoid_hom.map_one],
    },
    {
      intros x y hx,
      simp only [monoid_hom.map_mul],
      rw hx,
      congr,
      unfold eta_equalizer_iso_forward,
      rw pq_morph_to_L_morph_adj_comm_of,
      cases y with y hy,
      simp only,
      clear hx,
      clear x,
      apply pq_group_eta_equalizer_inclusion_injective,
      rw eta_equalizer_in_sub_pq,
      clear hy,
      revert y,
      refine pq_group_word_induction _ _,
      {
        simp only [monoid_hom.map_one],
      },
      {
        intros x y hx,
        simp only [monoid_hom.map_mul],
        rw hx,
        congr,
      },
    },
  end,
  right_inv := begin 
    refine pq_group_word_induction _ _,
    {
      simp only [monoid_hom.map_one],
    },
    {
      intros x y hx,
      simp only [monoid_hom.map_mul, hx],
      refl,
    },
  end,
  map_mul' := begin 
    intros x y,
    simp only [monoid_hom.map_mul],
  end }



end pq_like_equalizer
