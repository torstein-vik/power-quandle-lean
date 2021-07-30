
import pq_induction_principles
import minimal_sub_pq_gen_group
import sub_pq_normal
import pq_like

universe u

section pq_like_equalizer

-- Idea: Eq(eta, L(eta)) is normal. Useful for proving injectivity?

variables {Q : Type u} [power_quandle Q]

def eta_equalizer (Q : Type u) [power_quandle Q] : sub_power_quandle (pq_group Q) := { 
  carrier := λ x, of x = (L_of_morph of of_is_pq_morphism) x,
  closed_rhd := begin 
    intros x y hx hy,
    rw set.mem_def at *,
    rw ←rhd_of_eq_of_rhd,
    rw rhd_def_group x y,
    simp only [monoid_hom.map_mul, monoid_hom.map_mul_inv],
    rw ←rhd_def_group,
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
  end,
  closed_one := begin
    rw set.mem_def,
    rw of_one,
    simp only [monoid_hom.map_one],
  end }


lemma eta_equalizer_mem_def (x : pq_group Q) (hx : x ∈ (eta_equalizer Q : set (pq_group Q))) : of x = ((L_of_morph of of_is_pq_morphism) : pq_group Q →* pq_group (pq_group Q)) x :=
begin
  exact hx,
end

lemma eta_equalizer_mem_iff (x : pq_group Q) : (x ∈ (eta_equalizer Q : set (pq_group Q))) ↔ of x = ((L_of_morph of of_is_pq_morphism) : pq_group Q →* pq_group (pq_group Q)) x :=
begin
  split,
  exact id,
  exact id,
end

lemma eta_equalizer_normal : sub_pq_normal (eta_equalizer Q) :=
begin
  intros x y,
  cases y with y hy,
  simp only [subtype.coe_mk],
  show of (x ▷ y) = (L_of_morph of of_is_pq_morphism) (x ▷ y),
  have hy1 : of (y) = (L_of_morph of of_is_pq_morphism) (y) := hy,
  rw ←rhd_of_eq_of_rhd,
  conv {
    to_rhs,
    rw rhd_def_group,
  },
  simp only [monoid_hom.map_mul, monoid_hom.map_mul_inv],
  rw ←rhd_def_group,
  rw ←hy1,
  conv {
    to_rhs,
    rw inner_aut_eq,
  },
  rw counit_L_of,
end

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

lemma eta_equalizer_iso_forward_of (x : eta_equalizer Q) : eta_equalizer_iso_forward (of x) = (x.1) :=
begin
  unfold eta_equalizer_iso_forward,
  rw pq_morph_to_L_morph_adj_comm_of,
  cases x,
  refl,
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

lemma eta_equalizer_iso_backward_of (x : Q) : eta_equalizer_iso_backward (of x) = of (⟨of x, by fconstructor⟩ : eta_equalizer Q) :=
begin
  refl,
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

lemma inclusion_counit_L_of_morph_of (x : pq_group (eta_equalizer Q)) : pq_group_eta_equalizer_inclusion x = (L_of_morph of of_is_pq_morphism) (counit (pq_group_eta_equalizer_inclusion x)) :=
begin
  rw inclusion_eq_L_of_of_forward,
  rw counit_L_of,
end

lemma eta_equalizer_iso_forward_of_backward (x : pq_group Q) : eta_equalizer_iso_forward (eta_equalizer_iso_backward x) = x :=
begin
  revert x,
  refine pq_group_word_induction _ _,
  {
    simp only [monoid_hom.map_one],
  },
  {
    intros x y hx,
    simp only [monoid_hom.map_mul, hx],
    refl,
  },
end

end pq_like_equalizer
