
import minimal_sub_pq

universe u

section minimal_sub_pq_gen_group

variables {G : Type u} [group G]

inductive generated_by (gen : set G) : G → Prop
| unit : generated_by 1
| incl (x : G) (hx : x ∈ gen) : generated_by x
| mul (x y : G) (hx : generated_by x) (hy : generated_by y) : generated_by (x * y)
| inv (x : G) (hx : generated_by x) : generated_by (x⁻¹)

def group_generated_by (gen : set G) : Prop := ∀ g, generated_by gen g


def gen_set_counit (gen : set G) : (pq_group (free_gen_group_sub_pq gen)) →* G :=
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
      have ab_rw : (⟨a, ha⟩▷⟨b, hb⟩ : {x // x ∈ has_coe_t_aux.coe (free_gen_group_sub_pq gen)}) = ⟨a ▷ b, _⟩ := rfl,
      rw ab_rw,
    },
    {
      intros a n,
      cases a with a ha,
      have an_rw : (⟨a, ha⟩ ^ n : {x // x ∈ has_coe_t_aux.coe (free_gen_group_sub_pq gen)}) = ⟨a ^ n, _⟩ := rfl,
      rw an_rw,
    }
  }
end


theorem gen_set_counit_surjective (gen : set G) (hG : group_generated_by gen) : function.surjective (gen_set_counit gen) :=
begin
  intro x,
  specialize hG x,
  induction hG,
  {
    use 1,
    refl,
  },
  {
    fconstructor,
    apply of,
    fconstructor,
    exact hG_x,
    apply gen_in_free_group_sub_pq_carrier,
    exact hG_hx,
    refl,
  },
  {
    cases hG_ih_hx with a ha,
    cases hG_ih_hy with b hb,
    use a * b,
    simp only [monoid_hom.map_mul],
    rw ha,
    rw hb,
  },
  {
    cases hG_ih with a ha,
    use a⁻¹,
    simp only [inv_inj, monoid_hom.map_inv],
    assumption,
  },
end

def pq_gen_of {gen : set G} (g : G) (hg : g ∈ gen) : pq_group (free_gen_group_sub_pq gen) :=
begin
  apply of,
  fconstructor,
  exact g,
  fconstructor,
  exact hg,
end

lemma pq_gen_of_def (gen : set G) (g : G) (hg : g ∈ gen) : pq_gen_of g hg = of ⟨g, gen_in_free_group_sub_pq_carrier gen hg⟩ := rfl

def free_pq_gen_of {gen : set G} (g : G) (hg : free_group_sub_pq_carrier gen g) : pq_group (free_gen_group_sub_pq gen) :=
begin
  apply of,
  fconstructor,
  exact g,
  exact hg,
end

lemma free_pq_gen_of_def (gen : set G) (g : G) (hg : free_group_sub_pq_carrier gen g) : free_pq_gen_of g hg = of ⟨g, hg⟩ := rfl

lemma free_pq_gen_of_rhd (gen : set G) (x y : G) (hx : free_group_sub_pq_carrier gen x) (hy : free_group_sub_pq_carrier gen y) : 
free_pq_gen_of (x ▷ y) (free_group_sub_pq_carrier.rhd x y hx hy) = (free_pq_gen_of x hx) ▷ (free_pq_gen_of y hy) :=
begin
  unfold free_pq_gen_of,
  rw rhd_of_eq_of_rhd,
  apply congr_arg,
  refl,
end

lemma free_pq_gen_of_pow (gen : set G) (x : G) (n : ℤ) (hx : free_group_sub_pq_carrier gen x) : 
free_pq_gen_of (x ^ n) (free_group_sub_pq_carrier.pow x n hx) = (free_pq_gen_of x hx) ^ n :=
begin
  unfold free_pq_gen_of,
  rw ←of_pow_eq_pow_of,
  apply congr_arg,
  refl,
end

lemma generated_by_rhd (gen : set G) (x y : G) (hx : generated_by gen x) (hy : generated_by gen y) : generated_by gen (x ▷ y) :=
begin
  apply generated_by.mul,
  apply generated_by.mul,
  assumption,
  assumption,
  apply generated_by.inv,
  assumption,
end

lemma generated_by_pow_nat (gen : set G) (x : G) (n : ℕ) (hx : generated_by gen x) : generated_by gen (x ^ n) :=
begin
  induction n,
  apply generated_by.unit,
  rw pow_succ,
  apply generated_by.mul,
  assumption,
  assumption,
end

lemma generated_by_pow (gen : set G) (x : G) (n : ℤ) (hx : generated_by gen x) : generated_by gen (x ^ n) :=
begin
  induction n,
  {
    apply generated_by_pow_nat,
    assumption,
  },
  {
    rw gpow_neg_succ_of_nat,
    apply generated_by.inv,
    apply generated_by_pow_nat,
    assumption,
  },
end

def pq_gen_set_gen_set (gen : set G) : set (pq_group (free_gen_group_sub_pq gen)) := λ x : pq_group (free_gen_group_sub_pq gen), 
∃ g ∈ gen, x = pq_gen_of g H

theorem pq_gen_set_generated (gen : set G) : group_generated_by (pq_gen_set_gen_set gen) :=
begin
  intro x,
  induction x,
  {
    rw quot_mk_helper,
    induction x,
    {
      rw incl_unit_eq_unit,
      apply generated_by.unit,
    },
    {
      rw ←of_def,
      cases x with x hx,
      rw ←free_pq_gen_of_def,
      induction hx,
      {
        apply generated_by.incl,
        use hx_x,
        use hx_hx,
        refl,
      },
      {
        simp_rw ←rhd_def,
        suffices : generated_by (pq_gen_set_gen_set gen) ((free_pq_gen_of hx_x hx_hx) ▷ (free_pq_gen_of hx_y hx_hy)),
        convert this,
        {
          rw ←free_pq_gen_of_rhd,
          refl,
        },
        apply generated_by_rhd,
        assumption,
        assumption,
      },
      {
        suffices : generated_by (pq_gen_set_gen_set gen) ((free_pq_gen_of hx_x hx_hx) ^ hx_n),
        convert this,
        {
          rw ←free_pq_gen_of_pow,
        },
        apply generated_by_pow,
        assumption,
      },
    },
    {
      rw ←mul_def,
      apply generated_by.mul,
      assumption,
      assumption,
    },
    {
      rw ←inv_def,
      apply generated_by.inv,
      assumption,
    },
  },
  {refl,},
end

/-
theorem gen_set_counit_injective (gen : set G) (hG : group_generated_by gen) : function.injective (gen_set_counit gen) :=
begin
  refine (gen_set_counit gen).injective_iff.mpr _,
  intros x hx,
  
end
-/

end minimal_sub_pq_gen_group
