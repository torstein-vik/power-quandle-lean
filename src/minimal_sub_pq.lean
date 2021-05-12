
import pq_to_group
import sub_pq

universe u

section minimal_sub_pq


structure group_sub_pq (G : Type u) [group G] := 
(carrier : set G)
(closed_rhd : ∀ x y : G, x ∈ carrier → y ∈ carrier → (x * y * x⁻¹) ∈ carrier)
(closed_pow : ∀ x : G, ∀ n : ℤ, x ∈ carrier → x ^ n ∈ carrier)

variables {G : Type u} [group G]

inductive free_group_sub_pq_carrier (gen : set G) : G → Prop
| incl (x : G) (hx : x ∈ gen) : free_group_sub_pq_carrier x
| rhd (x y : G) (hx : free_group_sub_pq_carrier x) (hy : free_group_sub_pq_carrier y) : free_group_sub_pq_carrier (x * y * x⁻¹)
| pow (x : G) (n : ℤ) (hx : free_group_sub_pq_carrier x) : free_group_sub_pq_carrier (x ^ n)

lemma gen_in_free_group_sub_pq_carrier (gen : set G) : gen ≤ free_group_sub_pq_carrier gen :=
begin
  intros x hx,
  apply free_group_sub_pq_carrier.incl,
  exact hx,
end

def free_group_sub_pq (gen : set G) : group_sub_pq G := { 
  carrier := free_group_sub_pq_carrier gen,
  closed_rhd := free_group_sub_pq_carrier.rhd,
  closed_pow := free_group_sub_pq_carrier.pow, 
}


def gen_group_sub_pq (x : group_sub_pq G) : sub_power_quandle G := { 
  carrier := x.carrier,
  closed_rhd := x.closed_rhd,
  closed_pow := x.closed_pow }


def free_gen_group_sub_pq (gen : set G) : sub_power_quandle G := gen_group_sub_pq (free_group_sub_pq gen)


end minimal_sub_pq

section minimal_sub_pq_L

variables {Q : Type u} [power_quandle Q]

def of_gen : set (pq_group Q) := λ x, ∃ g : Q, x = of g

def of_gen_group_sub_pq : group_sub_pq (pq_group Q) := { 
  carrier := of_gen,
  closed_rhd := begin
    intros x y hx hy,
    rw ←rhd_def,
    cases hx with q1 hq1,
    cases hy with q2 hq2,
    use (q1 ▷ q2),
    rw hq1,
    rw hq2,
    rw rhd_of_eq_of_rhd,
  end,
  closed_pow := begin
    intros x n hx,
    cases hx with q hq,
    use (q^n),
    rw hq,
    rw of_pow_eq_pow_of,
  end }

def pq_group_to_sub_pq : (pq_group Q) →* (pq_group (gen_group_sub_pq (@of_gen_group_sub_pq Q _))) := 
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro q,
    apply of,
    fconstructor,
    exact of q,
    use q,
  },
  {
    split,
    {
      intros a b,
      simp_rw rhd_of_eq_of_rhd,
      apply congr_arg,
      simp_rw ←rhd_of_eq_of_rhd,
      refl,
    },
    {
      intros a n,
      simp_rw ←of_pow_eq_pow_of,
      apply congr_arg,
      simp_rw of_pow_eq_pow_of,
      refl,
    },
  },
end


def sub_pq_to_pq_group : (pq_group (gen_group_sub_pq (@of_gen_group_sub_pq Q _))) →* (pq_group Q) := 
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
      have hab := sub_power_quandle.closed_rhd _ a b ha hb,
      have rhd_rw : (⟨a, ha⟩ : {x // x ∈ has_coe_t_aux.coe (gen_group_sub_pq of_gen_group_sub_pq)}) ▷ ⟨b, hb⟩ = ⟨a ▷ b, hab⟩ := rfl,
      rw rhd_rw,
    },
    {
      intros a n,
      cases a with a ha,
      simp only,
      have han := sub_power_quandle.closed_pow _ a n ha,
      have pow_rw : (⟨a, ha⟩ : {x // x ∈ has_coe_t_aux.coe (gen_group_sub_pq of_gen_group_sub_pq)}) ^ n = ⟨a ^ n, han⟩ := rfl,
      rw pow_rw,
    },
  },
end

def pq_group_iso_sub_pq : (pq_group Q) ≃* (pq_group (gen_group_sub_pq (@of_gen_group_sub_pq Q _))) :=
begin
  fconstructor,
  {
    exact pq_group_to_sub_pq,
  },
  {
    exact sub_pq_to_pq_group,
  },
  {
    intro x,
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
        unfold pq_group_to_sub_pq,
        rw pq_morph_to_L_morph_adj_comm_of,
        unfold sub_pq_to_pq_group,
        rw pq_morph_to_L_morph_adj_comm_of,
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
  },
  {
    intro x,
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
        unfold sub_pq_to_pq_group,
        rw pq_morph_to_L_morph_adj_comm_of,
        cases x with x hx,
        simp only,
        cases hx with y hy,
        simp_rw hy,
        unfold pq_group_to_sub_pq,
        rw pq_morph_to_L_morph_adj_comm_of,
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
  },
  {
    intros a b,
    simp only [monoid_hom.map_mul],
  },
end


/-
noncomputable def sub_pq_to_pq_group : (pq_group (gen_group_sub_pq (@of_gen_group_sub_pq Q _))) →* (pq_group Q) := 
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro x,
    apply of,
    cases x with x hx,
    exact classical.some hx,
  },
  {
    split,
    {
      intros a b,
      cases a with a ha,
      cases b with b hb,
      simp only,
      have hx := classical.some_spec ha,
      have hy := classical.some_spec hb,
      rw ←hx,
      rw ←hy,
      have hab := sub_power_quandle.closed_rhd _ a b ha hb,
      have rhd_rw : (⟨a, ha⟩ : {x // x ∈ has_coe_t_aux.coe (gen_group_sub_pq of_gen_group_sub_pq)}) ▷ ⟨b, hb⟩ = ⟨a ▷ b, hab⟩ := rfl,
      rw rhd_rw,
      simp only,
      have hxy := classical.some_spec hab,
      rw ←hxy,
    },
    {
      intros a n,
      cases a with a ha,
      simp only,
      have hx := classical.some_spec ha,
      rw ←hx,
      have han := sub_power_quandle.closed_pow _ a n ha,
      have pow_rw : (⟨a, ha⟩ : {x // x ∈ has_coe_t_aux.coe (gen_group_sub_pq of_gen_group_sub_pq)}) ^ n = ⟨a ^ n, han⟩ := rfl,
      rw pow_rw,
      simp only,
      have hxn := classical.some_spec han,
      rw ←hxn,
    },
  },
end

noncomputable def pq_group_iso_sub_pq : (pq_group Q) ≃* (pq_group (gen_group_sub_pq (@of_gen_group_sub_pq Q _))) :=
begin
  fconstructor,
  {
    exact pq_group_to_sub_pq,
  },
  {
    exact sub_pq_to_pq_group,
  },
  {
    intro x,
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
        unfold pq_group_to_sub_pq,
        rw pq_morph_to_L_morph_adj_comm_of,
        unfold sub_pq_to_pq_group,
        rw pq_morph_to_L_morph_adj_comm_of,
        simp only,
        have hx := classical.some_spec (_ : ∃ (g : Q), of x = of g),
        rw ←hx,
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
  },
  {
    intro x,
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
        unfold sub_pq_to_pq_group,
        rw pq_morph_to_L_morph_adj_comm_of,
        simp only,
        cases x with x hx,
        simp only,
        unfold pq_group_to_sub_pq,
        rw pq_morph_to_L_morph_adj_comm_of,
        have hx1 := classical.some_spec hx,
        apply congr_arg,
        ext1,
        simp only [subtype.coe_mk],
        rw ←hx1,
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
  },
  {
    intros a b,
    simp only [monoid_hom.map_mul],
  },
end
-/


end minimal_sub_pq_L
