
import group_theory.free_group
import free_pq
import pq_to_group

universe u

section pq_group_free_pq

variables {S : Type u}


def from_free_group : free_group S →* pq_group (free_pq S) :=
begin
  apply free_group.to_group,
  intro s,
  exact of (free_pq_of s),
end

def from_free_pq : pq_group (free_pq S) →* free_group S :=
begin
  fapply pq_morph_to_L_morph_adj,
  {
    apply free_pq_adjoint,
    exact free_group.of,
  },
  {
    apply free_pq_adjoint_is_pq_morphism,
  },
end

theorem from_free_pq_composition (x : pq_group (free_pq S)) : from_free_group (from_free_pq x) = x :=
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
      unfold from_free_pq,
      rw pq_morph_to_L_morph_adj_comm_of,
      induction x,
      {
        rw quot_mk_helper_free_pq,
        induction x,
        {
          rw free_pq_one_def,
          rw one_preserved_by_morphism (free_pq_adjoint _),
          swap, apply free_pq_adjoint_is_pq_morphism,
          simp only [monoid_hom.map_one, of_one],
        },
        {
          rw ←free_pq_of_def,
          rw free_pq_adjoint_comm_of,
          unfold from_free_group,
          rw free_group.to_group.of,
        },
        {
          rw free_pq_rhd_def,
          rw ←rhd_of_eq_of_rhd,
          rw rhd_preserved_by_morphism (free_pq_adjoint _),
          swap, apply free_pq_adjoint_is_pq_morphism,
          rw rhd_def_group,
          simp only [monoid_hom.map_mul, monoid_hom.map_mul_inv],
          rw ←rhd_def_group,
          rw x_ih_x,
          rw x_ih_y,
        },
        {
          rw free_pq_pow_def,
          rw of_pow_eq_pow_of,
          rw pow_preserved_by_morphism (free_pq_adjoint _),
          swap, apply free_pq_adjoint_is_pq_morphism,
          rw monoid_hom.map_gpow,
          rw x_ih,
        },
      },
      {refl,},
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


theorem free_group_composition (x : free_group S) : from_free_pq (from_free_group x) = x :=
begin
  apply @free_group.induction_on S (λ x, from_free_pq (from_free_group x) = x),
  {
    simp only [monoid_hom.map_one],
  },
  {
    intro x,
    unfold pure,
    unfold from_free_group,
    rw free_group.to_group.of,
    refl,
  },
  {
    clear x,
    intro x,
    intro hx,
    simp only [inv_inj, monoid_hom.map_inv],
    assumption,
  },
  {
    clear x,
    intros x y hx hy,
    simp only [monoid_hom.map_mul],
    rw hx,
    rw hy,
  },
end


def pq_group_free_pq_iso_free_group : free_group S ≃* pq_group (free_pq S) := { 
  to_fun := from_free_group,
  inv_fun := from_free_pq,
  left_inv := free_group_composition,
  right_inv := from_free_pq_composition,
  map_mul' := begin 
    intros x y,
    simp only [monoid_hom.map_mul],
  end } 


end pq_group_free_pq
