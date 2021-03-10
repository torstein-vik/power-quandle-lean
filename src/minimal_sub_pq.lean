
import sub_pq
import group_to_pq
import pq_to_group

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

theorem pq_group_to_sub_pq : (pq_group Q) →* (pq_group (free_gen_group_sub_pq (@of_gen Q _))) := 
begin
  fapply pq_morph_to_L_morph_adj,
  {
    intro q,
    apply of,
    fconstructor,
    exact of q,
    apply gen_in_free_group_sub_pq_carrier,
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

theorem pq_group_iso_sub_pq : (pq_group Q) ≃* (pq_group (free_gen_group_sub_pq (@of_gen Q _))) :=
begin
  fconstructor,
  {
    exact pq_group_to_sub_pq,
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
  {
    intros a b,
    simp only [monoid_hom.map_mul],
  },
end

end minimal_sub_pq_L
