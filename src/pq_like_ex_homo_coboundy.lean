
import pq_group_homo_locus_pres_iso_ker_counit
import sub_pq

universes u v

section pq_morphism_kernel

variables {Q1 : Type u} {Q2 : Type v} [power_quandle Q1] [power_quandle Q2]

def pq_morphism_kernel (f : Q1 → Q2) (hf : is_pq_morphism f) : sub_power_quandle Q1 := { 
  carrier := λ x, f x = 1,
  closed_rhd := begin 
    intros x y hx hy,
    rw set.mem_def at *,
    rw hf.1,
    rw hx,
    rw hy,
    rw power_quandle.one_rhd,
  end,
  closed_pow := begin 
    intros x n hx,
    rw set.mem_def at *,
    rw hf.2,
    rw hx,
    rw pq_one_pow,
  end,
  closed_one := begin 
    rw set.mem_def,
    apply one_preserved_by_morphism,
    assumption,
  end }

end pq_morphism_kernel

section pq_like_ex_homo_coboundry

variables {G : Type u} [group G]

variables (f : G → homo_locus_pres G) (hf : is_pq_morphism f)

variables (hf1 : ∀ a b : G, homo_locus_of (a, b) = f a * f b * (f (a*b))⁻¹)

-- Goal: Prove Gr ker f ~= G

include f hf hf1


def pq_like_ex_homo_coboundry_iso_forward : pq_group (pq_morphism_kernel f hf) →* G :=
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
      refl,
    },
    {
      intros a n,
      cases a with a ha,
      refl,
    },
  },
end



def pq_like_ex_homo_coboundry_iso : pq_group (pq_morphism_kernel f hf) ≃* G := { 
  to_fun := sorry,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry,
  map_mul' := sorry }

end pq_like_ex_homo_coboundry
