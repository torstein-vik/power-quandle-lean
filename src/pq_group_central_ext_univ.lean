
import pq_induction_principles

universes u v

section pq_group_central_ext_univ

variables {G : Type u} [group G]

variables {H : Type v} [group H]

-- (f : H →* G) (hf : f.ker ≤ subgroup.center H) (s : G → H) (hs : is_pq_morphism s) (hsf : ∀ x : G, f (s x) = x)

def pq_group_central_ext_univ (s : G → H) (hs : is_pq_morphism s) : pq_group G →* H := pq_morph_to_L_morph_adj s hs

theorem pq_group_central_ext_univ_comm_sec (s : G → H) (hs : is_pq_morphism s) (x : G) : (pq_group_central_ext_univ s hs) (of x) = s x := rfl

-- Isn't this obvious?

-- What else can we deduce?

-- Can we factor s through homo_locus_pres?

-- Can we find sufficient criteria for pq_group G iso H?
-- If so, find H →* pq_group G. For that, H →* homo_locus_pres_prod G
-- Based on f, with a "crossed" pq-morphism H → homo_locus_pres G
-- OR what about of ∘ f? No... 
-- What conditions do we need?
-- How do we use f.ker ≤ subgroup.center H? 
-- f(x) = 1 implies ∀ y, xy = yx
-- Say x = s(f(x)) * b
-- We get f(x) = f(s(f(x))) * f(b) = f(x) * f(b) => f(b) = 1
-- Implies "H ≃ f.ker × s.im" s.im is just a power quandle...



variables (f : H →* G) (hf : f.ker ≤ subgroup.center H) (s : G → H) (hs : is_pq_morphism s) (hsf : ∀ x : G, f (s x) = x)

include hf hs hsf
def pq_group_central_ext_univ_ker_range_equiv : H ≃ f.ker × (set.range s) := { 
  to_fun := λ x : H, (⟨x * (s(f(x)))⁻¹, begin 
    show f(x * (s(f(x)))⁻¹) = 1,
    simp only [monoid_hom.map_mul_inv],
    rw hsf,
    simp only [mul_right_inv],
  end⟩, ⟨s(f(x)), set.mem_range_self (f x)⟩),
  inv_fun := λ ⟨⟨x, _⟩, ⟨y, _⟩⟩, x * y,
  left_inv := begin 
    intro x,
    simp only,
    show x * (s (f x))⁻¹ * s (f x) = x,
    simp only [inv_mul_cancel_right],
  end,
  right_inv := begin 
    rintros ⟨⟨a, ha⟩, ⟨b, hb⟩⟩,
    simp only,
    unfold pq_group_central_ext_univ_ker_range_equiv._match_1, -- Find better
    ext1,
    {
      simp only [monoid_hom.map_mul, subtype.mk_eq_mk],
      have ha1 : f a = 1 := ha,
      simp_rw ha1,
      simp_rw one_mul,
      rw set.mem_range at hb,
      cases hb with c hc,
      rw ←hc,
      rw hsf,
      simp only [mul_inv_cancel_right],
    },
    {
      simp only [monoid_hom.map_mul, subtype.mk_eq_mk],
      have ha1 : f a = 1 := ha,
      simp_rw ha1,
      simp_rw one_mul,
      rw set.mem_range at hb,
      cases hb with c hc,
      rw ←hc,
      rw hsf,
    },
  end }

end pq_group_central_ext_univ
