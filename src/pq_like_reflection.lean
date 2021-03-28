
import pq_like

universes u1 u2 u3 u4


section background

variables {G : Type u1} {H : Type u2} [group G] [group H]


def center_iso (f : G ≃* H) : subgroup.center G ≃* subgroup.center H := sorry

def center_cart : subgroup.center (G × H) ≃* (subgroup.center G) × (subgroup.center H) := sorry

variables {G1 : Type u3} {H1 : Type u4} [group G1] [group H1]

def cancel_iso (f1 : G ≃* H) (f2 : G × G1 ≃* H × H1) : G1 ≃* H1 := sorry

def cancel_iso_right (f1 : G1 ≃* H1) (f2 : G × G1 ≃* H × H1) : G ≃* H := sorry

def center_counit_ker : subgroup.center ((counit : pq_group G →* G).ker) ≃* (counit : pq_group G →* G).ker := sorry

end background

section counit_iso

variables {Q1 : Type u1} {Q2 : Type u2} [power_quandle Q1] [power_quandle Q2]


def counit_iso (f : pq_group Q1 ≃ pq_group Q2) (hf : is_pq_morphism f) 
(g : subgroup.center (pq_group Q1) ≃* subgroup.center (pq_group Q2))
: (counit : (pq_group (pq_group Q1)) →* (pq_group Q1)).ker ≃* (counit : (pq_group (pq_group Q2)) →* (pq_group Q2)).ker :=
begin
  let Lf := L_of_morph_iso f hf,
  let Lf1 := Lf.trans (pq_group_prod_ker_G),
  let Lf2 := (@pq_group_prod_ker_G Q1 _).symm.trans Lf1,
  let Lfc := center_iso Lf2,
  let Lfc1 := Lfc.trans (center_cart),
  let Lfc2 := (center_cart.symm).trans Lfc1,
  let Lfi := cancel_iso g Lfc2,
  let Lfi1 := Lfi.trans center_counit_ker,
  let Lfi2 := (center_counit_ker.symm).trans Lfi1,
  exact Lfi2,
end

def pq_iso (f : pq_group Q1 ≃ pq_group Q2) (hf : is_pq_morphism f) 
(g : subgroup.center (pq_group Q1) ≃* subgroup.center (pq_group Q2))
: pq_group Q1 ≃* pq_group Q2 :=
begin
  let Lf := L_of_morph_iso f hf,
  let Lf1 := Lf.trans (pq_group_prod_ker_G),
  let Lf2 := (@pq_group_prod_ker_G Q1 _).symm.trans Lf1,
  let ci := counit_iso f hf g,
  let pq_iso := cancel_iso_right ci Lf2,
  exact pq_iso,
end

end counit_iso
