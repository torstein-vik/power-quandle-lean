
import pq_to_group

universes u v

section word_induction

variables {Q : Type u} [power_quandle Q]

def create_list_from_pq : pre_pq_group Q → list Q
| pre_pq_group.unit := []
| (pre_pq_group.incl q) := [q]
| (pre_pq_group.mul a b) := (create_list_from_pq a) ++ (create_list_from_pq b)
| (pre_pq_group.inv a) := (create_list_from_pq a).reverse.map(λ q, q ^ (-1 : ℤ))

lemma create_list_from_pq_eq_id (x : pre_pq_group Q) : ((create_list_from_pq x).map(of)).prod = ⟦x⟧ :=
begin
  induction x,
  {
    unfold create_list_from_pq,
    refl,
  },
  {
    unfold create_list_from_pq,
    simp only [mul_one, list.prod_cons, list.prod_nil, list.map],
    refl,
  },
  {
    unfold create_list_from_pq,
    simp only [list.map_append, list.prod_append],
    rw x_ih_a,
    rw x_ih_b,
    refl,
  },
  {
    unfold create_list_from_pq,
    rw ←inv_def,
    rw ←x_ih,
    clear x_ih,
    induction x_a,
    {
      unfold create_list_from_pq,
      simp only [one_inv, list.prod_nil, list.map, list.reverse_nil],
    },
    {
      unfold create_list_from_pq,
      simp only [mul_one, list.reverse_singleton, list.prod_cons, list.prod_nil, list.map],
      rw of_pow_eq_pow_of,
      simp only [gpow_one, gpow_neg],
    },
    {
      unfold create_list_from_pq,
      simp only [list.map_reverse, mul_inv_rev, list.map_append, list.prod_append, list.reverse_append, list.map_map],
      rw ←x_a_ih_a,
      rw ←x_a_ih_b,
      simp only [list.map_reverse, list.map_map],
    },
    {
      unfold create_list_from_pq,
      simp only [list.map_reverse, list.reverse_reverse, list.map_map],
      have comp_is_id : (λ (q : Q), q ^ (-1 : ℤ)) ∘ (λ (q : Q), q ^ (-1 : ℤ)) = id,
      {
        funext,
        simp only [id.def, function.comp_app],
        rw power_quandle.pow_comp,
        norm_num,
        rw power_quandle.pow_one,
      },
      rw comp_is_id,
      simp only [function.comp.right_id],
      rw ←inv_inj,
      rw ←x_a_ih,
      simp only [list.map_reverse, inv_inv, list.map_map],
    },
  },
end

theorem pq_group_word_induction {P : pq_group Q → Prop} 
(h1 : P 1) 
(ih : ∀ x : pq_group Q, ∀ y : Q, P x → P (of y * x)) 
: ∀ x : pq_group Q, P x :=
begin
  intro x,
  induction x,
  {
    rw quot_mk_helper,
    let y := create_list_from_pq x,
    have y_def : y = create_list_from_pq x := rfl,
    have hy := create_list_from_pq_eq_id x,
    rw ←y_def at hy,
    rw ←hy,
    generalize : y = e,
    induction e,
    {
      simp only [list.prod_nil, list.map],
      exact h1,
    },
    {
      simp only [list.prod_cons, list.map],
      apply ih,
      exact e_ih,
    },
  },
  {refl,},
end

theorem pq_group_list {P : pq_group Q → Prop}
(hl : ∀ x : list Q, P (x.map of).prod)
: ∀ x : pq_group Q, P x :=
begin
  intro x,
  induction x,
  {
    rw quot_mk_helper,
    let y := create_list_from_pq x,
    have y_def : y = create_list_from_pq x := rfl,
    have hy := create_list_from_pq_eq_id x,
    rw ←y_def at hy,
    rw ←hy,
    apply hl,
  },
  {refl,},
end

variables {H : Type*}

def pq_group_list_data_pure (f : list Q → H) 
(hf : ∀ x y : pre_pq_group Q, setoid.r x y → f (create_list_from_pq x) = f (create_list_from_pq y)) 
: pq_group Q → H :=
begin
  intro x,
  induction x,
  {
    exact f (create_list_from_pq x),
  },
  {
    simp only [eq_rec_constant],
    apply hf,
    exact x_p,
  },
end

/-

def pq_group_list_data_property (sub_pq : set (pq_group Q)) (f : (set.preimage (λ x : list Q, (list.map (of) x).prod) sub_pq) → H) 
(hf : ∀ x y : pre_pq_group Q, ∀ hx : ⟦x⟧ ∈ sub_pq, ∀ hy : ⟦y⟧ ∈ sub_pq, setoid.r x y → f ⟨(create_list_from_pq x), begin 
  refine set.mem_preimage.mpr _,
  rw create_list_from_pq_eq_id,
  exact hx,
end⟩ = f ⟨(create_list_from_pq y), begin 
  refine set.mem_preimage.mpr _,
  rw create_list_from_pq_eq_id,
  exact hy,
end⟩) 
: sub_pq → H :=
begin
  intro x,
  cases x with x hx,
  induction x,
  {
    exact f ⟨(create_list_from_pq x), begin 
      refine set.mem_preimage.mpr _,
      rw create_list_from_pq_eq_id,
      exact hx,
    end⟩,
  },
  {
    have hab : ⟦x_a⟧ = ⟦x_b⟧,
    {
      apply quotient.sound,
      exact p,
    },
    funext,
    have hb := x,
    rw quot_mk_helper at hb,
    have ha : ⟦x_a⟧ ∈ sub_pq,
    {
      rw ←hab at hb,
      exact hb,
    },
    specialize hf x_a x_b ha hb p,
    rw ←hf,
    simp_rw hf,
    sorry,
  }
end

-/

/-
lemma pq_group_list_data_property_pre_aux (sub_pq : set (pq_group Q)) (x : pre_pq_group Q) (hx : ⟦x⟧ ∈ sub_pq) : (list.map of (create_list_from_pq x)).prod ∈ sub_pq :=
begin
  rw create_list_from_pq_eq_id,
  exact hx,
end

def pq_group_list_data_property_pre (sub_pq : set (pq_group Q)) (f : ∀ x : list Q, (list.map (of) x).prod ∈ sub_pq → H) 
(hf : ∀ x y : pre_pq_group Q, ∀ hy : ⟦y⟧ ∈ sub_pq, ∀ hxy : ⟦x⟧ = ⟦y⟧ , f (create_list_from_pq x) (pq_group_list_data_property_pre_aux _ _ begin rw hxy, exact hy end) = f (create_list_from_pq y) (pq_group_list_data_property_pre_aux _ _ hy)) 
: sub_pq → H :=
begin
  intro x,
  cases x with x hx,
  induction x,
  {
    exact f (create_list_from_pq x) (pq_group_list_data_property_pre_aux _ _ hx),
  },
  {
    
    have hab : ⟦x_a⟧ = ⟦x_b⟧,
    {
      apply quotient.sound,
      exact p,
    },
    funext,
    have hb := x,
    rw quot_mk_helper at hb,
    have ha : ⟦x_a⟧ ∈ sub_pq,
    {
      rw ←hab at hb,
      exact hb,
    },
    specialize hf x_a x_b hb hab,
    rw ←hf,
    simp_rw hf,
    
    
    
    /-
    rw ←hf,
    have : ∀ h1 h2 : (list.map of (create_list_from_pq x_a)).prod ∈ sub_pq, f (create_list_from_pq x_a) h1 = f (create_list_from_pq x_a) h2,
    {
      intros h1 h2,
      refl,
    },
    simp_rw hf,
    -/
    
    sorry,
  }
end

-/

end word_induction

section cleaned_induction

variables {Q : Type u} [power_quandle Q]

theorem pq_group_induction {P : pq_group Q → Prop}
(hof : ∀ q : Q, P (of q))
(hmul : ∀ a b : pq_group Q, P a → P b → P (a * b))
(hinv : ∀ a : pq_group Q, P a → P (a⁻¹))
: ∀ x : pq_group Q, P x :=
begin
  intro x,
  induction x,
  {
    rw quot_mk_helper,
    induction x,
    {
      rw incl_unit_eq_unit,
      convert hof 1,
      rw of_one,
    },
    {
      rw ←of_def,
      apply hof,
    },
    {
      rw ←mul_def,
      apply hmul,
      assumption,
      assumption,
    },
    {
      rw ←inv_def,
      apply hinv,
      assumption,
    },
  },
  {refl,},
end

end cleaned_induction


section morphism_equality

variables {Q : Type u} [power_quandle Q]

variables {G : Type v} [group G]

theorem morphism_equality (f g : pq_group Q →* G) (hfg : ∀ q : Q, f (of q) = g (of q)) : f = g :=
begin
  ext1,
  revert x,
  refine pq_group_word_induction _ _,
  {
    simp only [monoid_hom.map_one],
  },
  {
    intros x y hx,
    simp only [monoid_hom.map_mul, hx, hfg],
  },
end

theorem morphism_equality_elem (f g : pq_group Q →* G) (hfg : ∀ q : Q, f (of q) = g (of q)) (x : pq_group Q) : f x = g x :=
begin
  have me := morphism_equality f g hfg,
  rw me,
end

theorem morphism_equality_elem_id (f : pq_group Q →* pq_group Q) (hf : ∀ q : Q, f (of q) = of q) (x : pq_group Q) : f x = x :=
begin
  have me := morphism_equality_elem f (monoid_hom.id (pq_group Q)) hf x,
  simp only [monoid_hom.id_apply] at me,
  rw me,
end

variables {H : Type*} [group H]

theorem morphism_equality_comp_elem_id (f : pq_group Q →* H) (g : H →* pq_group Q) (hgf : ∀ q : Q, g (f (of q)) = of q) (x : pq_group Q) : g (f x) = x :=
begin
  revert x,
  refine pq_group_word_induction _ _,
  {
    simp only [monoid_hom.map_one],
  },
  {
    intros x y hx,
    simp only [hgf, hx, mul_right_inj, monoid_hom.map_mul],
  },
end

end morphism_equality

section counit_ker_induction

variables {G : Type u} [group G]


def counit_ker_decomp_pre : G → list G → list (G × G)
| y (a :: x) := (y, a) :: counit_ker_decomp_pre (y * a) x
| y [] := []
   
def counit_ker_decomp : list G → list (G × G) := λ x, counit_ker_decomp_pre 1 (x)


lemma counit_ker_pre_effect (x : list G) (a : G) : counit_ker_decomp_pre a x = (counit_ker_decomp x).map (λ b : (G × G), (a * b.1, b.2)) :=
begin
  induction x generalizing a,
  {
    refl,
  },
  {
    unfold counit_ker_decomp,
    unfold counit_ker_decomp_pre,
    simp only [true_and, mul_one, one_mul, eq_self_iff_true, list.map],
    rw x_ih,
    rw x_ih,
    simp only [list.map_map],
    congr,
    funext,
    simp only [and_true, prod.mk.inj_iff, eq_self_iff_true],
    rw mul_assoc,
  },
end

lemma counit_ker_decomp_append (x y : list G) : counit_ker_decomp (x ++ y) = counit_ker_decomp x ++ counit_ker_decomp_pre (x.prod) y :=
begin
  induction x,
  {
    simp only [list.nil_append, list.prod_nil],
    refl,
  },
  {
    simp only [list.cons_append, list.prod_cons],
    unfold counit_ker_decomp,
    unfold counit_ker_decomp_pre,
    simp only [true_and, one_mul, list.cons_append, eq_self_iff_true],
    rw counit_ker_pre_effect,
    rw counit_ker_pre_effect,
    rw counit_ker_pre_effect,
    rw x_ih,
    rw counit_ker_pre_effect,
    simp only [list.map_append, list.map_map],
    congr,
    funext,
    simp only [and_true, prod.mk.inj_iff, eq_self_iff_true],
    rw mul_assoc,
  },
end


lemma counit_ker_decomp_append_one (x : list G) (a : G) : counit_ker_decomp (x ++ [a]) = counit_ker_decomp x ++ [(x.prod, a)] :=
begin
  rw counit_ker_decomp_append,
  refl,
end

lemma counit_ker_decomp_comp (x : list G) : (x.map of).prod = ((counit_ker_decomp x).map (λ a : G × G, of a.1 * of a.2 * (of (a.1 * a.2))⁻¹)).prod * of (x.prod) :=
begin
  unfold counit_ker_decomp,
  induction x,
  {
    unfold counit_ker_decomp_pre,
    simp only [of_one, mul_one, list.prod_nil, list.map],
  },
  {
    unfold counit_ker_decomp_pre,
    simp only [of_one, one_mul, mul_right_inv, list.prod_cons, list.map],
    rw x_ih,
    clear x_ih,
    induction x_tl generalizing x_hd,
    {
      unfold counit_ker_decomp_pre,
      simp only [of_one, mul_one, one_mul, list.prod_nil, list.map],
    },
    {
      unfold counit_ker_decomp_pre,
      simp only [of_one, one_mul, mul_right_inv, list.prod_cons, list.map],
      have hx2 := x_tl_ih (x_hd * x_tl_hd),
      rw ←mul_assoc x_hd _ _,
      rw mul_assoc,
      rw ←hx2,
      clear hx2,
      rw ←mul_assoc,
      rw ←mul_assoc,
      simp only [inv_mul_cancel_right],
      have hx1 := x_tl_ih (x_tl_hd),
      rw mul_assoc,
      rw ←hx1,
      rw ←mul_assoc,
    },
  },
end

lemma counit_ker_decomp_comp_alt (x : list G) : (x.map of).prod * (of (x.prod))⁻¹ = ((counit_ker_decomp x).map (λ a : G × G, of a.1 * of a.2 * (of (a.1 * a.2))⁻¹)).prod :=
begin
  rw counit_ker_decomp_comp,
  simp only [mul_inv_cancel_right],
end

variables {H : Type*} [group H]

lemma hom_list_prod (x : list G) (f : G →* H) : f x.prod = (x.map f).prod :=
begin
  induction x,
  {
    simp only [list.prod_nil, list.map, monoid_hom.map_one],
  },
  {
    simp only [x_ih, monoid_hom.map_mul, list.prod_cons, list.map],
  },
end

lemma counit_ker_mem_list (x : list G) : (x.map of).prod ∈ (counit : pq_group G →* G).ker ↔ x.prod = 1 :=
begin
  rw counit.mem_ker,
  rw hom_list_prod,
  simp only [list.map_map],
  have : (counit ∘ of : G → G) = id,
  {
    funext,
    simp only [counit_of, id.def, function.comp_app],
  },
  rw this,
  simp only [list.map_id],
end

lemma counit_ker_decomp_comp_in_ker (x : list (G × G)) : ((x).map (λ a : G × G, of a.1 * of a.2 * (of (a.1 * a.2))⁻¹)).prod ∈ (counit : pq_group G →* G).ker :=
begin
  rw counit.mem_ker,
  rw hom_list_prod,
  simp only [list.map_map],
  suffices : counit ∘ (λ (a : G × G), of a.fst * of a.snd * (of (a.fst * a.snd))⁻¹) = λ (a : G × G), (1 : G),
  {
    rw this,
    simp only [list.prod_repeat, one_pow, list.map_const],
  },
  funext,
  simp only [counit_of, mul_inv_rev, monoid_hom.map_mul, function.comp_app, monoid_hom.map_mul_inv],
  group,
end


theorem counit_ker_induction_list {P : (counit : pq_group G →* G).ker → Prop}
(hl : ∀ x : list (G × G), P ⟨(list.map (λ (a : G × G), of a.fst * of a.snd * (of (a.fst * a.snd))⁻¹) (x)).prod, counit_ker_decomp_comp_in_ker x⟩)
: ∀ x : (counit : pq_group G →* G).ker, P x :=
begin 
  intro x,
  cases x with x hx,
  revert x,
  refine pq_group_list _,
  {
    intros x hx,
    have hx1 : x.prod = 1,
    {
      rw ←counit_ker_mem_list,
      exact hx,
    },
    have hx2 := counit_ker_decomp_comp x,
    generalize hxy : counit_ker_decomp x = y,
    rw hxy at hx2,
    rw hx1 at hx2,
    simp only [of_one, mul_one] at hx2,
    simp_rw hx2,
    exact hl y,
  },
end

theorem counit_ker_induction {P : (counit : pq_group G →* G).ker → Prop}
(hgen : ∀ a b : G, P ⟨of a * of b * (of (a*b))⁻¹, begin 
  refine counit.mem_ker.mpr _,
  simp only [counit_of, mul_inv_rev, monoid_hom.map_mul, monoid_hom.map_mul_inv],
  group,
end⟩)
(hmul : ∀ a b : (counit : pq_group G →* G).ker, P a → P b → P (a * b))
: ∀ x : (counit : pq_group G →* G).ker, P x :=
begin 
  apply counit_ker_induction_list,
  intro x,
  induction x,
  {
    simp only [list.prod_nil, list.map],
    convert hgen 1 1,
    simp only [of_one, one_inv, mul_one],
  },
  {
    simp only [list.prod_cons, list.map],
    /-
    have alg_decomp : (⟨of x_hd.fst * of x_hd.snd * (of (x_hd.fst * x_hd.snd))⁻¹ * (list.map (λ (a : G × G), of a.fst * of a.snd * (of (a.fst * a.snd))⁻¹) x_tl).prod, _⟩ : (counit : pq_group G →* G).ker) = (⟨of x_hd.fst * of x_hd.snd * (of (x_hd.fst * x_hd.snd))⁻¹, begin 
      refine counit.mem_ker.mpr _,
      simp only [counit_of, mul_inv_rev, monoid_hom.map_mul, monoid_hom.map_mul_inv],
      group,
    end⟩ * ⟨(list.map (λ (a : G × G), of a.fst * of a.snd * (of (a.fst * a.snd))⁻¹) x_tl).prod, counit_ker_decomp_comp_in_ker x_tl⟩ : (counit : pq_group G →* G).ker) := rfl,
    simp_rw alg_decomp,
    -/
    show P (⟨of x_hd.fst * of x_hd.snd * (of (x_hd.fst * x_hd.snd))⁻¹, begin 
      refine counit.mem_ker.mpr _,
      simp only [counit_of, mul_inv_rev, monoid_hom.map_mul, monoid_hom.map_mul_inv],
      group,
    end⟩ * ⟨(list.map (λ (a : G × G), of a.fst * of a.snd * (of (a.fst * a.snd))⁻¹) x_tl).prod, counit_ker_decomp_comp_in_ker x_tl⟩ : (counit : pq_group G →* G).ker),
    apply hmul,
    apply hgen,
    apply x_ih,
  },
end

end counit_ker_induction

/-
section conjugation_induction

variables {Q : Type u} [power_quandle Q]

theorem conjugation_induction {P : pq_group Q → Prop}
(hone : P 1)
(hof : ∀ x : Q, P (of x))
(hrhd : ∀ x y : pq_group Q, P x → P y → P (x ▷ y))
(hpow : ∀ x : pq_group Q, ∀ n : ℤ, P x → P (x ^ n))
: ∀ x : pq_group Q, P x :=
begin
  sorry,
end 

end conjugation_induction
-/

/-
def pq_group_word_induction_pre (α : pq_group Q → Sort v) 
(h1 : α 1) 
(hof : ∀ x : Q, α (of x))
(ih : ∀ x : pq_group Q, ∀ y : Q, α x → α (x * (of y)))
(ihinv : ∀ x : pq_group Q, α x → α (x⁻¹)) 
: Π x : pre_pq_group Q, α ⟦x⟧
| pre_pq_group.unit := h1
| (pre_pq_group.incl x) := hof x
| (pre_pq_group.inv x) := ihinv ⟦x⟧ (pq_group_word_induction_pre x)
| (pre_pq_group.mul x (pre_pq_group.mul y z)) := begin
  have htype : α ⟦(x.mul y).mul z⟧ = α ⟦x.mul (y.mul z)⟧,
  {
    apply congr_arg,
    apply quotient.sound,
    apply pre_pq_group_rel.rel,
    apply pre_pq_group_rel'.assoc,
  },

  rw ←htype,

  exact pq_group_word_induction_pre ((x.mul y).mul z),
end
| (pre_pq_group.mul x (pre_pq_group.unit)) := begin

end
-/
/-
def linearize_pre_pq_group_tree : pre_pq_group Q → pre_pq_group Q
| (pre_pq_group.unit) := pre_pq_group.unit
| (pre_pq_group.incl q) := pre_pq_group.incl q
| (pre_pq_group.inv pre_pq_group.unit) := pre_pq_group.unit
| (pre_pq_group.inv (pre_pq_group.incl q)) := pre_pq_group.incl (q ^ (-1 : ℤ))
| (pre_pq_group.inv (pre_pq_group.inv x)) := x
| (pre_pq_group.inv (pre_pq_group.mul x y)) := pre_pq_group.mul (linearize_pre_pq_group_tree (pre_pq_group.inv y)) (linearize_pre_pq_group_tree (pre_pq_group.inv x))
| (pre_pq_group.mul x (pre_pq_group.unit)) := linearize_pre_pq_group_tree x
| (pre_pq_group.mul x (pre_pq_group.incl y)) := (linearize_pre_pq_group_tree x).mul (pre_pq_group.incl y)
| (pre_pq_group.mul x (pre_pq_group.mul y z)) := ((linearize_pre_pq_group_tree (x.mul y))).mul (linearize_pre_pq_group_tree z)
| (pre_pq_group.mul x (pre_pq_group.inv (pre_pq_group.unit))) := (linearize_pre_pq_group_tree x)
| (pre_pq_group.mul x (pre_pq_group.inv (pre_pq_group.incl q))) := (linearize_pre_pq_group_tree x).mul (pre_pq_group.incl (q ^ (-1 : ℤ)))
| (pre_pq_group.mul x (pre_pq_group.inv (pre_pq_group.inv y))) := (linearize_pre_pq_group_tree x).mul (linearize_pre_pq_group_tree y)
| (pre_pq_group.mul x (pre_pq_group.inv (pre_pq_group.mul y z))) := ((linearize_pre_pq_group_tree x).mul (linearize_pre_pq_group_tree (z.inv))).mul (linearize_pre_pq_group_tree (y.inv))


open pre_pq_group unit

#check string

example : string → string → string := string.append

instance pre_pq_group_has_repr [has_repr Q] : has_repr (pre_pq_group Q) := ⟨begin 
  intro x,
  induction x,
  {
    exact "unit",
  },
  {
    exact "incl (" ++ (repr x) ++ ")",
  },
  {
    exact "(" ++ x_ih_a ++ ").mul (" ++ x_ih_b ++ ")",
  },
  {
    exact "(" ++ x_ih ++ ").inv",
  },
end⟩

def ex_val : pre_pq_group (unit) := ((incl star).mul ((incl star).mul ((incl star).mul (incl star))))

#eval linearize_pre_pq_group_tree ex_val


lemma linearized_pres : ∀ (x : pre_pq_group Q), ⟦x⟧ = ⟦linearize_pre_pq_group_tree x⟧
| (pre_pq_group.unit) := rfl
| (pre_pq_group.incl q) := rfl
| (pre_pq_group.inv pre_pq_group.unit) := begin
  unfold linearize_pre_pq_group_tree,
  simp only [←mul_def, ←of_def, ←inv_def, incl_unit_eq_unit],
  simp only [one_inv],
end
| (pre_pq_group.inv (pre_pq_group.incl q)) := begin 
  unfold linearize_pre_pq_group_tree,
  simp only [←mul_def, ←of_def, ←inv_def, incl_unit_eq_unit],
  rw of_pow_eq_pow_of,
  simp only [gpow_one, gpow_neg],
end
| (pre_pq_group.inv (pre_pq_group.inv x)) := begin
  unfold linearize_pre_pq_group_tree,
  simp only [←mul_def, ←of_def, ←inv_def, incl_unit_eq_unit],
  simp only [inv_inv],
end
| (pre_pq_group.inv (pre_pq_group.mul x y)) := begin 
  unfold linearize_pre_pq_group_tree,
  simp only [←mul_def, ←of_def, ←inv_def, incl_unit_eq_unit],
  rw ←linearized_pres (x.inv),
  rw ←linearized_pres (y.inv),
  simp only [mul_inv_rev],
  refl,
end
| (pre_pq_group.mul x (pre_pq_group.unit)) := begin 
  unfold linearize_pre_pq_group_tree,
  simp only [←mul_def, ←of_def, ←inv_def, incl_unit_eq_unit],
  rw ←linearized_pres (x),
  simp only [mul_one],
end
| (pre_pq_group.mul x (pre_pq_group.incl y)) := begin 
  unfold linearize_pre_pq_group_tree,
  simp only [←mul_def, ←of_def, ←inv_def, incl_unit_eq_unit],
  rw ←linearized_pres x,
end
| (pre_pq_group.mul x (pre_pq_group.mul y z)) := begin 
  unfold linearize_pre_pq_group_tree,
  simp only [←mul_def, ←of_def, incl_unit_eq_unit],
  rw ←linearized_pres (x.mul y),
  rw ←linearized_pres z,
  rw ←mul_assoc,
  refl,
end
| (pre_pq_group.mul x (pre_pq_group.inv (pre_pq_group.unit))) := begin 
  unfold linearize_pre_pq_group_tree,
  simp only [←mul_def, ←of_def, ←inv_def, incl_unit_eq_unit],
  rw ←linearized_pres x,
  simp only [one_inv, mul_one],
end
| (pre_pq_group.mul x (pre_pq_group.inv (pre_pq_group.incl q))) := begin
  unfold linearize_pre_pq_group_tree,
  simp only [←mul_def, ←of_def, ←inv_def, incl_unit_eq_unit],
  rw ←linearized_pres x,
  rw of_pow_eq_pow_of,
  simp only [gpow_one, gpow_neg],
end
| (pre_pq_group.mul x (pre_pq_group.inv (pre_pq_group.inv y))) := begin 
  unfold linearize_pre_pq_group_tree,
  simp only [←mul_def, ←of_def, ←inv_def, incl_unit_eq_unit],
  rw ←linearized_pres x,
  rw ←linearized_pres y,
  simp only [inv_inv],
end
| (pre_pq_group.mul x (pre_pq_group.inv (pre_pq_group.mul y z))) := begin 
  unfold linearize_pre_pq_group_tree,
  simp only [←mul_def, ←of_def, ←inv_def, incl_unit_eq_unit],
  rw ←linearized_pres x,
  rw ←linearized_pres z.inv,
  rw ←linearized_pres y.inv,
  simp only [mul_inv_rev, mul_assoc],
  refl,
end


lemma linearized_is_linear_mul : ∀ x : pre_pq_group Q,
 ∃ z : pre_pq_group Q, ∃ q : Q, linearize_pre_pq_group_tree (x) = z.mul (pre_pq_group.incl q) :=

-/