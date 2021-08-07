
import counit_ker_abelian
import pq_group_homo_locus
import pq_induction_principles

universe u

section pq_group_homo_locus_pres

inductive pre_homo_locus_pres (G : Type u) [group G] : Type u
| unit : pre_homo_locus_pres
| incl (x y : G) : pre_homo_locus_pres
| mul (x y : pre_homo_locus_pres) : pre_homo_locus_pres
| inv (x : pre_homo_locus_pres) : pre_homo_locus_pres

open pre_homo_locus_pres

inductive pre_homo_locus_pres_rel' (G : Type u) [group G] : pre_homo_locus_pres G → pre_homo_locus_pres G → Type u
| refl {a : pre_homo_locus_pres G} : pre_homo_locus_pres_rel' a a
| symm {a b : pre_homo_locus_pres G} (hab : pre_homo_locus_pres_rel' a b) : pre_homo_locus_pres_rel' b a
| trans {a b c : pre_homo_locus_pres G} 
  (hab : pre_homo_locus_pres_rel' a b) (hbc : pre_homo_locus_pres_rel' b c) : pre_homo_locus_pres_rel' a c
| congr_mul {a b a' b' : pre_homo_locus_pres G} 
  (ha : pre_homo_locus_pres_rel' a a') (hb : pre_homo_locus_pres_rel' b b') : 
  pre_homo_locus_pres_rel' (mul a b) (mul a' b') 
| congr_inv {a a' : pre_homo_locus_pres G} (ha : pre_homo_locus_pres_rel' a a') : 
  pre_homo_locus_pres_rel' (inv a) (inv a')
| assoc (a b c : pre_homo_locus_pres G) : pre_homo_locus_pres_rel' (mul (mul a b) c) (mul a (mul b c))
| one_mul (a : pre_homo_locus_pres G) : pre_homo_locus_pres_rel' (mul unit a) a
| mul_one (a : pre_homo_locus_pres G) : pre_homo_locus_pres_rel' (mul a unit) a
| mul_left_inv (a : pre_homo_locus_pres G) : pre_homo_locus_pres_rel' (mul (inv a) a) unit
| comm (a1 a2 b1 b2 : G) : pre_homo_locus_pres_rel' (mul (incl a1 a2) (incl b1 b2)) (mul (incl b1 b2) (incl a1 a2))
| homo_locus_eq_zero (a b : G) (hab : homo_locus (a, b)) : pre_homo_locus_pres_rel' (incl a b) unit
| third_cancel (a b x : G) : pre_homo_locus_pres_rel' (incl a b) (mul (mul (incl x a)  (incl (x * a) (b))) (inv (incl x (a * b))))
| rhd_inv (a b : G) : pre_homo_locus_pres_rel' (incl a b) (inv (incl (a * b) (a⁻¹)))

inductive pre_homo_locus_pres_rel (G : Type u) [group G] : pre_homo_locus_pres G → pre_homo_locus_pres G → Prop
| rel {a b : pre_homo_locus_pres G} (r : pre_homo_locus_pres_rel' G a b) : pre_homo_locus_pres_rel a b


variables {G : Type*} [group G]

lemma pre_homo_locus_pres_rel'.rel {a b : pre_homo_locus_pres G} : pre_homo_locus_pres_rel' G a b → pre_homo_locus_pres_rel G a b := pre_homo_locus_pres_rel.rel


@[refl]
lemma pre_homo_locus_pres_rel.refl {a : pre_homo_locus_pres G} : pre_homo_locus_pres_rel G a a := 
pre_homo_locus_pres_rel'.rel pre_homo_locus_pres_rel'.refl


@[symm]
lemma pre_homo_locus_pres_rel.symm {a b : pre_homo_locus_pres G} : pre_homo_locus_pres_rel G a b → pre_homo_locus_pres_rel G b a
| ⟨r⟩ := r.symm.rel


@[trans]
lemma pre_homo_locus_pres_rel.trans {a b c : pre_homo_locus_pres G} : 
pre_homo_locus_pres_rel G a b → pre_homo_locus_pres_rel G b c → pre_homo_locus_pres_rel G a c
| ⟨rab⟩ ⟨rbc⟩ := (rab.trans rbc).rel


instance pre_homo_locus_pres.setoid (G : Type*) [group G] : setoid (pre_homo_locus_pres G) :=
{
    r := pre_homo_locus_pres_rel G,
    iseqv := begin
        split, apply pre_homo_locus_pres_rel.refl,
        split, apply pre_homo_locus_pres_rel.symm,
        apply pre_homo_locus_pres_rel.trans,
    end
}


def homo_locus_pres (G : Type*) [group G] := quotient (pre_homo_locus_pres.setoid G)


instance homo_locus_pres_is_group : group (homo_locus_pres G) := 
{ mul := λ a b, quotient.lift_on₂ a b
                  (λ a b, ⟦pre_homo_locus_pres.mul a b⟧)
                  (λ a b a' b' ⟨ha⟩ ⟨hb⟩,
                    quotient.sound (pre_homo_locus_pres_rel'.congr_mul ha hb).rel),
  one := ⟦unit⟧,
  inv := λ a, quotient.lift_on a
                (λ a, ⟦pre_homo_locus_pres.inv a⟧)
                (λ a a' ⟨ha⟩,
                  quotient.sound (pre_homo_locus_pres_rel'.congr_inv ha).rel),
  mul_assoc := λ a b c,
    quotient.induction_on₃ a b c (λ a b c, quotient.sound (pre_homo_locus_pres_rel'.assoc a b c).rel),
  one_mul := λ a,
    quotient.induction_on a (λ a, quotient.sound (pre_homo_locus_pres_rel'.one_mul a).rel),
  mul_one := λ a,
    quotient.induction_on a (λ a, quotient.sound (pre_homo_locus_pres_rel'.mul_one a).rel),
  mul_left_inv := λ a,
    quotient.induction_on a (λ a, quotient.sound (pre_homo_locus_pres_rel'.mul_left_inv a).rel) }

def homo_locus_of (x : G × G) : homo_locus_pres G := ⟦incl x.1 x.2⟧

lemma homo_locus_of_def (x : G × G) : homo_locus_of x = ⟦incl x.1 x.2⟧ := rfl

lemma homo_locus_pres_one_def : (1 : homo_locus_pres G) = ⟦unit⟧ := rfl

lemma homo_locus_pres_mul_def (x y : pre_homo_locus_pres G) : (⟦x⟧ * ⟦y⟧ : homo_locus_pres G) = ⟦x.mul y⟧ := rfl 

lemma homo_locus_pres_inv_def (x : pre_homo_locus_pres G) : (⟦x⟧⁻¹ : homo_locus_pres G) = ⟦x.inv⟧ := rfl 

lemma homo_locus_pres_quot_mk_helper (x : pre_homo_locus_pres G) : quot.mk setoid.r x = ⟦x⟧ := rfl

variables {H : Type*} [group H]

/-

| third_cancel (a b x : G) : pre_homo_locus_pres_rel' (incl a b) (mul (incl x a) (mul (incl (x * a) (b)) (inv (incl x (a * b)))))
| rhd_inv (a b : G) : pre_homo_locus_pres_rel' (incl a b) (inv (incl (a * b) (a⁻¹)))
-/

def is_homo_locus_liftable (f : G × G → H) : Prop := (∀ a b : G × G, f a * f b = f b * f a) ∧ (∀ a b : G, homo_locus (a, b) → f (a, b) = 1) ∧ (∀ a b x : G, f (a, b) = f (x, a) * f (x * a, b) * ((f (x, (a * b)))⁻¹)) ∧ (∀ a b : G, f (a, b) = (f (a * b, a⁻¹))⁻¹)


def lift_homo_locus_pres_morph_pre (f : G × G → H) (hf : is_homo_locus_liftable f) : pre_homo_locus_pres G → H
| unit := 1
| (incl a b) := f (a, b)
| (mul a b) := lift_homo_locus_pres_morph_pre a * lift_homo_locus_pres_morph_pre b
| (inv a) := (lift_homo_locus_pres_morph_pre a)⁻¹

def lift_homo_locus_pres_morph (f : G × G → H) (hf : is_homo_locus_liftable f) : homo_locus_pres G →* H := { 
  to_fun := quotient.lift (lift_homo_locus_pres_morph_pre f hf) begin 
    intros a b hab,
    induction hab,
    induction hab_r,
    {
      refl,
    },
    {
      symmetry,
      assumption,
    },
    {
      transitivity,
      assumption,
      assumption,
    },
    {
      unfold lift_homo_locus_pres_morph_pre,
      congr,
      assumption,
      assumption,
    },
    {
      unfold lift_homo_locus_pres_morph_pre,
      congr,
      assumption,
    },
    {
      unfold lift_homo_locus_pres_morph_pre,
      rw mul_assoc,
    },
    {
      unfold lift_homo_locus_pres_morph_pre,
      rw one_mul,
    },
    {
      unfold lift_homo_locus_pres_morph_pre,
      rw mul_one,
    },
    {
      unfold lift_homo_locus_pres_morph_pre,
      rw mul_left_inv,
    },
    {
      unfold lift_homo_locus_pres_morph_pre,
      rw hf.1,
    },
    {
      unfold lift_homo_locus_pres_morph_pre,
      rw hf.2.1,
      assumption,
    },
    {
      unfold lift_homo_locus_pres_morph_pre,
      rw hf.2.2.1,
    },
    {
      unfold lift_homo_locus_pres_morph_pre,
      rw hf.2.2.2,
    },
  end,
  map_one' := begin 
    refl,
  end,
  map_mul' := begin 
    intros x y,
    induction x,
    induction y,
    refl,
    refl,
    refl,
  end }

lemma homo_locus_of_inv_alt (x y : G) : (homo_locus_of (x * y, x⁻¹))⁻¹ = homo_locus_of (x, y) :=
begin
  symmetry,
  apply quotient.sound,
  simp only,
  fconstructor,
  exact pre_homo_locus_pres_rel'.rhd_inv x y,
end

lemma homo_locus_of_inv (x y : G) : (homo_locus_of (x, y))⁻¹ = homo_locus_of (x * y, x⁻¹) :=
begin
  rw ←homo_locus_of_inv_alt,
  simp only [inv_inv],
end

lemma homo_locus_of_one (x y : G) (hxy : homo_locus (x, y)) : homo_locus_of (x, y) = 1 :=
begin
  apply quotient.sound,
  simp only,
  fconstructor,
  exact pre_homo_locus_pres_rel'.homo_locus_eq_zero x y hxy,
end

lemma homo_locus_pres_comm (x y : homo_locus_pres G) : x * y = y * x :=
begin
  induction x,
  induction y,
  {
    rw homo_locus_pres_quot_mk_helper,
    rw homo_locus_pres_quot_mk_helper,
    induction x,
    {
      rw ←homo_locus_pres_one_def,
      simp only [mul_one, one_mul],
    },
    {
      induction y,
      {
        rw ←homo_locus_pres_one_def,
        simp only [mul_one, one_mul],
      },
      {
        apply quotient.sound,
        fconstructor,
        exact pre_homo_locus_pres_rel'.comm x_x x_y y_x y_y,
      },
      {
        rw ←homo_locus_pres_mul_def,
        rw ←mul_assoc,
        rw y_ih_x,
        rw mul_assoc,
        rw y_ih_y,
        rw ←mul_assoc,
      },
      {
        rw ←homo_locus_pres_inv_def,
        have : (⟦y_x⟧ * ⟦y_x⟧⁻¹ * ⟦incl x_x x_y⟧ * ⟦y_x⟧ : homo_locus_pres G) = ⟦y_x⟧ * ⟦incl x_x x_y⟧ * ⟦y_x⟧⁻¹ * ⟦y_x⟧,
        {
          simp only [one_mul, mul_right_inv, inv_mul_cancel_right],
          rw y_ih,
        },
        rw mul_left_inj at this,
        rw mul_assoc at this,
        rw mul_assoc at this,
        rw mul_right_inj at this,
        rw this,
      },
    },
    {
      rw ←homo_locus_pres_mul_def,
      rw mul_assoc,
      rw x_ih_y,
      rw ←mul_assoc,
      rw x_ih_x,
      rw ←mul_assoc,
    },
    {
      rw ←homo_locus_pres_inv_def,
      have : (⟦x_x⟧ * ⟦x_x⟧⁻¹ * ⟦y⟧ * ⟦x_x⟧ : homo_locus_pres G) = ⟦x_x⟧ * ⟦y⟧ * ⟦x_x⟧⁻¹ * ⟦x_x⟧,
      {
        simp only [one_mul, mul_right_inv, inv_mul_cancel_right],
        rw x_ih,
      },
      rw mul_left_inj at this,
      rw mul_assoc at this,
      rw mul_assoc at this,
      rw mul_right_inj at this,
      rw this,
    },
  },
  refl,
  refl,
end

end pq_group_homo_locus_pres

section pq_group_homo_locus_pres_double_list

variables {G : Type u} [group G]

open pre_homo_locus_pres

def pre_homo_locus_pres_to_list : pre_homo_locus_pres G → list G
| unit := []
| (incl a b) := [a, b]
| (mul a b) := let x := (pre_homo_locus_pres_to_list a) in let y := (pre_homo_locus_pres_to_list b) in x ++ y ++ [x.prod⁻¹]
| (inv a) := let x := (pre_homo_locus_pres_to_list a) in (x.map (λ x : G, x⁻¹)).reverse

lemma pre_homo_locus_pres_to_list_eq_id (x : pre_homo_locus_pres G) : ((counit_ker_decomp (pre_homo_locus_pres_to_list x)).map (homo_locus_of)).prod = ⟦x⟧ :=
begin
  induction x,
  {
    unfold pre_homo_locus_pres_to_list,
    unfold counit_ker_decomp,
    unfold counit_ker_decomp_pre,
    simp only [list.prod_nil, list.map],
    refl,
  },
  {
    unfold pre_homo_locus_pres_to_list,
    unfold counit_ker_decomp,
    unfold counit_ker_decomp_pre,
    simp only [mul_one, one_mul, list.prod_cons, list.prod_nil, list.map],
    suffices : homo_locus_of (1, x_x) = 1,
    simp only [this, one_mul], refl,
    apply quotient.sound,
    simp only,
    fconstructor,
    refine pre_homo_locus_pres_rel'.homo_locus_eq_zero 1 x_x _,
    exact homo_locus_closed_left_one x_x,
  },
  {
    unfold pre_homo_locus_pres_to_list,
    simp only,
    have alg_rw : ⟦x_x.mul x_y⟧ = (⟦x_x⟧ * ⟦x_y⟧ : homo_locus_pres G) := rfl,
    rw alg_rw,
    clear alg_rw,
    rw ←x_ih_x,
    rw ←x_ih_y,
    clear x_ih_x x_ih_y,
    rw counit_ker_decomp_append,
    rw counit_ker_decomp_append,
    simp only [mul_right_inj, list.map_append, list.prod_append, list.append_assoc],
    unfold counit_ker_decomp_pre,
    simp only [mul_one, list.prod_cons, list.prod_nil, list.map],
    generalize : pre_homo_locus_pres_to_list x_x = x,
    generalize : pre_homo_locus_pres_to_list x_y = y,
    clear x_x x_y,
    unfold counit_ker_decomp,
    suffices : (list.map homo_locus_of (counit_ker_decomp_pre x.prod y)).prod = (list.map homo_locus_of (counit_ker_decomp_pre 1 y)).prod * (homo_locus_of (x.prod * y.prod, (x.prod)⁻¹))⁻¹,
    {
      rw this,
      simp only [inv_mul_cancel_right],
    },
    rw homo_locus_of_inv_alt,
    induction y generalizing x,
    {
      simp only [mul_one, list.prod_nil],
      unfold counit_ker_decomp_pre,
      simp only [one_mul, list.prod_nil, list.map],
      symmetry,
      apply quotient.sound,
      fconstructor,
      refine pre_homo_locus_pres_rel'.homo_locus_eq_zero (x.prod, 1).fst (x.prod, 1).snd _,
      simp only,
      exact homo_locus_closed_right_one (list.prod x),
    },
    {
      unfold counit_ker_decomp_pre,
      simp only [one_mul, list.prod_cons, list.map],
      specialize y_ih (x ++ [y_hd]),
      simp only [mul_inv_rev, mul_one, list.prod_append, list.prod_cons, list.prod_nil] at y_ih,
      rw y_ih,
      clear y_ih,
      rw ←mul_assoc,
      have one_rw : homo_locus_of (1, y_hd) = 1,
      {
        apply homo_locus_of_one,
        exact homo_locus_closed_left_one y_hd,
      },
      rw one_rw,
      rw one_mul,
      sorry,
    },
  },
  {
    sorry,
  },
end

end pq_group_homo_locus_pres_double_list

section pq_group_homo_locus_pres_iso_ker_counit

variables {G : Type u} [group G]

def homo_locus_pres_iso_ker_counit_forward : homo_locus_pres G →* (counit : pq_group G →* G).ker :=
begin
  fapply lift_homo_locus_pres_morph,
  {
    intro g,
    fconstructor,
    exact of g.1 * of g.2 * (of (g.1 * g.2))⁻¹,
    refine counit.mem_ker.mpr _,
    simp only [counit_of, mul_inv_rev, monoid_hom.map_mul, monoid_hom.map_mul_inv],
    group,
  },
  {
    split,
    {
      intros a b,
      cases a with a1 a2,
      cases b with b1 b2,
      simp only,
      rw counit_ker_abelian,
    },
    split,
    {
      intros a b hab,
      simp only,
      ext1,
      simp only [subgroup.coe_one, subgroup.coe_mk],
      simp only [homo_locus_def] at hab,
      rw hab,
      simp only [mul_right_inv],
    },
    split,
    {
      intros a b x,
      simp only,
      ext1,
      simp only [mul_inv_rev, subgroup.coe_inv, subgroup.coe_mul, inv_inv, subgroup.coe_mk],
      suffices : of a * (of (x * a))⁻¹ * (of (x * a) * of b * (of (x * a * b))⁻¹) * of (x * (a * b)) * (of (a * b))⁻¹ = of a * of b * (of (a * b))⁻¹,
      {
        assoc_rw this,
        clear this _inst,
        assoc_rw counit_ker_abelian_counit (of a * of b * (of (a * b))⁻¹) _ _,
        simp only [one_mul, mul_right_inv],
        simp only [counit_of, mul_inv_rev, monoid_hom.map_mul, monoid_hom.map_mul_inv],
        group,
      },
      group,
    },
    {
      intros a b,
      simp only,
      ext1,
      simp only [mul_inv_rev, subgroup.coe_inv, inv_inv, subgroup.coe_mk],
      rw ←rhd_def_group,
      rw ←rhd_of_eq_of_rhd,
      rw rhd_def_group,
      rw inv_of,
      simp only [inv_inv],
      group,
    },
  },
end


def homo_locus_pres_iso_ker_counit_backward_fun_aux_pre : G → list G → homo_locus_pres G
| y (a :: x) := homo_locus_of (y, a) * homo_locus_pres_iso_ker_counit_backward_fun_aux_pre (y * a) x
| y [] := 1
   
def homo_locus_pres_iso_ker_counit_backward_fun_aux : list G → homo_locus_pres G := λ x, homo_locus_pres_iso_ker_counit_backward_fun_aux_pre 1 (x)

def homo_locus_pres_iso_ker_counit_backward_fun : (counit : pq_group G →* G).ker → homo_locus_pres G := 
begin 
  fapply pq_group_list_data_property,
  exact (λ ⟨x, hx⟩, homo_locus_pres_iso_ker_counit_backward_fun_aux x),
  {
    intros x y hx hy hxy,
    
    induction hxy,
    induction hxy_r,
    {
      refl,
    },
    {
      symmetry,
      solve_by_elim
    },
    {
      have hb : ⟦hxy_r_b⟧ ∈ has_coe_t_aux.coe counit.ker,
      {
        suffices : ⟦hxy_r_a⟧ = ⟦hxy_r_b⟧, 
        rw ←this,
        exact hx,
        apply quotient.sound,
        fconstructor,
        assumption,
      },
      transitivity,
      apply hxy_r_ih_hab,
      assumption,
      solve_by_elim,
    },
    {
      unfold create_list_from_pq,

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
      sorry,
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
      sorry,
    },
    {
      sorry,
    },
  },
end

def homo_locus_pres_iso_ker_counit_backward : (counit : pq_group G →* G).ker →* homo_locus_pres G := { 
  to_fun := homo_locus_pres_iso_ker_counit_backward_fun,
  map_one' := sorry,
  map_mul' := sorry }

theorem homo_locus_pres_iso_ker_counit_forward_bijective : function.bijective (homo_locus_pres_iso_ker_counit_forward : homo_locus_pres G → (counit : pq_group G →* G).ker) :=
begin
  split,
  {
    refine homo_locus_pres_iso_ker_counit_forward.injective_iff.mpr _,
    intros a ha,
    --revert ha,
    --generalize hab : homo_locus_pres_iso_ker_counit_forward a = b,
    --intro hb,
    sorry,
    
  },
  {
    refine counit_ker_induction _ _,
    {
      intros a b,
      use homo_locus_of (a, b),
      refl,
    },
    {
      intros a b ha hb,
      cases ha with x hx,
      cases hb with y hy,
      use x * y,
      simp only [monoid_hom.map_mul, hx, hy],
    },
  },
end


def homo_locus_pres_iso_ker_counit : homo_locus_pres G ≃* (counit : pq_group G →* G).ker := { 
  to_fun := homo_locus_pres_iso_ker_counit_forward,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry,
  map_mul' := begin 
    intros x y,
    simp only [monoid_hom.map_mul],
  end }

end pq_group_homo_locus_pres_iso_ker_counit
