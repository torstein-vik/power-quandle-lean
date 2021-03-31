
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
        rw power_quandle.pow_1,
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

end word_induction

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