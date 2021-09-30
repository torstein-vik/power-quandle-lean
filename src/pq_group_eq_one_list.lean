
import pq_group_eq_list

universe u

section pq_group_eq_one_list


variables {Q : Type u} [power_quandle Q]

inductive pq_group_list_one : list Q → Prop
| unit : pq_group_list_one (list.nil)
| congr_append (x y : list Q) (hx : pq_group_list_one x) (hy : pq_group_list_one y) : pq_group_list_one (x ++ y)
| congr_append_three (x y z : list Q) (hy : pq_group_list_one y) (hxz : pq_group_list_one (x ++ z)) : pq_group_list_one (x ++ y ++ z)
| congr_append_three_alt (x y z : list Q) (hy : pq_group_list_one y) (hxz : pq_group_list_one (x ++ y ++ z)) : pq_group_list_one (x ++ z)
| congr_reverse_inv (x : list Q) (hx : pq_group_list_one x) : pq_group_list_one ((x.reverse.map (λ g, g ^ (-1 : ℤ))))
| swap_append (x y : list Q) (hxy : pq_group_list_one (x ++ y)) : pq_group_list_one (y ++ x) -- Can this be inferred from the others?
| pow_nat (a : Q) (n : ℕ) : pq_group_list_one ([a ^ (- (↑n : ℤ))] ++ (list.repeat a n) )
| inv_append (a : Q) : pq_group_list_one ([a ^ (-1 : ℤ), a])
| rhd_append (a b : Q) : pq_group_list_one ([a, b, a ^ (-1 : ℤ), (a ▷ b) ^ (-1 : ℤ)])

lemma congr_reverse_inv_alt (x : list Q) (hx : pq_group_list_one ((x.reverse.map (λ g, g ^ (-1 : ℤ))))) : pq_group_list_one x :=
begin
  convert pq_group_list_one.congr_reverse_inv _ hx,
  simp only [list.map_reverse, list.reverse_reverse, list.map_map],
  clear hx,
  suffices : (λ (g : Q), g ^ (-1 : ℤ)) ∘ (λ (g : Q), g ^ (-1 : ℤ)) = id,
  {
    rw this,
    simp only [list.map_id],
  },
  funext,
  simp only [id.def, function.comp_app],
  rw power_quandle.pow_comp,
  norm_num,
  rw power_quandle.pow_one,
end

lemma inv_append_alt (a : Q) : pq_group_list_one ([a, a ^ (-1 : ℤ)]) :=
begin
  convert pq_group_list_one.inv_append (a ^ (-1 : ℤ)),
  rw power_quandle.pow_comp,
  norm_num,
  rw power_quandle.pow_one,
end

/-
theorem pq_group_list_one_iff_pq_group_list_rel (x : list Q) : pq_group_list_one x ↔ pq_group_list_rel x (list.nil) :=
begin
  split,
  {
    sorry,
  },
  {
    sorry,
  },
end
-/

theorem pq_group_list_one_iff_eq_one (x : pre_pq_group Q) : pq_group_list_one (create_list_from_pq x) ↔ (⟦x⟧ : pq_group Q) = (1 : pq_group Q) :=
begin
  split,
  {
    rw ←create_list_from_pq_eq_id,
    generalize : create_list_from_pq x = y,
    clear x,
    rename y x,
    intro hx,
    induction hx,
    {
      refl,
    },
    {
      simp only [list.map_append, list.prod_append, hx_ih_hx, hx_ih_hy, one_mul],
    },
    {
      simp only [list.map_append, list.prod_append, list.append_assoc],
      simp only [list.map_append, list.prod_append] at hx_ih_hxz,
      rw hx_ih_hy,
      rw one_mul,
      rw hx_ih_hxz,
    },
    {
      simp only [list.map_append, list.prod_append, list.append_assoc] at hx_ih_hxz,
      simp only [list.map_append, list.prod_append],
      rw hx_ih_hy at hx_ih_hxz,
      rw one_mul at hx_ih_hxz,
      exact hx_ih_hxz,
    },
    {
      -- Factor out to lemma
      have proc_is_inv : ∀ a : list Q, (list.map of (list.map (λ (g : Q), g ^ (-1 : ℤ)) (list.reverse a))).prod = ((list.map of a).prod)⁻¹,
      {
        intros a,
        simp only [list.map_map, list.map_reverse], 
        induction a,
        {
          simp only [one_inv, list.prod_nil, list.map, list.reverse_nil],
        },
        {
          simp only [list.reverse_cons, mul_inv_rev, mul_one, list.prod_append, function.comp_app, list.prod_cons, list.prod_nil, list.map],
          rw a_ih,
          simp only [mul_right_inj],
          rw of_inv,
        },
      },
      rw proc_is_inv,
      rw hx_ih,
      rw one_inv,
    },
    {
      simp only [list.map_append, list.prod_append] at hx_ih,
      simp only [list.map_append, list.prod_append],
      suffices : ∀ x y : pq_group Q, x * y = 1 → y * x = 1,
      {
        apply this,
        assumption,
      },
      intros a b hab,
      suffices : a = b⁻¹,
      {
        rw this,
        simp only [mul_right_inv],
      },
      exact eq_inv_of_mul_eq_one hab,
    },
    {
      simp only [list.prod_repeat, list.map_repeat, list.prod_cons, list.singleton_append, list.map],
      rw of_pow_eq_pow_of,
      simp only [gpow_neg, mul_left_inv, gpow_coe_nat],
    },
    {
      simp only [mul_one, list.prod_cons, list.prod_nil, list.map],
      rw of_pow_eq_pow_of,
      simp only [gpow_one, gpow_neg, mul_left_inv],
    },
    {
      simp only [mul_one, list.prod_cons, list.prod_nil, list.map],
      rw of_pow_eq_pow_of,
      rw of_pow_eq_pow_of,
      rw ←rhd_of_eq_of_rhd,
      simp only [gpow_one, gpow_neg],
      rw rhd_def_group,
      simp only [conj_inv],
      simp only [←mul_assoc],
      simp only [mul_right_inv, mul_inv_cancel_right, inv_mul_cancel_right],
    },
  },
  {
    suffices : ∀ x y : pre_pq_group Q, ⟦x⟧ = ⟦y⟧ → pq_group_list_one (create_list_from_pq (y.inv.mul x)),
    {
      specialize this x pre_pq_group.unit,
      intro hx,
      specialize this hx,
      clear hx,
      unfold create_list_from_pq at this,
      simp only [list.append_nil, list.map, list.reverse_nil] at this,
      exact this,
    },
    clear x,
    intros x y hxy,
    rw pq_group_list_rel_iff_pq_group_eq at hxy,
    unfold create_list_from_pq,
    revert hxy,
    generalize : create_list_from_pq x = a,
    generalize : create_list_from_pq y = b,
    intros hab,
    clear x y,
    induction hab,
    {
      rename hab y,
      induction y,
      {
        simp only [list.append_nil, list.map, list.reverse_nil],
        exact pq_group_list_one.unit,
      },
      {
        simp only [list.reverse_cons, list.map_reverse, list.map_append, list.append_assoc, list.singleton_append, list.map],
        suffices : pq_group_list_one ((list.map (λ (q : Q), q ^ (-1 : ℤ)) y_tl).reverse ++ [y_hd ^ (-1 : ℤ), y_hd] ++ y_tl),
        {
          simp only [list.cons_append, list.append_assoc, list.singleton_append, list.map] at this,
          exact this,
        },
        apply pq_group_list_one.congr_append_three,
        {
          exact pq_group_list_one.inv_append y_hd,
        },
        {
          simp only [list.map_reverse] at y_ih,
          exact y_ih,
        },
      },
    },
    {
      apply congr_reverse_inv_alt,
      simp only [list.map_reverse, list.map_append, list.reverse_append, list.reverse_reverse, list.map_map],
      have func_is_id : (λ (g : Q), g ^ (-1 : ℤ)) ∘ (λ (q : Q), q ^ (-1 : ℤ)) = id,
      {
        funext,
        simp only [id.def, function.comp_app],
        rw power_quandle.pow_comp,
        norm_num,
        rw power_quandle.pow_one,
      },
      rw func_is_id,
      clear func_is_id,
      simp only [list.map_id],
      simp only [list.map_reverse] at hab_ih,
      exact hab_ih,
    },
    {
      suffices : pq_group_list_one (list.map (λ (q : Q), q ^ (-1 : ℤ)) hab_z.reverse ++ (hab_y ++ list.map (λ (q : Q), q ^ (-1 : ℤ)) hab_y.reverse) ++ hab_x),
      {
        apply pq_group_list_one.congr_append_three_alt _ _ _ _ this,
        clear this,
        clear hab_hxy hab_hyz hab_ih_hxy hab_ih_hyz a b hab_x hab_z,
        rename hab_y y,
        generalize hy : y.reverse = y1,
        have hy1 : y = y1.reverse,
        {
          rw ←hy,
          simp only [list.reverse_reverse],
        },
        rw hy1,
        clear hy hy1 y,
        rename y1 y,
        induction y,
        {
          simp only [list.append_nil, list.map, list.reverse_nil],
          exact pq_group_list_one.unit,
        },
        {
          suffices : pq_group_list_one ((y_tl).reverse ++ [y_hd, y_hd ^ (-1 : ℤ)] ++ list.map (λ (q : Q), q ^ (-1 : ℤ)) y_tl),
          {
            simp only [list.reverse_cons, list.append_assoc, list.singleton_append, list.map],
            simp only [list.cons_append, list.append_assoc, list.singleton_append, list.map] at this,
            exact this,
          },
          apply pq_group_list_one.congr_append_three,
          {
            exact inv_append_alt y_hd,
          },
          {
            exact y_ih,
          },
        },
      },
      suffices : pq_group_list_one ((list.map (λ (q : Q), q ^ (-1 : ℤ)) hab_z.reverse ++ hab_y) ++ (list.map (λ (q : Q), q ^ (-1 : ℤ)) hab_y.reverse ++ hab_x)),
      {
        simp only [list.append_assoc] at this,
        simp only [list.append_assoc],
        exact this,
      },
      apply pq_group_list_one.congr_append,
      assumption,
      assumption,
    },
    {
      simp only [list.map_reverse, list.map_append, list.reverse_append, list.append_assoc],
      suffices : pq_group_list_one ((list.map (λ (q : Q), q ^ (-1 : ℤ)) hab_x').reverse ++ ((list.map (λ (q : Q), q ^ (-1 : ℤ)) hab_y').reverse ++ hab_y) ++ hab_x),
      {
        simp only [list.append_assoc] at this,
        exact this,
      },
      apply pq_group_list_one.congr_append_three,
      simp only [list.map_reverse] at hab_ih_hy,
      assumption,
      simp only [list.map_reverse] at hab_ih_hx,
      assumption,
    },
    {
      suffices : pq_group_list_one (list.map (λ (q : Q), q ^ (-1 : ℤ)) (hab_x ++ (list.map (λ (g : Q), g ^ (-1 : ℤ)) hab_y.reverse)).reverse),
      {
        simp only [list.map_reverse, list.reverse_reverse, list.map_map],
        simp only [list.map_reverse, list.map_append, list.reverse_append, list.reverse_reverse, list.map_map] at this,
        exact this,
      },
      apply pq_group_list_one.congr_reverse_inv,
      apply pq_group_list_one.swap_append,
      apply hab_ih,
    },
    {
      apply congr_reverse_inv_alt,
      simp only [list.reverse_repeat, list.map_repeat, list.reverse_append, list.reverse_singleton, list.singleton_append, list.map],
      rw power_quandle.pow_comp,
      rw power_quandle.pow_comp,
      norm_num,
      rw power_quandle.pow_one,
      apply pq_group_list_one.pow_nat,
    },
    {
      simp only [list.nil_append, list.map, list.reverse_nil],
      apply pq_group_list_one.inv_append,
    },
    {
      simp only [list.reverse_singleton, list.singleton_append, list.map],
      apply congr_reverse_inv_alt,
      simp only [list.reverse_cons, list.cons_append, list.map_nil, list.reverse_singleton, list.singleton_append, list.map],
      convert pq_group_list_one.rhd_append hab_a (hab_b ^ (-1 : ℤ)),
      rw power_quandle.pow_comp,
      norm_num,
      rw power_quandle.pow_one,
      rw power_quandle.pow_rhd,      
    },
  },
end

end pq_group_eq_one_list
