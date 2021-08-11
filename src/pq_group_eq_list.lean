
import pq_induction_principles

universe u

section pq_group_eq_list

variables {Q : Type u} [power_quandle Q]


inductive pq_group_list_rel : list Q → list Q → Prop
| refl (x : list Q) : pq_group_list_rel x x
| symm (x y : list Q) (hxy : pq_group_list_rel x y) : pq_group_list_rel y x
| trans (x y z : list Q) (hxy : pq_group_list_rel x y) (hyz : pq_group_list_rel y z) : pq_group_list_rel x z
| congr_append (x x' y y' : list Q) (hx : pq_group_list_rel x x') (hy : pq_group_list_rel y y') : pq_group_list_rel (y ++ x) (y' ++ x')
| congr_reverse_inv (x y : list Q) (hxy : pq_group_list_rel x y) : pq_group_list_rel ((x.reverse.map (λ g, g ^ (-1 : ℤ)))) ((y.reverse.map (λ g, g ^ (-1 : ℤ))))
| pow_nat (a : Q) (n : ℕ) : pq_group_list_rel ([a ^ (↑n : ℤ)]) (list.repeat a n)
| inv_append (a : Q) : pq_group_list_rel ([a ^ (-1 : ℤ), a]) ([])
| rhd_append (a b : Q) : pq_group_list_rel ([a, b, a ^ (-1 : ℤ)]) ([a ▷ b])

lemma pq_group_list_rel_congr_reverse_inv_alt (x y : list Q) (hxy : pq_group_list_rel ((x.reverse.map (λ g, g ^ (-1 : ℤ)))) ((y.reverse.map (λ g, g ^ (-1 : ℤ))))) : pq_group_list_rel x y :=
begin
  suffices : ∀ a : list Q, (list.map (λ (g : Q), g ^ (-1 : ℤ)) ((list.map (λ (g : Q), g ^ (-1 : ℤ)) a.reverse)).reverse) = a,
  {
    rw ←this x,
    rw ←this y,
    apply pq_group_list_rel.congr_reverse_inv,
    exact hxy,
  },
  clear hxy x y,
  intros a,
  simp only [list.map_reverse, list.reverse_reverse, list.map_map],
  convert list.map_id a,
  funext,
  simp only [id.def, function.comp_app],
  rw power_quandle.pow_comp,
  norm_num,
  rw power_quandle.pow_one,
end

lemma pq_group_list_rel_inv_append_alt (a : Q) : pq_group_list_rel [a, a^(-1 : ℤ)] [] :=
begin
  have := pq_group_list_rel.inv_append (a ^ (-1 : ℤ)),
  rw power_quandle.pow_comp at this,
  norm_num at this,
  rw power_quandle.pow_one at this,
  exact this,
end

lemma pq_group_list_rel_pred_mul_nat (a : Q) (n : ℕ) : pq_group_list_rel [a ^ (↑n : ℤ)] ([a] ++ [a ^ ((↑n : ℤ) - 1)]) :=
begin
  apply pq_group_list_rel.trans,
  apply pq_group_list_rel.pow_nat,
  cases n,
  {
    simp only [list.repeat, zero_sub, int.coe_nat_zero, int.of_nat_eq_coe, list.singleton_append],
    refine pq_group_list_rel.symm [a, a ^ -1] list.nil _,
    apply pq_group_list_rel_inv_append_alt,
  },
  {
    have : list.repeat a n.succ = [a] ++ list.repeat a n,
    {
      refl,
    },
    rw this,
    apply pq_group_list_rel.congr_append,
    {
      simp only [int.coe_nat_succ, int.of_nat_eq_coe, add_sub_cancel],
      apply pq_group_list_rel.symm,
      apply pq_group_list_rel.pow_nat,
    },
    {
      exact pq_group_list_rel.refl [a],
    },
  },
end


lemma pq_group_list_rel_succ_mul_nat (a : Q) (n : ℕ) : pq_group_list_rel [a ^ (↑n : ℤ)] ([a ^ ((↑n : ℤ) + 1)] ++ [a ^ (-1 : ℤ)]) :=
begin
  apply pq_group_list_rel.trans,
  apply pq_group_list_rel.pow_nat,
  suffices : pq_group_list_rel (list.repeat a n) ([a ^ (↑n : ℤ)] ++ [a] ++ [a ^ (-1 : ℤ)]),
  {
    apply pq_group_list_rel.trans _ _ _ this _,
    clear this,
    apply pq_group_list_rel.congr_append,
    apply pq_group_list_rel.refl,
    apply pq_group_list_rel.symm,
    have := pq_group_list_rel.pow_nat a (n + 1),
    apply pq_group_list_rel.trans _ _ _ this _,
    clear this,
    rw list.repeat_add,
    simp only [list.repeat],
    apply pq_group_list_rel.congr_append,
    apply pq_group_list_rel.refl,
    apply pq_group_list_rel.symm,
    apply pq_group_list_rel.pow_nat,
  },
  have : list.repeat a n = list.repeat a n ++ list.nil,
  {
    simp only [list.append_nil],
  },
  rw this,
  clear this,
  rw list.append_assoc,
  apply pq_group_list_rel.congr_append,
  {
    simp only [list.singleton_append],
    apply pq_group_list_rel.symm,
    apply pq_group_list_rel_inv_append_alt,
  },
  {
    apply pq_group_list_rel.symm,
    exact pq_group_list_rel.pow_nat a n,
  },
end

theorem pq_group_list_rel_iff_pq_group_eq (a b : pre_pq_group Q) : ⟦a⟧ = ⟦b⟧ ↔ pq_group_list_rel (create_list_from_pq a) (create_list_from_pq b) :=
begin
  split,
  {
    intros hab,
    have hab1 := quotient.exact hab,
    clear hab,
    rename hab1 hab,
    induction hab,
    induction hab_r,
    {
      exact pq_group_list_rel.refl (create_list_from_pq hab_r),
    },
    {
      exact pq_group_list_rel.symm (create_list_from_pq hab_r_a) (create_list_from_pq hab_r_b) hab_r_ih,
    },
    {
      exact pq_group_list_rel.trans (create_list_from_pq hab_r_a) (create_list_from_pq hab_r_b) (create_list_from_pq hab_r_c) hab_r_ih_hab hab_r_ih_hbc,
    },
    {
      unfold create_list_from_pq,
      exact pq_group_list_rel.congr_append (create_list_from_pq hab_r_b) (create_list_from_pq hab_r_b')
      (create_list_from_pq hab_r_a)
      (create_list_from_pq hab_r_a')
      hab_r_ih_hb
      hab_r_ih_ha,
    },
    {
      unfold create_list_from_pq,
      exact pq_group_list_rel.congr_reverse_inv (create_list_from_pq hab_r_a) (create_list_from_pq hab_r_a') hab_r_ih,
    },
    {
      unfold create_list_from_pq,
      simp only [list.append_assoc],
      exact pq_group_list_rel.refl (create_list_from_pq hab_r_a ++ (create_list_from_pq hab_r_b ++ create_list_from_pq hab_r_c)),
    },
    {
      unfold create_list_from_pq,
      simp only [list.nil_append],
      exact pq_group_list_rel.refl (create_list_from_pq hab_r),
    },
    {
      unfold create_list_from_pq,
      simp only [list.append_nil],
      exact pq_group_list_rel.refl (create_list_from_pq hab_r),
    },
    {
      unfold create_list_from_pq,
      generalize : create_list_from_pq hab_r = x,
      induction x,
      {
        simp only [list.append_nil, list.map, list.reverse_nil],
        exact pq_group_list_rel.refl list.nil,
      },
      {
        simp only [list.reverse_cons, list.map_reverse, list.map_append, list.append_assoc, list.singleton_append, list.map],
        have : (list.map (λ (q : Q), q ^ (-(1 : ℤ))) x_tl).reverse ++ x_hd ^ (-(1 : ℤ)) :: x_hd :: x_tl = (list.map (λ (q : Q), q ^ (-(1 : ℤ))) x_tl).reverse ++ ([x_hd ^ (-1 : ℤ), x_hd]) ++ x_tl,
        {
          simp only [list.cons_append, eq_self_iff_true, list.append_assoc, list.singleton_append, list.map],
        },
        rw this,
        clear this,
        fapply pq_group_list_rel.trans _ (list.map (λ (q : Q), q ^ (-1 : ℤ)) x_tl.reverse ++ x_tl) _,
        swap, assumption,
        clear x_ih,
        rw list.append_assoc,
        apply pq_group_list_rel.congr_append,
        swap, 
        simp only [list.map_reverse],
        apply pq_group_list_rel.refl,
        have : x_tl = list.nil ++ x_tl := rfl,
        rw this,
        apply pq_group_list_rel.congr_append,
        simp only [list.nil_append],
        apply pq_group_list_rel.refl,
        exact pq_group_list_rel.inv_append x_hd,
      },
    },
    {
      unfold create_list_from_pq,
      simp only [list.cons_append, list.map_nil, list.reverse_singleton, list.singleton_append, list.map],
      exact pq_group_list_rel.rhd_append hab_r_a hab_r_b,
    },
    {
      unfold create_list_from_pq,
      induction hab_r_n,
      {
        apply pq_group_list_rel_pred_mul_nat,
      },
      {
        apply pq_group_list_rel_congr_reverse_inv_alt,
        simp only [list.reverse_cons, list.map_nil, list.reverse_singleton, list.singleton_append, list.map],
        simp only [power_quandle.pow_comp],
        simp only [mul_one, mul_neg_eq_neg_mul_symm, neg_sub],
        have := pq_group_list_rel_succ_mul_nat hab_r_a (hab_r_n + 1),
        simp only [list.singleton_append] at this,
        convert this,
        simp only [int.coe_nat_succ],
        ring,
      },
    },
    {
      unfold create_list_from_pq,
      simp only [list.reverse_singleton, list.map],
      induction hab_r_n,
      {
        apply pq_group_list_rel_succ_mul_nat hab_r_a hab_r_n,
      },
      {
        apply pq_group_list_rel_congr_reverse_inv_alt,
        simp only [list.reverse_cons, list.map_nil, list.reverse_singleton, list.singleton_append, list.map],
        simp only [power_quandle.pow_comp],
        simp only [mul_one, mul_neg_eq_neg_mul_symm, neg_add_rev, neg_neg],
        rw power_quandle.pow_one,
        have := pq_group_list_rel_pred_mul_nat hab_r_a (hab_r_n + 1),
        simp only [list.singleton_append] at this,
        convert this,
      },
    },
    {
      unfold create_list_from_pq,
      apply pq_group_list_rel.pow_nat hab_r 0,
    },
  },
  {
    intros hab,
    rw ←create_list_from_pq_eq_id,
    rw ←create_list_from_pq_eq_id,
    generalize hx : create_list_from_pq a = x, 
    generalize hy : create_list_from_pq b = y,
    rw hx at hab,
    rw hy at hab,
    clear hx hy a b,
    induction hab,
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
      simp only [list.map_append, list.prod_append],
      congr,
      assumption,
      assumption,
    },
    {
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
      rw proc_is_inv,
      congr,
      assumption,
    },
    {
      simp only [list.prod_repeat, mul_one, list.map_repeat, list.prod_cons, list.prod_nil, list.map],
      rw of_pow_eq_pow_of,
      refl,
    },
    {
      simp only [mul_one, list.prod_cons, list.prod_nil, list.map],
      rw ←of_inv,
      simp only [mul_left_inv],
    },
    {
      simp only [mul_one, list.prod_cons, list.prod_nil, list.map],
      rw ←rhd_of_eq_of_rhd,
      rw ←mul_assoc,
      rw ←of_inv,
      refl,
    },
  },
end

end pq_group_eq_list
