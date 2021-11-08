

-- TOOD: Cylic is sent to Cyclic
-- TODO: Dihedral is sent to Dihedral (x C2)



import pq_to_group

import algebra.group
import data.zmod.basic
import data.int.parity

universes u v

section cyclic_pq_group


@[ext] structure cyclic (n : nat) :=
(val : zmod n)

variables {n : nat}

def cyclic_mul : cyclic n → cyclic n → cyclic n
| ⟨a⟩ ⟨b⟩ := ⟨a + b⟩

def cyclic_inv : cyclic n → cyclic n
| ⟨a⟩ := ⟨-a⟩

instance cyclic_has_mul : has_mul (cyclic n) := ⟨cyclic_mul⟩

instance cyclic_has_neg : has_inv (cyclic n) := ⟨cyclic_inv⟩ 

instance cyclic_has_one : has_one (cyclic n) := ⟨⟨0⟩⟩


lemma cyclic_mul_def (a b : zmod n) : (⟨a⟩ * ⟨b⟩ : cyclic n) = ⟨a + b⟩ := rfl

lemma cyclic_inv_def (a : zmod n) : (⟨a⟩⁻¹ : cyclic n) = ⟨-a⟩ := rfl

lemma cyclic_one_def : (1 : cyclic n) = ⟨0⟩ := rfl


instance cyclic_comm_group : comm_group (cyclic n) :=
{
    mul_assoc := begin
        rintros ⟨a⟩ ⟨b⟩ ⟨c⟩,
        repeat {rw cyclic_mul_def},
        apply congr_arg,
        apply add_assoc,
    end,
    one_mul := begin
        rintro ⟨a⟩,
        rw cyclic_one_def,
        rw cyclic_mul_def,
        apply congr_arg,
        apply zero_add,
    end,
    mul_one := begin
        rintro ⟨a⟩,
        rw cyclic_one_def,
        rw cyclic_mul_def,
        apply congr_arg,
        apply add_zero,
    end,
    mul_left_inv := begin
        rintro ⟨a⟩,
        rw cyclic_inv_def,
        rw cyclic_mul_def,
        rw cyclic_one_def,
        apply congr_arg,
        apply add_left_neg,
    end,
    mul_comm := begin
        intros a b,
        cases a,
        cases b,
        rw cyclic_mul_def,
        rw cyclic_mul_def,
        apply congr_arg,
        exact add_comm a b,
    end,
    ..cyclic_has_mul,
    ..cyclic_has_neg,
    ..cyclic_has_one,
}

lemma one_val : (1 : (cyclic n)).val = 0 := rfl

def generator : (cyclic n) := ⟨1⟩ 

lemma cyclic_as_power (x : cyclic n) : ∃ k : int, x = generator^k :=
begin
    induction x,
    use (zmod.val_min_abs x),
    --simp at *,
    have gen_pow : ∀ k : int, (⟨k⟩ : cyclic n) = generator ^ k,
    {
        intro k,
        induction k,
        {
            induction k with l hl,
            {
                refl,
            },
            {
                simp at *,
                rw gpow_add_one,
                simp,
                rw ←hl,
                refl,
            },
        },
        {
            induction k with l hl,
            {
                simp,
                refl,
            },
            {
                simp at *,
                rw pow_succ,
                simp,
                rw ←hl,
                apply congr_arg,
                ring,
            },
        },
    },
    have h := gen_pow (x.val_min_abs),
    simp at h,
    assumption,
end


lemma cyclic_counit_form : function.surjective (of : (cyclic n) → pq_group (cyclic n)) :=
begin
    intro x,
    induction x,
    {
        induction x,
        {
            use 1,
            apply quotient.sound,
            fconstructor,
            apply pre_pq_group_rel'.pow_zero,
            exact 1,
        },
        {
            use x,
            refl,
        },
        {
            cases x_ih_a with a ha,
            cases x_ih_b with b hb,
            use (a * b),
            --apply quotient.sound,
            have ha2 := cyclic_as_power a,
            have hb2 := cyclic_as_power b,
            cases ha2 with k hk,
            cases hb2 with l hl,
            rw hk,
            rw hl,
            rw ←gpow_add,
            rw of_pow_eq_pow_of,
            have hr : quot.mk setoid.r (x_a.mul x_b) = ((quot.mk setoid.r x_a) * (quot.mk setoid.r x_b) : pq_group (cyclic n)),
            {
                refl,
            },
            rw hr,
            rw ←ha,
            rw ←hb,
            rw hk,
            rw hl,
            rw of_pow_eq_pow_of,
            rw of_pow_eq_pow_of,
            rw ←gpow_add,
        },
        {
            cases x_ih with y hy,
            use (y ^ (-1 : int)),
            rw of_pow_eq_pow_of,
            rw hy,
            simp,
            refl,
        },
    },
    {refl,},
end


theorem cyclic_counit_bijective : function.bijective (counit : pq_group (cyclic n) → cyclic n) :=
begin
    split,
    {
        intros x y,
        intro hxy,
        have hx := cyclic_counit_form x,
        have hy := cyclic_counit_form y,
        cases hx with xx hxx,
        cases hy with yy hyy,
        rw ←hxx at *,
        rw ←hyy at *,
        apply congr_arg,
        repeat {rw counit_of at hxy},
        assumption,
    },
    {
        apply counit_surjective,
    }
end


noncomputable theorem comonad_cyclic_iso : pq_group (cyclic n) ≃* cyclic n :=
begin
    fapply mul_equiv.of_bijective,
    exact counit,
    exact cyclic_counit_bijective,
end


end cyclic_pq_group


section klein_pq_group

local notation `C2` := (cyclic 2)

local notation `K` := C2 × C2

local notation `g` := (⟨1⟩ : C2) 

lemma cyclic2cases {p : cyclic 2 → Prop} (a : cyclic 2) (h0 : p 1) (h1 : p generator) : p a :=
begin
    cases a,
    cases a with a ha,
    cases a,
    {
        exact h0,
    },
    {
        cases a,
        {
            exact h1,
        },
        {
            exfalso,
            norm_num at ha,
            have ha' := nat.lt_of_succ_lt_succ (nat.lt_of_succ_lt_succ ha),
            exact nat.not_lt_zero a ha',
        }
    }
end

-- Stupid lemma
lemma not_zero_eq_one (c : zmod 2) (hc0 : c ≠ 0) : c = 1 := 
begin
    by_contradiction hc1,
    {
        cases c with c hc,
        cases c,
        {
            apply hc0,
            refl,
        },
        {
            cases c,
            {
                apply hc1,
                refl,
            },
            {
                clear hc0 hc1,
                norm_num at hc,
                have hc' := nat.lt_of_succ_lt_succ (nat.lt_of_succ_lt_succ hc),
                exact nat.not_lt_zero c hc'
            },
        }
    }
end

-- Stupid lemma
lemma not_one_eq_zero (c : zmod 2) (hc1 : c ≠ 1) : c = 0 := 
begin
    by_contradiction hc0,
    {
        cases c with c hc,
        cases c,
        {
            apply hc0,
            refl,
        },
        {
            cases c,
            {
                apply hc1,
                refl,
            },
            {
                clear hc0 hc1,
                norm_num at hc,
                have hc' := nat.lt_of_succ_lt_succ (nat.lt_of_succ_lt_succ hc),
                exact nat.not_lt_zero c hc'
            },
        }
    }
end

lemma pqK_of_commute (a b : K) : (of a) * (of b) = (of b) * (of a) :=
begin
    apply pq_group_commute,
    unfold commute,
    unfold semiconj_by,
    cases a with a1 a2;
    cases b with b1 b2;
    apply cyclic2cases a1;
    apply cyclic2cases a2;
    apply cyclic2cases b1;
    apply cyclic2cases b2;
    refl,
end

lemma pqK_commute (a b : pq_group K) : a * b = b * a :=
begin
    induction a,
    {
        rw quot_mk_helper,
        induction a,
        {
            rw incl_unit_eq_unit,
            simp,
        },
        {
            induction b,
            {
                rw quot_mk_helper,
                induction b,
                {
                    rw incl_unit_eq_unit,
                    simp,
                },
                {
                    apply pqK_of_commute,
                },
                {
                    rw ←mul_def,
                    rw mul_assoc,
                    rw ←b_ih_b,
                    rw ←mul_assoc,
                    rw b_ih_a,
                    rw mul_assoc,
                },
                {
                    rw ←inv_def,
                    apply commute.inv_right,
                    exact b_ih,
                },
            },
            {refl,},
        },
        {
            rw ←mul_def,
            rw mul_assoc,
            rw a_ih_b,
            rw ←mul_assoc,
            rw a_ih_a,
            rw mul_assoc,
        },
        {
            rw ←inv_def,
            apply commute.inv_left,
            exact a_ih,
        }
    },
    {refl,},
end

lemma C2_self_mul (a : C2) : a * a = 1 :=
begin
    apply cyclic2cases a;
    refl,
end

lemma C2_inv_is_self (a : C2) : a⁻¹ = a :=
begin
    apply cyclic2cases a;
    refl,
end

lemma K_self_mul (a : K) : a * a = 1 := 
begin
    cases a with a b,
    apply cyclic2cases a;
    apply cyclic2cases b;
    refl,
end

lemma pqK_self_mul (a : pq_group K) : a * a = 1 :=
begin
    induction a,
    {
        rw quot_mk_helper,
        induction a,
        {
            apply quotient.sound,
            fconstructor,
            apply pre_pq_group_rel'.mul_one,
        },
        {
            rw ←pow_two,
            rw ←gpow_of_nat,
            rw ←of_def,
            rw ←of_pow_eq_pow_of a (int.of_nat 2),
            rw gpow_of_nat,
            rw pow_two,
            rw K_self_mul,
            rw of_1_eq_unit,
        },
        {
            rw ←mul_def,
            have rw_order : ∀ c d : pq_group K, commute c d → c * d * (c * d) = c * c * (d * d),
            {
                intros c d hcd,
                have paren_rw : ∀ (a1 a2 a3 a4 : pq_group K), a1 * a2 * (a3 * a4) = a1 * (a2 * a3) * a4,
                {
                    intros a1 a2 a3 a4,
                    group,
                },
                unfold commute at hcd,
                unfold semiconj_by at hcd,
                rw paren_rw,
                rw ←hcd,
                rw ←paren_rw,
            },
            rw rw_order,
            rw a_ih_a,
            rw a_ih_b,
            rw mul_one,
            apply pqK_commute,
        },
        {
            rw ←inv_def,
            refine inv_inj.mp _,
            simp,
            exact a_ih,
        }
    },
    {refl,},
end


lemma Kpow2k : ∀ a : K, ∀ k : int, a^(2*k) = 1 :=
begin
    intros a k,
    rw mul_comm,
    rw gpow_mul,
    rw gpow_bit0,
    rw K_self_mul,
end


lemma Kpow2kplus1 : ∀ a : K, ∀ k : int, a^(2*k + 1) = a :=
begin
    intros a k,
    rw gpow_add_one,
    rw Kpow2k,
    simp only [one_mul],
end


lemma Kpow2kminus1 : ∀ a : K, ∀ k : int, a^(2*k - 1) = a :=
begin
    intros a k,
    have n_rw : 2 * k - 1 = 2*(k - 1) + 1,
    {
        ring,
    },
    rw n_rw,
    rw Kpow2kplus1,
end


open pre_pq_group

def f_pre_on_C2_fun : pre_pq_group K → C2
| unit := 1
| (incl (a, b)) := if (a.val = 1 ∧ b.val = 1) then g else 1
| (mul a b) := f_pre_on_C2_fun a * f_pre_on_C2_fun b
| (inv a) := (f_pre_on_C2_fun a)⁻¹

lemma f_pre_on_C2_fun_unit : f_pre_on_C2_fun (unit) = 1 := rfl
lemma f_pre_on_C2_fun_incl (a b : C2) : f_pre_on_C2_fun (incl (a, b)) = (if (a.val = 1 ∧ b.val = 1) then g else 1) := rfl
lemma f_pre_on_C2_fun_mul (a b : pre_pq_group K) : f_pre_on_C2_fun (mul a b) = f_pre_on_C2_fun a * f_pre_on_C2_fun b := rfl
lemma f_pre_on_C2_fun_inv (a : pre_pq_group K) : f_pre_on_C2_fun (inv a) = (f_pre_on_C2_fun a)⁻¹ := rfl


def f_on_C2_fun : pq_group K → C2 := quotient.lift f_pre_on_C2_fun (begin
    intros a b,
    intro hab,
    induction hab with c d habr,
    clear a,
    clear b,
    induction habr,
    {
        refl,
    },
    {
        apply eq.symm,
        assumption,
    },
    {
        apply eq.trans habr_ih_hab habr_ih_hbc,
    },
    {
        unfold f_pre_on_C2_fun,
        congr',
    },
    {
        unfold f_pre_on_C2_fun,
        congr',
    },
    {
        unfold f_pre_on_C2_fun,
        rw mul_assoc,
    },
    {
        unfold f_pre_on_C2_fun,
        rw one_mul,
    },
    {
        unfold f_pre_on_C2_fun,
        rw mul_one,
    },
    {
        unfold f_pre_on_C2_fun,
        rw mul_left_inv,
    },
    {
        unfold f_pre_on_C2_fun,
        simp only [mul_comm, inv_mul_cancel_left],
        congr',
        simp only [rhd_def_group, mul_comm, inv_mul_cancel_left],
    },
    {
        unfold f_pre_on_C2_fun,
        --cases habr_a with a b,
        --rw f_pre_on_C2_fun_incl,
        by_cases (even habr_n),
        {
            unfold even at h,
            cases h with k hk,
            rw hk,
            rw Kpow2k,
            rw Kpow2kminus1,
            rw C2_self_mul,
            refl,
        },
        {
            rw ←int.odd_iff_not_even at h,
            unfold odd at h,
            cases h with k hk,
            rw hk,
            simp only [add_sub_cancel],
            rw Kpow2k,
            rw Kpow2kplus1,
            group,
            refl,
        }
    },
    {
        unfold f_pre_on_C2_fun,
        by_cases (even habr_n),
        {
            unfold even at h,
            cases h with k hk,
            rw hk,
            rw Kpow2k,
            rw Kpow2kplus1,
            group,
            refl,
        },
        {
            rw ←int.odd_iff_not_even at h,
            unfold odd at h,
            cases h with k hk,
            rw hk,
            rw Kpow2kplus1,
            have n_rw : 2 * k + 1 + 1 = 2 * (k + 1),
            {
                ring,
            },
            rw n_rw,
            rw Kpow2k,
            have is_one : f_pre_on_C2_fun (incl 1) = 1,
            {
                refl,
            },
            rw is_one,
            simp,
            rw C2_inv_is_self,
        }
    },
    {
        refl,
    },
end) 


lemma f_on_C2_fun_unit : f_on_C2_fun (⟦unit⟧) = 1 := rfl
lemma f_on_C2_fun_incl (a b : C2) : f_on_C2_fun (⟦incl (a, b)⟧) = (if (a.val = 1 ∧ b.val = 1) then g else 1) := rfl
lemma f_on_C2_fun_mul (a b : pre_pq_group K) : f_on_C2_fun (⟦mul a b⟧) = f_on_C2_fun ⟦a⟧ * f_on_C2_fun ⟦b⟧ := rfl
lemma f_on_C2_fun_inv (a : pre_pq_group K) : f_on_C2_fun ⟦inv a⟧ = (f_on_C2_fun ⟦a⟧)⁻¹ := rfl

lemma f_on_C2_fun_of (a b : C2) : f_on_C2_fun (of (a, b)) = (if (a.val = 1 ∧ b.val = 1) then g else 1) := rfl


def f_on_KC2_fun : pq_group K → K × C2
| a := (counit a, f_on_C2_fun a)


def f_on_KC2 : pq_group K →* K × C2 := ⟨f_on_KC2_fun, rfl, begin
    intros x y,
    unfold f_on_KC2_fun,
    simp only [true_and, monoid_hom.map_mul, prod.mk.inj_iff, eq_self_iff_true, prod.mk_mul_mk],
    induction x,
    induction y,
    {
        refl,
    },
    {refl,},
    {refl,},
end⟩


/--

Construction of inverse:
f_on_KC2 (x) = (counit x, of (g, g) -> g, 1 otherwise)

Inverse:
f_on_KC2_inv (a, b, c) = of(a, b) * (c = 1 -> (of(g, 1)of(1, g)of(g, g)))

Let's test:
We test f_on_KC2 of f_on_KC2_inv
(0, 0, 1) -> of(g, 1)of(1, g)of(g, g) -> (0, 0, 1)
(1, 1, 1) -> of(g, g)of(g, 1)of(1, g)of(g, g) -> (1, 1, 0) WRONG!!!
(1, 1, 0) -> of (1, 1) -> (1, 1, 1)

-/


def f_on_KC2_inv_fun : K × C2 → pq_group K
| (a, b) := of(a.1, 1) * of (1, a.2) * (if (b.val = 0) then 1 else of (1, g) * of (g, 1) * of (g, g))

lemma of_mul_C2_left (a b : C2) : of(a * b, (1 : C2)) = of(a, 1) * of(b, 1) :=
begin
    apply cyclic2cases a,
    {
        have one_eq2 : ((1, 1) : K) = 1 := rfl,
        rw one_eq2,
        rw of_1_eq_unit,
        simp only [mul_one, one_mul],
    },
    {
        apply cyclic2cases b,
        {
            have one_eq2 : ((1, 1) : K) = 1 := rfl,
            rw one_eq2,
            rw of_1_eq_unit,
            simp only [mul_one, one_mul],
        },
        {
            rw pqK_self_mul,
            rw C2_self_mul,
            have one_eq2 : ((1, 1) : K) = 1 := rfl,
            rw one_eq2,
            rw of_1_eq_unit,
        },
    },
end

lemma of_mul_C2_right (a b : C2) : of((1 : C2), a * b) = of(1, a) * of(1, b) :=
begin
    apply cyclic2cases a,
    {
        have one_eq2 : ((1, 1) : K) = 1 := rfl,
        rw one_eq2,
        rw of_1_eq_unit,
        simp only [mul_one, one_mul],
    },
    {
        apply cyclic2cases b,
        {
            have one_eq2 : ((1, 1) : K) = 1 := rfl,
            rw one_eq2,
            rw of_1_eq_unit,
            simp only [mul_one, one_mul],
        },
        {
            rw pqK_self_mul,
            rw C2_self_mul,
            have one_eq2 : ((1, 1) : K) = 1 := rfl,
            rw one_eq2,
            rw of_1_eq_unit,
        },
    },
end

def f_on_KC2_inv : K × C2 →* pq_group K := ⟨f_on_KC2_inv_fun, begin
    have one_eq : ((1, 1) : K × C2) = 1 := rfl,
    rw ←one_eq,
    unfold f_on_KC2_inv_fun,
    rw if_pos,
    swap, refl,
    simp only [mul_one, prod.snd_one, prod.fst_one],
    have one_eq2 : ((1, 1) : K) = 1 := rfl,
    rw one_eq2,
    rw of_1_eq_unit,
    simp only [mul_one],
end, begin
    intros x y,
    cases x with x1 x2,
    cases y with y1 y2,
    have mul_rw : (x1, x2) * (y1, y2) = (x1 * y1, x2 * y2) := rfl,
    rw mul_rw,
    clear mul_rw,
    unfold f_on_KC2_inv_fun,
    have reorder : ∀ a b c d : pq_group K, a * b * (c * d) = a * c * (b * d),
    {
        intros a b c d,
        have redo_paren : ∀ a b c d : pq_group K, a * b * (c * d) = a * (b * c) * d,
        intros a b c d, group,
        rw redo_paren,
        rw pqK_commute b c,
        rw ←redo_paren, 
    },
    apply cyclic2cases x2;
    apply cyclic2cases y2;
    clear x2 y2,
    {
        rw if_pos,
        swap, refl,
        rw if_pos,
        swap, refl,
        simp only [prod.snd_mul, prod.fst_mul, mul_one],
        cases x1 with x11 x12,
        cases y1 with y11 y12,
        simp only,
        rw of_mul_C2_left,
        rw of_mul_C2_right,
        rw reorder,
    },
    {
        rw if_neg,
        swap, unfold generator, simp,
        rw if_pos,
        swap, refl,
        rw if_neg,
        swap, unfold generator, simp,
        simp only [prod.snd_mul, prod.fst_mul, mul_one],
        cases x1 with x11 x12,
        cases y1 with y11 y12,
        simp only,
        rw of_mul_C2_left,
        rw of_mul_C2_right,
        suffices : of (x11, 1) * of (y11, 1) * (of (1, x12) * of (1, y12)) = of (x11, 1) * of (1, x12) * (of (y11, 1) * of (1, y12)),
        rw this, group,
        rw reorder,
    },
    {
        rw if_neg,
        swap, unfold generator, simp,
        rw if_neg,
        swap, unfold generator, simp,
        rw if_pos,
        swap, refl,
        simp only [prod.snd_mul, prod.fst_mul, mul_one],
        cases x1 with x11 x12,
        cases y1 with y11 y12,
        simp only,
        rw of_mul_C2_left,
        rw of_mul_C2_right,
        rw pqK_commute _ ((of (y11, 1) * of (1, y12))),
        group,
        rw pqK_commute _ (of (1, y12)),
        group,
        rw pqK_commute _ (of (y11, 1)),
        group,
    },
    {
        rw if_pos,
        swap, refl,
        rw if_neg,
        swap, unfold generator, simp,
        simp only [prod.snd_mul, prod.fst_mul, mul_one],
        cases x1 with x11 x12,
        cases y1 with y11 y12,
        simp only,
        rw of_mul_C2_left,
        rw of_mul_C2_right,
        let x : pq_group K := (of (1, {val := 1}) * of ({val := 1}, 1) * of ({val := 1}, {val := 1})),
        have x_def : x = (of (1, {val := 1}) * of ({val := 1}, 1) * of ({val := 1}, {val := 1})) := rfl,
        rw ←x_def,
        rw pqK_commute (of (y11, 1) * of (1, y12)) x,
        rw reorder,
        suffices : of (x11, 1) * of (1, x12) * (of (y11, 1) * of (1, y12)) = of (x11, 1) * of (1, x12) * (x * x) * (of (y11, 1) * of (1, y12)),
        rw this, group,
        rw pqK_self_mul,
        simp only [mul_one],
    },
end⟩ 


theorem f_on_KC2_inv_f_on_KC2 : f_on_KC2_inv ∘ f_on_KC2 = id :=
begin
    funext,
    simp only [id.def, function.comp_app],
    induction x,
    {
        rw quot_mk_helper,
        induction x,
        {
            unfold f_on_KC2,
            simp,
            unfold f_on_KC2_fun,
            rw counit_unit,
            rw f_on_C2_fun_unit,
            unfold f_on_KC2_inv,
            simp only [monoid_hom.coe_mk],
            unfold f_on_KC2_inv_fun,
            rw if_pos,
            swap, refl,
            simp only [mul_one, prod.fst_one, prod.snd_one],
            have h1 : ((1, 1) : K) = 1 := rfl,
            rw h1,
            rw ←unit_eq_incl_1,
            apply quotient.sound,
            fconstructor,
            apply pre_pq_group_rel'.mul_one,
        },
        {
            unfold f_on_KC2,
            simp,
            unfold f_on_KC2_fun,
            rw counit_incl,
            cases x with a b,
            rw f_on_C2_fun_incl,
            by_cases (a.val = 1 ∧ b.val = 1),
            {
                rw if_pos,
                unfold f_on_KC2_inv,
                simp only [monoid_hom.coe_mk],
                unfold f_on_KC2_inv_fun,
                rw if_neg,
                {
                    simp,
                    cases h with ha hb,
                    have ha1 : a = ⟨1⟩,
                    ext, rw ha,
                    have hb1 : b = ⟨1⟩,
                    ext, rw hb,
                    rw ha1,
                    rw hb1,
                    rw ←of_def,
                    suffices : ∀ a b c : pq_group K, a * b * (b * a * c) = c,
                    apply this,
                    intros a b c,
                    have rw_order : a * b * (b * a * c) = (a * (b * b) * a) * c,
                    group,
                    rw rw_order,
                    simp only [mul_one, mul_left_eq_self, pqK_self_mul],
                },
                simp,
                exact h,
            },
            {
                rw if_neg,
                swap, assumption,
                unfold f_on_KC2_inv,
                simp only [monoid_hom.coe_mk],
                unfold f_on_KC2_inv_fun,
                rw if_pos,
                swap, refl,
                rw ←of_def,
                simp only [mul_one],
                by_cases ha1 : (a.val = 1),
                {
                    push_neg at h,
                    specialize h ha1,
                    have hb1 := not_one_eq_zero (b.val) h,
                    have ha : a = ⟨1⟩,
                    ext, rw ha1,
                    have hb : b = 1,
                    ext, rw hb1, refl,
                    rw ha,
                    rw hb,
                    simp,
                    have one_eq : ((1, 1) : K) = 1 := rfl,
                    rw one_eq,
                    rw of_1_eq_unit,
                },
                {
                    clear h,
                    have ha2 := not_one_eq_zero (a.val) ha1,
                    have ha : a = 1,
                    ext, rw ha2, refl,
                    rw ha,
                    simp only [mul_left_eq_self],
                    have one_eq : ((1, 1) : K) = 1 := rfl,
                    rw one_eq,
                    rw of_1_eq_unit,
                },
            },
        },
        {
            rw ←mul_def,
            rw monoid_hom.map_mul,
            rw monoid_hom.map_mul,
            congr',
        },
        {
            rw ←inv_def,
            rw monoid_hom.map_inv,
            rw monoid_hom.map_inv,
            congr',
        },
    },
    {refl,},
end

theorem f_on_KC2_f_on_KC2_inv : f_on_KC2 ∘ f_on_KC2_inv = id :=
begin
    funext,
    simp only [id.def, function.comp_app],
    cases x with y c,
    by_cases (c.val = 0),
    {
        unfold f_on_KC2_inv,
        simp only [monoid_hom.coe_mk],
        unfold f_on_KC2_inv_fun,
        rw if_pos,
        swap, exact h,
        unfold f_on_KC2,
        simp,
        unfold f_on_KC2_fun,
        rw counit_of,
        rw counit_of,
        rw f_on_C2_fun_of,
        rw if_neg,
        swap, push_neg, intro, rw one_val, norm_num,
        rw f_on_C2_fun_of,
        rw if_neg,
        swap, push_neg, rw one_val, norm_num,
        simp,
        cases c,
        simp at h,
        rw h,
        refl,
    },
    {
        unfold f_on_KC2_inv,
        simp only [monoid_hom.coe_mk],
        unfold f_on_KC2_inv_fun,
        rw if_neg,
        swap, exact h,
        unfold f_on_KC2,
        simp,
        unfold f_on_KC2_fun,
        repeat {rw counit_of,},
        repeat {rw f_on_C2_fun_of,},
        rw if_neg,
        swap, push_neg, rw one_val, norm_num,
        rw if_neg,
        swap, push_neg, rw one_val, norm_num,
        rw if_neg,
        swap, push_neg, rw one_val, norm_num,
        rw if_neg,
        swap, push_neg, rw one_val, norm_num,
        rw if_pos,
        swap, split, refl, refl,
        simp,
        split,
        refl,
        cases c,
        simp at *,
        apply eq.symm,
        apply not_zero_eq_one c h,
    },
end

theorem klein_pq_group_iso_klein_c2 : pq_group K ≃* K × C2 := 
{ to_fun := f_on_KC2,
  inv_fun := f_on_KC2_inv,
  left_inv := congr_fun f_on_KC2_inv_f_on_KC2,
  right_inv := congr_fun f_on_KC2_f_on_KC2_inv,
  map_mul' := is_mul_hom.map_mul ⇑f_on_KC2 }


end klein_pq_group

