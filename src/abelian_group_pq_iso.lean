
import algebra.group.basic

--import data.set.finite

import group_theory.subgroup
import group_theory.order_of_element


universe u


section abelian_group_pq_genfun

noncomputable theory

variables {G : Type u} [comm_group G] [fintype G]

def pow_kernel_set (G : Type u) [comm_group G] [fintype G] (n : nat) : set G := {x : G | x ^ n = 1}

/-
lemma pow_kernel_finite (n : nat) : set.finite ((pow_kernel_set G n) : set G) := set.finite.of_fintype (pow_kernel_set G n)

def pow_kernel (n : nat) : finset G := set.finite.to_finset (pow_kernel_finite n)
-/

instance pow_kernel_fintype (n : nat) : fintype (pow_kernel_set G n) := sorry 

def gen_fun (G : Type u) [comm_group G] [fintype G] : ℕ → ℕ := λ n, fintype.card (pow_kernel_set G n)

variables {H : Type u} [comm_group H] [fintype H]

lemma gen_fun_prod (n : nat) : (gen_fun (G × H)) (n) = gen_fun (G) (n) * gen_fun (H) (n) :=
begin
    unfold gen_fun,
    unfold pow_kernel_set,
    suffices h : {x : G × H | x ^ n = 1} = {x : G | x ^ n = 1}.prod {x : H | x ^ n = 1},
    {
        simp_rw h,
        rw ←fintype.card_prod,
        unfold_coes,
        simp_rw set.mem_prod,
        dsimp at *,
        rw fintype.card_eq,
        refine nonempty.intro _,
        fapply equiv.of_bijective,
        {
            rintro ⟨⟨x, y⟩, ⟨hx, hy⟩⟩,
            exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩,
        },
        split,
        {
            rintros ⟨⟨x1, y1⟩, ⟨hx1, hy1⟩⟩ ⟨⟨x2, y2⟩, ⟨hx2, hy2⟩⟩,
            simp only [and_imp, prod.mk.inj_iff],
            exact and.intro,
        },
        {
            rintro ⟨⟨x, y⟩, ⟨hx, hy⟩⟩,
            use ⟨⟨x, hx⟩, ⟨y, hy⟩⟩,
        },
    },
    have prod_pow : ∀ a : G, ∀ b : H, (a, b)^n = (a^n, b^n),
    {
        intros a b,
        induction n with n hn,
        {
            refl,
        },
        {
            rw pow_succ,
            rw hn,
            refl,
        },
    },
    ext,
    split,
    {
        intro hx,
        cases x with a b,
        refine set.mem_prod.mpr _,
        dsimp at *,
        rw prod.ext_iff at hx,
        rw prod_pow at hx,
        dsimp at hx,
        exact hx,
    },
    {
        intro hx,
        cases x with a b,
        dsimp at *,
        rw prod.ext_iff,
        rw prod_pow,
        dsimp,
        exact hx,
    },
end


end abelian_group_pq_genfun
