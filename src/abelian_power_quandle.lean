
import power_quandle

universes u v w

class abelian_power_quandle (Q : Type u) extends has_add Q, has_neg Q, has_zero Q, power_quandle Q :=
--(apq_unit_is_morphism_replacement : (0 : Q) ▷ (0 : Q) = 0 ∧ ∀ n : int, (0 : Q) ^ n = 0)
(apq_unit_is_morphism : let apq_unit : unit → Q := λ a, 0 in is_pq_morphism apq_unit)
(apq_inverse_is_morphism : is_pq_morphism (λ a : Q, -a))
(apq_addition_is_morphism : is_pq_morphism (λ a : Q × Q, a.1 + a.2))
(apq_addition_assoc : ∀ a b c : Q, a + (b + c) = (a + b) + c )
(apq_addition_comm : ∀ a b : Q, a + b = b + a)
(apq_addition_zero_right : ∀ a : Q, a + 0 = a)
(apq_addition_zero_left : ∀ a : Q, 0 + a = a)
(apq_inverse_addition_right : ∀ a : Q, a + -a = 0)
(apq_inverse_addition_left : ∀ a : Q, -a + a = 0)

section abelian_power_quandle

variables {Q : Type u} [abelian_power_quandle Q]

lemma rhd_interact_add : ∀ a b c d : Q, (a ▷ b) + (c ▷ d) = (a + c) ▷ (b + d) := 
begin
    intros a b c d,
    have add_is_morph := abelian_power_quandle.apq_addition_is_morphism,
    cases add_is_morph with h _,
    have h1 := h (a, c) (b, d),
    simp at h1,
    repeat {rw rhd_def_prod at h1},
    simp at h1,
    assumption,
end


lemma pow_dist_add : ∀ a b : Q, ∀ n : int, (a + b) ^ n = a ^ n + b ^ n := 
begin
    intros a b n,
    have add_is_morph := abelian_power_quandle.apq_addition_is_morphism,
    cases add_is_morph with _ h,
    have h1 := h (a, b) n,
    simp at h1,
    repeat {rw pow_def_prod at h1},
    simp at h1,
    apply eq.symm,
    assumption,
end

def ε (a : Q) := a ▷ 0
def α (a : Q) := 0 ▷ a

lemma ε_def (a : Q) : ε(a) = a ▷ 0 := rfl
lemma α_def (a : Q) : α(a) = 0 ▷ a := rfl

lemma rhd_as_eps_add_alpha : ∀ a b : Q, a ▷ b = ε(a) + α(b) :=
begin
    intros a b,
    rw ←abelian_power_quandle.apq_addition_zero_right a,
    rw ←abelian_power_quandle.apq_addition_zero_left b,
    rw ←rhd_interact_add,
    rw abelian_power_quandle.apq_addition_zero_right a,
    rw abelian_power_quandle.apq_addition_zero_left b,
    refl,
end

lemma alpha_is_id : ∀ a : Q, α(a) = a := 
begin
    intro a,
    have eps_a_pow_0 : ε(a ^ (0 : int)) = 0,
    {
        rw ε_def,
        rw pow_0_rhd,
    },
    apply eq.symm,
    have a_eq_sum : a = ε(a ^ (0 : int)) + α(a),
    {
        rw ←rhd_as_eps_add_alpha,
        rw pow_0_rhd,
    },
    rw eps_a_pow_0 at a_eq_sum,
    rw abelian_power_quandle.apq_addition_zero_left at a_eq_sum,
    assumption,
end

lemma eps_is_zero : ∀ a : Q, ε(a) = 0 :=
begin
    intro a,
    have goal_symm : 0 = ε(a),
    {
        exact calc 0 = a + -a : by rw abelian_power_quandle.apq_inverse_addition_right
                ...  = a ▷ a + -a : by rw quandle.self_idem_right
                ...  = ε(a) + α(a) + -a: by rw rhd_as_eps_add_alpha
                ...  = ε(a) + a + -a : by rw alpha_is_id
                ...  = ε(a) + (a + -a) : by rw abelian_power_quandle.apq_addition_assoc
                ...  = ε(a) + 0 : by rw abelian_power_quandle.apq_inverse_addition_right
                ...  = ε(a) : by rw abelian_power_quandle.apq_addition_zero_right,
    },
    apply eq.symm,
    assumption,
end

theorem apq_rhd_is_right : ∀ a b : Q, a ▷ b = b :=
begin
    intros a b,
    rw rhd_as_eps_add_alpha,
    rw eps_is_zero,
    rw alpha_is_id,
    exact abelian_power_quandle.apq_addition_zero_left b,
end

theorem apq_lhd_is_left : ∀ a b : Q, b ◁ a = b :=
begin
    intros a b,
    rw power_quandle.q_powneg_left,
    rw apq_rhd_is_right,
end

lemma apq_zero_pow : ∀ n : int, (0 : Q) ^ n = 0 :=
begin
    intro n,
    have u_morph := abelian_power_quandle.apq_unit_is_morphism,
    simp at u_morph,
    cases u_morph with h1 h2,
    simp at h2,
    rw ←h2,
end

lemma apq_neg_pow : ∀ a : Q, ∀ n : int, (-a) ^ n = -(a ^ n) :=
begin
    intros a n,
    have neg_morph := abelian_power_quandle.apq_inverse_is_morphism,
    cases neg_morph with h1 h2,
    simp at h2,
    rw h2,
end


end abelian_power_quandle



section abelian_power_quandle_morphism


variables {Q1 : Type u} [abelian_power_quandle Q1] {Q2 : Type v} [abelian_power_quandle Q2] {Q3 : Type w} [abelian_power_quandle Q3]


def is_apq_morphism (f : Q1 → Q2) := (∀ a b : Q1, f(a + b) = f(a) + f(b)) ∧ ∀ a : Q1, ∀ n : int, f(a^n) = f(a)^n


lemma apq_morphism_zero (f : Q1 → Q2) (hf : is_apq_morphism f) : f(0) = 0 :=
begin
    cases hf with hf1 hf2,
    have calculation := calc 0 = f(0) + -f(0)           : by rw abelian_power_quandle.apq_inverse_addition_right
                        ...    = f(0 + 0) + -f(0)       : by rw abelian_power_quandle.apq_addition_zero_right
                        ...    = f(0) + f(0) + -f(0)    : by rw hf1
                        ...    = f(0) + (f(0) + -f(0))  : by rw abelian_power_quandle.apq_addition_assoc
                        ...    = f(0) + 0               : by rw abelian_power_quandle.apq_inverse_addition_right
                        ...    = f(0)                   : by rw abelian_power_quandle.apq_addition_zero_right,
    
    apply eq.symm,
    exact calculation,
    
end


lemma apq_morphism_inverse (f : Q1 → Q2) (hf : is_apq_morphism f) : ∀ a : Q1, f(-a) = -f(a) :=
begin
    cases hf with hf1 hf2,
    intro a,

    have calculation := calc f(-a) = f(-a) + 0              : by rw abelian_power_quandle.apq_addition_zero_right
                        ...        = f(-a) + (f(a) + -f(a)) : by rw abelian_power_quandle.apq_inverse_addition_right
                        ...        = f(-a) + f(a) + -f(a)   : by rw abelian_power_quandle.apq_addition_assoc
                        ...        = f(-a + a) + -f(a)      : by rw hf1
                        ...        = f(0) + -f(a)           : by rw abelian_power_quandle.apq_inverse_addition_left
                        ...        = 0 + -f(a)              : by rw apq_morphism_zero f ⟨hf1, hf2⟩
                        ...        = -f(a)                  : by rw abelian_power_quandle.apq_addition_zero_left,
    exact calculation,
end


lemma apq_morphism_rhd (f : Q1 → Q2) (hf : is_apq_morphism f) : ∀ a b : Q1, f(a ▷ b) = f(a) ▷ f(b) :=
begin
    intros a b,
    rw apq_rhd_is_right,
    rw apq_rhd_is_right,
end


lemma apq_morphism_lhd (f : Q1 → Q2) (hf : is_apq_morphism f) : ∀ a b : Q1, f(b ◁ a) = f(b) ◁ f(a) :=
begin
    intros a b,
    rw apq_lhd_is_left,
    rw apq_lhd_is_left,
end


-- Next two: apq is a category
lemma id_is_apq_morphism : is_apq_morphism (id : Q1 → Q1) :=
begin
    split,
    {
        intros a b,
        refl,
    },
    {
        intros a n,
        refl,
    },
end


lemma apq_morphism_comp (f : Q1 → Q2) (g : Q2 → Q3) (hf : is_apq_morphism f) (hg : is_apq_morphism g) : is_apq_morphism (g ∘ f) :=
begin
    cases hf with hf1 hf2,
    cases hg with hg1 hg2,
    split,
    {
        intros a b,
        simp,
        rw hf1,
        rw hg1,
    },
    {
        intros a n,
        simp,
        rw hf2,
        rw hg2,
    },
end


-- Forgetful functor from APQ to PQ
lemma apq_morphism_is_pq_morphism (f : Q1 → Q2) (hf : is_apq_morphism f) : is_pq_morphism f :=
begin
    split,
    {
        exact apq_morphism_rhd f hf,
    },
    {
        cases hf with hf1 hf2,
        exact hf2,
    },
end

end abelian_power_quandle_morphism


-- Product of abelian power quandles
section abelian_power_quandle_product


variables {Q1 : Type u} [abelian_power_quandle Q1] {Q2 : Type v} [abelian_power_quandle Q2]


def product_add (a : Q1 × Q2) (b : Q1 × Q2) : Q1 × Q2 := (a.1 + b.1, a.2 + b.2)

def product_negative (a : Q1 × Q2) : Q1 × Q2 := (-a.1, -a.2)

def product_zero : Q1 × Q2 := (0, 0)


instance product_has_add : has_add (Q1 × Q2) := ⟨product_add⟩ 

instance product_has_neg : has_neg (Q1 × Q2) := ⟨product_negative⟩

instance product_has_zero : has_zero (Q1 × Q2) := ⟨product_zero⟩ 


lemma prod_add_def (a : Q1 × Q2) (b : Q1 × Q2) : a + b = (a.1 + b.1, a.2 + b.2) := rfl

lemma prod_neg_def (a : Q1 × Q2) : -a = (-a.1, -a.2) := rfl

lemma prod_zero_def : (0 : (Q1 × Q2)) = (0, 0) := rfl



lemma apq_unit_is_morphism_prod : let apq_unit : unit → Q1 × Q2 := λ a, 0 in is_pq_morphism apq_unit := 
begin
    simp,
    split,
    {
        intros a b,
        simp,
        rw prod_zero_def,
        rw rhd_def_prod,
        --simp,
        repeat {rw apq_rhd_is_right},
    },
    {
        intros a n,
        simp,
        rw prod_zero_def,
        rw pow_def_prod,
        --simp,
        repeat {rw apq_zero_pow},
    },
end


lemma apq_inverse_is_morphism_prod : is_pq_morphism (λ a : Q1 × Q2, -a) :=
begin
    split,
    {
        intros a b,
        simp,
        repeat {rw rhd_def_prod},
        repeat {rw prod_neg_def},
        --simp,
        repeat {rw apq_rhd_is_right},
    },
    {
        intros a n,
        simp,
        repeat {rw pow_def_prod},
        repeat {rw prod_neg_def},
        --simp,
        repeat {rw apq_neg_pow},
    },
end


lemma apq_addition_is_morphism_prod : is_pq_morphism (λ a : (Q1 × Q2) × (Q1 × Q2), a.1 + a.2) :=
begin
    split,
    {
        intros a b,
        simp,
        repeat {rw rhd_def_prod},
        repeat {rw prod_add_def},
        --simp,
        repeat {rw rhd_interact_add},
    },
    {
        intros a n,
        simp,
        repeat {rw pow_def_prod},
        repeat {rw prod_add_def},
        --simp,
        repeat {rw pow_dist_add},
    },
end


lemma apq_addition_assoc_prod : ∀ a b c : Q1 × Q2, a + (b + c) = (a + b) + c := 
begin
    intros a b c,
    repeat {rw prod_add_def},
    repeat {rw abelian_power_quandle.apq_addition_assoc},
end


lemma apq_addition_comm_prod : ∀ a b : Q1 × Q2, a + b = b + a :=
begin
    intros a b,
    repeat {rw prod_add_def},
    rw abelian_power_quandle.apq_addition_comm,
    apply congr_arg,
    rw abelian_power_quandle.apq_addition_comm,
end

lemma apq_addition_zero_right_prod : ∀ a : Q1 × Q2, a + 0 = a :=
begin
    intro a,
    repeat {rw prod_add_def},
    repeat {rw prod_zero_def},
    simp,
    repeat {rw abelian_power_quandle.apq_addition_zero_right},
    simp,
end


lemma apq_addition_zero_left_prod : ∀ a : Q1 × Q2, 0 + a = a :=
begin
    intro a,
    repeat {rw prod_add_def},
    repeat {rw prod_zero_def},
    simp,
    repeat {rw abelian_power_quandle.apq_addition_zero_left},
    simp,
end


lemma apq_inverse_addition_right_prod : ∀ a : Q1 × Q2, a + -a = 0 :=
begin
    intro a,
    rw prod_add_def,
    rw prod_neg_def,
    --simp,
    repeat {rw abelian_power_quandle.apq_inverse_addition_right},
    refl,
end


lemma apq_inverse_addition_left_prod : ∀ a : Q1 × Q2, -a + a = 0 :=
begin
    intro a,
    rw prod_add_def,
    rw prod_neg_def,
    --simp,
    repeat {rw abelian_power_quandle.apq_inverse_addition_left},
    refl,
end




instance product_abelian_power_quandle : abelian_power_quandle (Q1 × Q2) := abelian_power_quandle.mk
(apq_unit_is_morphism_prod)
(apq_inverse_is_morphism_prod)
(apq_addition_is_morphism_prod)
(apq_addition_assoc_prod)
(apq_addition_comm_prod)
(apq_addition_zero_right_prod)
(apq_addition_zero_left_prod)
(apq_inverse_addition_right_prod)
(apq_inverse_addition_left_prod)


-- TODO: Universal property

lemma pi1_apq_morph : is_apq_morphism (pi1 : (Q1 × Q2) → Q1) := 
begin
    split,
    {
        intros a b,
        repeat {rw pi1_def},
        rw prod_add_def,
    },
    {
        intros a n,
        repeat {rw pi1_def},
        rw pow_def_prod,
    },
end


lemma pi2_apq_morph : is_apq_morphism (pi2 : (Q1 × Q2) → Q2) :=
begin
    split,
    {
        intros a b,
        repeat {rw pi2_def},
        rw prod_add_def,
    },
    {
        intros a n,
        repeat {rw pi2_def},
        rw pow_def_prod,
    },
end

variables {Y : Type u} [abelian_power_quandle Y]

theorem prod_universal_prop_apq (f₁ : Y → Q1) (f₂ : Y → Q2) (hf₁ : is_apq_morphism f₁) (hf₂ : is_apq_morphism f₂) : 
        ∃ f : (Y → Q1 × Q2), (is_apq_morphism f) ∧ (pi1 ∘ f = f₁) ∧ (pi2 ∘ f = f₂) :=
begin
    cases hf₁ with hf₁a hf₁b,
    cases hf₂ with hf₂a hf₂b,
    let f := λ a : Y, (f₁ a, f₂ a),
    have f_def : ∀ a, f(a) = (f₁ a, f₂ a),
    {
        intro a,
        refl,
    },
    existsi f,
    split,
    {
        split,
        {
            intros a b,
            repeat {rw f_def},
            rw prod_add_def,
            --simp,
            repeat {rw hf₁a},
            repeat {rw hf₂a},
        },
        {
            intros a n,
            repeat {rw f_def},
            rw pow_def_prod,
            --simp,
            repeat {rw hf₁b},
            repeat {rw hf₂b},
        },
    },
    split,
    {refl,},
    {refl,},
end


def inclusion1 (a : Q1) : (Q1 × Q2) := (a, 0)
def inclusion2 (a : Q2) : (Q1 × Q2) := (0, a)

def inclusion1_def (a : Q1) : (inclusion1 a : Q1 × Q2) = (a, 0) := rfl
def inclusion2_def (a : Q2) : (inclusion2 a : Q1 × Q2) = (0, a) := rfl


lemma inclusion1_morph : is_apq_morphism (inclusion1 : Q1 → (Q1 × Q2)) :=
begin
    split,
    {
        intros a b,
        repeat {rw inclusion1_def},
        rw prod_add_def,
        simp,
        rw abelian_power_quandle.apq_addition_zero_right,
    },
    {
        intros a n,
        repeat {rw inclusion1_def},
        rw pow_def_prod,
        simp,
        rw apq_zero_pow,
    },
end


lemma inclusion2_morph : is_apq_morphism (inclusion2 : Q2 → (Q1 × Q2)) :=
begin
    split,
    {
        intros a b,
        repeat {rw inclusion2_def},
        rw prod_add_def,
        simp,
        rw abelian_power_quandle.apq_addition_zero_right,
    },
    {
        intros a n,
        repeat {rw inclusion2_def},
        rw pow_def_prod,
        simp,
        rw apq_zero_pow,
    },
end

theorem coprod_universal_prop_apq (f₁ : Q1 → Y) (f₂ : Q2 → Y) (hf₁ : is_apq_morphism f₁) (hf₂ : is_apq_morphism f₂) : 
        ∃ f : (Q1 × Q2 → Y), (is_apq_morphism f) ∧ (f ∘ inclusion1 = f₁) ∧ (f ∘ inclusion2 = f₂) :=
begin
    cases hf₁ with hf₁a hf₁b,
    cases hf₂ with hf₂a hf₂b,
    let f := λ x : (Q1 × Q2), f₁(x.1) + f₂(x.2),
    have f_def : ∀ x : (Q1 × Q2), f(x) = f₁(x.1) + f₂(x.2),
    {
        intro x,
        refl,
    },
    existsi f,
    split,
    {
        split,
        {
            intros a b,
            repeat {rw f_def},
            repeat {rw prod_add_def},
            simp,
            rw hf₁a,
            rw hf₂a,
            repeat {rw abelian_power_quandle.apq_addition_assoc},
            apply congr_arg (λ x, x + f₂ (b.snd)),
            repeat {rw ←abelian_power_quandle.apq_addition_assoc},
            rw abelian_power_quandle.apq_addition_comm (f₁ (b.fst)) (f₂ (a.snd)),
        },
        {
            intros a n,
            repeat {rw f_def},
            rw pow_def_prod,
            simp,
            rw hf₁b,
            rw hf₂b,
            rw pow_dist_add,
        },
    },
    split,
    {
        apply funext,
        intro x,
        simp,
        rw inclusion1_def,
        rw f_def,
        simp,
        rw apq_morphism_zero f₂,
        rw abelian_power_quandle.apq_addition_zero_right,
        exact ⟨hf₂a, hf₂b⟩, 
    },
    {
        apply funext,
        intro x,
        simp,
        rw inclusion2_def,
        rw f_def,
        simp,
        rw apq_morphism_zero f₁,
        rw abelian_power_quandle.apq_addition_zero_left,
        exact ⟨hf₁a, hf₁b⟩,
    },
end


end abelian_power_quandle_product


section abelian_power_quandle_zero_object

-- TODO: Define abelian power quandle on unit
-- TODO: Universal property as initial
-- TODO: Universal property as terminal


def point_add (a : unit) (b : unit) : unit := unit.star

def point_negative (a : unit) : unit := unit.star

def point_zero : unit := unit.star


instance point_has_add : has_add (unit) := ⟨point_add⟩ 

instance point_has_neg : has_neg (unit) := ⟨point_negative⟩

instance point_has_zero : has_zero (unit) := ⟨point_zero⟩ 


lemma all_functions_are_pq_morphism (f : unit → unit) : is_pq_morphism f :=
begin
    have is_id : f = id,
    {
        apply funext,
        intro x,
        cases (f x),
        cases x,
        refl,
    },
    rw is_id,
    apply id_is_pq_morphism,
end 



instance point_abelian_power_quandle : abelian_power_quandle unit := abelian_power_quandle.mk
(begin apply all_functions_are_pq_morphism, end)
(begin apply all_functions_are_pq_morphism, end)
(begin split, intros, apply unit_eq, intros, apply unit_eq end)
(begin intros, apply unit_eq, end)
(begin intros, apply unit_eq, end)
(begin intros, apply unit_eq, end)
(begin intros, apply unit_eq, end)
(begin intros, apply unit_eq, end)
(begin intros, apply unit_eq, end)


-- Universal property:

variables {Q : Type u} [abelian_power_quandle Q]


def initial_morphism_apq (a : unit) : Q := 0


lemma intial_morphism_apq_def (a : unit) : initial_morphism_apq a = (0 : Q) := rfl


lemma initial_morphism_is_apq_morphism : is_apq_morphism (initial_morphism_apq : (unit → Q)) :=
begin
    split,
    {
        intros a b,
        repeat {rw intial_morphism_apq_def},
        rw abelian_power_quandle.apq_addition_zero_right,
    },
    {
        intros a n,
        repeat {rw intial_morphism_apq_def},
        rw apq_zero_pow,
    },
end

theorem initial_apq_is_initial (f : unit → Q) (hf : is_apq_morphism f) : f = initial_morphism_apq :=
begin
    apply funext,
    intro a,
    repeat {rw intial_morphism_apq_def},
    have a_is_zero : a = 0,
    {apply unit_eq,},
    rw a_is_zero,
    rw apq_morphism_zero f,
    assumption,
end


def terminal_morphism_apq (a : Q) : unit := unit.star

lemma terminal_morphism_apq_is_morphism : is_apq_morphism (terminal_morphism_apq : (Q → unit)) :=
begin
    split,
    {
        intros a b,
        refl,
    },
    {
        intros a n,
        refl,
    },
end

theorem terminal_apq_is_terminal (f : Q → unit) (hf : is_apq_morphism f) : f = terminal_morphism_apq :=
begin
    apply funext,
    intro a,
    apply unit_eq,
end

end abelian_power_quandle_zero_object


