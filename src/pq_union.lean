
import power_quandle

universes u v

section power_quandle_union

variables {Q1 : Type u} [power_quandle Q1] {Q2 : Type v} [power_quandle Q2]


inductive pq_union_rel' : Q1 ⊕ Q2 → Q1 ⊕ Q2 → Type (max u v)
| refl {x : Q1 ⊕ Q2} : pq_union_rel' x x
| unit_glue1 : pq_union_rel' (sum.inl 1) (sum.inr 1)
| unit_glue2 : pq_union_rel' (sum.inr 1) (sum.inl 1)

inductive pq_union_rel : Q1 ⊕ Q2 → Q1 ⊕ Q2 → Prop
| rel {x y : Q1 ⊕ Q2} (hxy : pq_union_rel' x y) : pq_union_rel x y

@[refl]
lemma pq_union_rel_refl {x : Q1 ⊕ Q2} : pq_union_rel x x :=
begin
  refine pq_union_rel.rel _,
  exact pq_union_rel'.refl,
end

@[symm]
lemma pq_union_rel_symm {x y : Q1 ⊕ Q2} (hxy : pq_union_rel x y) : pq_union_rel y x :=
begin
  cases hxy,
  refine pq_union_rel.rel _,
  cases hxy_hxy,
  {
    exact pq_union_rel'.refl,
  },
  {
    exact pq_union_rel'.unit_glue2,
  },
  {
    exact pq_union_rel'.unit_glue1,
  },
end

@[trans]
lemma pq_union_rel_trans {x y z : Q1 ⊕ Q2} (hxy : pq_union_rel x y) (hyz : pq_union_rel y z) : pq_union_rel x z :=
begin
  cases hxy,
  cases hyz,
  refine pq_union_rel.rel _,
  cases hxy_hxy;
  cases hyz_hxy,
  exact pq_union_rel'.refl,
  exact pq_union_rel'.unit_glue1,
  exact pq_union_rel'.unit_glue2,
  exact pq_union_rel'.unit_glue1,
  exact pq_union_rel'.refl,
  exact pq_union_rel'.unit_glue2,
  exact pq_union_rel'.refl,
end

instance pq_union_rel_setoid : setoid (Q1 ⊕ Q2) := { 
  r := pq_union_rel,
  iseqv := begin 
    split,
    apply pq_union_rel_refl,
    split,
    apply pq_union_rel_symm,
    apply pq_union_rel_trans,
  end }

def pq_union (Q1 : Type u) [power_quandle Q1] (Q2 : Type v) [power_quandle Q2] := quotient (@pq_union_rel_setoid Q1 _ Q2 _)

end power_quandle_union


section power_quandle_union_pq

variables {Q1 : Type u} [power_quandle Q1] {Q2 : Type v} [power_quandle Q2]

lemma quot_mk_helper_pq_union (a : Q1 ⊕ Q2) : quot.mk setoid.r a = ⟦a⟧ := rfl

instance pq_union_has_one : has_one (pq_union Q1 Q2) := ⟨⟦sum.inl 1⟧⟩

lemma pq_union_one_def : (1 : pq_union Q1 Q2) = ⟦sum.inl 1⟧ := rfl

lemma pq_union_one_inl : ⟦sum.inl 1⟧ = (1 : pq_union Q1 Q2) := rfl
lemma pq_union_one_inr : ⟦sum.inr 1⟧ = (1 : pq_union Q1 Q2) := begin 
  rw pq_union_one_def,
  apply quotient.sound,
  fconstructor,
  exact pq_union_rel'.unit_glue2,
end

lemma pq_union_same1 (x y : Q1) : ((sum.inl x : Q1 ⊕ Q2) ≈ (sum.inl y)) ↔ x = y :=
begin
  split,
  {
    intro hxy,
    cases hxy,
    cases hxy_hxy,
    refl,
  },
  {
    intro hxy,
    rw hxy,
  },
end

lemma pq_union_same2 (x y : Q2) : ((sum.inr x : Q1 ⊕ Q2) ≈ (sum.inr y)) ↔ x = y :=
begin
  split,
  {
    intro hxy,
    cases hxy,
    cases hxy_hxy,
    refl,
  },
  {
    intro hxy,
    rw hxy,
  },
end

lemma pq_union_different1 (x : Q1) (y : Q2) : ((sum.inl x : Q1 ⊕ Q2) ≈ (sum.inr y)) ↔ (x = 1 ∧ y = 1) :=
begin
  split,
  {
    intro hxy,
    cases hxy,
    cases hxy_hxy,
    split,
    refl,
    refl,
  },
  {
    intro hxy,
    cases hxy with hxy1 hxy2,
    rw [hxy1, hxy2],
    fconstructor,
    exact pq_union_rel'.unit_glue1,
  },
end

lemma pq_union_different2 (x : Q2) (y : Q1) : ((sum.inr x : Q1 ⊕ Q2) ≈ (sum.inl y)) ↔ (x = 1 ∧ y = 1) :=
begin
  split,
  {
    intro hxy,
    cases hxy,
    cases hxy_hxy,
    split,
    refl,
    refl,
  },
  {
    intro hxy,
    cases hxy with hxy1 hxy2,
    rw [hxy1, hxy2],
    fconstructor,
    exact pq_union_rel'.unit_glue2,
  },
end

/-
lemma pq_union_different1 (x : Q1) (y : Q2) (hxy : (sum.inl x : Q1 ⊕ Q2) ≈ (sum.inr y)) : x = 1 :=
begin
  cases hxy,
  cases hxy_hxy,
  refl,
end

lemma pq_union_different2 (x : Q1) (y : Q2) (hxy : (sum.inl x : Q1 ⊕ Q2) ≈ (sum.inr y)) : y = 1 :=
begin
  cases hxy,
  cases hxy_hxy,
  refl,
end
-/

def pre_pq_union_rhd : Q1 ⊕ Q2 → Q1 ⊕ Q2 → Q1 ⊕ Q2
| (sum.inl x) (sum.inl y) := sum.inl (x ▷ y)
| (sum.inl x) (sum.inr y) := sum.inr y
| (sum.inr x) (sum.inl y) := sum.inl y
| (sum.inr x) (sum.inr y) := sum.inr (x ▷ y)

def pq_union_rhd : pq_union Q1 Q2 → pq_union Q1 Q2 → pq_union Q1 Q2 := λ x y, quotient.lift_on₂ x y (λ x y, ⟦pre_pq_union_rhd x y⟧) begin 
  intros a b c d hac hbd,
  apply quotient.sound,
  cases a;
  cases b;
  cases c;
  cases d;
  unfold pre_pq_union_rhd;
  try {exact hbd};
  try {rw pq_union_same1 at *};
  try {rw pq_union_same2 at *};
  try {rw pq_union_different1 at *};
  try {rw pq_union_different2 at *};
  try {congr, repeat {assumption}};
  try {split};
  try {simp only [hac, hbd, power_quandle.rhd_one, power_quandle.one_rhd]},
end

instance pq_union_has_rhd : has_rhd (pq_union Q1 Q2) := ⟨pq_union_rhd⟩

lemma pq_union_rhd_def (x y : pq_union Q1 Q2) : x ▷ y = pq_union_rhd x y := rfl

def pre_pq_union_pow : Q1 ⊕ Q2 → ℤ → Q1 ⊕ Q2
| (sum.inl x) n := sum.inl (x ^ n)
| (sum.inr x) n := sum.inr (x ^ n)

def pq_union_pow : pq_union Q1 Q2 → ℤ → pq_union Q1 Q2 := λ x n, quotient.lift_on x (λ x, ⟦pre_pq_union_pow x n⟧) begin 
  intros a b hab,
  apply quotient.sound,
  cases a;
  cases b;
  unfold pre_pq_union_pow;
  try {rw pq_union_same1 at *};
  try {rw pq_union_same2 at *};
  try {rw pq_union_different1 at *};
  try {rw pq_union_different2 at *};
  try {congr, repeat {assumption}};
  try {split};
  try {simp only [hab, pq_one_pow]},
end

instance pq_union_has_pow : has_pow (pq_union Q1 Q2) ℤ := ⟨pq_union_pow⟩

lemma pq_union_pow_def (x : pq_union Q1 Q2) (n : ℤ) : x ^ n = pq_union_pow x n := rfl

instance pq_union_is_pq : power_quandle (pq_union Q1 Q2) := { 
  rhd_dist := begin 
    intros a b c,
    induction a,
    induction b,
    induction c,
    {
      simp only [quot_mk_helper_pq_union],
      simp only [pq_union_rhd_def],
      unfold pq_union_rhd,
      simp only [quotient.lift_on_beta₂, quotient.eq],
      cases a;
      cases b;
      cases c;
      unfold pre_pq_union_rhd;
      rw power_quandle.rhd_dist,
    },
    {refl,},
    {refl,},
    {refl,},
  end,
  rhd_idem := begin 
    intro a,
    induction a,
    {
      simp only [quot_mk_helper_pq_union],
      simp only [pq_union_rhd_def],
      unfold pq_union_rhd,
      simp only [quotient.lift_on_beta₂, quotient.eq],
      cases a;
      unfold pre_pq_union_rhd;
      rw power_quandle.rhd_idem,
    },
    {refl,},
  end,
  pow_one := begin 
    intro a,
    induction a,
    {
      simp only [quot_mk_helper_pq_union],
      simp only [pq_union_pow_def],
      unfold pq_union_pow,
      simp only [quotient.lift_on_beta, quotient.eq],
      cases a;
      unfold pre_pq_union_pow;
      rw power_quandle.pow_one,
    },
    {refl,},
  end,
  pow_zero := begin 
    intro a,
    induction a,
    {
      simp only [quot_mk_helper_pq_union],
      simp only [pq_union_pow_def],
      unfold pq_union_pow,
      simp only [quotient.lift_on_beta, quotient.eq],
      cases a;
      unfold pre_pq_union_pow;
      rw power_quandle.pow_zero;
      simp only [pq_union_one_inl, pq_union_one_inr],
    },
    {refl,},
  end,
  pow_comp := begin 
    intros a n m,
    induction a,
    {
      simp only [quot_mk_helper_pq_union],
      simp only [pq_union_pow_def],
      unfold pq_union_pow,
      simp only [quotient.lift_on_beta, quotient.eq],
      cases a;
      unfold pre_pq_union_pow;
      rw power_quandle.pow_comp,
    },
    {refl,},
  end,
  rhd_one := begin 
    intro a,
    induction a,
    {
      simp only [quot_mk_helper_pq_union],
      simp only [pq_union_rhd_def, pq_union_one_def],
      unfold pq_union_rhd,
      simp only [quotient.lift_on_beta₂, quotient.eq],
      cases a;
      unfold pre_pq_union_rhd;
      rw power_quandle.rhd_one,
    },
    {refl,},
  end,
  one_rhd := begin 
    intro a,
    induction a,
    {
      simp only [quot_mk_helper_pq_union],
      simp only [pq_union_rhd_def, pq_union_one_def],
      unfold pq_union_rhd,
      simp only [quotient.lift_on_beta₂, quotient.eq],
      cases a;
      unfold pre_pq_union_rhd;
      rw power_quandle.one_rhd,
    },
    {refl,},
  end,
  pow_rhd := begin 
    intros a b n,
    induction a,
    induction b,
    {
      simp only [quot_mk_helper_pq_union],
      simp only [pq_union_rhd_def, pq_union_pow_def],
      unfold pq_union_rhd,
      unfold pq_union_pow,
      simp only [quotient.lift_on_beta, quotient.lift_on_beta₂, quotient.eq],
      cases a;
      cases b;
      unfold pre_pq_union_rhd;
      unfold pre_pq_union_pow;
      unfold pre_pq_union_rhd;
      rw power_quandle.pow_rhd,
    },
    {refl,},
    {refl,},
  end,
  rhd_pow_add := begin 
    intros a b n m,
    induction a,
    induction b,
    {
      simp only [quot_mk_helper_pq_union],
      simp only [pq_union_rhd_def, pq_union_pow_def],
      unfold pq_union_rhd,
      unfold pq_union_pow,
      simp only [quotient.lift_on_beta, quotient.lift_on_beta₂, quotient.eq],
      cases a;
      cases b;
      unfold pre_pq_union_pow;
      unfold pre_pq_union_rhd;
      rw power_quandle.rhd_pow_add,
    },
    {refl,},
    {refl,},
  end,
  ..pq_union_has_one,
  ..pq_union_has_rhd,
  ..pq_union_has_pow }


end power_quandle_union_pq
