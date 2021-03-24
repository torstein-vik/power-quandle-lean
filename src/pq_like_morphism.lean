
import pq_to_group

universes u1 u2

section pq_like_morphism

variables {Q1 : Type u1} {Q2 : Type u2} [power_quandle Q1] [power_quandle Q2]

variables {φ : pq_group Q1 →* pq_group Q2}

variables {hφ : ∃ f : Q1 → Q2, ∀ x, φ (of x) = of (f x) }

include hφ

theorem comes_from_pq_morph : ∃ f : Q1 → Q2, is_pq_morphism f ∧ ∀ x, φ (of x) = of (f x) :=
begin
  cases hφ with f hf,
  use f,
  split,
  {
    split,
    {
      intros a b,
      sorry,
    },
    {
      sorry,
    },
  },
  {
    exact hf,
  },
end

end pq_like_morphism
