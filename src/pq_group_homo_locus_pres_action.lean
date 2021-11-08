
import pq_group_homo_locus_pres

universe u

section pq_group_homo_locus_pres_action

-- lift_homo_locus_pres_morph

variables {G : Type u} [group G]

def homo_locus_pres_action (g : G) : homo_locus_pres G →* homo_locus_pres G :=
begin
  fapply lift_homo_locus_pres_morph,
  {
    intro x,
    exact homo_locus_of (g, x.1) * homo_locus_of (g * x.1, x.2),
  },
  {
    split,
    {
      sorry,
    },
    split,
    {
      intros a b hab,
      simp only,
      -- This is [g][a][b][gab]^-1, should equal [g][ab][gab]^-1
      sorry,
    },
    split,
    {
      sorry,
    },
    {
      sorry,
    },
  },
end

end pq_group_homo_locus_pres_action
