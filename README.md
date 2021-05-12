# power-quandle-lean

If you are interested in the formalization of power quandles, feel free to contact me. 

This code is of very poor quality, and very undocumented. There are many files which accomplish nothing of use. Thankfully, Lean is built in such a manner that no matter how poor quality the code is in, we can be sure there are no errors if Lean does not output an error or a warning. However, that does not mean the code cannot be misunderstood or have confusing notation.

Note the main definition of power quandles is different compared to the one in the paper, but they are equivalent. The definition in Lean is from an earlier version.

## Where to find what:

In rough order of when it appears in the paper:

* power_quandle.lean contains the main definition of power quandles, and basic consequences.
* group_to_pq.lean defines how a group is also a power quandle. It also contains that power quandle-isomorphic groups have group-isomorphic center quotient.
* abelian_power_quandle.lean contains the definition of abelian power quandles as well as the theorem that a rhd b = b.
* pq_to_group.lean defines the functor Gr : PowQdl -> Grp, and its adjointness. It also contains that Gr Pq (C_n) ~= C_n and that Gr Pq (C_2 x C_2) ~= (C_2)^3.
* counit_ker_abelian.lean establishes that the kernel of the counit is in the center.
* pq_group_union.lean establishes that Gr (Q1 U Q2) ~= Gr Q1 x Gr Q2.
* pq_hom_group_property.lean establishes that a power quandle morphism being a group homomorphism is equivalent to a certain diagram commuting.
* pq_group_equalizer_eta_L_eta.lean establishes that [x] = L(eta)(x) is equivalent to x = [y] for some y.
* pq_like.lean establishes that if G is pq-like, then Gr Pq (G) ~= A x G where A is abelian.
* minimal_sub_pq.lean establishes that if G is pq-like, then it is isomorphism to Gr (Q) where Q is a sub-power quandle of Pq (G).
* pq_like_semidirect_product.lean establishes that semidirect products are pq-like under a certain hypothesis.
* pq_group_free_pq.lean establishes that Gr of a free power quandle is the free group, with the same generating set.

