
import quandle

universe u

section pre_free_pq

inductive pre_free_pq (S : Type u) : Type u
| incl (x : S) : pre_free_pq
| rhd (x y : pre_free_pq) : pre_free_pq
| pow (x : pre_free_pq) (n : ℤ) : pre_free_pq

open pre_free_pq

inductive pre_free_pq_rel' (S : Type u) : pre_free_pq S → pre_free_pq S → Type u
| refl {x : pre_free_pq S} : pre_free_pq_rel' x x
| symm {a b : pre_free_pq S} (hab : pre_free_pq_rel' a b) : pre_free_pq_rel' b a
| trans {a b c : pre_free_pq S} 
  (hab : pre_free_pq_rel' a b) (hbc : pre_free_pq_rel' b c) : pre_free_pq_rel' a c
| congr_rhd {a b a' b' : pre_free_pq S} 
  (ha : pre_free_pq_rel' a a') (hb : pre_free_pq_rel' b b') : 
  pre_free_pq_rel' (rhd a b) (rhd a' b') 
| congr_pow {a a' : pre_free_pq S} {n : ℤ} (ha : pre_free_pq_rel' a a') : 
  pre_free_pq_rel' (pow a n) (pow a' n)
| right_dist (a b c : pre_free_pq S) : pre_free_pq_rel' (rhd a (rhd b c)) (rhd (rhd a b) (rhd a c))
| self_idem_right (a : pre_free_pq S) : pre_free_pq_rel' (rhd a a) (a)
| pow_one (a : pre_free_pq S) : pre_free_pq_rel' (pow a (1 : ℤ)) (a)
| pow_comp (a : pre_free_pq S) (n m : ℤ) : pre_free_pq_rel' (pow (pow a n) m) (pow a (n * m))
| rhd_pow_zero (a b : pre_free_pq S) : pre_free_pq_rel' (rhd a (pow b (0 : ℤ))) (pow b (0 : ℤ))
| rhd_pow (a b : pre_free_pq S) (n : ℤ) : pre_free_pq_rel' (pow (rhd a b) n) (rhd a (pow b n))
| rhd_pow_add (a b : pre_free_pq S) (n m : ℤ) : pre_free_pq_rel' (rhd (pow a n) (rhd (pow a m) b)) (rhd (pow a (n + m)) b)

end pre_free_pq

