
-- Purpose: Explore pq_group (free_group s)
-- Gr Pq F_S ≃* F_(F_S) / <∀ a b, [a][b][a]⁻¹[aba⁻¹]⁻¹, ∀ a n, [a]^n[a^n]⁻¹>
-- Could prove the above, if we use it.
-- Counit, Gr Pq F_S → F_S, can we understand it?
-- Rules: Free group on F_S, but:
--   * Can swap any two symbols, changing one.
--   * Can turn [a]⁻¹ into [a⁻¹]
--   * We have [1] = 1
--   * Repeated symbols collapse

-- IDEA: F_S is definetly pq-like, so Gr Pq F_S ≃* F_S × counit.ker

-- Counit.ker has presentation:
-- B_(F_S) ≃* < [a, b] for a,b in G | xy=yx, HL(a, b) => [a, b] = 1, [a, b] = [x, a] * [x * a, b] * ([x, a * b])^-1, ([a, b])^-1 = [a * b, a^-1]>

-- Understand HL(a, b). When is [a][b] = [ab]?
--   *  When ∃ n m, a^n = b^m