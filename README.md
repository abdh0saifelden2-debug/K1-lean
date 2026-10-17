# K1-lean

Lean skeleton for surrogate tests (finite-dimensional only). Statements first.

Close-out statement-match audit (frozen v2 ↔ Lean, whole file): [STATEMENT_MATCH.md](STATEMENT_MATCH.md).

## Mathlib facts (handoff inventory, pinned v4.35.0)

Verified against `.lake/packages/mathlib` at the pinned commit; `file:line`
refers to that checkout.

- `Fintype.sum_mul_sum (f g) : (∑ i, f i) * ∑ j, g j = ∑ i, ∑ j, f i * g j`
  (`Mathlib/Algebra/BigOperators/Ring/Finset.lean:66`). `Finset.sum_mul` /
  `Finset.mul_sum` failed to key-match on `univ` sums; use the `Fintype` form.
- `ite_eq_right (h : ¬c) : (if c then a else b) = b` — replaces deprecated
  `if_neg`. `rw [sub_eq_zero]` under an `ite` condition hits a dependent
  `Decidable` motive error; use `by_cases` + `ite_eq_right`.
- `‖(r : ℂ)‖ ^ 2 = r ^ 2` route: `← Complex.normSq_eq_norm_sq`,
  `Complex.normSq_ofReal`, `← pow_two`. `rw [RCLike.norm_ofReal]` does not
  key-match (instance mismatch); state `have hnormR : ‖(r : ℂ)‖ = |r| :=
  RCLike.norm_ofReal r` (term mode) and rewrite with the local hypothesis.
- `simp only [smul_eq_mul]` succeeds where `rw [smul_eq_mul]` fails on the
  module-scalar `•` instance (used in `hstar` in `Parseval.lean`).
- `norm_mul` and `abs_of_nonneg` are in scope and already used in
  `Parseval.lean:160`; `Complex.norm_mul` (protected,
  `Mathlib/Analysis/Complex/Norm.lean:75`) is an alternative with the same
  statement.
