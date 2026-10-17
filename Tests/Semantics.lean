/-
Semantics probes: pin the `rfl`/`rw` closure behavior our proofs rely on.

Motivation (milestone-2/3 review): several proofs close with `rfl` after a
`rw`, relying on definitional equality that includes unfolding of regular
`def`s, beta-reduction, and Nat literal arithmetic, while `rw` performs its
rewrite but does not itself close the goal it leaves. If this semantics ever
changed (toolchain bump, tactic rewrite), these probes fail first, before the
main library proofs break in confusing ways.

Evidence-only file: plain Lean core, imports nothing, proven by `rfl`.
-/

namespace SemanticsProbe

def foo : Nat := 5

/-- `rfl` unfolds a regular `def`. -/
theorem rfl_sees_def_unfolding : foo = 5 := rfl

def X (n : Nat) : Nat := n * 2

/-- `rfl` closes via beta-reduction plus Nat literal arithmetic. -/
theorem rfl_sees_beta_and_arith : X 3 = 3 * 2 := rfl

/-- `rw` pattern matching does *not* unfold regular `def`s: the occurrence
`6` inside `X 3` is invisible to `rw`, so the rewrite fails even though the
goal is definitionally trivial. This is why our proofs must arrange
syntactically matching occurrences or close with `rfl`. -/
theorem rw_misses_def_unfolding (_h : 6 = 6) : X 3 = 3 * 2 := by
  fail_if_success rw [_h]
  rfl

def A : Nat := 7

/-- On a syntactically matching occurrence, `rw` rewrites but does not close
the goal it leaves; the trailing `rfl` does the closing, including unfolding
of regular `def`s (the `rw [...]; rfl` idiom used e.g. in
`K1Lean.phase_surrogateSpectrum`). -/
theorem rw_noop_then_rfl_closes (h : 7 = 7) : A = 7 := by
  rw [h]
  rfl

end SemanticsProbe
