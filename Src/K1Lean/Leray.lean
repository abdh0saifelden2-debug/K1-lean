module

public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# Frozen discrete Leray symbol statement (v1, 2026-10-20)

Provenance: drafted and attacked in-thread (2026-10-19/20), then frozen. Two
attack rounds produced substantive corrections. The dimensional flaw: a 1D
torus cannot support the `κκᵀ` symbol; the paper's two-torus instantiation
takes `d = 2`, while the 2a statement is deliberately abstract in `d`. The
Nyquist pathology: `natAbs_valMinAbs_neg` does not give `S(−k) = S(k)` at even
`N` (counterexample: `κ₁ = (N/2, 1)` versus `κ₂ = (N/2, −1)`), so 2b freezes
with `[Odd N]` (fence below). Frozen with three amendments: (i) file/proof
order 1, 3, 2 — the row identity is proved from the column identity and
symmetry; (ii) the definition carries the hypothesis `hq : κ ⬝ᵥ κ ≠ 0`;
(iii) `[NeZero d]`. The acceptance gate for the proof is statement-matching
against this text, side by side, in addition to a green build.

## Setting
`d ≥ 1`, `κ : Fin d → ℝ`, `q(κ) := Σᵢ κᵢ² = κ ⬝ᵥ κ` with the nonzero
hypothesis `hq`, and the discrete Leray symbol
`S(κ) := I − κκᵀ/q(κ)`, i.e. `S(κ)ᵢⱼ = δᵢⱼ − κᵢκⱼ/q(κ)`.

## Statement
1. (column) `S(κ) *ᵥ κ = 0`.
2. (row) `κ ᵥ* S(κ) = 0`.
3. (symmetric) `S(κ)ᵀ = S(κ)`.
4. (idempotent) `S(κ) * S(κ) = S(κ)` (rank-one collapse).
5. (even) `S(−κ) = S(κ)`.

File order is 1, 3, 2, 4, 5: the row identity 2 is proved from claims 1 and 3
via `Matrix.mulVec_transpose`, so it appears after them; no declaration refers
forward.

## Register
This is the entire algebraic content of the Leray symbol: the finite-
dimensional symbol algebra, exact over `ℝ`. The operator layer — the two-torus
`(ZMod N)²`, `valMinAbs` wavenumbers, reality, idempotence as a projection,
and the spectral-divergence ledger — is deliberately 2b, frozen separately
after this layer merges.

## Not claimed
Anything with a lattice, Fourier transform or modulus; self-adjointness of the
Leray projector `P` (claim 8 was cut here; it is recorded in
`STATEMENT_MATCH.md` under mapped-prose/optional and revisited only if P1's
FDT argument needs it); no unitarity; no eigenvalue claims; no smoothness.

## Scope fence for 2b (Nyquist)
2b freezes with N odd; the even-N Nyquist modes are a documented limitation,
not in scope. Rationale: `valMinAbs (−k) = − valMinAbs k` fails exactly at
even-N self-paired bins, and the counterexample above shows `S(−k) = S(k)` can
fail there; with `N` odd, `valMinAbs_neg_of_ne_half` is total and claim 5
supplies the evenness step. Code behaviour (checked 2026-10-20, so that the
formalization does not silently assume what the numerics must engineer):
`K1-two-clocks-theory/compressible/ns.py`, class `Spectral2D` (used by
`boussinesq/solver.py`), builds wavenumbers with `np.fft.fftfreq(n)` (`0, 1,
…, −1`; at even `n` the Nyquist frequency sits at `−n/2`), applies the
2/3-rule dealiasing mask `kmax = n // 3` to products and derivatives
(`ddx_dealias`, `_dealias_advect`), and pins only the `k = 0` mode
(`k2_inv[0, 0] = 0`; `incompressible_pressure` sets `p_h[0, 0] = 0`). The raw
projection symbol (`helmholtz`, `projection_potential`) uses `kx, ky` with no
Nyquist zeroing. Even-N Nyquist handling is therefore an engineering choice
inside the documented limitation, not an assumption of this formalization.

## Forward scope (zero mode)
`S(0) = I` follows from the definition as its junk-value completion; it is the
projector convention, and it is the only correct one because constants are
exactly divergence-free. The code's `k² = 0` gauge pin (the `k2_inv` pin
above) is a different operation — the null-gauge of the Poisson solve — and
must not be conflated with `S(0) = I` in docstrings.

## Exactness scope
Exact over `ℝ` (ideal arithmetic); no floating point; finite-dimensional and
algebraic; no PDE claim.
-/

@[expose] public section

set_option autoImplicit false

namespace K1Lean

open Matrix

/-- The discrete Leray symbol `S(κ) = I − κκᵀ/q(κ)`, `q(κ) = κ ⬝ᵥ κ`, at
wavevector `κ` with the nonzero hypothesis `hq`. Paper-level meaning: this is
the symbol of the Leray projector `P = I − ∇(Δ⁻¹)∇·` on a periodic grid, with
the zero mode kept by the projector convention (`S(0) = I`; forward scope in
the module docstring). -/
set_option linter.unusedVariables false in
noncomputable def leraySymbol {d : ℕ} [NeZero d] (κ : Fin d → ℝ)
    (hq : κ ⬝ᵥ κ ≠ 0) : Matrix (Fin d) (Fin d) ℝ :=
  1 - Matrix.of fun i j => κ i * κ j / (κ ⬝ᵥ κ)

/-- Frozen claim 1: the symbol kills its own wavevector on the right (column
form), `S(κ) *ᵥ κ = 0`. -/
theorem leraySymbol_mulVec_self {d : ℕ} [NeZero d] (κ : Fin d → ℝ)
    (hq : κ ⬝ᵥ κ ≠ 0) : leraySymbol κ hq *ᵥ κ = 0 := by
  have hA : Matrix.of (fun i j => κ i * κ j / (κ ⬝ᵥ κ)) *ᵥ κ = κ := by
    funext i
    change (∑ j, κ i * κ j / (κ ⬝ᵥ κ) * κ j) = κ i
    calc
      (∑ j, κ i * κ j / (κ ⬝ᵥ κ) * κ j)
          = ∑ j, (κ i / (κ ⬝ᵥ κ)) * (κ j * κ j) :=
            Finset.sum_congr rfl fun j _ => by ring
      _ = (κ i / (κ ⬝ᵥ κ)) * ∑ j, κ j * κ j :=
            (Finset.mul_sum Finset.univ (fun j => κ j * κ j) _).symm
      _ = (κ i / (κ ⬝ᵥ κ)) * (κ ⬝ᵥ κ) := by
            simp [Matrix.dotProduct]
      _ = κ i := div_mul_cancel₀ _ hq
  unfold leraySymbol
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA, sub_self]

/-- Frozen claim 3: the symbol is symmetric, `S(κ)ᵀ = S(κ)`. -/
theorem leraySymbol_transpose {d : ℕ} [NeZero d] (κ : Fin d → ℝ)
    (hq : κ ⬝ᵥ κ ≠ 0) :
    (leraySymbol κ hq)ᵀ = leraySymbol κ hq := by
  ext i j
  change (if j = i then (1 : ℝ) else 0) - κ j * κ i / (κ ⬝ᵥ κ)
      = (if i = j then (1 : ℝ) else 0) - κ i * κ j / (κ ⬝ᵥ κ)
  by_cases h : i = j
  · subst h
    rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), mul_comm (κ j) (κ i)]

/-- Frozen claim 2: the symbol kills its own wavevector on the left (row
form), `κ ᵥ* S(κ) = 0`. Proved from claims 1 and 3 via
`Matrix.mulVec_transpose`; this is the form the 2b divergence ledger consumes. -/
theorem leraySymbol_vecMul_self {d : ℕ} [NeZero d] (κ : Fin d → ℝ)
    (hq : κ ⬝ᵥ κ ≠ 0) :
    κ ᵥ* leraySymbol κ hq = 0 := by
  calc
    κ ᵥ* leraySymbol κ hq = (leraySymbol κ hq)ᵀ *ᵥ κ :=
      (Matrix.mulVec_transpose (leraySymbol κ hq) κ).symm
    _ = leraySymbol κ hq *ᵥ κ := by rw [leraySymbol_transpose]
    _ = 0 := leraySymbol_mulVec_self κ hq

/-- Frozen claim 4: the symbol is idempotent, `S(κ) * S(κ) = S(κ)`
(rank-one collapse: `(κκᵀ)(κκᵀ) = q(κ)·κκᵀ`). -/
theorem leraySymbol_idem {d : ℕ} [NeZero d] (κ : Fin d → ℝ)
    (hq : κ ⬝ᵥ κ ≠ 0) :
    leraySymbol κ hq * leraySymbol κ hq = leraySymbol κ hq := by
  have hAA : Matrix.of (fun i j => κ i * κ j / (κ ⬝ᵥ κ)) *
      Matrix.of (fun i j => κ i * κ j / (κ ⬝ᵥ κ)) =
      Matrix.of (fun i j => κ i * κ j / (κ ⬝ᵥ κ)) := by
    ext i j
    change (∑ l, κ i * κ l / (κ ⬝ᵥ κ) * (κ l * κ j / (κ ⬝ᵥ κ)))
        = κ i * κ j / (κ ⬝ᵥ κ)
    calc
      (∑ l, κ i * κ l / (κ ⬝ᵥ κ) * (κ l * κ j / (κ ⬝ᵥ κ)))
          = ∑ l, (κ i * κ j * (κ ⬝ᵥ κ)⁻¹ * (κ ⬝ᵥ κ)⁻¹) * (κ l * κ l) :=
            Finset.sum_congr rfl fun l _ => by ring
      _ = (κ i * κ j * (κ ⬝ᵥ κ)⁻¹ * (κ ⬝ᵥ κ)⁻¹) * ∑ l, κ l * κ l :=
            (Finset.mul_sum Finset.univ (fun l => κ l * κ l) _).symm
      _ = (κ i * κ j * (κ ⬝ᵥ κ)⁻¹ * (κ ⬝ᵥ κ)⁻¹) * (κ ⬝ᵥ κ) := by
            simp [Matrix.dotProduct]
      _ = κ i * κ j / (κ ⬝ᵥ κ) := by
            have hcc : (κ ⬝ᵥ κ)⁻¹ * (κ ⬝ᵥ κ) = 1 := by
              rw [mul_comm (κ ⬝ᵥ κ)⁻¹ (κ ⬝ᵥ κ), mul_inv_cancel₀ hq]
            calc
              (κ i * κ j * (κ ⬝ᵥ κ)⁻¹ * (κ ⬝ᵥ κ)⁻¹) * (κ ⬝ᵥ κ)
                  = (κ i * κ j * (κ ⬝ᵥ κ)⁻¹) *
                      ((κ ⬝ᵥ κ)⁻¹ * (κ ⬝ᵥ κ)) := mul_assoc _ _ _
              _ = (κ i * κ j * (κ ⬝ᵥ κ)⁻¹) * 1 := by rw [hcc]
              _ = κ i * κ j / (κ ⬝ᵥ κ) := by
                    rw [mul_one, div_eq_mul_inv]
  unfold leraySymbol
  rw [sub_mul, mul_sub, one_mul, mul_one, hAA, sub_self, sub_zero]

/-- Frozen claim 5: the symbol is even, `S(−κ) = S(κ)`. This is the step that
2b consumes with `[Odd N]`; at even `N` the `valMinAbs` sign symmetry fails at
the Nyquist bins (see the scope fence in the module docstring). -/
theorem leraySymbol_neg {d : ℕ} [NeZero d] (κ : Fin d → ℝ)
    (hq : κ ⬝ᵥ κ ≠ 0) :
    leraySymbol (-κ) (by simpa [neg_dotProduct_neg] using hq) =
      leraySymbol κ hq := by
  ext i j
  change (if i = j then (1 : ℝ) else 0) - (-κ) i * (-κ) j / ((-κ) ⬝ᵥ (-κ))
      = (if i = j then (1 : ℝ) else 0) - κ i * κ j / (κ ⬝ᵥ κ)
  rw [Pi.neg_apply, neg_dotProduct_neg, neg_mul_neg]

end K1Lean
