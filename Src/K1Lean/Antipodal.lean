module

public import K1Lean.Parseval

/-!
# Frozen antipodal statement (v1, 2026-10-19)

Provenance: drafted and attacked in-thread (2026-10-19). Frozen after three
corrections: (i) the draft's "maximally wrong in any norm" was narrowed to
L2-only maximality (the spectrum pins L2 energy, not the sup norm); (ii) the
inverted "division-free" wording was corrected (the identity is division-free;
the zero branch only avoids division by zero); (iii) the "Not claimed" list now
states that no claim is made about typical or random draws. The acceptance gate
for the proof is statement-matching against this text, side by side, in
addition to a green build.

## Setting
`N ≥ 1`, indices modulo `N`; `f : Z/N → ℝ`. Code (numpy) convention:
* forward:  `f̂ₖ = Σₙ fₙ e^(−2πikn/N)`
* inverse:  `IDFT(X)ₙ = N⁻¹ Σₖ Xₖ e^(+2πikn/N)`

A phase field `u : Z/N → ℂ` is admissible when `star(uₖ) = u(−k)` and
`|uₖ| = 1` for all `k`.

## Statement
Define the antipodal phase
* `u^⊥ₖ = −f̂ₖ/|f̂ₖ|` if `f̂ₖ ≠ 0`,
* `u^⊥ₖ = 1` if `f̂ₖ = 0`,

and let `g := IDFT(|f̂| ⊙ u^⊥) = ZMod.dft.symm (surrogateSpectrum f u^⊥)`.

1. (admissible) `u^⊥` is admissible: `star(u^⊥ₖ) = u^⊥₋ₖ` and `|u^⊥ₖ| = 1`
   for every `k`.
2. (negation) `|f̂ₖ|·u^⊥ₖ = −f̂ₖ` for every `k`, zero modes included (`0 = −0`).
3. (antipodal) `g = −f` as complex functions; pointwise on the real field,
   `g.re n = −f n`.
4. (L2) `Σₙ (g.re n − f n)² = 4 Σₙ f n²`. Since every admissible `u'` gives a
   matched field `g'` with `Σₙ (g'.re n)² = Σₙ f n²` (finite Parseval), the
   antipodal field attains the triangle-inequality maximum `2‖f‖₂`:
   `‖g'.re − f‖₂ ≤ 2‖f‖₂` for every admissible `u'`, with equality at `u^⊥`.

Paper-level content: the spectrum-matched family contains the pointwise-negated
field. Hence spectral equivalence does not constrain the pointwise field's
sign/phase; it is not dynamical equivalence.

The zero branch avoids division by zero; the identity in 2 is division-free
(the amplitude multiplies `u^⊥`). Zero modes of `f̂` are closed under `k ↦ −k`
by Hermitian symmetry, so the branch is consistent; self-paired bins land in
the zero branch only when `f̂ = 0` there, where `1` is real and unit-modulus.
`N = 1` closes by the same case split.

## Exactness scope
Exact over `ℝ`/`ℂ` (ideal arithmetic); no floating point. The statement is
finite-dimensional and algebraic; it contains no PDE claim.

## Register
Certifies that the spectrum-matched family contains the pointwise-negated
field: spectrum matching does not constrain the sign/phase of the field. Its
L2 distance is maximal; its pointwise error is `2|f|` at every point.

## Not claimed
Anything about typical or random draws — the ensemble median `|r| = 0.07` is
empirical and untouched; the certified lemma concerns the family's extent, not
its center. No maximality in any norm other than L2 (a matched field's sup norm
is not fixed by the spectrum). No claim that spectrum matching bounds pointwise
error by a particular finite constant.

## Footnotes
Self-paired bins (`2k ≡ 0 mod N`) have `f̂ₖ ∈ ℝ`, so `u^⊥ₖ ∈ {−1, 1}` (or `1`
at zero); multidimensional grids act componentwise and are not separately
formalized.
-/

@[expose] public section

set_option autoImplicit false

namespace K1Lean

open ZMod

variable {N : ℕ} [NeZero N]

/-- The antipodal phase `u^⊥`: the spectrum-matched field is the pointwise
negated field. Paper-level meaning: the spectrum-matched family contains the
pointwise-negated field, so spectral equivalence does not constrain the
pointwise field's sign/phase. -/
noncomputable def antipodalPhase (f : ZMod N → ℝ) : ZMod N → ℂ := by
  classical
  exact fun k =>
    if ZMod.dft (fun j => (f j : ℂ)) k = 0 then 1
    else -ZMod.dft (fun j => (f j : ℂ)) k /
         ((‖ZMod.dft (fun j => (f j : ℂ)) k‖ : ℝ) : ℂ)

/-- Frozen claim 1: the antipodal phase is admissible (Hermitian and
unit-modulus). Zero modes of `f̂` are closed under `k ↦ −k` by
`dft_ofReal_conj`, so the zero branch is consistent. -/
theorem antipodalPhase_star (f : ZMod N → ℝ) (k : ZMod N) :
    star (antipodalPhase f k) = antipodalPhase f (-k) := by
  classical
  let F : ZMod N → ℂ := fun k => ZMod.dft (fun j => (f j : ℂ)) k
  have hF (k : ZMod N) : star (F k) = F (-k) := dft_ofReal_conj f k
  have hzero (k : ZMod N) : F k = 0 ↔ F (-k) = 0 := by
    constructor
    · intro hk
      have h := hF k
      rw [hk] at h
      simpa using h.symm
    · intro hk
      have h := hF k
      rw [hk] at h
      have h' := congrArg star h
      simpa using h'
  have hnorm (k : ZMod N) : ‖F (-k)‖ = ‖F k‖ := by
    rw [← hF k, Complex.star_def, Complex.norm_conj]
  by_cases hk : F k = 0
  · have hnk : F (-k) = 0 := (hzero k).mp hk
    have hk' : ZMod.dft (fun j => (f j : ℂ)) k = 0 := hk
    have hnk' : ZMod.dft (fun j => (f j : ℂ)) (-k) = 0 := hnk
    simp [antipodalPhase, hk', hnk']
  · have hnk : F (-k) ≠ 0 := fun h => hk ((hzero k).mpr h)
    have hk' : ZMod.dft (fun j => (f j : ℂ)) k ≠ 0 := hk
    have hnk' : ZMod.dft (fun j => (f j : ℂ)) (-k) ≠ 0 := hnk
    have hstar (z : ℂ) :
        star (-z / ((‖z‖ : ℝ) : ℂ)) = -star z / ((‖z‖ : ℝ) : ℂ) := by
      have hreal : star (((‖z‖ : ℝ)) : ℂ) = ((‖z‖ : ℝ) : ℂ) :=
        RCLike.conj_ofReal (‖z‖)
      rw [star_div₀, star_neg, hreal]
    calc
      star (antipodalPhase f k)
          = star (-F k / ((‖F k‖ : ℝ) : ℂ)) := by
            simp [antipodalPhase, F, hk']
      _ = -star (F k) / ((‖F k‖ : ℝ) : ℂ) := hstar (F k)
      _ = -F (-k) / ((‖F k‖ : ℝ) : ℂ) := by rw [hF k]
      _ = -F (-k) / ((‖F (-k)‖ : ℝ) : ℂ) := by rw [← hnorm k]
      _ = antipodalPhase f (-k) := by
            simp [antipodalPhase, F, hnk']

/-- Frozen claim 1: the antipodal phase has unit modulus at every mode. -/
theorem antipodalPhase_norm (f : ZMod N → ℝ) (k : ZMod N) :
    ‖antipodalPhase f k‖ = 1 := by
  classical
  let F : ZMod N → ℂ := fun k => ZMod.dft (fun j => (f j : ℂ)) k
  by_cases hk : F k = 0
  · have hk' : ZMod.dft (fun j => (f j : ℂ)) k = 0 := hk
    simp [antipodalPhase, hk']
  · have hk' : ZMod.dft (fun j => (f j : ℂ)) k ≠ 0 := hk
    have hpos : 0 < ‖F k‖ := norm_pos_iff.mpr hk
    have hnormR (r : ℝ) : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r
    calc
      ‖antipodalPhase f k‖ = ‖-F k / ((‖F k‖ : ℝ) : ℂ)‖ := by
        simp [antipodalPhase, F, hk']
      _ = ‖-F k‖ / ‖((‖F k‖ : ℝ) : ℂ)‖ := by rw [norm_div]
      _ = ‖F k‖ / ‖((‖F k‖ : ℝ) : ℂ)‖ := by rw [norm_neg]
      _ = ‖F k‖ / ‖F k‖ := by
        rw [hnormR, abs_of_nonneg (norm_nonneg (F k))]
      _ = 1 := div_self (ne_of_gt hpos)

/-- Frozen claim 1, packaged: `u^⊥` is admissible (Hermitian and
unit-modulus). -/
theorem antipodalPhase_admissible (f : ZMod N → ℝ) :
    (∀ k, star (antipodalPhase f k) = antipodalPhase f (-k)) ∧
      ∀ k, ‖antipodalPhase f k‖ = 1 :=
  ⟨antipodalPhase_star f, antipodalPhase_norm f⟩

/-- Frozen claim 2: the per-mode amplitude identity `|f̂ₖ|·u^⊥ₖ = −f̂ₖ`,
division-free; at zero modes it reads `0 = −0`. -/
theorem surrogateSpectrum_antipodalPhase (f : ZMod N → ℝ) (k : ZMod N) :
    surrogateSpectrum f (antipodalPhase f) k
      = -ZMod.dft (fun j => (f j : ℂ)) k := by
  classical
  let F : ZMod N → ℂ := fun k => ZMod.dft (fun j => (f j : ℂ)) k
  by_cases hk : F k = 0
  · have hk' : ZMod.dft (fun j => (f j : ℂ)) k = 0 := hk
    simp [surrogateSpectrum, antipodalPhase, hk']
  · have hk' : ZMod.dft (fun j => (f j : ℂ)) k ≠ 0 := hk
    have hpos : 0 < ‖F k‖ := norm_pos_iff.mpr hk
    have hcast : ((‖F k‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
    calc
      surrogateSpectrum f (antipodalPhase f) k
          = ((‖F k‖ : ℝ) : ℂ) * (-F k / ((‖F k‖ : ℝ) : ℂ)) := by
            simp [surrogateSpectrum, antipodalPhase, F, hk']
      _ = -F k := by
            rw [mul_div_assoc']
            exact mul_div_cancel_left₀ (-F k) hcast

/-- Frozen claim 3: the antipodal field is exactly the negated field,
`g = −f` as complex functions. -/
theorem antipodal (f : ZMod N → ℝ) :
    ZMod.dft.symm (surrogateSpectrum f (antipodalPhase f))
      = fun n => -(f n : ℂ) := by
  have hX : surrogateSpectrum f (antipodalPhase f)
      = fun k => -ZMod.dft (fun j => (f j : ℂ)) k := by
    funext k
    exact surrogateSpectrum_antipodalPhase f k
  have hneg :
      ZMod.dft.symm (fun k => -ZMod.dft (fun j => (f j : ℂ)) k)
        = -ZMod.dft.symm (ZMod.dft (fun j => (f j : ℂ))) := by
    change ZMod.dft.symm (-(ZMod.dft (fun j => (f j : ℂ))))
        = -(ZMod.dft.symm (ZMod.dft (fun j => (f j : ℂ))))
    exact ZMod.dft.symm.toLinearMap.map_neg (ZMod.dft (fun j => (f j : ℂ)))
  rw [hX, hneg]
  funext n
  simp [ZMod.dft.symm_apply_apply]

/-- Frozen claim 4, L2 corollary: the antipodal field has squared distance
`4 Σ f²`, i.e. distance `2‖f‖₂`. The universal L2 upper bound over all
admissible phases is the Parseval + triangle-inequality prose mapped in
`STATEMENT_MATCH.md`; it is deliberately not a declaration here. -/
theorem antipodal_energy (f : ZMod N → ℝ) :
    ∑ n : ZMod N,
        ((ZMod.dft.symm (surrogateSpectrum f (antipodalPhase f)) n).re - f n) ^ 2
      = 4 * ∑ n : ZMod N, (f n) ^ 2 := by
  have h := antipodal f
  have hterm (n : ZMod N) :
      ((ZMod.dft.symm (surrogateSpectrum f (antipodalPhase f)) n).re - f n) ^ 2
        = 4 * (f n) ^ 2 := by
    rw [congrFun h n]
    simp only [Complex.neg_re, Complex.ofReal_re]
    ring
  calc
    ∑ n : ZMod N,
        ((ZMod.dft.symm (surrogateSpectrum f (antipodalPhase f)) n).re - f n) ^ 2
        = ∑ n : ZMod N, 4 * (f n) ^ 2 :=
      Finset.sum_congr rfl fun n _ => hterm n
    _ = 4 * ∑ n : ZMod N, (f n) ^ 2 :=
      (Finset.mul_sum Finset.univ (fun n => (f n) ^ 2) 4).symm

end K1Lean
