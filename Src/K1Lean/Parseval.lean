import Mathlib.Analysis.Fourier.ZMod

/-!
# Frozen finite-Parseval / surrogate-spectrum statement (v2, amended)

Provenance: drafted in-thread and attacked over two adversarial review rounds
(2026-10-17), then amended before freeze: exactness scoping, multiplier
adjective pinned (real / even / nonnegative), register clause (bookkeeping vs
E5 empirics), zero-mode vacuity on claim 2, and `m·g` defined once. The
acceptance gate for every following milestone is statement-matching against
this text, side by side, in addition to a green build.

## Setting
`N ≥ 1`, indices modulo `N`; `f : Z/N → ℝ`. Code (numpy) convention:
* forward:  `f̂ₖ = Σₙ fₙ e^(−2πikn/N)`
* inverse:  `IDFT(X)ₙ = N⁻¹ Σₖ Xₖ e^(+2πikn/N)`

Both compositions are identities; finite Parseval: `Σₙ fₙ² = N⁻¹ Σₖ |f̂ₖ|²`.

## Admissible phase factors
`u : Z/N → ℂ` with `star(uₖ) = u(−k)` and `|uₖ| = 1` (Hermitian,
unit-modulus). Equivalently `uₖ = e^{iφₖ}` for `φ` with `φ(−k) ≡ −φₖ (mod 2π)`;
self-paired bins (`2k ≡ 0 mod N`) force `uₖ = ±1`. In the code,
`uₖ = 𝓕wₖ / ‖𝓕wₖ‖` for a real Gaussian draw `w` (and `1` at zeros);
`Complex.angle` never enters the formalization.

## Statement
For every `N ≥ 1`, every real `f`, every admissible `u`, with
`Xₖ := |f̂ₖ|·uₖ` and `g := IDFT(X)`:
1. `g` is real;
2. `DFT(g) = X` exactly; hence `|DFT(g)ₖ| = |f̂ₖ|` per mode, and
   `phase(DFT(g)ₖ) = uₖ` wherever `f̂ₖ ≠ 0`; at zero modes `DFT(g)ₖ = 0`;
3. for every bin `B`: `E_g(B) = E_f(B)` (bin sums of mode energies), and
   `Σ g² = Σ f²` (finite Parseval);
4. define `m·g := IDFT(k ↦ mₖ·Xₖ)` (and `m·f := IDFT(k ↦ mₖ·f̂ₖ)`); for every
   real, even (`m(−k) = mₖ`), nonnegative multiplier `m` — the `{0,1}` sharp
   shell filter is the motivating case, smooth `[0,1]` filters are covered by
   the same proof — `m·g` satisfies 1–3 with `f` replaced by `m·f`.

## Exactness scope
Claims are exact over `ℝ` (ideal arithmetic, Lean's target). In double
precision, shell-summed energies agree to machine precision × O(log N) ×
`E_total` (standard FFT rounding); per-mode phase identity is ideal-arithmetic
only. "Parseval-exact" in the paper denotes the ideal-arithmetic statement.

## Register
The formalized content is the spectral bookkeeping — DFT inversion plus the
Hermitian-reality bridge — i.e. certified exactness of spectrum matching for
the pre-projection surrogate. Load-bearing but shallow scaffolding. The E5
result (median |r| = 0.07, divergence unrepaired) is empirical and untouched by
this.

## Not claimed
Phases decorrelate (no phase-correlation claim); `div g ≠ 0` in general; the
sharpened PFD clause: the match is certified before projection; the Leray
projection (anisotropic symbol `I − kkᵀ/|k|²`) is exactly the operation that
breaks per-mode matching.

## Footnotes
Zero modes: amplitude `0` annihilates `uₖ` (no division anywhere in the
statement); `angle(0)` at a self-paired bin lands in `{0,π}` anyway; `N = 1`
gives `g = ±f`; multi-dimensional grids act componentwise, self-paired meaning
`2kᵢ ≡ 0` for all `i`.
-/

set_option autoImplicit false

namespace K1Lean

open ZMod

variable {N : ℕ} [NeZero N]

/-- Conjugation acts on the DFT by negation of the frequency. (Milestone 1
mechanism toward frozen claim 2: for real input this is Hermitian symmetry.) -/
theorem dft_star (Φ : ZMod N → ℂ) (k : ZMod N) :
    star (ZMod.dft Φ k) = ZMod.dft (fun j => star (Φ j)) (-k) := by
  have hchar (x : ZMod N) :
      starRingEnd ℂ (stdAddChar (N := N) x) = stdAddChar (-x) :=
    (AddChar.map_neg_eq_conj (stdAddChar (N := N)) x).symm
  simp only [ZMod.dft_apply, smul_eq_mul]
  rw [← starRingEnd_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hchar, starRingEnd_apply]
  have harg : -(j * -k) = -(-(j * k)) := by ring
  rw [harg]

/-- Milestone 1: the DFT of a real field is Hermitian, `(𝓕f k)† = 𝓕f (−k)`. -/
theorem dft_ofReal_conj (f : ZMod N → ℝ) (k : ZMod N) :
    star (ZMod.dft (fun j => (f j : ℂ)) k) = ZMod.dft (fun j => (f j : ℂ)) (-k) := by
  have hchar (x : ZMod N) :
      starRingEnd ℂ (stdAddChar (N := N) x) = stdAddChar (-x) :=
    (AddChar.map_neg_eq_conj (stdAddChar (N := N)) x).symm
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) :=
    RCLike.conj_ofReal r
  simp only [ZMod.dft_apply, smul_eq_mul]
  rw [← starRingEnd_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hchar, starRingEnd_apply, hreal]
  have harg : -(j * -k) = -(-(j * k)) := by ring
  rw [harg]

/-- Milestone 2: for Hermitian `X` (`star (X k) = X (-k)`, the shape of a real
field's spectrum), the inverse-DFT output is self-conjugate — the Lean form of
"`g` is real" in the frozen text. The `Equiv.neg` reindex is discharged inside
mathlib's `dft_comp_neg`; the `1/N` scalar is pinned by the named `hN`, not by
tactical search. -/
theorem invDFT_selfConj (X : ZMod N → ℂ) (hX : ∀ k, star (X k) = X (-k)) (k : ZMod N) :
    star (ZMod.dft.symm X k) = ZMod.dft.symm X k := by
  have hN : star ((N : ℂ)⁻¹) = (N : ℂ)⁻¹ := by
    rw [star_inv₀, star_natCast]
  have hfun : (fun j : ZMod N => star (X j)) = fun j => X (-j) :=
    funext fun j => hX j
  rw [ZMod.invDFT_apply', smul_eq_mul, star_mul', hN, dft_star, neg_neg, hfun]
  exact congrArg (fun t => (N : ℂ)⁻¹ * t) (congrFun (ZMod.dft_comp_neg X) k)

/-- Milestone 2 corollary: reality, imaginary-part form. -/
theorem invDFT_im_eq_zero (X : ZMod N → ℂ) (hX : ∀ k, star (X k) = X (-k)) (k : ZMod N) :
    (ZMod.dft.symm X k).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  simpa only [Complex.star_def] using invDFT_selfConj X hX k

/-- Milestone 2 corollary: reality, packaged (frozen claim 1) — the inverse-DFT
output equals its own real-part coercion. -/
theorem invDFT_eq_ofReal_re (X : ZMod N → ℂ) (hX : ∀ k, star (X k) = X (-k)) (k : ZMod N) :
    ZMod.dft.symm X k = ((ZMod.dft.symm X k).re : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]
  · rw [invDFT_im_eq_zero X hX k, Complex.ofReal_im]

/-- Frozen setting: the surrogate spectrum `Xₖ := |f̂ₖ|·uₖ` — mode modulus of
the real field's DFT carried by the phase field `u`. -/
def surrogateSpectrum (f : ZMod N → ℝ) (u : ZMod N → ℂ) : ZMod N → ℂ :=
  fun k => (‖ZMod.dft (fun j => (f j : ℂ)) k‖ : ℂ) * u k

/-- Milestone 3 bridge: with Hermitian `u`, the surrogate spectrum is Hermitian
(`star(|f̂ₖ|·uₖ) = |f̂ₖ|·u₋ₖ`; the amplitude switch `|f̂₋ₖ| = |f̂ₖ|` is
milestone 1's Hermitian symmetry of `f̂`). -/
theorem surrogateSpectrum_star (f : ZMod N → ℝ) (u : ZMod N → ℂ)
    (hu : ∀ k, star (u k) = u (-k)) (k : ZMod N) :
    star (surrogateSpectrum f u k) = surrogateSpectrum f u (-k) := by
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := RCLike.conj_ofReal r
  have hnorm : ‖ZMod.dft (fun j => (f j : ℂ)) k‖ =
      ‖ZMod.dft (fun j => (f j : ℂ)) (-k)‖ := by
    rw [← dft_ofReal_conj f k, Complex.star_def, Complex.norm_conj]
  dsimp only [surrogateSpectrum]
  rw [star_mul', hreal, hu k, hnorm]

/-- Frozen claim 2, exactness half: `DFT(g) = X` exactly for `g := IDFT(X)`. -/
theorem dft_invDFT (X : ZMod N → ℂ) : ZMod.dft (ZMod.dft.symm X) = X :=
  ZMod.dft.apply_symm_apply X

/-- The surrogate spectrum carries the right per-mode amplitudes: with
unit-modulus `u`, `‖Xₖ‖ = |f̂ₖ|`. -/
theorem norm_surrogateSpectrum (f : ZMod N → ℝ) (u : ZMod N → ℂ)
    (hu2 : ∀ k, ‖u k‖ = 1) (k : ZMod N) :
    ‖surrogateSpectrum f u k‖ = ‖ZMod.dft (fun j => (f j : ℂ)) k‖ := by
  have hnormR (r : ℝ) : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r
  dsimp only [surrogateSpectrum]
  rw [norm_mul, hu2 k, mul_one, hnormR, abs_of_nonneg (norm_nonneg _)]

/-- Frozen claim 2, magnitude half: per mode, `|DFT(g)ₖ| = |f̂ₖ|`. -/
theorem norm_dft_invDFT_surrogateSpectrum (f : ZMod N → ℝ) (u : ZMod N → ℂ)
    (hu2 : ∀ k, ‖u k‖ = 1) (k : ZMod N) :
    ‖ZMod.dft (ZMod.dft.symm (surrogateSpectrum f u)) k‖ =
      ‖ZMod.dft (fun j => (f j : ℂ)) k‖ := by
  rw [dft_invDFT]
  exact norm_surrogateSpectrum f u hu2 k

/-- Frozen claim 2, phase half, division-free form: `Xₖ = ‖Xₖ‖·uₖ` — phase
recovery by normalization; at zero modes this reads `0 = 0·uₖ`, and
`Complex.angle` never enters. -/
theorem phase_surrogateSpectrum (f : ZMod N → ℝ) (u : ZMod N → ℂ)
    (hu2 : ∀ k, ‖u k‖ = 1) (k : ZMod N) :
    surrogateSpectrum f u k = (‖surrogateSpectrum f u k‖ : ℂ) * u k := by
  rw [norm_surrogateSpectrum f u hu2 k]
  rfl

end K1Lean
