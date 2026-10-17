module

public import Mathlib.Analysis.Fourier.ZMod

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

@[expose] public section

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
noncomputable def surrogateSpectrum (f : ZMod N → ℝ) (u : ZMod N → ℂ) : ZMod N → ℂ :=
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

/-- Milestone 4, engine (audited public core): finite Parseval in bilinear form.
For complex `h`, the unnormalized DFT preserves the total `z·z†` energy up to
the exact factor `N`: `Σₖ 𝓕hₖ·(𝓕hₖ)† = N·Σₙ hₙ·hₙ†`. This is the load-bearing
computation behind frozen claim 3 (`Σ g² = Σ f²`) and milestone 5's bin sums. -/
theorem parseval_complex (h : ZMod N → ℂ) :
    ∑ k : ZMod N, ZMod.dft h k * star (ZMod.dft h k)
      = (N : ℂ) * ∑ n : ZMod N, h n * star (h n) := by
  have hchar (x : ZMod N) : starRingEnd ℂ (stdAddChar (N := N) x) = stdAddChar (-x) :=
    (AddChar.map_neg_eq_conj (stdAddChar (N := N)) x).symm
  have hstar (k : ZMod N) :
      star (ZMod.dft h k) = ∑ i : ZMod N, stdAddChar (i * k) * star (h i) := by
    simp only [ZMod.dft_apply, smul_eq_mul]
    rw [← starRingEnd_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hchar, starRingEnd_apply, neg_neg]
  have h1 (t : ZMod N) :
      ∑ i : ZMod N, stdAddChar (N := N) (t * i) = if t = 0 then (N : ℂ) else 0 := by
    split_ifs with ht
    · simp only [ht, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const,
        Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N ht)
  have harg (j i k : ZMod N) : -(j * k) + i * k = (i - j) * k := by
    rw [add_comm, sub_mul, sub_eq_add_neg]
  have hterm (j i k : ZMod N) :
      (stdAddChar (-(j * k)) * h j) * (stdAddChar (i * k) * star (h i))
        = stdAddChar ((i - j) * k) * (h j * star (h i)) := by
    rw [mul_mul_mul_comm, ← AddChar.map_add_eq_mul, harg]
  have hswap (F : ZMod N → ZMod N → ZMod N → ℂ) :
      (∑ k : ZMod N, ∑ j : ZMod N, ∑ i : ZMod N, F k j i)
        = ∑ j : ZMod N, ∑ i : ZMod N, ∑ k : ZMod N, F k j i := by
    trans ∑ j : ZMod N, ∑ k : ZMod N, ∑ i : ZMod N, F k j i
    · exact Finset.sum_comm
    · exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
  calc
    (∑ k : ZMod N, ZMod.dft h k * star (ZMod.dft h k))
        = ∑ k : ZMod N, ∑ j : ZMod N, ∑ i : ZMod N,
            (stdAddChar (-(j * k)) * h j) * (stdAddChar (i * k) * star (h i)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hstar k, ZMod.dft_apply, Fintype.sum_mul_sum]
          simp only [smul_eq_mul]
    _ = ∑ k : ZMod N, ∑ j : ZMod N, ∑ i : ZMod N,
            stdAddChar ((i - j) * k) * (h j * star (h i)) := by
          exact Finset.sum_congr rfl fun k _ =>
            Finset.sum_congr rfl fun j _ =>
              Finset.sum_congr rfl fun i _ => hterm j i k
    _ = ∑ j : ZMod N, ∑ i : ZMod N, ∑ k : ZMod N,
            stdAddChar ((i - j) * k) * (h j * star (h i)) :=
          hswap (fun k j i => stdAddChar ((i - j) * k) * (h j * star (h i)))
    _ = ∑ j : ZMod N, ∑ i : ZMod N,
            (∑ k : ZMod N, stdAddChar ((i - j) * k)) * (h j * star (h i)) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
    _ = ∑ j : ZMod N, ∑ i : ZMod N,
            (if i - j = 0 then (N : ℂ) else 0) * (h j * star (h i)) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          rw [h1]
    _ = ∑ j : ZMod N, (N : ℂ) * (h j * star (h j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have hstep (i : ZMod N) :
              (if i - j = 0 then (N : ℂ) else 0) * (h j * star (h i))
                = if i = j then (N : ℂ) * (h j * star (h i)) else 0 := by
            by_cases hij : i = j
            · subst hij
              simp
            · have hne : i - j ≠ 0 := fun h => hij (sub_eq_zero.mp h)
              rw [ite_eq_right hne, ite_eq_right hij]
              exact zero_mul _
          refine (Finset.sum_congr rfl fun i _ => hstep i).trans ?_
          exact Fintype.sum_ite_eq' j (fun i => (N : ℂ) * (h j * star (h i)))
    _ = (N : ℂ) * ∑ n : ZMod N, h n * star (h n) := by
          rw [Finset.mul_sum]

/-- Frozen claim 3, finite-Parseval half (frozen line 18): for real `f`,
`Σₙ fₙ² = N⁻¹·Σₖ ‖𝓕fₖ‖²` in the code (numpy) normalization. Derived from the
audited bilinear engine `parseval_complex` via the coercion bridges
`‖z‖² = z·z†` and `r² = r·r`. -/
theorem parseval (f : ZMod N → ℝ) :
    ∑ n : ZMod N, (f n) ^ 2
      = (N : ℝ)⁻¹ * ∑ k : ZMod N, ‖ZMod.dft (fun j => (f j : ℂ)) k‖ ^ 2 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have htermL (z : ℂ) : Complex.ofRealHom (‖z‖ ^ 2) = z * star z := by
    rw [Complex.ofRealHom_eq_coe, ← Complex.normSq_eq_norm_sq, Complex.star_def,
      ← Complex.mul_conj]
  have hnorm (r : ℝ) : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, ← pow_two]
  have htermR (r : ℝ) : Complex.ofRealHom (r ^ 2) = (r : ℂ) * star (r : ℂ) := by
    rw [← hnorm r]
    exact htermL (r : ℂ)
  have hcast :
      Complex.ofRealHom (∑ k : ZMod N, ‖ZMod.dft (fun j => (f j : ℂ)) k‖ ^ 2)
        = ∑ k : ZMod N,
            ZMod.dft (fun j => (f j : ℂ)) k * star (ZMod.dft (fun j => (f j : ℂ)) k) := by
    rw [map_sum Complex.ofRealHom]
    exact Finset.sum_congr rfl fun k _ =>
      htermL (ZMod.dft (fun j => (f j : ℂ)) k)
  have hsum :
      (∑ n : ZMod N, (f n : ℂ) * star (f n : ℂ))
        = Complex.ofRealHom (∑ n : ZMod N, (f n) ^ 2) := by
    rw [map_sum Complex.ofRealHom]
    exact Finset.sum_congr rfl fun n _ => (htermR (f n)).symm
  have hmain :
      Complex.ofRealHom (∑ k : ZMod N, ‖ZMod.dft (fun j => (f j : ℂ)) k‖ ^ 2)
        = (N : ℂ) * Complex.ofRealHom (∑ n : ZMod N, (f n) ^ 2) := by
    rw [hcast, parseval_complex (fun j : ZMod N => (f j : ℂ)), hsum]
  have hmul :
      (N : ℂ) * Complex.ofRealHom (∑ n : ZMod N, (f n) ^ 2)
        = Complex.ofRealHom ((N : ℝ) * ∑ n : ZMod N, (f n) ^ 2) := by
    rw [map_mul]
    rw [show Complex.ofRealHom (N : ℝ) = (N : ℂ) from map_natCast Complex.ofRealHom N]
  have hBA :
      (∑ k : ZMod N, ‖ZMod.dft (fun j : ZMod N => (f j : ℂ)) k‖ ^ 2)
        = (N : ℝ) * ∑ n : ZMod N, (f n) ^ 2 :=
    Complex.ofReal_injective (by
      simpa only [Complex.ofRealHom_eq_coe] using hmain.trans hmul)
  rw [hBA, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- Frozen claim 3, surrogate half: for admissible `u` (Hermitian and
unit-modulus), the surrogate-spectrum inverse DFT `g := IDFT(|f̂|·u)` carries the
same total energy as `f`, `Σₙ gₙ² = Σₙ fₙ²`. `g`'s reality is milestone 2
(`invDFT_eq_ofReal_re`), so its entries are rendered as `.re`. -/
theorem parseval_surrogateSpectrum (f : ZMod N → ℝ) (u : ZMod N → ℂ)
    (hu1 : ∀ k, star (u k) = u (-k)) (hu2 : ∀ k, ‖u k‖ = 1) :
    ∑ n : ZMod N, (ZMod.dft.symm (surrogateSpectrum f u) n).re ^ 2 =
      ∑ n : ZMod N, (f n) ^ 2 := by
  let gr : ZMod N → ℝ := fun n => (ZMod.dft.symm (surrogateSpectrum f u) n).re
  change ∑ n : ZMod N, gr n ^ 2 = ∑ n : ZMod N, (f n) ^ 2
  have hX : ∀ k, star (surrogateSpectrum f u k) = surrogateSpectrum f u (-k) :=
    surrogateSpectrum_star f u hu1
  have hgr : (fun j : ZMod N => (gr j : ℂ)) = ZMod.dft.symm (surrogateSpectrum f u) :=
    funext fun j => (invDFT_eq_ofReal_re (surrogateSpectrum f u) hX j).symm
  have hdft : ZMod.dft (fun j : ZMod N => (gr j : ℂ)) = surrogateSpectrum f u := by
    rw [hgr, dft_invDFT]
  have hsum :
      (∑ k : ZMod N, ‖ZMod.dft (fun j : ZMod N => (gr j : ℂ)) k‖ ^ 2)
        = ∑ k : ZMod N, ‖ZMod.dft (fun j => (f j : ℂ)) k‖ ^ 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hdft, norm_surrogateSpectrum f u hu2 k]
  rw [parseval gr, hsum, ← parseval f]

/-! ## Milestone 5: multiplier action (`m·f`, `m·g`)

Frozen claim 4, plus the per-bin energy statement for the surrogate spectrum
(claim 3, bin half). Entries are carried as real fields via `.re`; the
`_im_eq_zero`/`_dft` lemmas certify that the IDFT entries are real and that the
forward DFT recovers the filtered spectrum, so the `.re` rendering loses
nothing. -/

/-- Multiplier action on a spectrum: `(m · X)ₖ = mₖ · Xₖ`. -/
noncomputable def mulSpectrum (m : ZMod N → ℝ) (X : ZMod N → ℂ) : ZMod N → ℂ :=
  fun k => (m k : ℂ) * X k

/-- Frozen claim 4: `m·f := IDFT(k ↦ mₖ · f̂ₖ)`, carried as a real field via
`.re`; `mulField_dft` certifies the IDFT entries are real. -/
noncomputable def mulField (m : ZMod N → ℝ) (f : ZMod N → ℝ) : ZMod N → ℝ :=
  fun n => (ZMod.dft.symm (mulSpectrum m (fun k => ZMod.dft (fun j => (f j : ℂ)) k)) n).re

/-- Surrogate analogue of `mulField`: `m·g := IDFT(k ↦ mₖ · ĝₖ)`, where
`ĝ = surrogateSpectrum f u`, carried as a real field via `.re`. -/
noncomputable def mulSurrogate (m : ZMod N → ℝ) (f : ZMod N → ℝ) (u : ZMod N → ℂ) :
    ZMod N → ℝ :=
  fun n => (ZMod.dft.symm (mulSpectrum m (surrogateSpectrum f u)) n).re

/-- Hermitian symmetry of the multiplier-filtered field spectrum. -/
theorem mulSpectrum_dft_star (m : ZMod N → ℝ) (f : ZMod N → ℝ)
    (hm : ∀ k, m (-k) = m k) (k : ZMod N) :
    star (mulSpectrum m (fun k => ZMod.dft (fun j => (f j : ℂ)) k) k)
      = mulSpectrum m (fun k => ZMod.dft (fun j => (f j : ℂ)) k) (-k) := by
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := RCLike.conj_ofReal r
  dsimp only [mulSpectrum]
  rw [star_mul', hreal, ← hm k, dft_ofReal_conj]

/-- Hermitian symmetry of the multiplier-filtered surrogate spectrum. -/
theorem mulSpectrum_surrogate_star (m : ZMod N → ℝ) (f : ZMod N → ℝ)
    (u : ZMod N → ℂ) (hm : ∀ k, m (-k) = m k)
    (hu1 : ∀ k, star (u k) = u (-k)) (k : ZMod N) :
    star (mulSpectrum m (surrogateSpectrum f u) k)
      = mulSpectrum m (surrogateSpectrum f u) (-k) := by
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := RCLike.conj_ofReal r
  dsimp only [mulSpectrum]
  rw [star_mul', hreal, ← hm k, surrogateSpectrum_star f u hu1]

/-- Reality certificate: the IDFT underlying `mulField` has zero imaginary
part at every entry. -/
theorem mulField_im_eq_zero (m : ZMod N → ℝ) (f : ZMod N → ℝ)
    (hm : ∀ k, m (-k) = m k) (n : ZMod N) :
    (ZMod.dft.symm
        (mulSpectrum m (fun k => ZMod.dft (fun j => (f j : ℂ)) k)) n).im = 0 :=
  invDFT_im_eq_zero _ (mulSpectrum_dft_star m f hm) n

/-- Reality certificate: the IDFT underlying `mulSurrogate` has zero imaginary
part at every entry. -/
theorem mulSurrogate_im_eq_zero (m : ZMod N → ℝ) (f : ZMod N → ℝ) (u : ZMod N → ℂ)
    (hm : ∀ k, m (-k) = m k) (hu1 : ∀ k, star (u k) = u (-k)) (n : ZMod N) :
    (ZMod.dft.symm (mulSpectrum m (surrogateSpectrum f u)) n).im = 0 :=
  invDFT_im_eq_zero _ (mulSpectrum_surrogate_star m f u hm hu1) n

/-- Frozen claim 4, field half: the forward DFT of `.re`-rendered `m·f` is
exactly the filtered spectrum. -/
theorem mulField_dft (m : ZMod N → ℝ) (f : ZMod N → ℝ)
    (hm : ∀ k, m (-k) = m k) :
    ZMod.dft (fun n => (mulField m f n : ℂ))
      = mulSpectrum m (fun k => ZMod.dft (fun j => (f j : ℂ)) k) := by
  have hX := mulSpectrum_dft_star m f hm
  have hfun : (fun n : ZMod N => (mulField m f n : ℂ))
      = ZMod.dft.symm (mulSpectrum m (fun k => ZMod.dft (fun j => (f j : ℂ)) k)) := by
    funext n
    dsimp only [mulField]
    exact (invDFT_eq_ofReal_re _ hX n).symm
  rw [hfun]
  exact ZMod.dft.apply_symm_apply _

/-- Frozen claim 4, surrogate half: the forward DFT of `.re`-rendered `m·g` is
exactly the filtered surrogate spectrum. -/
theorem mulSurrogate_dft (m : ZMod N → ℝ) (f : ZMod N → ℝ) (u : ZMod N → ℂ)
    (hm : ∀ k, m (-k) = m k) (hu1 : ∀ k, star (u k) = u (-k)) :
    ZMod.dft (fun n => (mulSurrogate m f u n : ℂ))
      = mulSpectrum m (surrogateSpectrum f u) := by
  have hX := mulSpectrum_surrogate_star m f u hm hu1
  have hfun : (fun n : ZMod N => (mulSurrogate m f u n : ℂ))
      = ZMod.dft.symm (mulSpectrum m (surrogateSpectrum f u)) := by
    funext n
    dsimp only [mulSurrogate]
    exact (invDFT_eq_ofReal_re _ hX n).symm
  rw [hfun]
  exact ZMod.dft.apply_symm_apply _

/-- Frozen claim 4, magnitude half: `m·g` and `m·f` have the same per-mode
magnitudes. `hm`/`hu1` are needed because the statement is phrased on the DFT
of the `.re` field, not on the bare filtered spectrum. -/
theorem norm_mulSurrogate (m : ZMod N → ℝ) (f : ZMod N → ℝ) (u : ZMod N → ℂ)
    (hm : ∀ k, m (-k) = m k) (hm0 : ∀ k, 0 ≤ m k)
    (hu1 : ∀ k, star (u k) = u (-k)) (hu2 : ∀ k, ‖u k‖ = 1) (k : ZMod N) :
    ‖ZMod.dft (fun n => (mulSurrogate m f u n : ℂ)) k‖
      = ‖ZMod.dft (fun n => (mulField m f n : ℂ)) k‖ := by
  rw [mulSurrogate_dft m f u hm hu1, mulField_dft m f hm]
  dsimp only [mulSpectrum]
  have hnormm : ‖((m k : ℝ) : ℂ)‖ = |m k| := RCLike.norm_ofReal (m k)
  rw [norm_mul, norm_mul, hnormm, abs_of_nonneg (hm0 k), norm_surrogateSpectrum f u hu2 k]

/-- Frozen claim 4, phase half: `m·g` has the same phase as `g`. -/
theorem phase_mulSurrogate (m : ZMod N → ℝ) (f : ZMod N → ℝ) (u : ZMod N → ℂ)
    (hm : ∀ k, m (-k) = m k) (hm0 : ∀ k, 0 ≤ m k)
    (hu1 : ∀ k, star (u k) = u (-k)) (hu2 : ∀ k, ‖u k‖ = 1) (k : ZMod N) :
    ZMod.dft (fun n => (mulSurrogate m f u n : ℂ)) k
      = (‖ZMod.dft (fun n => (mulSurrogate m f u n : ℂ)) k‖ : ℂ) * u k := by
  have hnorm : ‖ZMod.dft (fun n => (mulSurrogate m f u n : ℂ)) k‖
      = m k * ‖surrogateSpectrum f u k‖ := by
    rw [mulSurrogate_dft m f u hm hu1]
    dsimp only [mulSpectrum]
    have hnormm : ‖((m k : ℝ) : ℂ)‖ = |m k| := RCLike.norm_ofReal (m k)
    rw [norm_mul, hnormm, abs_of_nonneg (hm0 k)]
  rw [hnorm, mulSurrogate_dft m f u hm hu1]
  dsimp only [mulSpectrum]
  conv_lhs => rw [phase_surrogateSpectrum f u hu2 k]
  rw [← mul_assoc, ← Complex.ofReal_mul]

/-- Frozen claim 3, bin half: every bin of the surrogate spectrum carries the
same energy as the corresponding bin of `f̂`, `E_g(B) = E_f(B)`.

Bookkeeping convention: `E(B) := (N:ℝ)⁻¹ · ∑ k ∈ B, ‖·‖²`; the common factor
is dropped from both sides. The left side renders `dft (dft.symm X)` (the
forward transform of the surrogate field); `dft_invDFT` reduces it to `X`. -/
theorem bin_energy_surrogateSpectrum (f : ZMod N → ℝ) (u : ZMod N → ℂ)
    (hu2 : ∀ k, ‖u k‖ = 1) (B : Finset (ZMod N)) :
    (∑ k ∈ B, ‖ZMod.dft (ZMod.dft.symm (surrogateSpectrum f u)) k‖ ^ 2)
      = ∑ k ∈ B, ‖ZMod.dft (fun j => (f j : ℂ)) k‖ ^ 2 := by
  rw [dft_invDFT]
  exact Finset.sum_congr rfl fun k _ => by rw [norm_surrogateSpectrum f u hu2 k]

/-- Frozen claim 4, bin half: `m·g` and `m·f` have equal energy in every bin.
The common `1/N` bookkeeping factor is dropped. -/
theorem bin_energy_mulSurrogate (m : ZMod N → ℝ) (f : ZMod N → ℝ) (u : ZMod N → ℂ)
    (hm : ∀ k, m (-k) = m k) (hm0 : ∀ k, 0 ≤ m k)
    (hu1 : ∀ k, star (u k) = u (-k)) (hu2 : ∀ k, ‖u k‖ = 1)
    (B : Finset (ZMod N)) :
    (∑ k ∈ B, ‖ZMod.dft (fun n => (mulSurrogate m f u n : ℂ)) k‖ ^ 2)
      = ∑ k ∈ B, ‖ZMod.dft (fun n => (mulField m f n : ℂ)) k‖ ^ 2 :=
  Finset.sum_congr rfl fun k _ => by
    rw [norm_mulSurrogate m f u hm hm0 hu1 hu2 k]

/-- Frozen claim 4: multiplier action preserves the total energy,
`Σₙ (m·g)ₙ² = Σₙ (m·f)ₙ²`. -/
theorem parseval_mulSurrogate (m : ZMod N → ℝ) (f : ZMod N → ℝ) (u : ZMod N → ℂ)
    (hm : ∀ k, m (-k) = m k) (hm0 : ∀ k, 0 ≤ m k)
    (hu1 : ∀ k, star (u k) = u (-k)) (hu2 : ∀ k, ‖u k‖ = 1) :
    (∑ n : ZMod N, (mulSurrogate m f u n) ^ 2)
      = ∑ n : ZMod N, (mulField m f n) ^ 2 := by
  have hsums :
      (∑ k : ZMod N, ‖ZMod.dft (fun j => (mulSurrogate m f u j : ℂ)) k‖ ^ 2)
        = ∑ k : ZMod N, ‖ZMod.dft (fun j => (mulField m f j : ℂ)) k‖ ^ 2 :=
    Finset.sum_congr rfl fun k _ => by
      rw [norm_mulSurrogate m f u hm hm0 hu1 hu2 k]
  rw [parseval (mulSurrogate m f u), parseval (mulField m f), hsums]

end K1Lean
