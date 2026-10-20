# Statement match: frozen statements ↔ `K1Lean`

This file contains the close-out audits for the frozen finite-Parseval /
surrogate-spectrum statement (v2, 2026-10-17), the frozen antipodal
statement (v1, 2026-10-19), and the frozen discrete Leray symbol statement
(v1, 2026-10-20). Each frozen text is the module docstring at the top
of its Lean file; every line is mapped below to its Lean counterpart, or
explicitly marked as commentary / modeling text that makes no theorem-level
claim. The declaration inventories are exhaustive for the respective files.

Verification runs: GitHub Actions (build → exe → audit → semantics → cheat
scan) and an independent Kaggle build from a dataset snapshot. Signatures and
axioms are printed by `Tests/Audit.lean`; every audited declaration depends
only on `[propext, Classical.choice, Quot.sound]`.

## Setting

| frozen line | Lean counterpart |
|---|---|
| `N ≥ 1`, indices modulo `N` | `{N : ℕ}` with `[NeZero N]`; index type `ZMod N` |
| `f : Z/N → ℝ` | `f : ZMod N → ℝ` |
| numpy convention: `f̂ₖ = Σₙ fₙ e^(−2πikn/N)`, `IDFT(X)ₙ = N⁻¹ Σₖ Xₖ e^(+2πikn/N)` | `ZMod.dft` and `ZMod.dft.symm` (mathlib v4.35.0, pinned by `lake-manifest.json`); sign convention fixed by `dft_star`/`dft_ofReal_conj`, `1/N` normalization fixed by `parseval` (`N⁻¹` appears exactly once) |
| both compositions are identities | `dft_invDFT` covers DFT∘IDFT; IDFT∘DFT = id is `LinearEquiv.symm_apply_apply` (structural from `dft` being a linear equivalence) |
| finite Parseval: `Σₙ fₙ² = N⁻¹ Σₖ |f̂ₖ|²` | `parseval` (engine: `parseval_complex`) |

## Admissible phase factors

| frozen line | Lean counterpart |
|---|---|
| `u : Z/N → ℂ`, `star(uₖ) = u(−k)` | hypothesis `hu1 : ∀ k, star (u k) = u (-k)` (used in `surrogateSpectrum_star`, all `invDFT_*` lemmas, `parseval_surrogateSpectrum`, and the M5 `mulSurrogate` lemmas) |
| `|uₖ| = 1` | hypothesis `hu2 : ∀ k, ‖u k‖ = 1` (used in `norm_surrogateSpectrum`, `phase_surrogateSpectrum`, `bin_energy_*`, `parseval_*`) |
| equivalently `uₖ = e^{iφₖ}`; self-paired bins force `uₖ = ±1` | descriptive equivalence; no separate Lean theorem is needed by the chain. The formalization takes `(hu1, hu2)` abstractly (this is the stronger, implementation-independent form) |
| in the code `uₖ = 𝓕wₖ / ‖𝓕wₖ‖` for real Gaussian `w` (and `1` at zeros) | modeling/usage line about the numerical pipeline; not a Lean claim (a probabilistic statement about a random draw is outside the frozen exact-arithmetic scope) |
| `Complex.angle` never enters the formalization | confirmed by grep: `angle` occurs only in docstrings/comments, never in a proof term |

## Statement

For every `N ≥ 1`, every real `f`, every admissible `u`, with `Xₖ := |f̂ₖ|·uₖ`
and `g := IDFT(X)`:

| frozen claim | Lean counterpart |
|---|---|
| 1. `g` is real | `invDFT_selfConj` (self-conjugate), `invDFT_im_eq_zero` (imaginary part zero), `invDFT_eq_ofReal_re` (`IDFT X = ↑(IDFT X).re`); the public energy theorem renders `g` as `(ZMod.dft.symm X n).re` |
| 2. `DFT(g) = X` exactly | `dft_invDFT` applied to `X := surrogateSpectrum f u`, plus `invDFT_eq_ofReal_re` to identify the `.re` rendering with the complex IDFT (`parseval_surrogateSpectrum` carries this as its internal `hgr`/`hdft`) |
| 2. `|DFT(g)ₖ| = |f̂ₖ|` per mode | `norm_dft_invDFT_surrogateSpectrum` (directly `dft (dft.symm X)` form), `norm_surrogateSpectrum` (per-term `|Xₖ| = |f̂ₖ|`) |
| 2. `phase(DFT(g)ₖ) = uₖ` wherever `f̂ₖ ≠ 0`; zero modes `DFT(g)ₖ = 0` | `phase_surrogateSpectrum`, division-free: `Xₖ = ‖Xₖ‖·uₖ` everywhere. At `Xₖ = 0` this reads `0 = 0·uₖ`; no division and no nonzero-mode side condition |
| 3. for every bin `B`: `E_g(B) = E_f(B)` | `bin_energy_surrogateSpectrum` for every `B : Finset (ZMod N)`; LHS renders `‖dft (dft.symm X) k‖²`, reduced by `dft_invDFT` |
| 3. `Σ g² = Σ f²` (finite Parseval) | `parseval_surrogateSpectrum` |
| 4. `m·g := IDFT(k ↦ mₖ·Xₖ)`, `m·f := IDFT(k ↦ mₖ·f̂ₖ)` | `mulSurrogate`, `mulField` (real fields via `.re`), with exactness `mulSurrogate_dft`, `mulField_dft`; reality certified by `mulSurrogate_im_eq_zero`, `mulField_im_eq_zero` |
| 4. for every real, even, nonnegative `m` | `m : ZMod N → ℝ`, `hm : ∀ k, m (-k) = m k`, `hm0 : ∀ k, 0 ≤ m k` |
| 4. `{0,1}` sharp shell filter is the motivating case; smooth `[0,1]` filters covered by the same proof | no separate hypothesis or lemma: the theorem quantifies over all real/even/nonnegative `m`, exactly as the frozen sentence says. `{0,1}` shell filters are an instance |
| 4. `m·g` satisfies 1–3 with `f` replaced by `m·f` | (1) reality: `mulSurrogate_dft` + `mulSurrogate_im_eq_zero` (the `.re` field's forward DFT is the filtered spectrum, so nothing is lost); (2) exact spectrum: `mulSurrogate_dft`; magnitudes: `norm_mulSurrogate`; division-free phase: `phase_mulSurrogate`; (3) bins: `bin_energy_mulSurrogate`; total: `parseval_mulSurrogate` |

Note on the claimed phase in item 4: `DFT(m·g)ₖ = mₖ·|f̂ₖ|·uₖ`, and
`|DFT(m·f)ₖ| = mₖ·|f̂ₖ|` because `mₖ ≥ 0`; hence `DFT(m·g)ₖ = |DFT(m·f)ₖ|·uₖ`,
which is the claim-2 form with `f` replaced by `m·f`. This is what
`norm_mulSurrogate` + `phase_mulSurrogate` certify.

Implementation detail (flagged at the M5 gate): `norm_mulSurrogate` and
`phase_mulSurrogate` are phrased on the DFT of the `.re` field, so they carry
`hm` (and `hu1`) in addition to the signed-off `hm0`/`hu2`; the same
hypotheses are already load-bearing in `mulSurrogate_dft`. Nothing else in the
signed-off statement list changed.

## Exactness scope

| frozen line | status |
|---|---|
| claims are exact over `ℝ` | all Lean types are exact (`ℝ`, `ℂ`); no floating point appears in any statement or proof |
| double-precision shell-sum remarks (`machine precision × O(log N) × E_total`) | numerical-analysis commentary; deliberately not formalized |
| per-mode phase identity is ideal-arithmetic only | the formal statement is the ideal one; no floating-point claim is made |
| "Parseval-exact" denotes the ideal-arithmetic statement | `parseval`, `parseval_surrogateSpectrum`, `parseval_mulSurrogate` |

## Register

| frozen line | status |
|---|---|
| formalized content is spectral bookkeeping (DFT inversion + Hermitian-reality bridge) | the declaration inventory below is exactly this chain; no analytic/PDE content |
| certified exactness of spectrum matching for the pre-projection surrogate | `parseval_surrogateSpectrum`, `bin_energy_surrogateSpectrum`, and the M5 multiplier lemmas; no projector is used in `Parseval.lean` |
| E5 result (median `|r| = 0.07`, divergence unrepaired) is empirical and untouched | no E5 declaration, hypothesis, or claim exists in the Lean sources |

## Not claimed (confirmed absent from the file)

| frozen "Not claimed" line | confirmation |
|---|---|
| phases decorrelate | no declaration or hypothesis about phase correlation exists |
| `div g ≠ 0` in general | no divergence declaration exists; the Lean chain is purely spectral |
| sharpened PFD clause (match certified before projection); Leray projection breaks per-mode matching | absent from `Parseval.lean`. `Surrogate.lean` contains only the degenerate placeholder `isProjector P := P * P = P` and `projector_idempotent` (a restatement of the hypothesis); it does not model the Leray symbol and is not connected to the frozen claims (honesty caveat recorded) |

## Footnotes

| frozen line | Lean counterpart / status |
|---|---|
| zero modes: amplitude `0` annihilates `uₖ`; no division anywhere | `phase_surrogateSpectrum` is division-free; `surrogateSpectrum` multiplies by `u k`, it never divides |
| `angle(0)` at a self-paired bin lands in `{0,π}` | `Complex.angle` is not used at all |
| `N = 1` gives `g = ±f` | follows from `hu1`+`hu2`; the intermediate fact `star z = z ∧ ‖z‖ = 1 → z = ±1` is not separately stated. The general theorems apply (`NeZero 1` holds); no special case is claimed separately |
| multi-dimensional grids act componentwise, self-paired meaning `2kᵢ ≡ 0` for all `i` | the formalization is the 1D `ZMod N` statement; the multidimensional statement is the per-axis application of it and is not separately formalized |

## Whole-file declaration inventory (`Src/K1Lean/Parseval.lean`)

All declarations are in namespace `K1Lean`; every one is either a frozen claim's
counterpart, a mechanism directly used by one, or a definitional rendering
device.

| declaration | role |
|---|---|
| `dft_star` | M1 mechanism: conjugation ↔ frequency negation |
| `dft_ofReal_conj` | M1: real-field spectrum is Hermitian |
| `invDFT_selfConj` | claim 1 (g self-conjugate) |
| `invDFT_im_eq_zero` | claim 1 (imaginary part zero) |
| `invDFT_eq_ofReal_re` | claim 1 (`.re` rendering identity) |
| `surrogateSpectrum` | definition of `Xₖ = |f̂ₖ|·uₖ` |
| `surrogateSpectrum_star` | `X` is Hermitian (bridge for claim 1) |
| `dft_invDFT` | setting: composition identity |
| `norm_surrogateSpectrum` | claim 2: `|Xₖ| = |f̂ₖ|` |
| `norm_dft_invDFT_surrogateSpectrum` | claim 2: `|DFT(g)ₖ| = |f̂ₖ|` |
| `phase_surrogateSpectrum` | claim 2: division-free phase identity |
| `parseval_complex` | M4 engine (complex bilinear Parseval) |
| `parseval` | setting/claim 3 engine: finite Parseval for real fields |
| `parseval_surrogateSpectrum` | claim 3: `Σ g² = Σ f²` |
| `mulSpectrum` | claim 4: `m·X` |
| `mulField` | claim 4: `m·f` as a real field |
| `mulSurrogate` | claim 4: `m·g` as a real field |
| `mulSpectrum_dft_star` | claim 4 bridge: filtered field spectrum Hermitian |
| `mulSpectrum_surrogate_star` | claim 4 bridge: filtered surrogate spectrum Hermitian |
| `mulField_im_eq_zero` | claim 4 (1): reality of `m·f`'s IDFT |
| `mulSurrogate_im_eq_zero` | claim 4 (1): reality of `m·g`'s IDFT |
| `mulField_dft` | claim 4 (2): `DFT(m·f) = m·f̂` |
| `mulSurrogate_dft` | claim 4 (2): `DFT(m·g) = m·X` |
| `norm_mulSurrogate` | claim 4 (2): per-mode magnitudes |
| `phase_mulSurrogate` | claim 4 (2): division-free phase |
| `bin_energy_surrogateSpectrum` | claim 3: bin energies |
| `bin_energy_mulSurrogate` | claim 4 (3): bin energies for `m·g` vs `m·f` |
| `parseval_mulSurrogate` | claim 4 (3): total energy for `m·g` vs `m·f` |

`Src/K1Lean/Surrogate.lean` (`Surrogate.isProjector`, `Surrogate.projector_idempotent`)
is the separate placeholder skeleton; it has no Lean connection to
`Parseval.lean` and does not enter the frozen claims (see "Not claimed").

## Bookkeeping conventions recorded at the five gates

1. Bin energies use the unnormalized mode sums `∑ k ∈ B, ‖·‖²`; the frozen
   `E(B) := (N:ℝ)⁻¹ · ∑ k ∈ B, ‖·‖²` common factor is dropped from both sides
   (documented in the bin docstrings).
2. `bin_energy_surrogateSpectrum`'s LHS renders `dft (dft.symm X)`; `dft_invDFT`
   reduces it to `X` (documented in the docstring and here).
3. The frozen numpy convention is the pinned mathlib `ZMod.dft` convention; the
   `1/N` normalization is pinned by the named `hN`/`inv_mul_cancel₀` chain in
   `parseval`, not by tactic search.
4. The formalization is 1D, componentwise-extendable in the paper's sense; this
   is stated, not hidden.
5. M5 hypothesis correction (above) is the only deviation from the signed-off
   signatures, and it only *adds* hypotheses required to state the DFT-level
   claims on the `.re` field.

---

# Frozen antipodal statement (v1, 2026-10-19) ↔ `K1Lean.Antipodal`

This is the statement-match audit for the antipodal lemma. The frozen text is
the module docstring at the top of `Src/K1Lean/Antipodal.lean` (v1,
2026-10-19). The declaration inventory at the end is exhaustive for that file.

Attacked in-thread before freeze: (i) "maximally wrong in any norm" was
narrowed to L2-only maximality; (ii) the inverted "division-free" wording was
corrected; (iii) the typical/random-draw fence was added to "Not claimed".

## Setting

| frozen line | Lean counterpart |
|---|---|
| `N ≥ 1`, indices modulo `N`; `f : Z/N → ℝ` | `{N : ℕ}` with `[NeZero N]`; `f : ZMod N → ℝ` |
| numpy forward/inverse convention | the same pinned `ZMod.dft` / `ZMod.dft.symm` as the Parseval statement (audited above) |
| `u` admissible: `star(uₖ) = u(−k)`, `|uₖ| = 1` | hypothesis pair `hu1`/`hu2`, as in the Parseval audit; here the pair is *proved* for `u^⊥` in `antipodalPhase_admissible` |

## Statement

| frozen claim | Lean counterpart |
|---|---|
| `u^⊥ₖ = −f̂ₖ/|f̂ₖ|` for `f̂ₖ ≠ 0`, `1` for `f̂ₖ = 0` | definition `antipodalPhase` (zero branch explicit; no division by zero) |
| 1. `u^⊥` admissible | `antipodalPhase_admissible`, components `antipodalPhase_star` and `antipodalPhase_norm` |
| zero-set symmetry `f̂ₖ = 0 ↔ f̂₋ₖ = 0` | internal step in `antipodalPhase_star`, derived from `dft_ofReal_conj` (M1); no DFT sum is unfolded |
| self-paired bins are real; the zero branch is real and unit | descriptive; follows from `dft_ofReal_conj` and the branch value `1` |
| `N = 1` | no special case; `[NeZero 1]` and the same case split |
| 2. `|f̂ₖ|·u^⊥ₖ = −f̂ₖ`, zero modes `0 = −0` | `surrogateSpectrum_antipodalPhase` |
| 3. `g = −f` as complex functions | `antipodal` (`ZMod.dft.symm (surrogateSpectrum f u^⊥) = fun n => −(f n : ℂ)`) |
| 3. pointwise on the real field, `g.re n = −f n` | `congrFun (antipodal f) n` + `Complex.neg_re` / `Complex.ofReal_re`, used in `antipodal_energy` |
| 4. `Σ (g.re − f)² = 4 Σ f²` | `antipodal_energy` |
| 4. universal L2 bound `‖g'.re − f‖₂ ≤ 2‖f‖₂` for every admissible `u'` | mapped prose (below), deliberately not a declaration |

## Mapped prose

The universal L2 sentence is **considered and deliberately scoped out**, not
missed. The ingredients are already certified:

| prose claim | Lean counterpart |
|---|---|
| every admissible `u'` yields `Σ (g'.re)² = Σ f²` | `parseval_surrogateSpectrum f u' hu1 hu2` (frozen claim 3 of the Parseval statement) |
| hence `‖g'.re − f‖₂ ≤ ‖g'.re‖₂ + ‖f‖₂ = 2‖f‖₂` | triangle inequality on the finite L2 norm; the equality case is the antipodal `u^⊥` (`antipodal_energy`) |

A verifier who wants the universal bound machine-checked gets a fifth lemma
(Cauchy–Schwarz on the finite sum), not a rewrite of the frozen statement.

## Register

| frozen line | status |
|---|---|
| the family contains the pointwise-negated field | `antipodal` + `antipodalPhase_admissible` |
| L2 distance maximal; pointwise error `2|f|` | `antipodal_energy`; the pointwise error is the `.re` corollary |
| the certified lemma concerns extent, not center | no declaration about typical draws; `|r| = 0.07` remains empirical |

## Not claimed (confirmed absent from `Antipodal.lean`)

| frozen "Not claimed" line | confirmation |
|---|---|
| typical or random draws are near-antipodal | no declaration or hypothesis about draws, randomness, or the ensemble median |
| maximality in any norm other than L2 | no sup-norm or other-norm statement exists |
| a particular finite pointwise-error bound | no such declaration exists |

## Declaration inventory (`Src/K1Lean/Antipodal.lean`)

All declarations are in namespace `K1Lean`.

| declaration | role |
|---|---|
| `antipodalPhase` | definition of `u^⊥`; docstring carries the paper-level sentence |
| `antipodalPhase_star` | claim 1 (Hermitian), internal helper |
| `antipodalPhase_norm` | claim 1 (unit modulus), internal helper |
| `antipodalPhase_admissible` | claim 1 (packaged) |
| `surrogateSpectrum_antipodalPhase` | claim 2 (per-mode negation) |
| `antipodal` | claim 3 (`g = −f`) |
| `antipodal_energy` | claim 4 (L2 equality) |

`Tests/Audit.lean` prints signatures and `#print axioms` for the four public
declarations; every audited declaration depends only on
`[propext, Classical.choice, Quot.sound]`.

---

# Frozen discrete Leray symbol statement (v1, 2026-10-20) ↔ `K1Lean.Leray`

This is the statement-match audit for the discrete Leray symbol (layer 2a).
The frozen text is the module docstring at the top of `Src/K1Lean/Leray.lean`
(v1, 2026-10-20). The declaration inventory at the end is exhaustive for that
file.

Attacked in-thread before freeze (two rounds). First round: the dimensional
flaw (a 1D torus cannot support `κκᵀ`; the paper's two-torus instantiation
takes `d = 2`, while 2a is abstract in `d`) and the split into 2a/2b. Second
round, attacking the feasibility note: the even-N Nyquist pathology
(`natAbs_valMinAbs_neg` does not give `S(−k) = S(k)` at even `N`; counterexample
`κ₁ = (N/2, 1)` vs `κ₂ = (N/2, −1)`). Frozen with three amendments: (i)
file/proof order 1, 3, 2; (ii) the definition carries `hq : κ ⬝ᵥ κ ≠ 0`;
(iii) `[NeZero d]`.

## Setting

| frozen line | Lean counterpart |
|---|---|
| `d ≥ 1` | `{d : ℕ}` with `[NeZero d]`; index type `Fin d` |
| `κ : Fin d → ℝ` | `κ : Fin d → ℝ` |
| `q(κ) := Σᵢ κᵢ² = κ ⬝ᵥ κ` | `Matrix.dotProduct κ κ` (notation `⬝ᵥ`) |
| `hq` (nonzero) | explicit definition argument `hq : κ ⬝ᵥ κ ≠ 0` |
| `S(κ) := I − κκᵀ/q(κ)` | `leraySymbol κ hq := 1 - Matrix.of (fun i j => κ i * κ j / (κ ⬝ᵥ κ))` |

## Statement

| frozen claim | Lean counterpart |
|---|---|
| 1. column: `S(κ) *ᵥ κ = 0` | `leraySymbol_mulVec_self` |
| 2. row: `κ ᵥ* S(κ) = 0` | `leraySymbol_vecMul_self`, proved from claims 1 and 3 via `Matrix.mulVec_transpose` |
| 3. symmetric: `S(κ)ᵀ = S(κ)` | `leraySymbol_transpose` |
| 4. idempotent: `S(κ) * S(κ) = S(κ)` | `leraySymbol_idem` (rank-one collapse `(κκᵀ)² = q·κκᵀ`) |
| 5. even: `S(−κ) = S(κ)` | `leraySymbol_neg` |
| file/proof order 1, 3, 2, 4, 5 | declarations appear in that order; claim 2 has no forward reference |

## Mapped prose: claim 8 (self-adjointness) — considered and cut

Self-adjointness of the Leray projector `P` is **deliberately not claimed** at
this layer. It is recorded here as mapped-prose/optional, not as a missed line:
the 2a symbol `S(κ)` is symmetric as a real matrix (`leraySymbol_transpose`),
but the operator-level self-adjointness statement needs the 2b Hilbert-space
setting (reality plus the `L²` inner-product bookkeeping). It is revisited only
if the P1 FDT argument needs it, and 2b defers it as well.

## Register

| frozen line | status |
|---|---|
| "the entire algebraic content of the Leray symbol" | the declaration inventory is exactly the symbol chain: definition, column/row kill, symmetry, idempotence, evenness |
| finite-dimensional, exact over `ℝ` | all Lean types are exact (`Matrix (Fin d) (Fin d) ℝ`); no lattice, Fourier transform, or floating point appears |
| the operator layer is 2b | no operator declaration exists in `Leray.lean`; 2a is the abstract symbol algebra |

## Not claimed (confirmed absent from `Leray.lean`)

| frozen "Not claimed" line | confirmation |
|---|---|
| anything with a lattice, Fourier transform or modulus | no `ZMod`, `dft`, `valMinAbs`, or norm declaration exists in the file |
| self-adjointness of `P` (claim 8) | cut here; see mapped-prose section above; no self-adjointness declaration exists |
| unitarity | no orthogonality/unitarity statement exists |
| eigenvalues | no spectral/eigenvalue statement exists |
| smoothness | no differentiability or regularity statement exists |

## Scope fence carried for 2b (Nyquist)

| frozen line | status |
|---|---|
| "2b freezes with N odd; the even-N Nyquist modes are a documented limitation, not in scope." | recorded verbatim in the module docstring; 2a itself is parity-free (`d` arbitrary) |
| Nyquist pathology | `natAbs_valMinAbs_neg` does not give `S(−k) = S(k)` at even `N` (counterexample in the docstring); with `N` odd, `valMinAbs_neg_of_ne_half` is total and `leraySymbol_neg` supplies the evenness step |
| code behaviour cited, not assumed | `compressible/ns.py` `Spectral2D`: `np.fft.fftfreq` wavenumbers (even-N Nyquist at `−n/2`), 2/3-rule mask `kmax = n // 3`, `k2_inv` pinning only `k = 0`; raw projection uses `kx, ky` with no Nyquist zeroing |

## Forward scope (zero mode)

| frozen line | status |
|---|---|
| `S(0) = I` is the projector convention (constants are exactly divergence-free) | stated as forward scope; 2a's `hq` excludes the zero wavevector, so no declaration is made at `κ = 0` |
| the code's `k² = 0` gauge pin is a different operation | documented (null-gauge of the Poisson solve, `k2_inv`/`p_h[0,0] = 0`); not conflated with `S(0) = I` |

## Declaration inventory (`Src/K1Lean/Leray.lean`)

All declarations are in namespace `K1Lean`.

| declaration | role |
|---|---|
| `leraySymbol` | definition of `S(κ)`, with `hq` |
| `leraySymbol_mulVec_self` | claim 1 (column kill) |
| `leraySymbol_transpose` | claim 3 (symmetry) |
| `leraySymbol_vecMul_self` | claim 2 (row kill), from claims 1 and 3 |
| `leraySymbol_idem` | claim 4 (idempotence) |
| `leraySymbol_neg` | claim 5 (evenness) |

`Tests/Audit.lean` prints signatures and `#print axioms` for the five public
declarations; every audited declaration depends only on
`[propext, Classical.choice, Quot.sound]`.

## Deferred to 2b

The operator layer is frozen separately after this file merges, with `[Odd N]`
from line one: the two-torus `(ZMod N)²`, `valMinAbs` wavenumbers, reality of
`P`, `P ∘ P = P`, the spectral divergence ledger
(`div v` symbol `i Σⱼ κⱼ(k) v̂ⱼ(k)`), the placeholder wake
(`Surrogate.isProjector` via `LinearMap.toMatrix`), and the witness theorem
`∃ f, admissible u, k* ≠ 0 : ‖(P g)̂(k*)‖ ≠ ‖f̂(k*)‖`. None of these is claimed
here.

## 2b Statement

| frozen claim | Lean counterpart |
|---|---|
| 1. reality bridge | `Pc_ofReal` (`hN : Odd N`) |
| 2. idempotence, complex level | `Pc_idem` |
| 2. idempotence, real level | `P_idem` (`hN : Odd N`, via claims 1 and `Pc_idem`) |
| 3. spectral divergence ledger, complex | `divHat_Pc` |
| 3. spectral divergence ledger, real | `divHat_P` (`hN : Odd N`, via claims 1 and 3) |
| 4. placeholder wake | `P'`, `P'_comp`, `isProjector_toMatrix` (`hN : Odd N`) |
| 5. per-mode break | `perMode_break` (`hN : Odd N`, `h3 : 3 ≤ N`) |

The frozen `divHat` was corrected in the definitional layer from the field-only
ledger to the internal-DFT ledger
`divHat v k = if κ k = 0 then 0 else I * ∑ⱼ (κ k ⱼ : ℂ) * dft2 (v ⱼ) k`.
The frozen claim statements are unchanged; the correction is recorded in the
module docstring and is forced by the constant-field `e₁` counterexample to the
field-only version.

## 2b Supporting Declarations

| declaration | role |
|---|---|
| `kappa_zero_iff`, `kappa_neg`, `kappa_dot_ne_zero` | `valMinAbs` wavenumber algebra |
| `uncurryT`, `dft2vec`, `dft2`, `dft2Fun` | cast-free 2-D DFT construction and kernel form |
| `dft2_apply`, `dft2_symm_apply` | forward/inverse kernel formulas, normalization `N⁻²` |
| `dft2_star`, `dft2_ofReal_conj` | conjugation law and reality bridge |
| `dft2_comp_neg`, `idft2_selfConj`, `idft2_im_eq_zero`, `idft2_eq_ofReal_re` | negation reindexing and self-conjugate inverse |
| `Phat`, `PhatC`, `PhatC_eq_leraySymbol`, `Phat_zero`, `PhatC_zero`, `Phat_neg`, `PhatC_neg`, `PhatC_idem` | symbol at zero/nonzero modes, evenness, idempotence |
| `dft2Pi`, `mulPhat`, `Pc`, `toComplex`, `ofComplexRe`, `P`, `P_apply`, `Pc_apply` | complex and real vector-field operator layer |
| `divHat`, `surrogateSpectrum2`, `surrogateField`, `surrogateField_reality` | spectral ledger and surrogate field/spectrum bridge |
| `P'`, `P'_comp` | curried real operator and its idempotence |

## 2b Register

The frozen register is the operator layer: 2-D DFT, zero-mode projector
convention, reality bridge, idempotence at both levels, spectral divergence
ledger, awake `Surrogate.isProjector` matrix, and the per-mode break. Exact over
`ℂ`/`ℝ`; no PDE, time evolution, finite differences, or lattice.

## 2b Not Claimed

Even `N` (Nyquist fence); vanishing of any finite-difference divergence (only
the spectral ledger); zero-mean convention (`S(0) = I` keeps the mean);
smoothness of `κ` in `k` (`valMinAbs` folding); self-adjointness (2a claim 8
stays cut, mapped-prose/optional); analytic/PDE regularity of `P`.

## 2b Audit

`Tests/Audit.lean` prints signatures for the frozen claims and supporting
declarations, and `#print axioms` for the claims, supporting `dft2` layer, and
surrogate bridge. Every audited declaration must depend only on
`[propext, Classical.choice, Quot.sound]`.
