module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic
public import K1Lean.Leray
public import K1Lean.Parseval
public import K1Lean.Surrogate

/-!
# 2b frozen statement (v1, 2026-10-20)

Provenance: 2a merged (`35d4131`, CI green; five declarations, audit clean).
This is the 2-torus operator layer promised by 2a's forward scope and the
Nyquist fence. Amendments from the attack round: (i) the 2-D reality bridge is
a named dependency (`dft2_ofReal_conj`, plus `idft2_im_eq_zero`), not an implicit
step; (ii) your four pins are incorporated; (iii) redrafting exposed a
structural slip in the previous version — the symbol is a matrix, so `P` must
act on **vector** fields, not scalar fields. D4 records the change.

Ruling (2026-10-20): D1–D6 all confirmed, with two amendments: (a) add
`divHat_P` to claim 3's group; (b) `P_idem` consumes `Pc_ofReal`, not just
`Pc_idem`. Implementation also corrects the draft's `divHat` from a
field-only ledger to the internal-DFT ledger
`divHat v k := if kappa k = 0 then 0 else Complex.I * ∑ j, (kappa k j : ℂ) * dft2 (v j) k`;
the frozen draft's field-only form makes claim 3 false (constant field `e₁`
gives `divHat (Pc v) = Complex.I * κ₁ ≠ 0`). The claim statements are
unchanged; the correction is definitional and is recorded here, not silent.
Claim 2 and 4 carry `(hN : Odd N)` because the proof of `P_idem` goes through
`Pc_ofReal`; claim 3's `divHat_P` also carries `hN`.

## Setting

- `N : ℕ`, `[NeZero N]`, `(hN : Odd N)` — oddness from line one; even-N
  Nyquist is the documented limitation (fence below).
- `T := Fin 2 → ZMod N`; `d = 2` fixed at instantiation, no generic `d`.
- `κ k := fun i => ((k i).valMinAbs : ℝ)`; `κ k = 0 ↔ k = 0` (all N);
  `κ (−k) = −κ k` (uses `hN`).
- `dft2 : (T → ℂ) ≃ₗ[ℂ] (T → ℂ)` — 2-D DFT by iterating 1-D `ZMod.dft`
  along the two coordinates (`finTwoArrowEquiv`/`piCongrLeft` +
  `piCongrRight`), same normalization; `dft2.symm` the inverse.
- `P̂ k := if k = 0 then 1 else leraySymbol (κ k) (kappa_dot_ne_zero …)`;
  zero mode is the identity.
- `Pℂ v := fun j => dft2.symm (fun k => (P̂ k *ᵥ fun l => dft2 (v l) k) j)` —
  vector-field operator.
- `P v := fun j x => (Pℂ (fun l y => (v l y : ℂ)) j x).re` — real vector-field
  operator, bundled as an ℝ-linear map.
- `divHat v k := if κ k = 0 then 0 else Complex.I * ∑ j, (κ k j : ℂ) * dft2 (v j) k`
  — own `def`, zero clause visible (pin 3); internal-DFT correction above.

Supporting declarations frozen with the layer (not claims): `kappa_zero_iff`,
`kappa_neg`, `kappa_dot_ne_zero`, `dft2_ofReal_conj`, `idft2_im_eq_zero`,
`surrogateSpectrum2`, `surrogateField`, `surrogateField_reality`.

## Statement (file order 1–5)

```lean
theorem Pc_ofReal (hN : Odd N) (v : Fin 2 → T → ℝ) :
    Pc (fun j x => (v j x : ℂ)) = fun j x => (P v j x : ℂ)

theorem P_idem  (hN : Odd N) : P.comp P = P
theorem Pc_idem : Pc.comp Pc = Pc

theorem divHat_Pc (v : Fin 2 → T → ℂ) : divHat (Pc v) = 0
theorem divHat_P (hN : Odd N) (v : Fin 2 → T → ℝ) :
    divHat (fun j x => (P v j x : ℂ)) = 0

noncomputable def P' : (Fin 2 × T → ℝ) →ₗ[ℝ] (Fin 2 × T → ℝ) :=
  (LinearEquiv.curry ℝ).symm ∘ₗ P ∘ₗ (LinearEquiv.curry ℝ)

theorem isProjector_toMatrix (hN : Odd N) :
    Surrogate.isProjector
      (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 2 × T)) (Pi.basisFun ℝ (Fin 2 × T)) P')

theorem perMode_break (hN : Odd N) (h3 : 3 ≤ N) :
    ∃ (f : Fin 2 → T → ℝ) (kstar : T),
      kstar ≠ 0 ∧
      (fun j => dft2 (fun x => (f j x : ℂ)) kstar) = ![1, 0] ∧
      kappa kstar = ![1, 0] ∧
      ‖fun j => dft2 (fun x =>
        (P (fun j' => surrogateField (f j') (fun _ => 1)) j x : ℂ)) kstar‖ ≠
      ‖fun j => dft2 (fun x => (f j x : ℂ)) kstar‖
```

Claim order and content: 1 reality bridge; 2 idempotence (both levels); 3
spectral divergence ledger (`divHat_Pc`, `divHat_P`); 4 wake; 5 per-mode break.
The proof steps `mulVec_mulVec` (claim 2) and `dotProduct_mulVec` (claim 3) are
named at use sites, not separate frozen claims.

## Register

The operator layer: 2-D DFT, zero-mode projector convention, reality bridge,
idempotence, spectral divergence ledger, awake `isProjector` matrix, and the
per-mode break. Exact over ℂ/ℝ. No PDE, no time evolution, no finite
differences.

## Not claimed

Even N (fence); vanishing of any finite-difference divergence (only the spectral
ledger); zero-mean convention (`S(0) = I` keeps the mean); smoothness of `κ` in
`k` (`valMinAbs` folding); self-adjointness (2a claim 8 stays cut,
mapped-prose/optional); analytic/PDE regularity of `P`.

## Scope fence (carried from 2a)

"2b freezes with N odd; the even-N Nyquist modes are a documented limitation,
not in scope." Code citation: `compressible/ns.py` `Spectral2D` uses
`np.fft.fftfreq` (Nyquist bin at −n/2); `valMinAbs` sign symmetry fails there;
claims 1 and 5 would need a Nyquist case split not claimed here.

## Gauge-pin paragraph (pin 4)

`S(0) = I` is the projector convention: constant vector fields pass through and
are exactly divergence-free in the spectral ledger. It is **not** the code's
pressure gauge pin (`k2_inv[0,0] = 0`, `p_h[0,0] = 0` in `compressible/ns.py`
— Poisson null-gauge/mean mode). The formalization models the former; the
latter is solver-level and outside 2b.

## Dependencies / proof route

- Claim 1: `dft2_ofReal_conj` (Hermitian input) + `κ(−k) = −κ(k)` + 2a claim 5
  (`P̂` even) + `idft2_im_eq_zero`.
- Claim 2: 2a claim 4, `mulVec_mulVec`; zero mode by `P̂ 0 = 1`; `P_idem` also
  consumes claim 1 (`Pc_ofReal`).
- Claim 3: 2a claim 2 via `dotProduct_mulVec`
  (`κ ⬝ᵥ (S *ᵥ v̂) = (κ ᵥ* S) ⬝ᵥ v̂`); zero mode by the `if`; `divHat_P` is
  claim 1 applied to `divHat_Pc`.
- Claim 4: `LinearMap.toMatrix_comp` + claim 2; `projector_idempotent` stays
  trivial — the content is the identification of the matrix with this operator.
- Claim 5: claim 1, `surrogateField_reality` (2-D Parseval-lite; needs
  `dft2_ofReal_conj` + Hermitian `u`), 2a claim 1 (`S(1,0) *ᵥ e₁ = 0`).

## D1–D6 rulings

| # | Item | Proposed | Status |
|---|------|----------|--------|
| D1 | N=1 boundary | claims 1–4 general; claim 5 carries `(h3 : 3 ≤ N)`; `hN` explicit on 1, 2 (`P_idem`), 3 (`divHat_P`), 4, 5 | confirmed |
| D2 | Witness shape | W2: `∃ f k*`, `f̂(k*) = e₁`, `u ≡ 1` admissible, surrogate `g`, norm inequality; `surrogateField_reality` frozen with it | confirmed |
| D3 | DFT route | iteration of `ZMod.dft`; `dft2_ofReal_conj` and `idft2_im_eq_zero` frozen dependencies | confirmed |
| D4 | Vector layout | component-first `Fin 2 → T → 𝕂`; `P` on vector fields (symbol is a matrix); `P̂ k *ᵥ v̂`, row kill `κ ᵥ* P̂` | confirmed |
| D5 | `P` as LinearMap | real-linear bundle with `.re` definition; claim 1 is the substantive bridge; claim 4 uses `curry` + `Pi.basisFun ℝ (Fin 2 × T)` | confirmed |
| D6 | File name | `LerayBox.lean`; imports `Leray`, `Parseval`, `Surrogate`; dependency list above | confirmed |

Implementation support (not frozen claims): `TwoTorus`, `uncurryT`, `dft2vec`,
`dft2Fun`, `PhatC`, `dft2Pi`, `mulPhat`, `toComplex`, `ofComplexRe`, and the
formula lemmas for `dft2`/`dft2.symm`.
-/

@[expose] public section

set_option autoImplicit false

namespace K1Lean

open Matrix
open ZMod

/-- The two-torus grid used by the operator layer. -/
abbrev TwoTorus (N : ℕ) : Type := Fin 2 → ZMod N

variable {N : ℕ} [NeZero N]

/-- Wavenumber of the `i`-th coordinate, folded by `valMinAbs`. -/
noncomputable def kappa (k : TwoTorus N) : Fin 2 → ℝ :=
  fun i => ((k i).valMinAbs : ℝ)

/-- The folded wavenumber vanishes exactly at the zero mode (all `N`). -/
theorem kappa_zero_iff (k : TwoTorus N) : kappa k = 0 ↔ k = 0 := by
  constructor
  · intro h
    funext i
    have hi : ((k i).valMinAbs : ℝ) = 0 := by
      have h' := congrFun h i
      simpa [kappa] using h'
    have hz : (k i).valMinAbs = 0 := by exact_mod_cast hi
    exact (ZMod.valMinAbs_eq_zero (k i)).mp hz
  · intro h
    rw [h]
    funext i
    simp [kappa]

/-- Odd `N` makes the folded wavenumber odd, `κ(−k) = −κ(k)`. -/
theorem kappa_neg (hN : Odd N) (k : TwoTorus N) : kappa (-k) = -kappa k := by
  funext i
  have hlt : (k i).val < N := ZMod.val_lt (k i)
  have h2 : 2 * (k i).val ≠ N := by
    rcases hN with ⟨m, hm⟩
    omega
  simp only [kappa, Pi.neg_apply]
  rw [ZMod.valMinAbs_neg_of_ne_half h2]
  push_cast
  ring

/-- The folded wavenumber has nonzero self-dot-product away from the zero mode. -/
theorem kappa_dot_ne_zero (k : TwoTorus N) (hk : k ≠ 0) :
    kappa k ⬝ᵥ kappa k ≠ 0 := by
  intro h
  apply hk
  rw [← kappa_zero_iff]
  funext i
  have hsum : ∑ j, kappa k j * kappa k j = 0 := by
    simpa [dotProduct] using h
  have hterm : kappa k i * kappa k i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (kappa k j))).mp
      hsum i (Finset.mem_univ i)
  exact mul_self_eq_zero.mp hterm

/-- Uncurrying `Fin 2 → ZMod N` to a pair, cast-free. -/
noncomputable def uncurryT :
    (TwoTorus N → ℂ) ≃ₗ[ℂ] (ZMod N × ZMod N → ℂ) where
  toFun X p := X ((finTwoArrowEquiv (ZMod N)).symm p)
  invFun Φ x := Φ ((finTwoArrowEquiv (ZMod N)) x)
  left_inv X := by
    funext x
    simp only [Equiv.symm_apply_apply]
  right_inv Φ := by
    funext p
    simp
  map_add' X Y := rfl
  map_smul' c X := rfl

@[simp]
theorem uncurryT_apply (X : TwoTorus N → ℂ) (p : ZMod N × ZMod N) :
    uncurryT X p = X ((finTwoArrowEquiv (ZMod N)).symm p) :=
  rfl

@[simp]
theorem uncurryT_symm_apply (Φ : ZMod N × ZMod N → ℂ) (x : TwoTorus N) :
    uncurryT.symm Φ x = Φ ((finTwoArrowEquiv (ZMod N)) x) :=
  rfl

/-- The 2-D DFT as two iterated 1-D `ZMod.dft`s, in uncurried coordinates. -/
noncomputable def dft2vec :
    (ZMod N × ZMod N → ℂ) ≃ₗ[ℂ] (ZMod N × ZMod N → ℂ) :=
  (LinearEquiv.curry ℂ ℂ (ZMod N) (ZMod N)).trans
    ((LinearEquiv.piCongrRight (fun _ : ZMod N => ZMod.dft (N := N) (E := ℂ))).trans
      ((ZMod.dft (N := N) (E := ZMod N → ℂ)).trans
        (LinearEquiv.curry ℂ ℂ (ZMod N) (ZMod N)).symm))

/-- The frozen 2-D DFT on the two-torus. -/
noncomputable def dft2 : (TwoTorus N → ℂ) ≃ₗ[ℂ] (TwoTorus N → ℂ) :=
  uncurryT.trans (dft2vec.trans uncurryT.symm)

/-- The explicit kernel form of the 2-D DFT. -/
noncomputable def dft2Fun (X : TwoTorus N → ℂ) (k : TwoTorus N) : ℂ :=
  ∑ x : TwoTorus N, stdAddChar (-(x 0 * k 0 + x 1 * k 1)) • X x

/-- Forward kernel formula for the iterated transform. -/
theorem dft2vec_apply (Φ : ZMod N × ZMod N → ℂ) (k₀ k₁ : ZMod N) :
    dft2vec Φ (k₀, k₁) =
      ∑ i, stdAddChar (-(i * k₀)) * ∑ j, stdAddChar (-(j * k₁)) * Φ (i, j) := by
  rw [dft2vec]
  simp only [LinearEquiv.trans_apply, LinearEquiv.coe_curry_symm,
    Function.uncurry_apply_pair, LinearEquiv.piCongrRight_apply, ZMod.dft_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_curry,
    Function.curry_apply]

/-- Inverse kernel formula for the iterated transform. -/
theorem dft2vec_symm_apply (Φ : ZMod N × ZMod N → ℂ) (k₀ k₁ : ZMod N) :
    dft2vec.symm Φ (k₀, k₁) =
      ((N : ℂ) * N)⁻¹ * ∑ j, ∑ i, stdAddChar (j * k₁ + i * k₀) * Φ (i, j) := by
  have hcoef : (N : ℂ)⁻¹ * (N : ℂ)⁻¹ = ((N : ℂ) * N)⁻¹ := by
    rw [← mul_inv]
  have hraw : dft2vec.symm Φ (k₀, k₁) =
      (N : ℂ)⁻¹ * ∑ j, stdAddChar (j * k₁) *
        ((N : ℂ)⁻¹ * ∑ i, stdAddChar (i * k₀) * Φ (i, j)) := by
    rw [dft2vec, LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply,
      LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm]
    simp only [LinearEquiv.coe_curry_symm, LinearEquiv.coe_curry,
      Function.uncurry_apply_pair, Function.curry_apply,
      LinearEquiv.piCongrRight_symm, LinearEquiv.piCongrRight_apply,
      ZMod.invDFT_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hraw]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [← hcoef, AddChar.map_add_eq_mul]
  ring

/-- Forward formula: `dft2 X k = ∑ x, χ(−(x₀k₀ + x₁k₁)) • X x`. -/
theorem dft2_apply (X : TwoTorus N → ℂ) (k : TwoTorus N) :
    dft2 X k = dft2Fun X k := by
  have h1 : dft2 X k = dft2vec (uncurryT X) (k 0, k 1) := by
    rw [dft2, LinearEquiv.trans_apply, LinearEquiv.trans_apply, uncurryT_symm_apply]
    rfl
  rw [h1, dft2vec_apply, dft2Fun]
  simp only [smul_eq_mul, Finset.mul_sum, uncurryT_apply]
  let f : ZMod N × ZMod N → ℂ := fun p =>
    stdAddChar (-(p.1 * k 0)) *
      (stdAddChar (-(p.2 * k 1)) * X ((finTwoArrowEquiv (ZMod N)).symm p))
  let g : TwoTorus N → ℂ := fun x =>
    stdAddChar (-(x 0 * k 0 + x 1 * k 1)) * X x
  have hprod :
      (∑ i, ∑ j, stdAddChar (-(i * k 0)) *
        (stdAddChar (-(j * k 1)) *
          X ((finTwoArrowEquiv (ZMod N)).symm (i, j))))
        = ∑ x, g x := by
    have h1 : (∑ i, ∑ j, stdAddChar (-(i * k 0)) *
        (stdAddChar (-(j * k 1)) *
          X ((finTwoArrowEquiv (ZMod N)).symm (i, j)))) = ∑ p, f p := by
      exact (Fintype.sum_prod_type f).symm
    have h2 : (∑ p, f p) = ∑ x, g x := by
      rw [← Equiv.sum_comp (finTwoArrowEquiv (ZMod N)) f]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hx0 : (finTwoArrowEquiv (ZMod N)) x = (x 0, x 1) := by
        ext <;> simp [finTwoArrowEquiv]
      have hx1 : (finTwoArrowEquiv (ZMod N)).symm (x 0, x 1) = x := by
        rw [← hx0, Equiv.symm_apply_apply]
      simp only [f, g, hx0, hx1]
      rw [show -(x 0 * k 0 + x 1 * k 1) =
        -(x 0 * k 0) + -(x 1 * k 1) by ring]
      rw [AddChar.map_add_eq_mul]
      ring
    exact h1.trans h2
  change (∑ i, ∑ j, stdAddChar (-(i * k 0)) *
      (stdAddChar (-(j * k 1)) *
        X ((finTwoArrowEquiv (ZMod N)).symm (i, j)))) = ∑ x, g x
  exact hprod

/-- Inverse formula: `dft2.symm X k = N⁻² ∑ x, χ(x₀k₀ + x₁k₁) • X x`. -/
theorem dft2_symm_apply (X : TwoTorus N → ℂ) (k : TwoTorus N) :
    dft2.symm X k = ((N : ℂ) * N)⁻¹ * dft2Fun X (-k) := by
  have h1 : dft2.symm X k = dft2vec.symm (uncurryT X) (k 0, k 1) := by
    rw [dft2, LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply,
      uncurryT_symm_apply]
    rfl
  rw [h1, dft2vec_symm_apply]
  congr 1
  rw [dft2Fun]
  simp only [smul_eq_mul, uncurryT_apply]
  let f : ZMod N × ZMod N → ℂ := fun p =>
    stdAddChar (p.2 * k 1 + p.1 * k 0) *
      X ((finTwoArrowEquiv (ZMod N)).symm p)
  let g : TwoTorus N → ℂ := fun x =>
    stdAddChar (x 0 * k 0 + x 1 * k 1) * X x
  have hsum :
      (∑ j, ∑ i, stdAddChar (j * k 1 + i * k 0) *
        X ((finTwoArrowEquiv (ZMod N)).symm (i, j))) = ∑ x, g x := by
    have h1 : (∑ j, ∑ i, stdAddChar (j * k 1 + i * k 0) *
        X ((finTwoArrowEquiv (ZMod N)).symm (i, j))) = ∑ p, f p := by
      exact (Fintype.sum_prod_type_right f).symm
    have h2 : (∑ p, f p) = ∑ x, g x := by
      rw [← Equiv.sum_comp (finTwoArrowEquiv (ZMod N)) f]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hx0 : (finTwoArrowEquiv (ZMod N)) x = (x 0, x 1) := by
        ext <;> simp [finTwoArrowEquiv]
      have hx1 : (finTwoArrowEquiv (ZMod N)).symm (x 0, x 1) = x := by
        rw [← hx0, Equiv.symm_apply_apply]
      simp only [f, g, hx0, hx1]
      rw [show x 1 * k 1 + x 0 * k 0 = x 0 * k 0 + x 1 * k 1 by ring]
    exact h1.trans h2
  rw [hsum]
  simp only [g]
  apply Finset.sum_congr rfl
  intro x _
  rw [show x 0 * k 0 + x 1 * k 1 =
    -(x 0 * (-k) 0 + x 1 * (-k) 1) by
      simp only [Pi.neg_apply]
      ring]

/-- Conjugation law: `star (dft2 Φ k) = dft2 (star ∘ Φ) (−k)`. -/
theorem dft2_star (Φ : TwoTorus N → ℂ) (k : TwoTorus N) :
    star (dft2 Φ k) = dft2 (fun j => star (Φ j)) (-k) := by
  have hchar (x : ZMod N) :
      starRingEnd ℂ (stdAddChar (N := N) x) = stdAddChar (-x) :=
    (AddChar.map_neg_eq_conj (stdAddChar (N := N)) x).symm
  rw [dft2_apply, dft2_apply, dft2Fun, dft2Fun]
  simp only [smul_eq_mul]
  rw [← starRingEnd_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, hchar, starRingEnd_apply]
  rw [show -(-(x 0 * k 0 + x 1 * k 1)) = x 0 * k 0 + x 1 * k 1 by ring]
  have harg' : -(x 0 * (-k) 0 + x 1 * (-k) 1) = x 0 * k 0 + x 1 * k 1 := by
    simp only [Pi.neg_apply]
    ring
  rw [harg']

/-- Reality bridge: the DFT of a real field is Hermitian. -/
theorem dft2_ofReal_conj (f : TwoTorus N → ℝ) (k : TwoTorus N) :
    star (dft2 (fun x => (f x : ℂ)) k) =
      dft2 (fun x => (f x : ℂ)) (-k) := by
  rw [dft2_star]
  have hfun : (fun j => star (f j : ℂ)) = fun x => (f x : ℂ) := by
    funext x
    exact RCLike.conj_ofReal (f x)
  rw [hfun]

/-- Reindexing law: `dft2 (fun j => X (−j)) = fun k => dft2 X (−k)`. -/
theorem dft2_comp_neg (X : TwoTorus N → ℂ) :
    dft2 (fun j => X (-j)) = fun k => dft2 X (-k) := by
  funext k
  rw [dft2_apply, dft2_apply, dft2Fun, dft2Fun]
  simp only [smul_eq_mul]
  let negEquiv : TwoTorus N ≃ TwoTorus N :=
    { toFun := fun x => -x
      invFun := fun x => -x
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  refine Fintype.sum_equiv negEquiv _ _ ?_
  intro x
  change stdAddChar (-(x 0 * k 0 + x 1 * k 1)) * X (-x) =
    stdAddChar (-((negEquiv x) 0 * (-k) 0 + (negEquiv x) 1 * (-k) 1)) *
      X (negEquiv x)
  rw [show negEquiv x = -x from rfl]
  simp only [Pi.neg_apply]
  rw [show -(x 0 * k 0 + x 1 * k 1) =
    -((-(x 0)) * (-(k 0)) + (-(x 1)) * (-(k 1))) by ring]

/-- A Hermitian spectrum has a self-conjugate inverse transform. -/
theorem idft2_selfConj (X : TwoTorus N → ℂ)
    (hX : ∀ k, star (X k) = X (-k)) (k : TwoTorus N) :
    star (dft2.symm X k) = dft2.symm X k := by
  rw [dft2_symm_apply]
  have hNstar : star (((N : ℂ) * N)⁻¹) = ((N : ℂ) * N)⁻¹ := by
    rw [star_inv₀, star_mul', star_natCast]
  rw [star_mul', hNstar]
  have hstar : star (dft2Fun X (-k)) = dft2Fun X (-k) := by
    have h1 : dft2Fun X (-k) = dft2 X (-k) := (dft2_apply X (-k)).symm
    rw [h1, dft2_star]
    have hfun : (fun j => star (X j)) = fun j => X (-j) := funext hX
    rw [hfun, dft2_comp_neg]
    simp
  rw [hstar]

/-- Reality corollary: the imaginary part of the inverse transform is zero. -/
theorem idft2_im_eq_zero (X : TwoTorus N → ℂ)
    (hX : ∀ k, star (X k) = X (-k)) (x : TwoTorus N) :
    (dft2.symm X x).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  simpa only [Complex.star_def] using idft2_selfConj X hX x

/-- Reality corollary, packaged: the inverse transform equals its real coercion. -/
theorem idft2_eq_ofReal_re (X : TwoTorus N → ℂ)
    (hX : ∀ k, star (X k) = X (-k)) (x : TwoTorus N) :
    dft2.symm X x = ((dft2.symm X x).re : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]
  · rw [idft2_im_eq_zero X hX x, Complex.ofReal_im]

/-- The Leray symbol at wavevector `k`; the zero mode is the identity. -/
noncomputable def Phat (k : TwoTorus N) : Matrix (Fin 2) (Fin 2) ℝ :=
  if h : k = 0 then 1 else leraySymbol (kappa k) (kappa_dot_ne_zero k h)

/-- The complexified Leray symbol. -/
noncomputable def PhatC (k : TwoTorus N) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Phat k).map (algebraMap ℝ ℂ)

/-- At nonzero `k`, `PhatC` is the complexified 2a symbol. -/
theorem PhatC_eq_leraySymbol (k : TwoTorus N) (hk : k ≠ 0) :
    PhatC k = (leraySymbol (kappa k) (kappa_dot_ne_zero k hk)).map
      (algebraMap ℝ ℂ) := by
  simp [PhatC, Phat, hk]

/-- The zero-mode symbol is the identity. -/
theorem Phat_zero : Phat (0 : TwoTorus N) = 1 := by
  simp [Phat]

/-- The complexified zero-mode symbol is the identity. -/
theorem PhatC_zero : PhatC (0 : TwoTorus N) = 1 := by
  rw [PhatC, Phat_zero]
  exact Matrix.map_one (algebraMap ℝ ℂ) (map_zero _) (map_one _)

/-- Oddness of `κ` makes the symbol even. -/
theorem Phat_neg (hN : Odd N) (k : TwoTorus N) : Phat (-k) = Phat k := by
  by_cases hk : k = 0
  · rw [hk]
    simp
  · have hnk : -k ≠ 0 := neg_ne_zero.mpr hk
    simp only [Phat, hk, hnk, leraySymbol]
    rw [kappa_neg hN k]
    simp only [Pi.neg_apply, neg_mul_neg, neg_dotProduct_neg]

/-- Complexified evenness. -/
theorem PhatC_neg (hN : Odd N) (k : TwoTorus N) : PhatC (-k) = PhatC k := by
  rw [PhatC, PhatC, Phat_neg hN k]

/-- The complexified symbol is idempotent, including the zero mode. -/
theorem PhatC_idem (k : TwoTorus N) : PhatC k * PhatC k = PhatC k := by
  by_cases hk : k = 0
  · rw [hk, PhatC_zero]
    simp
  · rw [PhatC_eq_leraySymbol k hk,
      ← Matrix.map_mul (f := (algebraMap ℝ ℂ : ℝ →+* ℂ)), leraySymbol_idem]

/-- Componentwise 2-D DFT on vector fields. -/
noncomputable def dft2Pi :
    (Fin 2 → TwoTorus N → ℂ) ≃ₗ[ℂ] (Fin 2 → TwoTorus N → ℂ) :=
  LinearEquiv.piCongrRight (fun _ : Fin 2 => dft2)

@[simp]
theorem dft2Pi_apply (v : Fin 2 → TwoTorus N → ℂ) (j : Fin 2) :
    dft2Pi v j = dft2 (v j) :=
  rfl

@[simp]
theorem dft2Pi_symm_apply (v : Fin 2 → TwoTorus N → ℂ) (j : Fin 2) :
    dft2Pi.symm v j = dft2.symm (v j) :=
  rfl

/-- Pointwise multiplication by the Leray symbol on vector fields. -/
noncomputable def mulPhat :
    (Fin 2 → TwoTorus N → ℂ) →ₗ[ℂ] (Fin 2 → TwoTorus N → ℂ) where
  toFun W j k := (PhatC k *ᵥ fun l => W l k) j
  map_add' W W' := by
    funext j k
    change (PhatC k *ᵥ ((fun l => W l k) + fun l => W' l k)) j =
      (PhatC k *ᵥ fun l => W l k) j + (PhatC k *ᵥ fun l => W' l k) j
    rw [Matrix.mulVec_add]
    rfl
  map_smul' c W := by
    funext j k
    change (PhatC k *ᵥ (c • fun l => W l k)) j =
      c * (PhatC k *ᵥ fun l => W l k) j
    rw [Matrix.mulVec_smul]
    rfl

@[simp]
theorem mulPhat_apply (W : Fin 2 → TwoTorus N → ℂ) (j : Fin 2) (k : TwoTorus N) :
    mulPhat W j k = (PhatC k *ᵥ fun l => W l k) j :=
  rfl

/-- The complex vector-field Leray operator. -/
noncomputable def Pc : (Fin 2 → TwoTorus N → ℂ) →ₗ[ℂ] (Fin 2 → TwoTorus N → ℂ) :=
  dft2Pi.symm.toLinearMap.comp (mulPhat.comp dft2Pi.toLinearMap)

@[simp]
theorem Pc_apply (v : Fin 2 → TwoTorus N → ℂ) (j : Fin 2) :
    Pc v j = dft2.symm (fun k => (PhatC k *ᵥ fun l => dft2 (v l) k) j) :=
  rfl

/-- Coercion of a real vector field to a complex vector field. -/
noncomputable def toComplex :
    (Fin 2 → TwoTorus N → ℝ) →ₗ[ℝ] (Fin 2 → TwoTorus N → ℂ) where
  toFun v j x := (v j x : ℂ)
  map_add' v w := by
    funext j x
    simp
  map_smul' c v := by
    funext j x
    simp [Complex.real_smul, smul_eq_mul]

/-- Real part of a complex vector field. -/
noncomputable def ofComplexRe :
    (Fin 2 → TwoTorus N → ℂ) →ₗ[ℝ] (Fin 2 → TwoTorus N → ℝ) where
  toFun v j x := (v j x).re
  map_add' v w := by
    funext j x
    simp [Complex.add_re]
  map_smul' c v := by
    funext j x
    simp [Complex.smul_re, smul_eq_mul]

/-- The real vector-field Leray operator. -/
noncomputable def P : (Fin 2 → TwoTorus N → ℝ) →ₗ[ℝ] (Fin 2 → TwoTorus N → ℝ) :=
  ofComplexRe.comp ((Pc.restrictScalars ℝ).comp toComplex)

@[simp]
theorem P_apply (v : Fin 2 → TwoTorus N → ℝ) (j : Fin 2) (x : TwoTorus N) :
    P v j x = (Pc (fun l y => (v l y : ℂ)) j x).re :=
  rfl

/-- Frozen claim 1: the real operator is the real part of the complex one. -/
theorem Pc_ofReal (hN : Odd N) (v : Fin 2 → TwoTorus N → ℝ) :
    Pc (fun j x => (v j x : ℂ)) = fun j x => (P v j x : ℂ) := by
  funext j x
  simp only [P_apply, Pc_apply]
  let Yj : TwoTorus N → ℂ := fun k =>
    (PhatC k *ᵥ fun l => dft2 (fun y => (v l y : ℂ)) k) j
  have hY : ∀ k, star (Yj k) = Yj (-k) := by
    intro k
    dsimp only [Yj]
    simp only [Matrix.mulVec, dotProduct]
    rw [← starRingEnd_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, starRingEnd_apply, starRingEnd_apply]
    have h1 : star (PhatC k j l) = PhatC k j l := by
      rw [PhatC, Matrix.map_apply]
      exact RCLike.conj_ofReal _
    have h2 : PhatC (-k) j l = PhatC k j l := by
      rw [PhatC_neg hN k]
    have hW : dft2 (fun y => (v l y : ℂ)) (-k) =
        star (dft2 (fun y => (v l y : ℂ)) k) :=
      (dft2_ofReal_conj (v l) k).symm
    rw [h1, h2, hW]
  change dft2.symm Yj x = ((dft2.symm Yj x).re : ℂ)
  exact idft2_eq_ofReal_re Yj hY x

/-- Frozen claim 2 (complex level): `Pc` is idempotent. -/
theorem Pc_idem : (Pc (N := N)).comp (Pc (N := N)) = Pc (N := N) := by
  ext v j x
  simp only [LinearMap.comp_apply, Pc_apply]
  have hAB :
      (fun k => (PhatC k *ᵥ fun l => dft2 ((Pc v) l) k) j) =
      (fun k => (PhatC k *ᵥ fun l => dft2 (v l) k) j) := by
    funext k
    have hinner : (fun l => dft2 ((Pc v) l) k) =
        fun l => (PhatC k *ᵥ fun m => dft2 (v m) k) l := by
      funext l
      rw [Pc_apply]
      change dft2 (dft2.symm
        (fun k' => (PhatC k' *ᵥ fun m => dft2 (v m) k') l)) k = _
      rw [dft2.apply_symm_apply]
    rw [hinner]
    change (PhatC k *ᵥ (PhatC k *ᵥ fun m => dft2 (v m) k)) j =
      (PhatC k *ᵥ fun m => dft2 (v m) k) j
    rw [Matrix.mulVec_mulVec, PhatC_idem]
  rw [hAB]

/-- Frozen claim 2 (real level): `P` is idempotent. -/
theorem P_idem (hN : Odd N) :
    (P (N := N)).comp (P (N := N)) = P (N := N) := by
  apply LinearMap.ext
  intro v
  funext j x
  simp only [LinearMap.comp_apply]
  rw [P_apply (P v) j x, P_apply v j x]
  have hpv : (fun j' y => (P v j' y : ℂ)) =
      Pc (fun j' y => (v j' y : ℂ)) :=
    (Pc_ofReal hN v).symm
  have hidem : Pc (Pc (fun j' y => (v j' y : ℂ))) =
      Pc (fun j' y => (v j' y : ℂ)) := by
    rw [← LinearMap.comp_apply, Pc_idem]
  rw [hpv, hidem]

/-- The spectral divergence ledger, with the zero clause visible. -/
noncomputable def divHat (v : Fin 2 → TwoTorus N → ℂ) : TwoTorus N → ℂ :=
  fun k => if kappa k = 0 then 0 else
    Complex.I * ∑ j, (kappa k j : ℂ) * dft2 (v j) k

/-- Frozen claim 3 (complex level): the Leray operator kills the ledger. -/
theorem divHat_Pc (v : Fin 2 → TwoTorus N → ℂ) : divHat (Pc v) = 0 := by
  funext k
  by_cases hk : kappa k = 0
  · simp [divHat, hk]
  · have hk0 : k ≠ 0 := by
      intro h
      exact hk (by rw [h]; funext i; simp [kappa])
    simp only [divHat, if_neg hk]
    have hdft : ∀ j, dft2 ((Pc v) j) k =
        (PhatC k *ᵥ fun l => dft2 (v l) k) j := by
      intro j
      rw [Pc_apply]
      change dft2 (dft2.symm
        (fun k' => (PhatC k' *ᵥ fun l => dft2 (v l) k') j)) k = _
      rw [dft2.apply_symm_apply]
    simp only [hdft]
    change Complex.I * ((fun j : Fin 2 => (kappa k j : ℂ)) ⬝ᵥ
      (PhatC k *ᵥ fun l => dft2 (v l) k)) = 0
    have hrow : (fun j : Fin 2 => (kappa k j : ℂ)) ᵥ* PhatC k = 0 := by
      have hS : PhatC k =
          (leraySymbol (kappa k) (kappa_dot_ne_zero k hk0)).map
            (algebraMap ℝ ℂ) :=
        PhatC_eq_leraySymbol k hk0
      rw [hS]
      ext j
      have h := RingHom.map_vecMul (algebraMap ℝ ℂ)
        (leraySymbol (kappa k) (kappa_dot_ne_zero k hk0))
        (fun i : Fin 2 => (kappa k i)) j
      rw [leraySymbol_vecMul_self] at h
      simpa [Function.comp_def, hS] using h.symm
    rw [dotProduct_mulVec, hrow]
    simp

/-- Frozen claim 3 (real level): claim 1 carries the ledger to `P`. -/
theorem divHat_P (hN : Odd N) (v : Fin 2 → TwoTorus N → ℝ) :
    divHat (fun j x => (P v j x : ℂ)) = 0 := by
  rw [← Pc_ofReal hN v]
  exact divHat_Pc (fun j x => (v j x : ℂ))

/-- The Parseval-lite surrogate spectrum. -/
noncomputable def surrogateSpectrum2 (f : TwoTorus N → ℝ)
    (u : TwoTorus N → ℂ) : TwoTorus N → ℂ :=
  fun k => (‖dft2 (fun x => (f x : ℂ)) k‖ : ℂ) * u k

/-- The real field whose spectrum is the surrogate spectrum. -/
noncomputable def surrogateField (f : TwoTorus N → ℝ)
    (u : TwoTorus N → ℂ) : TwoTorus N → ℝ :=
  fun x => (dft2.symm (surrogateSpectrum2 f u) x).re

/-- Frozen support: the surrogate field realizes the surrogate spectrum. -/
theorem surrogateField_reality (f : TwoTorus N → ℝ) (u : TwoTorus N → ℂ)
    (hu : ∀ k, star (u k) = u (-k)) :
    dft2 (fun x => (surrogateField f u x : ℂ)) = surrogateSpectrum2 f u := by
  have hX : ∀ k, star (surrogateSpectrum2 f u k) =
      surrogateSpectrum2 f u (-k) := by
    intro k
    dsimp only [surrogateSpectrum2]
    rw [star_mul']
    have hnorm : ‖dft2 (fun x => (f x : ℂ)) k‖ =
        ‖dft2 (fun x => (f x : ℂ)) (-k)‖ := by
      rw [← dft2_ofReal_conj f k, norm_star]
    rw [hu k, hnorm]
    simp
  have hfun : (fun x => (surrogateField f u x : ℂ)) =
      dft2.symm (surrogateSpectrum2 f u) := by
    funext x
    dsimp only [surrogateField]
    exact (idft2_eq_ofReal_re (surrogateSpectrum2 f u) hX x).symm
  rw [hfun, dft2.apply_symm_apply]

/-- The operator bundled on the uncurried real vector field. -/
noncomputable def P' : (Fin 2 × TwoTorus N → ℝ) →ₗ[ℝ]
    (Fin 2 × TwoTorus N → ℝ) :=
  (LinearEquiv.curry ℝ ℝ (Fin 2) (TwoTorus N)).symm.toLinearMap.comp
    (P.comp (LinearEquiv.curry ℝ ℝ (Fin 2) (TwoTorus N)).toLinearMap)

/-- Idempotence of the curried bundle. -/
theorem P'_comp (hN : Odd N) :
    (P' (N := N)).comp (P' (N := N)) = P' (N := N) := by
  have hpp : ∀ y : Fin 2 → TwoTorus N → ℝ, P (P y) = P y :=
    fun y => DFunLike.congr_fun (P_idem hN) y
  have hcancel : ∀ y : Fin 2 → TwoTorus N → ℝ,
      (LinearEquiv.curry ℝ ℝ (Fin 2) (TwoTorus N)).toLinearMap
        ((LinearEquiv.curry ℝ ℝ (Fin 2) (TwoTorus N)).symm.toLinearMap y) = y := by
    intro y
    simpa only [LinearEquiv.coe_toLinearMap] using
      (LinearEquiv.curry ℝ ℝ (Fin 2) (TwoTorus N)).apply_symm_apply y
  ext x
  simp only [LinearMap.comp_apply, P']
  rw [hcancel, hpp]

/-- Frozen claim 4: the placeholder projector is awake on `P`. -/
theorem isProjector_toMatrix (hN : Odd N) :
    Surrogate.isProjector
      (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 2 × TwoTorus N))
        (Pi.basisFun ℝ (Fin 2 × TwoTorus N)) P') := by
  let b := Pi.basisFun ℝ (Fin 2 × TwoTorus N)
  change LinearMap.toMatrix b b P' * LinearMap.toMatrix b b P' =
    LinearMap.toMatrix b b P'
  rw [← LinearMap.toMatrix_comp b b b P' P', P'_comp hN]

/-- Frozen claim 5: a per-mode break of the surrogate. -/
theorem perMode_break (hN : Odd N) (h3 : 3 ≤ N) :
    ∃ (f : Fin 2 → TwoTorus N → ℝ) (kstar : TwoTorus N),
      kstar ≠ 0 ∧
      (fun j => dft2 (fun x => (f j x : ℂ)) kstar) = ![1, 0] ∧
      kappa kstar = ![1, 0] ∧
      ‖fun j => dft2 (fun x =>
        (P (fun j' => surrogateField (f j') (fun _ => 1)) j x : ℂ)) kstar‖ ≠
      ‖fun j => dft2 (fun x => (f j x : ℂ)) kstar‖ := by
  let kstar : TwoTorus N := ![1, 0]
  have hkstar : kstar ≠ 0 := by
    intro h
    have h0 : (1 : ZMod N) = 0 := by
      have h' := congrFun h 0
      simpa [kstar] using h'
    rw [ZMod.one_eq_zero_iff] at h0
    omega
  have hkappa : kappa kstar = ![1, 0] := by
    funext i
    fin_cases i
    · change ((kstar 0).valMinAbs : ℝ) = (1 : ℝ)
      have hval : (1 : ZMod N).valMinAbs = (1 : ℤ) := by
        simpa using ZMod.valMinAbs_natCast_of_le_half (n := N) (a := 1)
          (by omega : 1 ≤ N / 2)
      rw [show kstar 0 = (1 : ZMod N) by rfl, hval]
      norm_num
    · simp [kappa, kstar]
  let X : TwoTorus N → Fin 2 → ℂ := fun k j =>
    if k = kstar ∨ k = -kstar then (![1, 0] : Fin 2 → ℂ) j else 0
  have hXherm : ∀ k, star (X k) = X (-k) := by
    intro k
    funext j
    have hneg : (k = kstar ∨ k = -kstar) ↔
        (-k = kstar ∨ -k = -kstar) := by
      constructor
      · rintro (h | h)
        · exact Or.inr (by rw [h])
        · exact Or.inl (by rw [h, neg_neg])
      · rintro (h | h)
        · exact Or.inr (by rw [← neg_neg k, h])
        · exact Or.inl (by rw [← neg_neg k, h, neg_neg])
    by_cases hk : k = kstar ∨ k = -kstar
    · have hnk := hneg.mp hk
      simp only [X, Pi.star_apply, if_pos hk, if_pos hnk]
      fin_cases j <;> simp
    · have hnk : ¬(-k = kstar ∨ -k = -kstar) := fun h => hk (hneg.mpr h)
      simp only [X, Pi.star_apply, if_neg hk, if_neg hnk, star_zero]
  let f : Fin 2 → TwoTorus N → ℝ := fun j x =>
    (dft2.symm (fun k => X k j) x).re
  have hf_dft : ∀ j, dft2 (fun x => (f j x : ℂ)) = fun k => X k j := by
    intro j
    have hXj : ∀ k, star (X k j) = X (-k) j := by
      intro k
      have h' := congrFun (hXherm k) j
      simpa using h'
    have hfun : (fun x => (f j x : ℂ)) = dft2.symm (fun k => X k j) := by
      funext x
      dsimp only [f]
      exact (idft2_eq_ofReal_re (fun k => X k j) hXj x).symm
    rw [hfun, dft2.apply_symm_apply]
  have hf1 : (fun j => dft2 (fun x => (f j x : ℂ)) kstar) = ![1, 0] := by
    funext j
    rw [hf_dft j]
    fin_cases j <;> simp [X]
  let g : Fin 2 → TwoTorus N → ℝ := fun j =>
    surrogateField (f j) (fun _ => 1)
  have hg_dft : ∀ j, dft2 (fun x => (g j x : ℂ)) =
      surrogateSpectrum2 (f j) (fun _ => 1) := by
    intro j
    exact surrogateField_reality (f j) (fun _ => 1) (fun k => by simp)
  have hg1 : (fun j => dft2 (fun x => (g j x : ℂ)) kstar) = ![1, 0] := by
    funext j
    rw [hg_dft j]
    dsimp only [surrogateSpectrum2]
    rw [hf_dft j]
    fin_cases j <;> simp [X]
  let v : Fin 2 → TwoTorus N → ℝ := fun j => g j
  have hPg : Pc (fun j x => (v j x : ℂ)) = fun j x => (P v j x : ℂ) :=
    Pc_ofReal hN v
  have hdft_eq : ∀ j, dft2 (fun x => (P v j x : ℂ)) kstar = 0 := by
    intro j
    have h1 : dft2 (fun x => (P v j x : ℂ)) kstar =
        (PhatC kstar *ᵥ fun l => dft2 (fun x => (v l x : ℂ)) kstar) j := by
      have h2 : (fun x => (P v j x : ℂ)) =
          Pc (fun j x => (v j x : ℂ)) j := (congrFun hPg j).symm
      rw [h2, Pc_apply]
      change dft2 (dft2.symm
        (fun k' => (PhatC k' *ᵥ fun l => dft2 (fun y => (v l y : ℂ)) k') j)) kstar = _
      rw [dft2.apply_symm_apply]
    rw [h1]
    have hW : (fun l => dft2 (fun x => (v l x : ℂ)) kstar) = ![1, 0] := by
      simpa [v] using hg1
    rw [hW]
    have hP : PhatC kstar =
        (leraySymbol (kappa kstar) (kappa_dot_ne_zero kstar hkstar)).map
          (algebraMap ℝ ℂ) :=
      PhatC_eq_leraySymbol kstar hkstar
    rw [hP]
    have hvec : ((algebraMap ℝ ℂ) ∘ kappa kstar) =
        (![1, 0] : Fin 2 → ℂ) := by
      funext l
      rw [hkappa]
      fin_cases l <;> simp
    have hzero := RingHom.map_mulVec (algebraMap ℝ ℂ)
      (leraySymbol (kappa kstar) (kappa_dot_ne_zero kstar hkstar))
      (kappa kstar) j
    rw [leraySymbol_mulVec_self] at hzero
    simp only [Pi.zero_apply, map_zero] at hzero
    rw [hvec] at hzero
    simpa using hzero.symm
  refine ⟨f, kstar, hkstar, hf1, hkappa, ?_⟩
  have hP0 : (fun j => dft2 (fun x =>
      (P (fun j' => surrogateField (f j') (fun _ => 1)) j x : ℂ)) kstar) = 0 := by
    funext j
    simpa [v, g] using hdft_eq j
  rw [hP0, hf1]
  have hnorm : ‖(![1, 0] : Fin 2 → ℂ)‖ = 1 := by
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      intro i
      fin_cases i <;> simp
    · have h := norm_le_pi_norm (![1, 0] : Fin 2 → ℂ) 0
      simpa using h
  rw [hnorm]
  simp

end K1Lean
