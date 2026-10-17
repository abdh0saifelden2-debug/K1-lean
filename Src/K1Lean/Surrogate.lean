module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

set_option autoImplicit false

namespace Surrogate

/-- Idempotent projection matrix: the discrete Leray projector's defining property. -/
def isProjector {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ) : Prop :=
  P * P = P

/-- Applied twice, the projector changes nothing. -/
theorem projector_idempotent {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ)
    (h : isProjector P) : P * P = P := h

end Surrogate
