-- Surrogate skeleton (finite-dimensional only)
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NormedSpace

namespace Surrogate

/-- Finite-dimensional state -/
structure State (n : Type*) where
  val : n → ℝ

/-- Projector (idempotent) statement skeleton -/
def isProjector {n m : Type*} (P : Matrix m n ℝ) : Prop :=
  P * P = P

end Surrogate
