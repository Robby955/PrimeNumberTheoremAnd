import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.VerticalDecay

/-!
# Kadiri Gamma vertical decay compatibility wrappers

The reusable critical-line Gamma estimates live in
`PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.VerticalDecay`.
This sidecar keeps the historical Kadiri declaration names stable.
-/

namespace Kadiri

open Complex Real

/-- Exact critical-line identity:
`‖Γ(1/2+iτ)‖² = π / cosh(πτ)`. -/
theorem gamma_half_vertical_norm_sq (τ : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * τ) :=
  Complex.gamma_half_vertical_norm_sq τ

/-- Critical-line Gamma decay:
`‖Γ(1/2+iτ)‖ ≤ √(2π) exp(-π|τ|/2)`. -/
theorem gamma_half_vertical_norm_le_exp (τ : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤
      Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2)) :=
  Complex.gamma_half_vertical_norm_le_exp τ

end Kadiri
