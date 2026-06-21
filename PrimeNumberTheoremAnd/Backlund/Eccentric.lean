/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Eccentric Backlund route constants

This file records small arithmetic pieces for the local eccentric-Jensen Backlund
route. The analytic Phragmen-Lindelöf, Jensen, and pairing inputs are separate
from these final numeric weakenings.
-/

open Real

namespace Backlund

/-- The high-height RHS supplied by the eccentric-Jensen route. -/
noncomputable def eccentricHighRhs (T : ℝ) : ℝ :=
  0.120 * Real.log T + 0.275 * Real.log (Real.log T) + 5.13

/-- Kadiri's published Backlund RHS in the project convention. -/
noncomputable def kadiriRhs (T : ℝ) : ℝ :=
  riemannZeta.RvM 0.137 0.443 6.1 T

/--
At the high-height cutoff from the eccentric-Jensen route, the sharper local RHS is
bounded by Kadiri's published RHS.
-/
theorem eccentricHighRhs_le_kadiriRhs {T : ℝ} (hT : (6800000 : ℝ) ≤ T) :
    eccentricHighRhs T ≤ kadiriRhs T := by
  unfold eccentricHighRhs kadiriRhs riemannZeta.RvM
  have hT_one : (1 : ℝ) ≤ T := by linarith
  have hlog_nonneg : 0 ≤ Real.log T := Real.log_nonneg hT_one
  have hlog_ge_one : (1 : ℝ) ≤ Real.log T := by
    have hexp6800000 : Real.exp (1 : ℝ) ≤ (6800000 : ℝ) := by
      linarith [Real.exp_one_lt_d9]
    have hexp : Real.exp (1 : ℝ) ≤ T := le_trans hexp6800000 hT
    exact (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < T)).2 hexp
  have hloglog_nonneg : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hlog_ge_one
  have h1 : (0.120 : ℝ) * Real.log T ≤ 0.137 * Real.log T :=
    mul_le_mul_of_nonneg_right (by norm_num : (0.120 : ℝ) ≤ 0.137) hlog_nonneg
  have h2 :
      (0.275 : ℝ) * Real.log (Real.log T) ≤ 0.443 * Real.log (Real.log T) :=
    mul_le_mul_of_nonneg_right (by norm_num : (0.275 : ℝ) ≤ 0.443) hloglog_nonneg
  have h3 : (5.13 : ℝ) ≤ 6.1 := by norm_num
  linarith

/--
Hadamard three-lines for a function after division by a supplied nonzero
normalizer. This is the reusable PL-log shell: the concrete shifted log-power
normalizer is a separate input.
-/
theorem log_phragmen_lindelof_normalized {f normalizer : ℂ → ℂ}
    {σ₀ σ₁ C₀ C₁ : ℝ} {z : ℂ} (hσ : σ₀ < σ₁)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)
    (hnormalizer :
      ∀ w ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁, normalizer w ≠ 0)
    (hd : DiffContOnCl ℂ (fun w => f w / normalizer w)
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁))
    (hB : BddAbove (Set.image (fun w => ‖f w / normalizer w‖)
      (Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)))
    (hleft : ∀ w : ℂ, w.re = σ₀ → ‖f w‖ ≤ C₀ * ‖normalizer w‖)
    (hright : ∀ w : ℂ, w.re = σ₁ → ‖f w‖ ≤ C₁ * ‖normalizer w‖) :
    ‖f z‖ ≤
      (C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
        C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀))) * ‖normalizer z‖ := by
  have hleft' :
      ∀ w ∈ Complex.re ⁻¹' ({σ₀} : Set ℝ), ‖f w / normalizer w‖ ≤ C₀ := by
    intro w hw
    have hwre : w.re = σ₀ := by simpa using hw
    have hwstrip : w ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁ := by
      simp [Complex.HadamardThreeLines.verticalClosedStrip, hwre, hσ.le]
    have hnorm_pos : 0 < ‖normalizer w‖ :=
      norm_pos_iff.mpr (hnormalizer w hwstrip)
    rw [norm_div]
    exact (div_le_iff₀ hnorm_pos).2 (hleft w hwre)
  have hright' :
      ∀ w ∈ Complex.re ⁻¹' ({σ₁} : Set ℝ), ‖f w / normalizer w‖ ≤ C₁ := by
    intro w hw
    have hwre : w.re = σ₁ := by simpa using hw
    have hwstrip : w ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁ := by
      simp [Complex.HadamardThreeLines.verticalClosedStrip, hwre, hσ.le]
    have hnorm_pos : 0 < ‖normalizer w‖ :=
      norm_pos_iff.mpr (hnormalizer w hwstrip)
    rw [norm_div]
    exact (div_le_iff₀ hnorm_pos).2 (hright w hwre)
  have hnorm :
      ‖f z / normalizer z‖ ≤
        C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
          C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀)) :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (f := fun w => f w / normalizer w) (z := z) (a := C₀) (b := C₁)
      (l := σ₀) (u := σ₁) hσ hz hd hB hleft' hright'
  have hnormalizer_z : normalizer z ≠ 0 := hnormalizer z hz
  have hmul : ‖f z / normalizer z‖ * ‖normalizer z‖ = ‖f z‖ := by
    rw [norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hnormalizer_z)]
  rw [← hmul]
  exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg (normalizer z))

end Backlund
