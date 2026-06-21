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

/-- A point with real part greater than one has nonzero principal complex log. -/
theorem log_ne_zero_of_one_lt_re {z : ℂ} (hz : (1 : ℝ) < z.re) :
    Complex.log z ≠ 0 := by
  intro hlog
  have hnorm : (1 : ℝ) < ‖z‖ := lt_of_lt_of_le hz (Complex.re_le_norm z)
  have hlog_pos : (0 : ℝ) < Real.log ‖z‖ := Real.log_pos hnorm
  have hlog_re : (Complex.log z).re = 0 := by rw [hlog]; simp
  rw [Complex.log_re] at hlog_re
  linarith

/-- On a shifted vertical closed strip with positive real part, `Q + z` is in the slit plane. -/
theorem shifted_mem_slitPlane_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (0 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    (Q : ℂ) + z ∈ Complex.slitPlane := by
  refine Or.inl ?_
  have hzre : σ₀ ≤ z.re := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.1
  have hpos : (0 : ℝ) < Q + z.re := by nlinarith
  simpa using hpos

/-- On a shifted vertical closed strip with `Q + σ₀ > 1`, `log (Q + z)` is nonzero. -/
theorem shifted_log_ne_zero_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (1 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    Complex.log ((Q : ℂ) + z) ≠ 0 := by
  apply log_ne_zero_of_one_lt_re
  have hzre : σ₀ ≤ z.re := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.1
  have hpos : (1 : ℝ) < Q + z.re := by nlinarith
  simpa using hpos

/-- On a shifted vertical closed strip with `Q + σ₀ > 1`, `log (Q + z)` is in the slit plane. -/
theorem shifted_log_mem_slitPlane_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (1 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    Complex.log ((Q : ℂ) + z) ∈ Complex.slitPlane := by
  refine Or.inl ?_
  rw [Complex.log_re]
  apply Real.log_pos
  have hzre : σ₀ ≤ z.re := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.1
  have hpos : (1 : ℝ) < (((Q : ℂ) + z).re) := by
    simp
    nlinarith
  exact lt_of_lt_of_le hpos (Complex.re_le_norm _)

/-- The closure of a Hadamard open vertical strip is the corresponding closed strip. -/
theorem verticalStrip_closure_eq_verticalClosedStrip {σ₀ σ₁ : ℝ} (hσ : σ₀ ≠ σ₁) :
    closure (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁) =
      Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁ := by
  rw [Complex.HadamardThreeLines.verticalStrip, Complex.HadamardThreeLines.verticalClosedStrip,
    Complex.closure_preimage_re, closure_Ioo hσ]

/-- The shifted principal log is differentiable on a positive-real-part vertical strip. -/
theorem shifted_log_diffContOnCl_on_verticalStrip {Q σ₀ σ₁ : ℝ}
    (hσ : σ₀ < σ₁) (hQ : (0 : ℝ) < Q + σ₀) :
    DiffContOnCl ℂ (fun z : ℂ => Complex.log ((Q : ℂ) + z))
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁) := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [verticalStrip_closure_eq_verticalClosedStrip hσ.ne]
  exact ((differentiableOn_const (Q : ℂ)).add differentiableOn_id).clog
    (fun z hz => shifted_mem_slitPlane_on_verticalClosedStrip hQ hz)

/-- Constant complex powers of `Q + z` are differentiable on a positive shifted strip. -/
theorem shifted_cpow_const_diffContOnCl_on_verticalStrip {Q σ₀ σ₁ : ℝ} (c : ℂ)
    (hσ : σ₀ < σ₁) (hQ : (0 : ℝ) < Q + σ₀) :
    DiffContOnCl ℂ (fun z : ℂ => ((Q : ℂ) + z) ^ c)
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁) := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [verticalStrip_closure_eq_verticalClosedStrip hσ.ne]
  exact ((differentiableOn_const (Q : ℂ)).add differentiableOn_id).cpow_const
    (fun z hz => shifted_mem_slitPlane_on_verticalClosedStrip hQ hz)

/-- Constant complex powers of `log (Q + z)` are differentiable on a shifted strip. -/
theorem shifted_log_cpow_const_diffContOnCl_on_verticalStrip {Q σ₀ σ₁ : ℝ} (c : ℂ)
    (hσ : σ₀ < σ₁) (hQ : (1 : ℝ) < Q + σ₀) :
    DiffContOnCl ℂ (fun z : ℂ => (Complex.log ((Q : ℂ) + z)) ^ c)
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁) := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [verticalStrip_closure_eq_verticalClosedStrip hσ.ne]
  have hQ0 : (0 : ℝ) < Q + σ₀ := by linarith
  exact (((differentiableOn_const (Q : ℂ)).add differentiableOn_id).clog
    (fun z hz => shifted_mem_slitPlane_on_verticalClosedStrip hQ0 hz)).cpow_const
    (fun z hz => shifted_log_mem_slitPlane_on_verticalClosedStrip hQ hz)

/-- The shifted log-power normalizer used by the PL-log interpolation shell. -/
noncomputable def shiftedLogPowerNormalizer (Q : ℝ) (α β : ℂ) (z : ℂ) : ℂ :=
  ((Q : ℂ) + z) ^ α * (Complex.log ((Q : ℂ) + z)) ^ β

/-- For real exponent weights, the normalizer norm is the expected product of real powers. -/
theorem norm_shiftedLogPowerNormalizer_ofReal (Q α β : ℝ) (z : ℂ) :
    ‖shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) z‖ =
      ‖(Q : ℂ) + z‖ ^ α * ‖Complex.log ((Q : ℂ) + z)‖ ^ β := by
  unfold shiftedLogPowerNormalizer
  rw [norm_mul]
  simp

/-- The shifted log-power normalizer is nonzero on shifted strips with `Q + σ₀ > 1`. -/
theorem shiftedLogPowerNormalizer_ne_zero_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ}
    (α β : ℂ) {z : ℂ} (hQ : (1 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    shiftedLogPowerNormalizer Q α β z ≠ 0 := by
  unfold shiftedLogPowerNormalizer
  refine mul_ne_zero ?_ ?_
  · rw [Complex.cpow_ne_zero_iff]
    have hQ0 : (0 : ℝ) < Q + σ₀ := by linarith
    exact Or.inl (Complex.slitPlane_ne_zero
      (shifted_mem_slitPlane_on_verticalClosedStrip hQ0 hz))
  · rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (Complex.slitPlane_ne_zero
      (shifted_log_mem_slitPlane_on_verticalClosedStrip hQ hz))

/-- The shifted log-power normalizer is differentiable on shifted positive strips. -/
theorem shiftedLogPowerNormalizer_diffContOnCl_on_verticalStrip {Q σ₀ σ₁ : ℝ}
    (α β : ℂ) (hσ : σ₀ < σ₁) (hQ : (1 : ℝ) < Q + σ₀) :
    DiffContOnCl ℂ (shiftedLogPowerNormalizer Q α β)
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁) := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [verticalStrip_closure_eq_verticalClosedStrip hσ.ne]
  unfold shiftedLogPowerNormalizer
  have hQ0 : (0 : ℝ) < Q + σ₀ := by linarith
  exact
    (((differentiableOn_const (Q : ℂ)).add differentiableOn_id).cpow_const
      (fun z hz => shifted_mem_slitPlane_on_verticalClosedStrip hQ0 hz)).mul
    ((((differentiableOn_const (Q : ℂ)).add differentiableOn_id).clog
      (fun z hz => shifted_mem_slitPlane_on_verticalClosedStrip hQ0 hz)).cpow_const
      (fun z hz => shifted_log_mem_slitPlane_on_verticalClosedStrip hQ hz))

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
