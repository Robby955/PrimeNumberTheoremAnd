/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaBinet

/-!
# Radial-ray phase bounds from the sharp digamma remainder

This file isolates the parts of the radial-ray Stirling phase route that are
direct consequences of the sharp second-Binet digamma bound. The remaining
log-Gamma branch derivative and constant-pinning layer is intentionally not
declared here until it is available as a theorem.
-/

@[expose] public section

open Filter MeasureTheory Topology
open scoped Topology

namespace Complex

/-- The second-order digamma remainder. -/
noncomputable def digammaRem (z : ℂ) : ℂ :=
  digamma z - (Complex.log z - z⁻¹ / 2)

/-- Sharp full-norm A1 bound, restated for the radial-ray remainder. -/
theorem digammaRem_full_norm_bound {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re) :
    ‖digammaRem z‖ ≤ 1 / (6 * ‖z‖ ^ 2) := by
  simpa [digammaRem] using digamma_second_order_full_norm (z := z) hz

lemma norm_pos_of_re_ge_quarter {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re) :
    0 < ‖z‖ := by
  rw [norm_pos_iff]
  intro hz0
  have hzre : z.re = 0 := by simp [hz0]
  linarith

lemma ray_re_ge_quarter {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re) {t : ℝ}
    (ht : 1 ≤ t) :
    (1 / 4 : ℝ) ≤ (((t : ℂ) * z).re) := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith [mul_le_mul_of_nonneg_left hz ht0]

lemma norm_ofReal_mul_complex {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    ‖(t : ℂ) * z‖ = t * ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]

/-- A radial ray starting at `z` stays in `Re ≥ 1/4`, and its norm scales linearly. -/
theorem ray_containment {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re) {t : ℝ}
    (ht : 1 ≤ t) :
    (1 / 4 : ℝ) ≤ (((t : ℂ) * z).re) ∧ ‖(t : ℂ) * z‖ = t * ‖z‖ := by
  exact ⟨ray_re_ge_quarter hz ht,
    norm_ofReal_mul_complex (le_trans zero_le_one ht) z⟩

/--
Pointwise bound for the radial-ray digamma remainder integrand. This is the
analytic estimate needed before integrating along `t ↦ t z`.
-/
theorem norm_digammaRem_ray_le {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re) {t : ℝ}
    (ht : 1 ≤ t) :
    ‖digammaRem ((t : ℂ) * z) * z‖ ≤ 1 / (6 * ‖z‖ * t ^ 2) := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hzpos : 0 < ‖z‖ := norm_pos_of_re_ge_quarter hz
  have hray_re : (1 / 4 : ℝ) ≤ (((t : ℂ) * z).re) :=
    ray_re_ge_quarter hz ht
  have hray_norm : ‖(t : ℂ) * z‖ = t * ‖z‖ :=
    norm_ofReal_mul_complex ht0 z
  have hA1 := digammaRem_full_norm_bound (z := (t : ℂ) * z) hray_re
  have hmul := mul_le_mul_of_nonneg_right hA1 (norm_nonneg z)
  calc
    ‖digammaRem ((t : ℂ) * z) * z‖
        = ‖digammaRem ((t : ℂ) * z)‖ * ‖z‖ := by
          rw [norm_mul]
    _ ≤ (1 / (6 * ‖(t : ℂ) * z‖ ^ 2)) * ‖z‖ := hmul
    _ = 1 / (6 * ‖z‖ * t ^ 2) := by
          rw [hray_norm]
          field_simp [hzpos.ne', htpos.ne']

/-- Same ray estimate, with the majorant written in the form used by improper integrals. -/
theorem norm_digammaRem_ray_le_rpow {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re) {t : ℝ}
    (ht : 1 ≤ t) :
    ‖digammaRem ((t : ℂ) * z) * z‖ ≤
      (1 / (6 * ‖z‖)) * t ^ (-(2 : ℝ)) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hzpos : 0 < ‖z‖ := norm_pos_of_re_ge_quarter hz
  have h := norm_digammaRem_ray_le (z := z) hz ht
  convert h using 1
  rw [Real.rpow_neg htpos.le, Real.rpow_two]
  field_simp [hzpos.ne', htpos.ne']

lemma integrableOn_ray_majorant {z : ℂ} (_hz : (1 / 4 : ℝ) ≤ z.re) :
    IntegrableOn (fun t : ℝ => (1 / (6 * ‖z‖)) * t ^ (-(2 : ℝ)))
      (Set.Ici (1 : ℝ)) volume := by
  have hIoi : IntegrableOn (fun t : ℝ => (1 / (6 * ‖z‖)) * t ^ (-(2 : ℝ)))
      (Set.Ioi (1 : ℝ)) volume :=
    (integrableOn_Ioi_rpow_of_lt (a := (-(2 : ℝ))) (c := (1 : ℝ)) (by norm_num)
      zero_lt_one).const_mul (1 / (6 * ‖z‖))
  exact (integrableOn_Ici_iff_integrableOn_Ioi
    (f := fun t : ℝ => (1 / (6 * ‖z‖)) * t ^ (-(2 : ℝ))) (b := (1 : ℝ))).2 hIoi

lemma continuousOn_digammaRem_ray {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re) :
    ContinuousOn (fun t : ℝ => digammaRem ((t : ℂ) * z) * z) (Set.Ici (1 : ℝ)) := by
  intro t ht
  have ht1 : 1 ≤ t := ht
  have hre_ge : (1 / 4 : ℝ) ≤ (((t : ℂ) * z).re) := ray_re_ge_quarter hz ht1
  have hre_pos : 0 < (((t : ℂ) * z).re) := by linarith
  have hwcont : ContinuousAt (fun u : ℝ => (u : ℂ) * z) t := by fun_prop
  have hdigamma : ContinuousAt (fun u : ℝ => digamma ((u : ℂ) * z)) t :=
    by
      change Tendsto (fun u : ℝ => digamma ((u : ℂ) * z)) (𝓝 t)
        (𝓝 (digamma ((t : ℂ) * z)))
      exact (continuousAt_digamma_of_re_pos hre_pos).tendsto.comp hwcont.tendsto
  have hslit : ((t : ℂ) * z) ∈ slitPlane := Or.inl hre_pos
  have hlog : ContinuousAt (fun u : ℝ => Complex.log ((u : ℂ) * z)) t :=
    hwcont.clog hslit
  have hne : ((t : ℂ) * z) ≠ 0 := slitPlane_ne_zero hslit
  have hinv : ContinuousAt (fun u : ℝ => (((u : ℂ) * z)⁻¹ / 2)) t :=
    (hwcont.inv₀ hne).div_const 2
  have hbase :
      ContinuousAt
        (fun u : ℝ =>
          (digamma ((u : ℂ) * z) - (Complex.log ((u : ℂ) * z) - (((u : ℂ) * z)⁻¹ / 2))) *
            z) t :=
    (hdigamma.sub (hlog.sub hinv)).mul continuousAt_const
  simpa [digammaRem] using hbase.continuousWithinAt

/-- The radial-ray digamma remainder integrand is integrable on `[1, ∞)`. -/
theorem integrableOn_digammaRem_ray {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re) :
    IntegrableOn (fun t : ℝ => digammaRem ((t : ℂ) * z) * z)
      (Set.Ici (1 : ℝ)) volume := by
  have hmaj := integrableOn_ray_majorant (z := z) hz
  have hmeas : AEStronglyMeasurable (fun t : ℝ => digammaRem ((t : ℂ) * z) * z)
      (volume.restrict (Set.Ici (1 : ℝ))) :=
    (continuousOn_digammaRem_ray (z := z) hz).aestronglyMeasurable measurableSet_Ici
  exact hmaj.mono' hmeas (by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    exact norm_digammaRem_ray_le_rpow (z := z) hz ht)

lemma integral_ray_majorant {z : ℂ} (_hz : (1 / 4 : ℝ) ≤ z.re) :
    ∫ t in Set.Ici (1 : ℝ), (1 / (6 * ‖z‖)) * t ^ (-(2 : ℝ)) =
      1 / (6 * ‖z‖) := by
  rw [integral_Ici_eq_integral_Ioi, MeasureTheory.integral_const_mul,
    integral_Ioi_rpow_of_lt]
  · norm_num [Real.one_rpow]
  · norm_num
  · exact zero_lt_one

/-- Integral norm bound for the radial-ray digamma remainder. -/
theorem norm_integral_rem_le {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re) :
    ‖∫ t in Set.Ici (1 : ℝ), digammaRem ((t : ℂ) * z) * z‖ ≤
      1 / (6 * ‖z‖) := by
  have hnorm := MeasureTheory.norm_integral_le_integral_norm
    (μ := volume.restrict (Set.Ici (1 : ℝ)))
    (f := fun t : ℝ => digammaRem ((t : ℂ) * z) * z)
  have hmono :
      ∫ t in Set.Ici (1 : ℝ), ‖digammaRem ((t : ℂ) * z) * z‖ ≤
        ∫ t in Set.Ici (1 : ℝ), (1 / (6 * ‖z‖)) * t ^ (-(2 : ℝ)) := by
    exact MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict (Set.Ici (1 : ℝ)))
      (f := fun t : ℝ => ‖digammaRem ((t : ℂ) * z) * z‖)
      (g := fun t : ℝ => (1 / (6 * ‖z‖)) * t ^ (-(2 : ℝ)))
      (Filter.Eventually.of_forall fun t => norm_nonneg (digammaRem ((t : ℂ) * z) * z))
      (integrableOn_ray_majorant (z := z) hz)
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
        exact norm_digammaRem_ray_le_rpow (z := z) hz ht)
  calc
    ‖∫ t in Set.Ici (1 : ℝ), digammaRem ((t : ℂ) * z) * z‖
        ≤ ∫ t in Set.Ici (1 : ℝ), ‖digammaRem ((t : ℂ) * z) * z‖ := hnorm
    _ ≤ ∫ t in Set.Ici (1 : ℝ), (1 / (6 * ‖z‖)) * t ^ (-(2 : ℝ)) := hmono
    _ = 1 / (6 * ‖z‖) := integral_ray_majorant (z := z) hz

end Complex
