/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
public import PrimeNumberTheoremAnd.EulerMaclaurin2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Binet-type digamma remainder bounds

This file records the analytic estimate needed for the Binet digamma remainder kernel

`({t} - 1 / 2) * (t + s)⁻²`.

It does not introduce a logarithmic Gamma branch. It proves the reusable kernel bound,
the shifted majorant integral, integrability on `(0, ∞)`, and the resulting norm bound
for `0 < s.re`.
-/

@[expose] public section

open Filter Finset Interval MeasureTheory Nat Topology
open scoped ENNReal Topology BigOperators

namespace Complex

/-- The fractional-part kernel appearing in the Binet form of the digamma remainder. -/
noncomputable def digammaBinetRemainderKernel (s : ℂ) (t : ℝ) : ℂ :=
  ((Int.fract t - 1 / 2 : ℝ) : ℂ) * (((t : ℂ) + s)⁻¹) ^ (2 : ℕ)

/-- The first Bernoulli sawtooth kernel is bounded by `1 / 2`. -/
lemma norm_fract_sub_half_le (t : ℝ) :
    ‖((Int.fract t - 1 / 2 : ℝ) : ℂ)‖ ≤ (1 / 2 : ℝ) := by
  rw [norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [Int.fract_nonneg t, Int.fract_lt_one t]

/--
Pointwise domination of the Binet digamma remainder kernel by the shifted square
majorant.
-/
lemma norm_digammaBinetRemainderKernel_le {s : ℂ} (hs : 0 < s.re) {t : ℝ}
    (ht : 0 < t) :
    ‖digammaBinetRemainderKernel s t‖ ≤
      (1 / 2 : ℝ) * (t + s.re) ^ (-(2 : ℝ)) := by
  have hpos : 0 < t + s.re := by linarith
  have hnorm_ge : t + s.re ≤ ‖(t : ℂ) + s‖ := by
    have h := Complex.re_le_norm ((t : ℂ) + s)
    simpa [add_comm, add_left_comm, add_assoc] using h
  have hnorm_pos : 0 < ‖(t : ℂ) + s‖ := lt_of_lt_of_le hpos hnorm_ge
  have hinv : ‖(t : ℂ) + s‖⁻¹ ≤ (t + s.re)⁻¹ := by
    exact inv_anti₀ hpos hnorm_ge
  have hpow : ‖(t : ℂ) + s‖⁻¹ ^ (2 : ℕ) ≤ (t + s.re)⁻¹ ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ (inv_nonneg.mpr hnorm_pos.le) hinv 2
  have hpow_eq : (t + s.re) ^ (-(2 : ℝ)) = (t + s.re)⁻¹ ^ (2 : ℕ) := by
    rw [Real.rpow_neg hpos.le, Real.rpow_two, inv_pow]
  rw [digammaBinetRemainderKernel, norm_mul, norm_pow, norm_inv, hpow_eq]
  exact mul_le_mul (norm_fract_sub_half_le t) hpow
    (pow_nonneg (inv_nonneg.mpr hnorm_pos.le) 2) (by norm_num)

/-- The shifted square majorant is integrable on `(0, ∞)`. -/
lemma integrableOn_digammaBinetRemainderMajorant {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => (1 / 2 : ℝ) * (t + σ) ^ (-(2 : ℝ)))
      (Set.Ioi (0 : ℝ)) volume := by
  have hmp : MeasurePreserving (fun t : ℝ => t + σ) volume volume :=
    measurePreserving_add_right (volume : Measure ℝ) σ
  have hemb : MeasurableEmbedding (fun t : ℝ => t + σ) :=
    (Homeomorph.addRight σ).measurableEmbedding
  have hbase : IntegrableOn (fun u : ℝ => u ^ (-(2 : ℝ))) (Set.Ioi σ) volume :=
    integrableOn_Ioi_rpow_of_lt (a := (-(2 : ℝ))) (c := σ) (by norm_num) hσ
  have hpre : (fun t : ℝ => t + σ) ⁻¹' Set.Ioi σ = Set.Ioi (0 : ℝ) := by
    rw [Set.preimage_add_const_Ioi]
    simp
  have hcomp := (hmp.integrableOn_comp_preimage hemb
    (f := fun u : ℝ => u ^ (-(2 : ℝ))) (s := Set.Ioi σ)).2 hbase
  rw [hpre] at hcomp
  exact hcomp.const_mul (1 / 2 : ℝ)

/-- Evaluation of the shifted square majorant integral. -/
lemma integral_Ioi_digammaBinetRemainderMajorant {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in Set.Ioi (0 : ℝ), (1 / 2 : ℝ) * (t + σ) ^ (-(2 : ℝ)) =
      1 / (2 * σ) := by
  have hmp : MeasurePreserving (fun t : ℝ => t + σ) volume volume :=
    measurePreserving_add_right (volume : Measure ℝ) σ
  have hemb : MeasurableEmbedding (fun t : ℝ => t + σ) :=
    (Homeomorph.addRight σ).measurableEmbedding
  have hpre : (fun t : ℝ => t + σ) ⁻¹' Set.Ioi σ = Set.Ioi (0 : ℝ) := by
    rw [Set.preimage_add_const_Ioi]
    simp
  have hshift := hmp.setIntegral_preimage_emb hemb
    (fun u : ℝ => (1 / 2 : ℝ) * u ^ (-(2 : ℝ))) (Set.Ioi σ)
  rw [hpre] at hshift
  rw [hshift]
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt]
  · norm_num [Real.rpow_neg_one]
    ring
  · norm_num
  · exact hσ

/-- The Binet digamma remainder kernel is integrable on `(0, ∞)` for `0 < s.re`. -/
lemma integrableOn_digammaBinetRemainderKernel {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (digammaBinetRemainderKernel s) (Set.Ioi (0 : ℝ)) volume := by
  have hmaj := integrableOn_digammaBinetRemainderMajorant (σ := s.re) hs
  have hmeas : AEStronglyMeasurable (digammaBinetRemainderKernel s)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hmeas' : Measurable (digammaBinetRemainderKernel s) := by
      unfold digammaBinetRemainderKernel
      exact ((measurable_fract.sub measurable_const).complex_ofReal.mul (by fun_prop))
    exact hmeas'.aestronglyMeasurable
  exact hmaj.mono' hmeas (by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_digammaBinetRemainderKernel_le hs ht)

/--
Norm bound for the integral of the Binet digamma remainder kernel. This is the
current closed support theorem for the future Binet-to-digamma identity.
-/
lemma norm_integral_digammaBinetRemainderKernel_le {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi (0 : ℝ), digammaBinetRemainderKernel s t‖ ≤ 1 / (2 * s.re) := by
  have hnorm := MeasureTheory.norm_integral_le_integral_norm
    (μ := volume.restrict (Set.Ioi (0 : ℝ))) (f := digammaBinetRemainderKernel s)
  have hmono : ∫ t in Set.Ioi (0 : ℝ), ‖digammaBinetRemainderKernel s t‖ ≤
      ∫ t in Set.Ioi (0 : ℝ), (1 / 2 : ℝ) * (t + s.re) ^ (-(2 : ℝ)) := by
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => norm_nonneg (digammaBinetRemainderKernel s t))
      (integrableOn_digammaBinetRemainderMajorant (σ := s.re) hs)
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        exact norm_digammaBinetRemainderKernel_le hs ht)
  calc
    ‖∫ t in Set.Ioi (0 : ℝ), digammaBinetRemainderKernel s t‖
        ≤ ∫ t in Set.Ioi (0 : ℝ), ‖digammaBinetRemainderKernel s t‖ := hnorm
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), (1 / 2 : ℝ) * (t + s.re) ^ (-(2 : ℝ)) := hmono
    _ = 1 / (2 * s.re) := integral_Ioi_digammaBinetRemainderMajorant hs

/-- The second-order Binet remainder kernel coming from the EM2 remainder term. -/
noncomputable def digammaBinetSecondOrderRemainderKernel (s : ℂ) (t : ℝ) : ℂ :=
  (2 : ℂ) * bernoulli2PeriodizedHalf t * (((t : ℂ) + s)⁻¹) ^ (3 : ℕ)

/-- Pointwise domination of the second-order Binet remainder kernel. -/
lemma norm_digammaBinetSecondOrderRemainderKernel_le {s : ℂ} (hs : 0 < s.re) {t : ℝ}
    (ht : 0 < t) :
    ‖digammaBinetSecondOrderRemainderKernel s t‖ ≤
      (1 / 6 : ℝ) * (t + s.re) ^ (-(3 : ℝ)) := by
  have hpos : 0 < t + s.re := by linarith
  have hnorm_ge : t + s.re ≤ ‖(t : ℂ) + s‖ := by
    have h := Complex.re_le_norm ((t : ℂ) + s)
    simpa [add_comm, add_left_comm, add_assoc] using h
  have hnorm_pos : 0 < ‖(t : ℂ) + s‖ := lt_of_lt_of_le hpos hnorm_ge
  have hinv : ‖(t : ℂ) + s‖⁻¹ ≤ (t + s.re)⁻¹ := by
    exact inv_anti₀ hpos hnorm_ge
  have hpow : ‖(t : ℂ) + s‖⁻¹ ^ (3 : ℕ) ≤ (t + s.re)⁻¹ ^ (3 : ℕ) := by
    exact pow_le_pow_left₀ (inv_nonneg.mpr hnorm_pos.le) hinv 3
  have hpow_eq : (t + s.re) ^ (-(3 : ℝ)) = (t + s.re)⁻¹ ^ (3 : ℕ) := by
    have hnat : (t + s.re) ^ (3 : ℝ) = (t + s.re) ^ (3 : ℕ) := by
      exact Real.rpow_natCast (t + s.re) 3
    rw [Real.rpow_neg hpos.le]
    rw [hnat]
    exact (inv_pow (t + s.re) 3).symm
  calc
    ‖digammaBinetSecondOrderRemainderKernel s t‖
        = 2 * ‖bernoulli2PeriodizedHalf t‖ * ‖(t : ℂ) + s‖⁻¹ ^ (3 : ℕ) := by
          rw [digammaBinetSecondOrderRemainderKernel, norm_mul, norm_mul, norm_pow, norm_inv]
          norm_num
    _ ≤ 2 * (1 / 12 : ℝ) * ((t + s.re)⁻¹ ^ (3 : ℕ)) := by
          gcongr
          exact norm_bernoulli2PeriodizedHalf_le t
    _ = (1 / 6 : ℝ) * (t + s.re) ^ (-(3 : ℝ)) := by
          rw [hpow_eq]
          ring

/-- The shifted cubic majorant is integrable on `(0, ∞)`. -/
lemma integrableOn_digammaBinetSecondOrderRemainderMajorant {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => (1 / 6 : ℝ) * (t + σ) ^ (-(3 : ℝ)))
      (Set.Ioi (0 : ℝ)) volume := by
  have hmp : MeasurePreserving (fun t : ℝ => t + σ) volume volume :=
    measurePreserving_add_right (volume : Measure ℝ) σ
  have hemb : MeasurableEmbedding (fun t : ℝ => t + σ) :=
    (Homeomorph.addRight σ).measurableEmbedding
  have hbase : IntegrableOn (fun u : ℝ => u ^ (-(3 : ℝ))) (Set.Ioi σ) volume :=
    integrableOn_Ioi_rpow_of_lt (a := (-(3 : ℝ))) (c := σ) (by norm_num) hσ
  have hpre : (fun t : ℝ => t + σ) ⁻¹' Set.Ioi σ = Set.Ioi (0 : ℝ) := by
    rw [Set.preimage_add_const_Ioi]
    simp
  have hcomp := (hmp.integrableOn_comp_preimage hemb
    (f := fun u : ℝ => u ^ (-(3 : ℝ))) (s := Set.Ioi σ)).2 hbase
  rw [hpre] at hcomp
  exact hcomp.const_mul (1 / 6 : ℝ)

/-- Evaluation of the shifted cubic majorant integral. -/
lemma integral_Ioi_digammaBinetSecondOrderRemainderMajorant {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in Set.Ioi (0 : ℝ), (1 / 6 : ℝ) * (t + σ) ^ (-(3 : ℝ)) =
      1 / (12 * σ ^ 2) := by
  have hmp : MeasurePreserving (fun t : ℝ => t + σ) volume volume :=
    measurePreserving_add_right (volume : Measure ℝ) σ
  have hemb : MeasurableEmbedding (fun t : ℝ => t + σ) :=
    (Homeomorph.addRight σ).measurableEmbedding
  have hpre : (fun t : ℝ => t + σ) ⁻¹' Set.Ioi σ = Set.Ioi (0 : ℝ) := by
    rw [Set.preimage_add_const_Ioi]
    simp
  have hshift := hmp.setIntegral_preimage_emb hemb
    (fun u : ℝ => (1 / 6 : ℝ) * u ^ (-(3 : ℝ))) (Set.Ioi σ)
  rw [hpre] at hshift
  rw [hshift]
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt]
  · norm_num
    field_simp [ne_of_gt hσ]
    ring
  · norm_num
  · exact hσ

/-- The second-order Binet remainder kernel is integrable on `(0, ∞)` for `0 < s.re`. -/
lemma integrableOn_digammaBinetSecondOrderRemainderKernel {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (digammaBinetSecondOrderRemainderKernel s) (Set.Ioi (0 : ℝ)) volume := by
  have hmaj := integrableOn_digammaBinetSecondOrderRemainderMajorant (σ := s.re) hs
  have hmeas : AEStronglyMeasurable (digammaBinetSecondOrderRemainderKernel s)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hmeas' : Measurable (digammaBinetSecondOrderRemainderKernel s) := by
      unfold digammaBinetSecondOrderRemainderKernel
      have htail : Measurable (fun t : ℝ => (((t : ℂ) + s)⁻¹) ^ (3 : ℕ)) := by
        fun_prop
      exact (measurable_const.mul continuous_bernoulli2PeriodizedHalf.measurable).mul htail
    exact hmeas'.aestronglyMeasurable
  exact hmaj.mono' hmeas (by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_digammaBinetSecondOrderRemainderKernel_le hs ht)

/-- Norm bound for the integral of the second-order Binet remainder kernel. -/
lemma norm_integral_digammaBinetSecondOrderRemainderKernel_le {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t‖ ≤
      1 / (12 * s.re ^ 2) := by
  have hnorm := MeasureTheory.norm_integral_le_integral_norm
    (μ := volume.restrict (Set.Ioi (0 : ℝ))) (f := digammaBinetSecondOrderRemainderKernel s)
  have hmono : ∫ t in Set.Ioi (0 : ℝ), ‖digammaBinetSecondOrderRemainderKernel s t‖ ≤
      ∫ t in Set.Ioi (0 : ℝ), (1 / 6 : ℝ) * (t + s.re) ^ (-(3 : ℝ)) := by
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => norm_nonneg (digammaBinetSecondOrderRemainderKernel s t))
      (integrableOn_digammaBinetSecondOrderRemainderMajorant (σ := s.re) hs)
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        exact norm_digammaBinetSecondOrderRemainderKernel_le hs ht)
  calc
    ‖∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t‖
        ≤ ∫ t in Set.Ioi (0 : ℝ), ‖digammaBinetSecondOrderRemainderKernel s t‖ := hnorm
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), (1 / 6 : ℝ) * (t + s.re) ^ (-(3 : ℝ)) := hmono
    _ = 1 / (12 * s.re ^ 2) :=
      integral_Ioi_digammaBinetSecondOrderRemainderMajorant hs

/-!
## Positive second-Binet kernel estimates

These lemmas are independent of the Binet identity itself. They prove the full-norm
majorant for the DLMF 5.9.15 kernel after normalizing by `‖z‖ ^ 2`.
-/

/-- Rational lower proxy for `π` used in the exponential majorant. -/
noncomputable def digammaBinetA0 : ℝ := (157 : ℝ) / 50

lemma digammaBinetA0_pos : 0 < digammaBinetA0 := by
  norm_num [digammaBinetA0]

lemma digammaBinetA0_le_pi : digammaBinetA0 ≤ Real.pi := by
  have hpi := Real.pi_gt_d2
  norm_num [digammaBinetA0] at hpi ⊢
  exact hpi.le

/-- Squared norm of the quadratic denominator in the second Binet kernel. -/
lemma norm_sq_add_real_sq_sq (z : ℂ) (t : ℝ) :
    ‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖ ^ 2 =
      (t ^ 2 - ‖z‖ ^ 2) ^ 2 + 4 * z.re ^ 2 * t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  rw [← Complex.normSq_eq_norm_sq z]
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, pow_two]
  ring_nf

lemma two_mul_re_mul_le_norm_sq_add_real_sq {z : ℂ} {t : ℝ}
    (hx : 0 ≤ z.re) (ht : 0 ≤ t) :
    2 * z.re * t ≤ ‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖ := by
  have hsq := norm_sq_add_real_sq_sq z t
  have hnonneg : 0 ≤ 2 * z.re * t := by positivity
  have hle_sq : (2 * z.re * t) ^ 2 ≤
      ‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (t ^ 2 - ‖z‖ ^ 2)]
  have habs := sq_le_sq.mp hle_sq
  rwa [abs_of_nonneg hnonneg, abs_of_nonneg (norm_nonneg _)] at habs

lemma norm_sq_le_norm_sq_add_real_sq_add {z : ℂ} {t : ℝ} :
    ‖z‖ ^ 2 ≤ ‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖ + t ^ 2 := by
  have htri := norm_sub_le (z ^ 2 + ((t ^ 2 : ℝ) : ℂ)) (((t ^ 2 : ℝ) : ℂ))
  have hrewrite : (z ^ 2 + ((t ^ 2 : ℝ) : ℂ) - ((t ^ 2 : ℝ) : ℂ)) = z ^ 2 := by
    ring
  rw [hrewrite] at htri
  rw [norm_pow] at htri
  norm_num at htri
  have ht2 : ‖((t ^ 2 : ℝ) : ℂ)‖ = t ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
  simpa [ht2] using htri

lemma two_mul_re_mul_norm_sq_mul_le {z : ℂ} {t : ℝ}
    (hx : 0 ≤ z.re) (ht : 0 ≤ t) :
    2 * z.re * ‖z‖ ^ 2 * t ≤
      (2 * z.re * t + t ^ 2) * ‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖ := by
  let D : ℝ := ‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖
  have h2 : 2 * z.re * t ≤ D := by
    simpa [D] using two_mul_re_mul_le_norm_sq_add_real_sq (z := z) (t := t) hx ht
  have h3 : ‖z‖ ^ 2 ≤ D + t ^ 2 := by
    simpa [D] using norm_sq_le_norm_sq_add_real_sq_add (z := z) (t := t)
  have h2nonneg : 0 ≤ 2 * z.re * t := by positivity
  calc
    2 * z.re * ‖z‖ ^ 2 * t = (2 * z.re * t) * ‖z‖ ^ 2 := by ring
    _ ≤ (2 * z.re * t) * (D + t ^ 2) := by
      exact mul_le_mul_of_nonneg_left h3 h2nonneg
    _ = (2 * z.re * t) * D + (2 * z.re * t) * t ^ 2 := by ring
    _ ≤ (2 * z.re * t) * D + D * t ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg t)]
    _ = (2 * z.re * t + t ^ 2) * D := by ring

lemma norm_sq_div_norm_sq_add_real_sq_le_one_add {z : ℂ} {t : ℝ}
    (hx : 0 < z.re) (ht : 0 < t) :
    ‖z‖ ^ 2 / ‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖ ≤ 1 + t / (2 * z.re) := by
  let D : ℝ := ‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖
  have h2 : 2 * z.re * t ≤ D := by
    simpa [D] using two_mul_re_mul_le_norm_sq_add_real_sq (z := z) (t := t) hx.le ht.le
  have hDpos : 0 < D := by
    have hleft : 0 < 2 * z.re * t := by positivity
    exact lt_of_lt_of_le hleft h2
  have hcross := two_mul_re_mul_norm_sq_mul_le (z := z) (t := t) hx.le ht.le
  have hdivD : (2 * z.re * ‖z‖ ^ 2 * t) / D ≤ 2 * z.re * t + t ^ 2 := by
    rw [div_le_iff₀ hDpos]
    simpa [D] using hcross
  have hpos : 0 < 2 * z.re * t := by positivity
  have hdiv2 : ((2 * z.re * ‖z‖ ^ 2 * t) / D) / (2 * z.re * t) ≤
      (2 * z.re * t + t ^ 2) / (2 * z.re * t) := by
    exact div_le_div_of_nonneg_right hdivD hpos.le
  calc
    ‖z‖ ^ 2 / ‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖
        = ((2 * z.re * ‖z‖ ^ 2 * t) / D) / (2 * z.re * t) := by
          field_simp [D, hx.ne', ht.ne', hDpos.ne']
          ring
    _ ≤ (2 * z.re * t + t ^ 2) / (2 * z.re * t) := hdiv2
    _ = 1 + t / (2 * z.re) := by
          field_simp [hx.ne', ht.ne']

lemma two_mul_mul_exp_le_exp_two_sub_one {u : ℝ} (hu : 0 ≤ u) :
    2 * u * Real.exp u ≤ Real.exp (2 * u) - 1 := by
  have hsinh : u ≤ Real.sinh u := (Real.self_le_sinh_iff).2 hu
  have hmul := mul_le_mul_of_nonneg_right hsinh (show 0 ≤ 2 * Real.exp u by positivity)
  rw [Real.sinh_eq] at hmul
  have hright :
      (Real.exp u - Real.exp (-u)) / 2 * (2 * Real.exp u) =
        Real.exp (2 * u) - 1 := by
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero u]
    rw [sq]
    rw [← Real.exp_add]
    ring_nf
  have hleft : u * (2 * Real.exp u) = 2 * u * Real.exp u := by ring
  rwa [hleft, hright] at hmul

lemma two_mul_a0_mul_exp_le_exp_two_pi_sub_one {t : ℝ} (ht : 0 ≤ t) :
    2 * digammaBinetA0 * t * Real.exp (digammaBinetA0 * t) ≤
      Real.exp (2 * Real.pi * t) - 1 := by
  have ha0_nonneg : 0 ≤ digammaBinetA0 := digammaBinetA0_pos.le
  have hbase := two_mul_mul_exp_le_exp_two_sub_one
    (u := digammaBinetA0 * t) (mul_nonneg ha0_nonneg ht)
  have hmono : Real.exp (2 * (digammaBinetA0 * t)) - 1 ≤
      Real.exp (2 * Real.pi * t) - 1 := by
    have harg : 2 * (digammaBinetA0 * t) ≤ 2 * Real.pi * t := by
      nlinarith [digammaBinetA0_le_pi, ht]
    have hexp := Real.exp_le_exp.mpr harg
    linarith
  calc
    2 * digammaBinetA0 * t * Real.exp (digammaBinetA0 * t)
        = 2 * (digammaBinetA0 * t) * Real.exp (digammaBinetA0 * t) := by ring
    _ ≤ Real.exp (2 * (digammaBinetA0 * t)) - 1 := hbase
    _ ≤ Real.exp (2 * Real.pi * t) - 1 := hmono

lemma exp_two_pi_mul_sub_one_pos {t : ℝ} (ht : 0 < t) :
    0 < Real.exp (2 * Real.pi * t) - 1 := by
  rw [sub_pos]
  exact Real.one_lt_exp_iff.mpr (by positivity)

lemma two_mul_div_exp_two_pi_sub_one_le {t : ℝ} (ht : 0 < t) :
    (2 * t) / (Real.exp (2 * Real.pi * t) - 1) ≤
      Real.exp (-(digammaBinetA0 * t)) / digammaBinetA0 := by
  have hEpos := exp_two_pi_mul_sub_one_pos ht
  rw [div_le_iff₀ hEpos]
  let c : ℝ := Real.exp (-(digammaBinetA0 * t)) / digammaBinetA0
  have hc_nonneg : 0 ≤ c := by
    exact div_nonneg (Real.exp_pos _).le digammaBinetA0_pos.le
  have hineq := two_mul_a0_mul_exp_le_exp_two_pi_sub_one (t := t) ht.le
  have hmul := mul_le_mul_of_nonneg_left hineq hc_nonneg
  have hleft :
      c * (2 * digammaBinetA0 * t * Real.exp (digammaBinetA0 * t)) = 2 * t := by
    dsimp [c]
    field_simp [digammaBinetA0_pos.ne', Real.exp_ne_zero (digammaBinetA0 * t)]
    rw [← Real.exp_add]
    ring_nf
    rw [Real.exp_zero]
  calc
    2 * t = c * (2 * digammaBinetA0 * t * Real.exp (digammaBinetA0 * t)) := hleft.symm
    _ ≤ c * (Real.exp (2 * Real.pi * t) - 1) := hmul
    _ = Real.exp (-(digammaBinetA0 * t)) / digammaBinetA0 *
        (Real.exp (2 * Real.pi * t) - 1) := by rfl

/-- Scaled damped sine moment on the positive half-line. -/
lemma integral_Ioi_exp_neg_mul_sin_scaled (a b : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sin (b * x) =
      b / (a ^ 2 + b ^ 2) := by
  let z : ℂ := (-(a : ℂ)) + (b : ℂ) * Complex.I
  have hzre : z.re < 0 := by simp [z, ha]
  have hint : Integrable (fun x : ℝ => Complex.exp (z * x))
      (volume.restrict (Set.Ioi 0)) := by
    exact integrableOn_exp_mul_complex_Ioi (a := z) hzre 0
  have him := integral_im (μ := volume.restrict (Set.Ioi 0)) hint
  have hpoint : (fun x : ℝ => Real.exp (-a * x) * Real.sin (b * x)) =
      fun x : ℝ => (Complex.exp (z * x)).im := by
    funext x
    simp [z, Complex.exp_im, mul_add, mul_comm, mul_left_comm]
  calc
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sin (b * x)
        = ∫ x : ℝ in Set.Ioi 0, (Complex.exp (z * x)).im := by
          rw [hpoint]
    _ = (∫ x : ℝ in Set.Ioi 0, Complex.exp (z * x)).im := by
          simpa using him
    _ = (-Complex.exp (z * (0 : ℝ)) / z).im := by
          rw [integral_exp_mul_complex_Ioi (a := z) hzre 0]
    _ = b / (a ^ 2 + b ^ 2) := by
          have hden : a ^ 2 + b ^ 2 ≠ 0 := by
            nlinarith [sq_pos_of_pos ha, sq_nonneg b]
          simp [div_eq_mul_inv, z, Complex.inv_im, Complex.normSq_apply]
          field_simp [hden]
          simp

/-- HasSum form of the geometric expansion of the positive Binet denominator. -/
lemma hasSum_exp_neg_two_pi_nat_add_one (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ => Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * t)))
      (1 / (Real.exp (2 * Real.pi * t) - 1)) := by
  let q : ℝ := Real.exp (-(2 * Real.pi * t))
  have hq_nonneg : 0 ≤ q := by positivity
  have harg_pos : 0 < 2 * Real.pi * t := by positivity
  have hq_lt_one : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    linarith
  have hterm :
      (fun n : ℕ => Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * t))) =
        fun n : ℕ => q * q ^ n := by
    funext n
    dsimp [q]
    rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    congr 1
    norm_num
    ring
  have hgeom : HasSum (fun n : ℕ => q * q ^ n) (q * (1 - q)⁻¹) := by
    exact (hasSum_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left q
  have htarget : q * (1 - q)⁻¹ = 1 / (Real.exp (2 * Real.pi * t) - 1) := by
    dsimp [q]
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero (2 * Real.pi * t),
      sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr harg_pos)).symm]
  rw [hterm]
  rwa [htarget] at hgeom

/-- Tsum form of the geometric expansion of the positive Binet denominator. -/
lemma tsum_exp_neg_two_pi_nat_add_one (t : ℝ) (ht : 0 < t) :
    (∑' n : ℕ, Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * t))) =
      1 / (Real.exp (2 * Real.pi * t) - 1) := by
  let q : ℝ := Real.exp (-(2 * Real.pi * t))
  have hq_nonneg : 0 ≤ q := by positivity
  have harg_pos : 0 < 2 * Real.pi * t := by positivity
  have hq_lt_one : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    linarith
  have hterm :
      (fun n : ℕ => Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * t))) =
        fun n : ℕ => q * q ^ n := by
    funext n
    dsimp [q]
    rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    congr 1
    norm_num
    ring
  rw [hterm]
  rw [tsum_mul_left]
  rw [tsum_geometric_of_lt_one hq_nonneg hq_lt_one]
  dsimp [q]
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero (2 * Real.pi * t),
    sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr harg_pos)).symm]

/-- Each geometric term in the positive Binet denominator has an explicit sine moment. -/
lemma integral_Ioi_exp_neg_two_pi_nat_add_one_mul_sin (u : ℝ) (n : ℕ) :
    ∫ t : ℝ in Set.Ioi 0,
        Real.exp (-(2 * Real.pi * ((n : ℝ) + 1)) * t) * Real.sin (u * t) =
      u / ((2 * Real.pi * ((n : ℝ) + 1)) ^ 2 + u ^ 2) := by
  have ha : 0 < 2 * Real.pi * ((n : ℝ) + 1) := by positivity
  simpa [mul_assoc] using
    integral_Ioi_exp_neg_mul_sin_scaled
      (a := 2 * Real.pi * ((n : ℝ) + 1)) (b := u) ha

/-- The positive kernel in the second Binet formula for `digamma`. -/
noncomputable def digammaBinetKernel (z : ℂ) (t : ℝ) : ℂ :=
  ((2 * t : ℝ) : ℂ) /
    ((z ^ 2 + ((t ^ 2 : ℝ) : ℂ)) *
      (((Real.exp (2 * Real.pi * t) - 1 : ℝ) : ℂ)))

/-- The `n`th geometric-Bose term in the positive second-Binet kernel expansion. -/
noncomputable def binetTerm (z : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (((2 * t : ℝ) : ℂ) / (z ^ 2 + ((t ^ 2 : ℝ) : ℂ))) *
    ((Real.exp (-(2 * Real.pi * ((n : ℝ) + 1)) * t) : ℝ) : ℂ)

/-- The exponential majorant for the positive second-Binet kernel. -/
noncomputable def binetMajorant (x t : ℝ) : ℝ :=
  Real.exp (-(digammaBinetA0 * t)) / digammaBinetA0 +
    t * Real.exp (-(digammaBinetA0 * t)) / (2 * digammaBinetA0 * x)

lemma norm_digammaBinetKernel_eq {z : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖digammaBinetKernel z t‖ =
      (2 * t) /
        (‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖ * (Real.exp (2 * Real.pi * t) - 1)) := by
  have hnum : ‖((2 * t : ℝ) : ℂ)‖ = 2 * t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hEpos := exp_two_pi_mul_sub_one_pos ht
  have hE :
      ‖(((Real.exp (2 * Real.pi * t) - 1 : ℝ) : ℂ))‖ =
        Real.exp (2 * Real.pi * t) - 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hEpos.le]
  rw [digammaBinetKernel, norm_div, norm_mul, hnum, hE]

lemma exp_neg_two_pi_nat_add_one_mul_assoc (n : ℕ) (t : ℝ) :
    Real.exp (-(2 * Real.pi * ((n : ℝ) + 1) * t)) =
      Real.exp (-(2 * Real.pi * ((n : ℝ) + 1)) * t) := by
  congr 1
  ring

lemma digammaBinetKernel_eq_tsum_binetTerm (z : ℂ) {t : ℝ} (ht : 0 < t) :
    digammaBinetKernel z t = ∑' n : ℕ, binetTerm z n t := by
  let A : ℂ := ((2 * t : ℝ) : ℂ) / (z ^ 2 + ((t ^ 2 : ℝ) : ℂ))
  let e : ℕ → ℝ := fun n => Real.exp (-(2 * Real.pi * ((n : ℝ) + 1)) * t)
  have hgeom_old := tsum_exp_neg_two_pi_nat_add_one t ht
  have hgeom : (∑' n : ℕ, e n) = 1 / (Real.exp (2 * Real.pi * t) - 1) := by
    rw [← hgeom_old]
    congr
    ext n
    exact (exp_neg_two_pi_nat_add_one_mul_assoc n t).symm
  have hgeomC : (((1 / (Real.exp (2 * Real.pi * t) - 1) : ℝ) : ℂ)) =
      ∑' n : ℕ, ((e n : ℝ) : ℂ) := by
    rw [← hgeom]
    exact Complex.ofReal_tsum e
  calc
    digammaBinetKernel z t = A * (((1 / (Real.exp (2 * Real.pi * t) - 1) : ℝ) : ℂ)) := by
      simp [A, digammaBinetKernel, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ = A * (∑' n : ℕ, ((e n : ℝ) : ℂ)) := by rw [hgeomC]
    _ = ∑' n : ℕ, A * ((e n : ℝ) : ℂ) := by
      rw [tsum_mul_left]
    _ = ∑' n : ℕ, binetTerm z n t := by
      simp [A, e, binetTerm, mul_comm, mul_left_comm]

lemma binetTerm_integrableOn (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    IntegrableOn (binetTerm z n) (Set.Ioi (0 : ℝ)) volume := by
  let a : ℝ := 2 * Real.pi * ((n : ℝ) + 1)
  have ha : 0 < a := by positivity
  have hbase : IntegrableOn (fun t : ℝ => Real.exp (-a * t))
      (Set.Ioi (0 : ℝ)) volume := by
    simpa [Real.rpow_zero, Real.rpow_one, mul_comm] using
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := 0) (p := 1) (b := a)
        (by norm_num : (-1 : ℝ) < 0) (by norm_num : (1 : ℝ) ≤ 1) ha
  have hmaj : IntegrableOn (fun t : ℝ => (1 / z.re) * Real.exp (-a * t))
      (Set.Ioi (0 : ℝ)) volume := hbase.const_mul (1 / z.re)
  have hmeas : AEStronglyMeasurable (binetTerm z n)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    unfold binetTerm
    exact (by fun_prop : Measurable (fun t : ℝ =>
      (((2 * t : ℝ) : ℂ) / (z ^ 2 + ((t ^ 2 : ℝ) : ℂ))) *
        ((Real.exp (-(2 * Real.pi * ((n : ℝ) + 1)) * t) : ℝ) : ℂ))).aestronglyMeasurable
  exact hmaj.mono' hmeas (by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := ht
    have hDlower : 2 * z.re * t ≤ ‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖ := by
      exact two_mul_re_mul_le_norm_sq_add_real_sq (z := z) (t := t) hz.le htpos.le
    have hDpos : 0 < ‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖ := by
      have hleft : 0 < 2 * z.re * t := by positivity
      exact lt_of_lt_of_le hleft hDlower
    have hnum : ‖((2 * t : ℝ) : ℂ)‖ = 2 * t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hexp_nonneg : 0 ≤ Real.exp (-(2 * Real.pi * ((n : ℝ) + 1)) * t) :=
      (Real.exp_pos _).le
    have hexp_norm :
        ‖((Real.exp (-(2 * Real.pi * ((n : ℝ) + 1)) * t) : ℝ) : ℂ)‖ =
          Real.exp (-(2 * Real.pi * ((n : ℝ) + 1)) * t) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hexp_nonneg]
    have hquot : (2 * t) / ‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖ ≤ 1 / z.re := by
      rw [div_le_iff₀ hDpos]
      field_simp [hz.ne']
      nlinarith [hDlower]
    calc
      ‖binetTerm z n t‖ =
          ((2 * t) / ‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖) *
            Real.exp (-(2 * Real.pi * ((n : ℝ) + 1)) * t) := by
            rw [binetTerm, norm_mul, norm_div, hnum, hexp_norm]
      _ ≤ (1 / z.re) * Real.exp (-(2 * Real.pi * ((n : ℝ) + 1)) * t) := by
            exact mul_le_mul_of_nonneg_right hquot hexp_nonneg
      _ = (1 / z.re) * Real.exp (-a * t) := by
            simp [a])

lemma norm_sq_mul_norm_digammaBinetKernel_le {z : ℂ} {t : ℝ}
    (hx : 0 < z.re) (ht : 0 < t) :
    ‖z‖ ^ 2 * ‖digammaBinetKernel z t‖ ≤ binetMajorant z.re t := by
  let D : ℝ := ‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖
  let E : ℝ := Real.exp (2 * Real.pi * t) - 1
  have h2 : 2 * z.re * t ≤ D := by
    simpa [D] using two_mul_re_mul_le_norm_sq_add_real_sq (z := z) (t := t) hx.le ht.le
  have hDpos : 0 < D := by
    have hleft : 0 < 2 * z.re * t := by positivity
    exact lt_of_lt_of_le hleft h2
  have hEpos : 0 < E := by
    simpa [E] using exp_two_pi_mul_sub_one_pos ht
  have hnorm := norm_digammaBinetKernel_eq (z := z) ht
  have hdiv : ‖z‖ ^ 2 / D ≤ 1 + t / (2 * z.re) := by
    simpa [D] using norm_sq_div_norm_sq_add_real_sq_le_one_add (z := z) (t := t) hx ht
  have hquot : (2 * t) / E ≤
      Real.exp (-(digammaBinetA0 * t)) / digammaBinetA0 := by
    simpa [E] using two_mul_div_exp_two_pi_sub_one_le (t := t) ht
  have hquot_nonneg : 0 ≤ (2 * t) / E := by
    exact div_nonneg (by positivity) hEpos.le
  have hfactor_nonneg : 0 ≤ 1 + t / (2 * z.re) := by
    positivity
  rw [hnorm]
  calc
    ‖z‖ ^ 2 *
        ((2 * t) / (‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖ *
          (Real.exp (2 * Real.pi * t) - 1)))
        = (‖z‖ ^ 2 / D) * ((2 * t) / E) := by
          have hden :
              ‖z ^ 2 + ((t ^ 2 : ℝ) : ℂ)‖ *
                (Real.exp (2 * Real.pi * t) - 1) = D * E := by
            rfl
          rw [hden]
          field_simp [hDpos.ne', hEpos.ne']
    _ ≤ (1 + t / (2 * z.re)) * ((2 * t) / E) := by
          exact mul_le_mul_of_nonneg_right hdiv hquot_nonneg
    _ ≤ (1 + t / (2 * z.re)) *
        (Real.exp (-(digammaBinetA0 * t)) / digammaBinetA0) := by
          exact mul_le_mul_of_nonneg_left hquot hfactor_nonneg
    _ = binetMajorant z.re t := by
          dsimp [binetMajorant]
          field_simp [digammaBinetA0_pos.ne', hx.ne']

lemma integrableOn_exp_neg_a0_mul_Ioi :
    IntegrableOn (fun t : ℝ => Real.exp (-(digammaBinetA0 * t)))
      (Set.Ioi (0 : ℝ)) volume := by
  simpa [Real.rpow_zero, Real.rpow_one, mul_comm] using
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := 0) (p := 1) (b := digammaBinetA0)
      (by norm_num : (-1 : ℝ) < 0) (by norm_num : (1 : ℝ) ≤ 1)
      digammaBinetA0_pos

/-- The Planck sine integrand is integrable on `(0, ∞)`. -/
lemma integrableOn_abs_sin_div_exp_two_pi_sub_one (u : ℝ) :
    IntegrableOn
      (fun t : ℝ => |Real.sin (u * t)| / (Real.exp (2 * Real.pi * t) - 1))
      (Set.Ioi (0 : ℝ)) volume := by
  have hbase : IntegrableOn
      (fun t : ℝ => (|u| / (2 * digammaBinetA0)) *
        Real.exp (-(digammaBinetA0 * t)))
      (Set.Ioi (0 : ℝ)) volume :=
    integrableOn_exp_neg_a0_mul_Ioi.const_mul (|u| / (2 * digammaBinetA0))
  have hmaj : IntegrableOn
      (fun t : ℝ => |u| * (Real.exp (-(digammaBinetA0 * t)) / (2 * digammaBinetA0)))
      (Set.Ioi (0 : ℝ)) volume := by
    refine hbase.congr_fun ?_ measurableSet_Ioi
    intro t ht
    field_simp [digammaBinetA0_pos.ne']
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => |Real.sin (u * t)| / (Real.exp (2 * Real.pi * t) - 1))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    exact (by fun_prop : Measurable
      (fun t : ℝ => |Real.sin (u * t)| / (Real.exp (2 * Real.pi * t) - 1)))
        |>.aestronglyMeasurable
  refine hmaj.mono' hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := ht
  have hEpos := exp_two_pi_mul_sub_one_pos htpos
  have hsin : |Real.sin (u * t)| ≤ |u| * t := by
    calc
      |Real.sin (u * t)| ≤ |u * t| :=
        (show |Real.sin (u * t)| ≤ |u * t| from Real.abs_sin_le_abs)
      _ = |u| * t := by rw [abs_mul, abs_of_pos htpos]
  have hdiv : |Real.sin (u * t)| / (Real.exp (2 * Real.pi * t) - 1) ≤
      (|u| * t) / (Real.exp (2 * Real.pi * t) - 1) := by
    exact div_le_div_of_nonneg_right hsin hEpos.le
  have hk := two_mul_div_exp_two_pi_sub_one_le (t := t) htpos
  have hk' : t / (Real.exp (2 * Real.pi * t) - 1) ≤
      Real.exp (-(digammaBinetA0 * t)) / (2 * digammaBinetA0) := by
    calc
      t / (Real.exp (2 * Real.pi * t) - 1)
          = ((2 * t) / (Real.exp (2 * Real.pi * t) - 1)) / 2 := by ring
      _ ≤ (Real.exp (-(digammaBinetA0 * t)) / digammaBinetA0) / 2 := by
          exact div_le_div_of_nonneg_right hk (by norm_num)
      _ = Real.exp (-(digammaBinetA0 * t)) / (2 * digammaBinetA0) := by
          field_simp [digammaBinetA0_pos.ne']
  calc
    ‖|Real.sin (u * t)| / (Real.exp (2 * Real.pi * t) - 1)‖
        = |Real.sin (u * t)| / (Real.exp (2 * Real.pi * t) - 1) := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact div_nonneg (abs_nonneg _) hEpos.le
    _ ≤ (|u| * t) / (Real.exp (2 * Real.pi * t) - 1) := hdiv
    _ = |u| * (t / (Real.exp (2 * Real.pi * t) - 1)) := by ring
    _ ≤ |u| * (Real.exp (-(digammaBinetA0 * t)) / (2 * digammaBinetA0)) := by
          exact mul_le_mul_of_nonneg_left hk' (abs_nonneg u)

/-- Sine transform of the geometric expansion of the positive Binet denominator. -/
lemma hasSum_integral_exp_neg_two_pi_nat_add_one_mul_sin (u : ℝ) :
    HasSum
      (fun n : ℕ => u / ((2 * Real.pi * ((n : ℝ) + 1)) ^ 2 + u ^ 2))
      (∫ t : ℝ in Set.Ioi 0,
        Real.sin (u * t) / (Real.exp (2 * Real.pi * t) - 1)) := by
  let F : ℕ → ℝ → ℝ := fun n t =>
    Real.exp (-(2 * Real.pi * ((n : ℝ) + 1)) * t) * Real.sin (u * t)
  let B : ℕ → ℝ → ℝ := fun n t =>
    Real.exp (-(2 * Real.pi * ((n : ℝ) + 1)) * t) * |Real.sin (u * t)|
  let f : ℝ → ℝ := fun t =>
    Real.sin (u * t) / (Real.exp (2 * Real.pi * t) - 1)
  have hF_meas : ∀ n, AEStronglyMeasurable (F n)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro n
    exact (by fun_prop : Measurable (F n)).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), ‖F n t‖ ≤ B n t := by
    intro n
    filter_upwards with t
    dsimp [F, B]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hbound_summable :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), Summable fun n => B n t := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have h := (hasSum_exp_neg_two_pi_nat_add_one t ht).summable
    simpa [B] using h.mul_right |Real.sin (u * t)|
  have hbound_tsum_eq :
      (fun t : ℝ => ∑' n : ℕ, B n t) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun t : ℝ => |Real.sin (u * t)| / (Real.exp (2 * Real.pi * t) - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hsum := (hasSum_exp_neg_two_pi_nat_add_one t ht).mul_right |Real.sin (u * t)|
    simpa [B, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsum.tsum_eq
  have hbound_integrable : Integrable (fun t : ℝ => ∑' n : ℕ, B n t)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    exact (integrableOn_abs_sin_div_exp_two_pi_sub_one u).congr hbound_tsum_eq.symm
  have hlim : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), HasSum (fun n => F n t) (f t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hsum := (hasSum_exp_neg_two_pi_nat_add_one t ht).mul_right (Real.sin (u * t))
    simpa [F, f, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsum
  have hswap := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := F) (f := f) (bound := B)
    hF_meas hbound hbound_summable hbound_integrable hlim
  have hterms : (fun n : ℕ => ∫ t, F n t ∂volume.restrict (Set.Ioi (0 : ℝ))) =
      fun n : ℕ => u / ((2 * Real.pi * ((n : ℝ) + 1)) ^ 2 + u ^ 2) := by
    funext n
    dsimp [F]
    rw [← integral_Ioi_exp_neg_two_pi_nat_add_one_mul_sin (u := u) (n := n)]
  have hfint : (∫ t, f t ∂volume.restrict (Set.Ioi (0 : ℝ))) =
      ∫ t : ℝ in Set.Ioi 0,
        Real.sin (u * t) / (Real.exp (2 * Real.pi * t) - 1) := rfl
  rw [hterms, hfint] at hswap
  exact hswap

/-- A nonzero pure-imaginary complex number is not an integer. -/
lemma pure_imag_mem_integerComplement {y : ℝ} (hy : y ≠ 0) :
    (((y : ℂ) * Complex.I) ∈ Complex.integerComplement) := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨m, hm⟩
  have him := congrArg Complex.im hm
  simp at him
  exact hy him.symm

/-- Imaginary part of one cotangent Mittag-Leffler term on the positive imaginary axis. -/
lemma cot_term_pure_imag_im (y : ℝ) (n : ℕ) :
    ((1 / (((y : ℂ) * Complex.I) - (n + 1 : ℂ)) +
        1 / (((y : ℂ) * Complex.I) + (n + 1 : ℂ))).im) =
      -2 * y / (((n : ℝ) + 1) ^ 2 + y ^ 2) := by
  simp [Complex.inv_im, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  ring_nf

/-- Closed form for the imaginary part of `π cot(πiy) - 1/(iy)`. -/
lemma cot_lhs_pure_imag_im (y : ℝ) (hy : 0 < y) :
    (Real.pi * Complex.cot (Real.pi * ((y : ℂ) * Complex.I)) -
        1 / ((y : ℂ) * Complex.I)).im =
      -Real.pi - 2 * Real.pi / (Real.exp (2 * Real.pi * y) - 1) + 1 / y := by
  have hEpos : 0 < Real.exp (2 * Real.pi * y) - 1 := by
    rw [sub_pos]
    exact Real.one_lt_exp_iff.mpr (by positivity)
  have hEpos' : -1 + Real.exp (Real.pi * y * 2) ≠ 0 := by
    have h : 0 < Real.exp (Real.pi * y * 2) - 1 := by
      rw [sub_pos]
      exact Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  have hq : 1 - Real.exp (-(Real.pi * y * 2)) ≠ 0 := by
    rw [ne_eq, sub_eq_zero]
    intro h
    have : Real.exp (-(Real.pi * y * 2)) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith [Real.pi_pos, hy]
    linarith
  rw [Complex.cot_pi_eq_exp_ratio]
  simp [Complex.exp_re, Complex.exp_im, Complex.inv_im,
    Complex.normSq_apply, Complex.div_re, Complex.div_im]
  field_simp [hy.ne', hEpos.ne', hq, Real.exp_ne_zero (2 * Real.pi * y),
    Real.exp_ne_zero (-(Real.pi * y * 2))]
  ring_nf
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero (Real.pi * y * 2), hEpos']
  ring_nf
  field_simp [hEpos']
  ring

/-- Cotangent summation on the positive imaginary axis, in real `HasSum` form. -/
lemma hasSum_cot_pure_imag (y : ℝ) (hy : 0 < y) :
    HasSum (fun n : ℕ => -2 * y / (((n : ℝ) + 1) ^ 2 + y ^ 2))
      (-Real.pi - 2 * Real.pi / (Real.exp (2 * Real.pi * y) - 1) + 1 / y) := by
  let z : ℂ := (y : ℂ) * Complex.I
  have hz : z ∈ Complex.integerComplement := by
    simpa [z] using pure_imag_mem_integerComplement hy.ne'
  have hsumm : Summable (fun n : ℕ =>
      1 / (z - (n + 1)) + 1 / (z + (n + 1))) := by
    simpa [cotTerm] using summable_cotTerm hz
  have hcot : HasSum (fun n : ℕ =>
      1 / (z - (n + 1)) + 1 / (z + (n + 1)))
      (Real.pi * Complex.cot (Real.pi * z) - 1 / z) := by
    rw [cot_series_rep' (x := z) hz]
    exact hsumm.hasSum
  have him0 := Complex.imCLM.hasSum hcot
  have him : HasSum
      (fun b : ℕ => (1 / (z - (b + 1)) + 1 / (z + (b + 1))).im)
      ((Real.pi * Complex.cot (Real.pi * z) - 1 / z).im) := by
    simpa using him0
  have htarget :
      (Real.pi * Complex.cot (Real.pi * z) - 1 / z).im =
        -Real.pi - 2 * Real.pi / (Real.exp (2 * Real.pi * y) - 1) + 1 / y := by
    simpa [z] using cot_lhs_pure_imag_im y hy
  rw [htarget] at him
  have hterm :
      (fun b : ℕ => (1 / (z - (b + 1)) + 1 / (z + (b + 1))).im) =
        fun n : ℕ => -2 * y / (((n : ℝ) + 1) ^ 2 + y ^ 2) := by
    funext n
    simpa [z] using cot_term_pure_imag_im y n
  rw [hterm] at him
  exact him

/-- Series form of the Planck sine transform. -/
lemma hasSum_planck_sine_terms (u : ℝ) (hu : 0 < u) :
    HasSum
      (fun n : ℕ => u / ((2 * Real.pi * ((n : ℝ) + 1)) ^ 2 + u ^ 2))
      ((1 / (Real.exp u - 1) + 1 / 2 - 1 / u) / 2) := by
  let y : ℝ := u / (2 * Real.pi)
  have hy : 0 < y := by positivity
  have hA := hasSum_cot_pure_imag y hy
  have hscaled := hA.mul_left (-(1 / (4 * Real.pi)))
  have hterm :
      (fun n : ℕ => u / ((2 * Real.pi * ((n : ℝ) + 1)) ^ 2 + u ^ 2)) =
        fun n : ℕ => -(1 / (4 * Real.pi)) *
          (-2 * y / (((n : ℝ) + 1) ^ 2 + y ^ 2)) := by
    funext n
    dsimp [y]
    field_simp [Real.pi_ne_zero]
    ring
  have hconst :
      ((1 / (Real.exp u - 1) + 1 / 2 - 1 / u) / 2) =
        -(1 / (4 * Real.pi)) *
          (-Real.pi - 2 * Real.pi / (Real.exp (2 * Real.pi * y) - 1) + 1 / y) := by
    dsimp [y]
    have hE : Real.exp (2 * Real.pi * (u / (2 * Real.pi))) = Real.exp u := by
      congr 1
      field_simp [Real.pi_ne_zero]
    rw [hE]
    field_simp [Real.pi_ne_zero, hu.ne',
      sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr hu)).symm]
    ring
  rw [hterm, hconst]
  exact hscaled

/-- The Planck sine transform on `(0, ∞)`. -/
lemma integral_sin_div_exp_two_pi_sub_one_eq (u : ℝ) (hu : 0 < u) :
    ∫ t : ℝ in Set.Ioi 0,
        Real.sin (u * t) / (Real.exp (2 * Real.pi * t) - 1) =
      (1 / (Real.exp u - 1) + 1 / 2 - 1 / u) / 2 := by
  exact (hasSum_integral_exp_neg_two_pi_nat_add_one_mul_sin u).unique
    (hasSum_planck_sine_terms u hu)

lemma integrableOn_mul_exp_neg_a0_mul_Ioi :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(digammaBinetA0 * t)))
      (Set.Ioi (0 : ℝ)) volume := by
  simpa [Real.rpow_one, mul_comm, mul_left_comm, mul_assoc] using
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := 1) (p := 1) (b := digammaBinetA0)
      (by norm_num : (-1 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 1)
      digammaBinetA0_pos

lemma integral_exp_neg_a0_mul_Ioi :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(digammaBinetA0 * t)) =
      1 / digammaBinetA0 := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow
    (p := 1) (q := 0) (b := digammaBinetA0)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (-1 : ℝ) < 0)
    digammaBinetA0_pos
  calc
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(digammaBinetA0 * t))
        = ∫ t in Set.Ioi (0 : ℝ),
            t ^ (0 : ℝ) * Real.exp (-digammaBinetA0 * t ^ (1 : ℝ)) := by
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro t ht
          simp [Real.rpow_zero, Real.rpow_one, mul_comm]
    _ = digammaBinetA0 ^ (-((0 : ℝ) + 1) / 1) * (1 / 1) *
        Real.Gamma (((0 : ℝ) + 1) / 1) := h
    _ = 1 / digammaBinetA0 := by
          rw [show -((0 : ℝ) + 1) / 1 = (-1 : ℝ) by norm_num]
          rw [show ((0 : ℝ) + 1) / 1 = (1 : ℝ) by norm_num]
          rw [Real.Gamma_one, Real.rpow_neg_one]
          ring

lemma integral_mul_exp_neg_a0_mul_Ioi :
    ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-(digammaBinetA0 * t)) =
      1 / digammaBinetA0 ^ 2 := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow
    (p := 1) (q := 1) (b := digammaBinetA0)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (-1 : ℝ) < 1)
    digammaBinetA0_pos
  calc
    ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-(digammaBinetA0 * t))
        = ∫ t in Set.Ioi (0 : ℝ),
            t ^ (1 : ℝ) * Real.exp (-digammaBinetA0 * t ^ (1 : ℝ)) := by
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro t ht
          simp [Real.rpow_one, mul_comm]
    _ = digammaBinetA0 ^ (-((1 : ℝ) + 1) / 1) * (1 / 1) *
        Real.Gamma (((1 : ℝ) + 1) / 1) := h
    _ = 1 / digammaBinetA0 ^ 2 := by
          rw [show -((1 : ℝ) + 1) / 1 = (-(2 : ℝ)) by norm_num]
          rw [show ((1 : ℝ) + 1) / 1 = (2 : ℝ) by norm_num]
          rw [Real.Gamma_two]
          rw [Real.rpow_neg (digammaBinetA0_pos.le), Real.rpow_two]
          ring

lemma integrableOn_binetMajorant {x : ℝ} (hx : x ≠ 0) :
    IntegrableOn (binetMajorant x) (Set.Ioi (0 : ℝ)) volume := by
  have h0 : IntegrableOn
      (fun t : ℝ => (1 / digammaBinetA0) * Real.exp (-(digammaBinetA0 * t)))
      (Set.Ioi (0 : ℝ)) volume :=
    integrableOn_exp_neg_a0_mul_Ioi.const_mul (1 / digammaBinetA0)
  have h1 : IntegrableOn
      (fun t : ℝ => (1 / (2 * digammaBinetA0 * x)) *
        (t * Real.exp (-(digammaBinetA0 * t))))
      (Set.Ioi (0 : ℝ)) volume :=
    integrableOn_mul_exp_neg_a0_mul_Ioi.const_mul (1 / (2 * digammaBinetA0 * x))
  refine (h0.add h1).congr_fun ?_ measurableSet_Ioi
  intro t ht
  change (1 / digammaBinetA0) * Real.exp (-(digammaBinetA0 * t)) +
      (1 / (2 * digammaBinetA0 * x)) *
        (t * Real.exp (-(digammaBinetA0 * t))) = binetMajorant x t
  rw [binetMajorant]
  field_simp [digammaBinetA0_pos.ne', hx]

lemma integral_binetMajorant {x : ℝ} (hx : 0 < x) :
    ∫ t in Set.Ioi (0 : ℝ), binetMajorant x t =
      1 / digammaBinetA0 ^ 2 + 1 / (2 * digammaBinetA0 ^ 3 * x) := by
  have h0 : Integrable (fun t : ℝ =>
      (1 / digammaBinetA0) * Real.exp (-(digammaBinetA0 * t)))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrableOn_exp_neg_a0_mul_Ioi.const_mul (1 / digammaBinetA0)
  have h1 : Integrable (fun t : ℝ =>
      (1 / (2 * digammaBinetA0 * x)) *
        (t * Real.exp (-(digammaBinetA0 * t))))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrableOn_mul_exp_neg_a0_mul_Ioi.const_mul (1 / (2 * digammaBinetA0 * x))
  have hdecomp :
      (fun t : ℝ => binetMajorant x t) =
        fun t : ℝ =>
          (1 / digammaBinetA0) * Real.exp (-(digammaBinetA0 * t)) +
            (1 / (2 * digammaBinetA0 * x)) *
              (t * Real.exp (-(digammaBinetA0 * t))) := by
    ext t
    change Real.exp (-(digammaBinetA0 * t)) / digammaBinetA0 +
        t * Real.exp (-(digammaBinetA0 * t)) / (2 * digammaBinetA0 * x) =
      (1 / digammaBinetA0) * Real.exp (-(digammaBinetA0 * t)) +
        (1 / (2 * digammaBinetA0 * x)) *
          (t * Real.exp (-(digammaBinetA0 * t)))
    field_simp [digammaBinetA0_pos.ne', hx.ne']
  rw [hdecomp]
  rw [MeasureTheory.integral_add h0 h1]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [integral_exp_neg_a0_mul_Ioi, integral_mul_exp_neg_a0_mul_Ioi]
  field_simp [digammaBinetA0_pos.ne', hx.ne']

lemma integral_binetMajorant_le_one_sixth {x : ℝ} (hx : (1 / 4 : ℝ) ≤ x) :
    1 / digammaBinetA0 ^ 2 + 1 / (2 * digammaBinetA0 ^ 3 * x) ≤
      1 / 6 := by
  have hxpos : 0 < x := by linarith
  have hterm : 1 / (2 * digammaBinetA0 ^ 3 * x) ≤ 2 / digammaBinetA0 ^ 3 := by
    have ha03 : 0 < digammaBinetA0 ^ 3 := pow_pos digammaBinetA0_pos 3
    have hdenpos : 0 < 2 * digammaBinetA0 ^ 3 * x := by positivity
    rw [div_le_iff₀ hdenpos]
    field_simp [digammaBinetA0_pos.ne']
    nlinarith [hx]
  have hconst : 1 / digammaBinetA0 ^ 2 + 2 / digammaBinetA0 ^ 3 < 1 / 6 := by
    norm_num [digammaBinetA0]
  linarith

lemma norm_integral_digammaBinetKernel_le {z : ℂ} (hz : (1 / 4 : ℝ) ≤ z.re) :
    ‖∫ t in Set.Ioi (0 : ℝ), digammaBinetKernel z t‖ ≤
      1 / (6 * ‖z‖ ^ 2) := by
  have hzpos : 0 < z.re := by linarith
  have hnorm_pos : 0 < ‖z‖ := by
    rw [norm_pos_iff]
    intro hz0
    have : z.re = 0 := by simp [hz0]
    linarith
  have hnorm_sq_pos : 0 < ‖z‖ ^ 2 := pow_pos hnorm_pos 2
  have hmaj_int : IntegrableOn
      (fun t : ℝ => binetMajorant z.re t / ‖z‖ ^ 2)
      (Set.Ioi (0 : ℝ)) volume := by
    have hbase : IntegrableOn
        (fun t : ℝ => (1 / ‖z‖ ^ 2) * binetMajorant z.re t)
        (Set.Ioi (0 : ℝ)) volume :=
      (integrableOn_binetMajorant (x := z.re) hzpos.ne').const_mul
        (1 / ‖z‖ ^ 2)
    refine hbase.congr_fun ?_ measurableSet_Ioi
    intro t ht
    change (1 / ‖z‖ ^ 2) * binetMajorant z.re t =
      binetMajorant z.re t / ‖z‖ ^ 2
    field_simp [hnorm_sq_pos.ne']
  have hnorm := MeasureTheory.norm_integral_le_integral_norm
    (μ := volume.restrict (Set.Ioi (0 : ℝ))) (f := digammaBinetKernel z)
  have hmono :
      ∫ t in Set.Ioi (0 : ℝ), ‖digammaBinetKernel z t‖ ≤
        ∫ t in Set.Ioi (0 : ℝ), binetMajorant z.re t / ‖z‖ ^ 2 := by
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => norm_nonneg (digammaBinetKernel z t))
      hmaj_int
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        have htpos : 0 < t := ht
        have hk := norm_sq_mul_norm_digammaBinetKernel_le (z := z) (t := t) hzpos htpos
        rw [le_div_iff₀ hnorm_sq_pos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hk)
  have hint_eval :
      ∫ t in Set.Ioi (0 : ℝ), binetMajorant z.re t / ‖z‖ ^ 2 =
        (∫ t in Set.Ioi (0 : ℝ), binetMajorant z.re t) / ‖z‖ ^ 2 := by
    rw [MeasureTheory.integral_div]
  have hmajor :
      (∫ t in Set.Ioi (0 : ℝ), binetMajorant z.re t) / ‖z‖ ^ 2 ≤
        (1 / 6) / ‖z‖ ^ 2 := by
    rw [integral_binetMajorant hzpos]
    exact div_le_div_of_nonneg_right (integral_binetMajorant_le_one_sixth hz)
      hnorm_sq_pos.le
  calc
    ‖∫ t in Set.Ioi (0 : ℝ), digammaBinetKernel z t‖
        ≤ ∫ t in Set.Ioi (0 : ℝ), ‖digammaBinetKernel z t‖ := hnorm
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), binetMajorant z.re t / ‖z‖ ^ 2 := hmono
    _ = (∫ t in Set.Ioi (0 : ℝ), binetMajorant z.re t) / ‖z‖ ^ 2 := hint_eval
    _ ≤ (1 / 6) / ‖z‖ ^ 2 := hmajor
    _ = 1 / (6 * ‖z‖ ^ 2) := by ring

/-- The logarithmic term from the vertical Binet split is bounded by its quadratic error. -/
lemma half_log_one_add_sq_div_le {x y : ℝ} (hy : y ≠ 0) :
    (1 / 2 : ℝ) * Real.log (1 + x ^ 2 / y ^ 2) ≤ x ^ 2 / (2 * y ^ 2) := by
  have harg : 0 < 1 + x ^ 2 / y ^ 2 := by positivity
  have hlog := Real.log_le_sub_one_of_pos harg
  have hlog' : Real.log (1 + x ^ 2 / y ^ 2) ≤ x ^ 2 / y ^ 2 := by
    calc
      Real.log (1 + x ^ 2 / y ^ 2) ≤ 1 + x ^ 2 / y ^ 2 - 1 := hlog
      _ = x ^ 2 / y ^ 2 := by ring
  calc
    (1 / 2 : ℝ) * Real.log (1 + x ^ 2 / y ^ 2)
        ≤ (1 / 2 : ℝ) * (x ^ 2 / y ^ 2) := by
          exact mul_le_mul_of_nonneg_left hlog' (by norm_num)
    _ = x ^ 2 / (2 * y ^ 2) := by
          field_simp [hy]

/-- The arctangent tail integral for the shifted square denominator. -/
lemma integral_Ioi_inv_sq_add_sq_eq_pi_div_two_sub_arctan {x y : ℝ} (hy : 0 < y) :
    ∫ u in Set.Ioi x, (1 / (u ^ 2 + y ^ 2) : ℝ) =
      y⁻¹ * (Real.pi / 2 - Real.arctan (x / y)) := by
  have hscale := MeasureTheory.integral_comp_mul_right_Ioi
    (g := fun u : ℝ => (1 / (u ^ 2 + y ^ 2) : ℝ)) (a := x / y) (b := y) hy
  have hlower : x / y * y = x := by field_simp [hy.ne']
  have hcomp : (fun v : ℝ => (1 / (((v * y) ^ 2 + y ^ 2)) : ℝ)) =
      fun v : ℝ => y⁻¹ ^ 2 * (1 / (v ^ 2 + 1) : ℝ) := by
    funext v
    field_simp [hy.ne']
  have hstd : ∫ v in Set.Ioi (x / y), (1 / (v ^ 2 + 1) : ℝ) =
      Real.pi / 2 - Real.arctan (x / y) := by
    simpa [one_div, add_comm] using integral_Ioi_inv_one_add_sq (i := x / y)
  rw [hcomp, MeasureTheory.integral_const_mul, hstd, hlower] at hscale
  simp only [smul_eq_mul] at hscale
  field_simp [hy.ne'] at hscale ⊢
  linarith

/-- The shifted arctangent integral in the `t + x` form used by the vertical majorant. -/
lemma integral_Ioi_shifted_inv_sq_add_sq_eq_arctan {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ∫ t in Set.Ioi (0 : ℝ), (1 / ((t + x) ^ 2 + y ^ 2) : ℝ) =
      y⁻¹ * Real.arctan (y / x) := by
  have hmp : MeasurePreserving (fun t : ℝ => t + x) volume volume :=
    measurePreserving_add_right (volume : Measure ℝ) x
  have hemb : MeasurableEmbedding (fun t : ℝ => t + x) :=
    (Homeomorph.addRight x).measurableEmbedding
  have hpre : (fun t : ℝ => t + x) ⁻¹' Set.Ioi x = Set.Ioi (0 : ℝ) := by
    rw [Set.preimage_add_const_Ioi]
    simp
  have hshift := hmp.setIntegral_preimage_emb hemb
    (fun u : ℝ => (1 / (u ^ 2 + y ^ 2) : ℝ)) (Set.Ioi x)
  rw [hpre] at hshift
  rw [hshift]
  rw [integral_Ioi_inv_sq_add_sq_eq_pi_div_two_sub_arctan (x := x) (y := y) hy]
  have hxy : 0 < x / y := div_pos hx hy
  have harctan : Real.pi / 2 - Real.arctan (x / y) = Real.arctan (y / x) := by
    rw [← Real.arctan_inv_of_pos hxy]
    congr 1
    field_simp [hx.ne', hy.ne']
  rw [harctan]

private lemma resolvent_ne_of_re_pos {s : ℂ} {t : ℝ} (hpos : 0 < t + s.re) :
    (t : ℂ) + s ≠ 0 := by
  intro h
  have hre : (((t : ℂ) + s).re) = t + s.re := by simp [add_comm]
  rw [h] at hre
  simp at hre
  linarith

private lemma shifted_line_mem_slitPlane {s : ℂ} (hs : 0 < s.re) {t : ℝ} (ht : 0 ≤ t) :
    (t : ℂ) + s ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  rw [add_re, ofReal_re]
  linarith

private lemma hasDerivAt_resolvent_of_re_pos {s : ℂ} {t : ℝ} (hpos : 0 < t + s.re) :
    HasDerivAt (fun u : ℝ => (((u : ℂ) + s)⁻¹))
      (-(((t : ℂ) + s)⁻¹) ^ (2 : ℕ)) t := by
  have hlin : HasDerivAt (fun u : ℝ => (u : ℂ) + s) 1 t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const s
  have hne : (t : ℂ) + s ≠ 0 := resolvent_ne_of_re_pos hpos
  have hinv : HasFDerivAt (fun z : ℂ => z⁻¹)
      (ContinuousLinearMap.toSpanSingleton ℂ (-( ((t : ℂ) + s) ^ 2)⁻¹))
      ((t : ℂ) + s) := by
    simpa using hasFDerivAt_inv hne
  have hcomp := HasFDerivAt.comp_hasDerivAt t (hinv.restrictScalars ℝ) hlin
  change HasDerivAt ((fun z : ℂ => z⁻¹) ∘ fun u : ℝ => (u : ℂ) + s)
    (-(((t : ℂ) + s)⁻¹) ^ (2 : ℕ)) t
  simpa [Function.comp, pow_two, div_eq_mul_inv] using hcomp

private lemma deriv_resolvent_of_re_pos {s : ℂ} {t : ℝ} (hpos : 0 < t + s.re) :
    deriv (fun u : ℝ => (((u : ℂ) + s)⁻¹)) t =
      -(((t : ℂ) + s)⁻¹) ^ (2 : ℕ) :=
  (hasDerivAt_resolvent_of_re_pos hpos).deriv

private lemma hasDerivAt_deriv_resolvent {s : ℂ} (hs : 0 < s.re) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun y : ℝ => deriv (fun u : ℝ => (((u : ℂ) + s)⁻¹)) y)
      ((2 : ℂ) * (((t : ℂ) + s)⁻¹) ^ (3 : ℕ)) t := by
  have hnear : ∀ᶠ y in nhds t, 0 < y + s.re := by
    have htpos : 0 < t + s.re := by linarith
    exact (isOpen_lt continuous_const (continuous_id.add continuous_const)).mem_nhds htpos
  have heq : (fun y : ℝ => deriv (fun u : ℝ => (((u : ℂ) + s)⁻¹)) y) =ᶠ[nhds t]
      fun y : ℝ => -(((y : ℂ) + s) ^ (2 : ℕ))⁻¹ := by
    filter_upwards [hnear] with y hy
    rw [deriv_resolvent_of_re_pos hy]
    rw [inv_pow]
  have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) + s) 1 t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const s
  have hpow : HasDerivAt (fun z : ℂ => -(z⁻¹) ^ (2 : ℕ))
      ((2 : ℂ) * (((t : ℂ) + s)⁻¹) ^ (3 : ℕ)) ((t : ℂ) + s) := by
    have hne : (t : ℂ) + s ≠ 0 := resolvent_ne_of_re_pos (by linarith)
    have hinv : HasDerivAt (fun z : ℂ => z⁻¹) (-(((t : ℂ) + s)⁻¹) ^ (2 : ℕ))
        ((t : ℂ) + s) := by
      simpa [pow_two, div_eq_mul_inv] using hasDerivAt_inv hne
    have hsq := (hinv.pow 2).neg
    have hfunc : (-(fun z : ℂ => z⁻¹) ^ (2 : ℕ)) =ᶠ[nhds ((t : ℂ) + s)]
        (fun z : ℂ => -(z⁻¹) ^ (2 : ℕ)) := by
      exact Filter.Eventually.of_forall fun z => by
        simp [Pi.pow_apply]
    have hderiv :
        -(↑(2 : ℕ) * ((t : ℂ) + s)⁻¹ ^ (2 - 1) * -((t : ℂ) + s)⁻¹ ^ (2 : ℕ)) =
          (2 : ℂ) * (((t : ℂ) + s)⁻¹) ^ (3 : ℕ) := by
      ring
    exact (hsq.congr_of_eventuallyEq hfunc).congr_deriv hderiv
  have hcomp := hpow.comp t hlin
  have heq_comp :
      (fun y : ℝ => deriv (fun u : ℝ => (((u : ℂ) + s)⁻¹)) y) =ᶠ[nhds t]
        ((fun z : ℂ => -(z⁻¹) ^ (2 : ℕ)) ∘ fun y : ℝ => (y : ℂ) + s) := by
    refine heq.trans (Filter.Eventually.of_forall fun y => ?_)
    simp [Function.comp, inv_pow]
  have hres := hcomp.congr_of_eventuallyEq heq_comp
  simpa [mul_one] using hres

private lemma continuousOn_resolvent {s : ℂ} (hs : 0 < s.re) {N : ℝ} (hN : 0 ≤ N) :
    ContinuousOn (fun t : ℝ => (((t : ℂ) + s)⁻¹)) (Set.uIcc (0 : ℝ) N) := by
  rw [Set.uIcc_of_le hN]
  refine ContinuousOn.inv₀ ?_ ?_
  · exact (Complex.continuous_ofReal.continuousOn.add continuousOn_const)
  · intro t ht
    exact resolvent_ne_of_re_pos (by linarith [hs, ht.1])

private lemma integral_resolvent {s : ℂ} (hs : 0 < s.re) {N : ℝ} (hN : 0 ≤ N) :
    ∫ t in (0 : ℝ)..N, (((t : ℂ) + s)⁻¹) =
      Complex.log ((N : ℂ) + s) - Complex.log s := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) N,
      HasDerivAt (fun u : ℝ => Complex.log ((u : ℂ) + s)) (((t : ℂ) + s)⁻¹) t := by
    intro t ht
    rw [Set.uIcc_of_le hN] at ht
    have hinner : HasDerivAt (fun u : ℝ => (u : ℂ) + s) 1 t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const s
    have hlog := Complex.hasDerivAt_log (shifted_line_mem_slitPlane hs ht.1)
    change HasDerivAt (Complex.log ∘ fun u : ℝ => (u : ℂ) + s) (((t : ℂ) + s)⁻¹) t
    simpa using hlog.comp t hinner
  have hcont : IntervalIntegrable (fun t : ℝ => (((t : ℂ) + s)⁻¹)) volume (0 : ℝ) N :=
    (continuousOn_resolvent hs hN).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont
  simpa using h

private lemma B1_natCast (n : ℕ) : B1 (n : ℝ) = -(1 / 2 : ℝ) := by
  unfold B1
  simp

private lemma B1_eq_fract_sub_half_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    (B1 t : ℂ) = ((Int.fract t - 1 / 2 : ℝ) : ℂ) := by
  unfold B1
  rw [← Int.self_sub_floor t, natCast_floor_eq_intCast_floor ht]

private lemma integral_deriv_resolvent_mul_B1_eq_neg_kernel {s : ℂ}
    (hs : 0 < s.re) (N : ℕ) :
    (∫ t in (0 : ℝ)..(N : ℝ),
        deriv (fun u : ℝ => (((u : ℂ) + s)⁻¹)) t * (B1 t : ℂ)) =
      -∫ t in (0 : ℝ)..(N : ℝ), digammaBinetRemainderKernel s t := by
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with t ht
  rw [Set.uIoc_of_le (Nat.cast_nonneg N)] at ht
  have ht0 : 0 ≤ t := ht.1.le
  rw [deriv_resolvent_of_re_pos (by linarith [hs, ht0])]
  rw [B1_eq_fract_sub_half_of_nonneg ht0]
  simp [digammaBinetRemainderKernel, mul_comm]

/-- Finite first-order Euler-Maclaurin identity for the shifted resolvent. -/
theorem sum_Ioc_resolvent_eq_log_boundary_sub_integral_firstOrder {s : ℂ}
    (hs : 0 < s.re) (N : ℕ) :
    ∑ k ∈ Finset.Ioc 0 N, (((k : ℂ) + s)⁻¹) =
      (Complex.log ((N : ℂ) + s) - Complex.log s) - s⁻¹ / 2 +
        (((N : ℂ) + s)⁻¹) / 2 -
        ∫ t in (0 : ℝ)..(N : ℝ), digammaBinetRemainderKernel s t := by
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hdiff : ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      DifferentiableAt ℝ (fun u : ℝ => (((u : ℂ) + s)⁻¹)) t := by
    intro t ht
    exact (hasDerivAt_resolvent_of_re_pos (by linarith [hs, ht.1])).differentiableAt
  have hderiv_cont : ContinuousOn
      (deriv (fun u : ℝ => (((u : ℂ) + s)⁻¹))) [[(0 : ℝ), (N : ℝ)]] := by
    have hbase : ContinuousOn (fun t : ℝ => -(((t : ℂ) + s)⁻¹) ^ (2 : ℕ))
        [[(0 : ℝ), (N : ℝ)]] := by
      rw [Set.uIcc_of_le hNnonneg]
      refine ContinuousOn.neg (ContinuousOn.pow (ContinuousOn.inv₀ ?_ ?_) 2)
      · exact (Complex.continuous_ofReal.continuousOn.add continuousOn_const)
      · intro t ht
        exact resolvent_ne_of_re_pos (by linarith [hs, ht.1])
    exact hbase.congr (by
      intro t ht
      rw [Set.uIcc_of_le hNnonneg] at ht
      exact deriv_resolvent_of_re_pos (by linarith [hs, ht.1]))
  have hEM := sum_eq_integral_add_integral_deriv
    (𝕜 := ℂ) (f := fun u : ℝ => (((u : ℂ) + s)⁻¹))
    (a := (0 : ℝ)) (b := (N : ℝ)) (by norm_num) hNnonneg hdiff hderiv_cont
  rw [Nat.floor_natCast, Nat.floor_zero] at hEM
  change (∑ k ∈ Finset.Ioc 0 N, (fun u : ℝ => (((u : ℂ) + s)⁻¹)) k) = _
  rw [hEM]
  rw [integral_resolvent hs hNnonneg]
  have hB10 : B1 (0 : ℝ) = -(1 / 2 : ℝ) := by simpa using B1_natCast 0
  rw [hB10, B1_natCast N]
  have hkernel := integral_deriv_resolvent_mul_B1_eq_neg_kernel (s := s) hs N
  calc
    (fun u : ℝ => (((u : ℂ) + s)⁻¹)) 0 * ((-(1 / 2 : ℝ) : ℝ) : ℂ) -
        (fun u : ℝ => (((u : ℂ) + s)⁻¹)) (N : ℝ) * ((-(1 / 2 : ℝ) : ℝ) : ℂ) +
        (Complex.log ((((N : ℝ) : ℂ) + s)) - Complex.log s) +
        (∫ t in (0 : ℝ)..(N : ℝ),
          deriv (fun u : ℝ => (((u : ℂ) + s)⁻¹)) t * (B1 t : ℂ)) =
      (fun u : ℝ => (((u : ℂ) + s)⁻¹)) 0 * ((-(1 / 2 : ℝ) : ℝ) : ℂ) -
        (fun u : ℝ => (((u : ℂ) + s)⁻¹)) (N : ℝ) * ((-(1 / 2 : ℝ) : ℝ) : ℂ) +
        (Complex.log ((((N : ℝ) : ℂ) + s)) - Complex.log s) +
        (-(∫ t in (0 : ℝ)..(N : ℝ), digammaBinetRemainderKernel s t)) := by
          exact congrArg
            (fun z : ℂ =>
              (fun u : ℝ => (((u : ℂ) + s)⁻¹)) 0 * ((-(1 / 2 : ℝ) : ℝ) : ℂ) -
                (fun u : ℝ => (((u : ℂ) + s)⁻¹)) (N : ℝ) *
                  ((-(1 / 2 : ℝ) : ℝ) : ℂ) +
                (Complex.log ((((N : ℝ) : ℂ) + s)) - Complex.log s) + z)
            hkernel
    _ = Complex.log ((N : ℂ) + s) - Complex.log s - s⁻¹ / 2 +
        (((N : ℂ) + s)⁻¹) / 2 -
        ∫ t in (0 : ℝ)..(N : ℝ), digammaBinetRemainderKernel s t := by
          simp only [ofReal_zero, zero_add, ofReal_natCast]
          norm_num
          ring_nf

private lemma bernoulli2PeriodizedHalf_natCast (n : ℕ) :
    bernoulli2PeriodizedHalf (n : ℝ) = (1 / 12 : ℂ) := by
  simp [bernoulli2PeriodizedHalf]
  norm_num

private lemma integral_deriv_deriv_resolvent_mul_bernoulli_eq_kernel {s : ℂ}
    (hs : 0 < s.re) (N : ℕ) :
    (∫ t in (0 : ℝ)..(N : ℝ),
        deriv (deriv (fun u : ℝ => (((u : ℂ) + s)⁻¹))) t *
          bernoulli2PeriodizedHalf t) =
      ∫ t in (0 : ℝ)..(N : ℝ),
        digammaBinetSecondOrderRemainderKernel s t := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with t ht
  rw [Set.uIoc_of_le (Nat.cast_nonneg N)] at ht
  have ht0 : 0 ≤ t := ht.1.le
  rw [(hasDerivAt_deriv_resolvent hs ht0).deriv]
  simp [digammaBinetSecondOrderRemainderKernel, mul_assoc, mul_comm]

/-- Finite second-order Euler-Maclaurin identity for the shifted resolvent. -/
theorem sum_Ioc_resolvent_eq_log_boundary_sub_integral {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ∑ k ∈ Finset.Ioc 0 N, (((k : ℂ) + s)⁻¹) =
      (Complex.log ((N : ℂ) + s) - Complex.log s) - s⁻¹ / 2 +
        (((N : ℂ) + s)⁻¹) / 2 +
        ((s⁻¹) ^ (2 : ℕ)) / 12 -
        ((((N : ℂ) + s)⁻¹) ^ (2 : ℕ)) / 12 -
        ∫ t in (0 : ℝ)..(N : ℝ),
          digammaBinetSecondOrderRemainderKernel s t := by
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hdiff : ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      DifferentiableAt ℝ (fun u : ℝ => (((u : ℂ) + s)⁻¹)) t := by
    intro t ht
    exact (hasDerivAt_resolvent_of_re_pos (by linarith [hs, ht.1])).differentiableAt
  have hderiv_cont : ContinuousOn
      (deriv (fun u : ℝ => (((u : ℂ) + s)⁻¹))) [[(0 : ℝ), (N : ℝ)]] := by
    have hbase : ContinuousOn (fun t : ℝ => -(((t : ℂ) + s)⁻¹) ^ (2 : ℕ))
        [[(0 : ℝ), (N : ℝ)]] := by
      rw [Set.uIcc_of_le hNnonneg]
      refine ContinuousOn.neg (ContinuousOn.pow (ContinuousOn.inv₀ ?_ ?_) 2)
      · exact (Complex.continuous_ofReal.continuousOn.add continuousOn_const)
      · intro t ht
        exact resolvent_ne_of_re_pos (by linarith [hs, ht.1])
    exact hbase.congr (by
      intro t ht
      rw [Set.uIcc_of_le hNnonneg] at ht
      exact deriv_resolvent_of_re_pos (by linarith [hs, ht.1]))
  have hsecond : ∀ t ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      HasDerivAt (fun y : ℝ => deriv (fun u : ℝ => (((u : ℂ) + s)⁻¹)) y)
        (deriv (deriv (fun u : ℝ => (((u : ℂ) + s)⁻¹))) t) t := by
    intro t ht
    have h := hasDerivAt_deriv_resolvent hs ht.1.le
    exact h.congr_deriv h.deriv.symm
  have hsecond_cont : ContinuousOn
      (fun t : ℝ => deriv (deriv (fun u : ℝ => (((u : ℂ) + s)⁻¹))) t)
      [[(0 : ℝ), (N : ℝ)]] := by
    have hbase : ContinuousOn
        (fun t : ℝ => (2 : ℂ) * (((t : ℂ) + s)⁻¹) ^ (3 : ℕ))
        [[(0 : ℝ), (N : ℝ)]] := by
      rw [Set.uIcc_of_le hNnonneg]
      refine continuousOn_const.mul (ContinuousOn.pow (ContinuousOn.inv₀ ?_ ?_) 3)
      · exact (Complex.continuous_ofReal.continuousOn.add continuousOn_const)
      · intro t ht
        exact resolvent_ne_of_re_pos (by linarith [hs, ht.1])
    exact hbase.congr (by
      intro t ht
      rw [Set.uIcc_of_le hNnonneg] at ht
      exact (hasDerivAt_deriv_resolvent hs ht.1).deriv)
  have hEM := sum_eq_integral_add_boundary_deriv_bernoulli2
    (f := fun u : ℝ => (((u : ℂ) + s)⁻¹))
    (a := (0 : ℝ)) (b := (N : ℝ)) (by norm_num) hNnonneg
    hdiff hderiv_cont hsecond hsecond_cont
  rw [Nat.floor_natCast, Nat.floor_zero] at hEM
  change (∑ k ∈ Finset.Ioc 0 N, (fun u : ℝ => (((u : ℂ) + s)⁻¹)) k) = _
  rw [hEM]
  rw [integral_resolvent hs hNnonneg]
  have hB10 : B1 (0 : ℝ) = -(1 / 2 : ℝ) := by simpa using B1_natCast 0
  have hB20 : bernoulli2PeriodizedHalf (0 : ℝ) = (1 / 12 : ℂ) := by
    simpa using bernoulli2PeriodizedHalf_natCast 0
  rw [hB10, B1_natCast N, hB20, bernoulli2PeriodizedHalf_natCast N]
  rw [deriv_resolvent_of_re_pos (s := s) (t := 0) (by simpa using hs)]
  rw [deriv_resolvent_of_re_pos (s := s) (t := (N : ℝ)) (by linarith [hs, hNnonneg])]
  rw [integral_deriv_deriv_resolvent_mul_bernoulli_eq_kernel hs N]
  simp only [ofReal_zero, zero_add, ofReal_natCast]
  norm_num
  ring_nf

private lemma sum_range_succ_resolvent_eq (s : ℂ) (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), (s + m)⁻¹ =
      s⁻¹ + ∑ k ∈ Finset.Ioc 0 N, (((k : ℂ) + s)⁻¹) := by
  have hrange : Finset.range (N + 1) = insert 0 (Finset.Ioc 0 N) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    constructor
    · intro hk
      by_cases h0 : k = 0
      · exact Or.inl h0
      · right
        exact ⟨Nat.pos_of_ne_zero h0, Nat.le_of_lt_succ hk⟩
    · intro hk
      rcases hk with rfl | hk
      · exact Nat.succ_pos N
      · exact Nat.lt_succ_of_le hk.2
  rw [hrange]
  rw [Finset.sum_insert]
  · simp [add_comm]
  · simp

private lemma tendsto_log_nat_sub_log_nat_add {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => (Real.log N : ℂ) - Complex.log ((N : ℂ) + s)) atTop
      (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => ((N : ℂ)⁻¹)) atTop (𝓝 0) := by
    have hreal : Tendsto (fun N : ℕ => ((N : ℝ)⁻¹)) atTop (𝓝 0) := by
      apply Tendsto.inv_tendsto_atTop
      exact tendsto_natCast_atTop_atTop
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_inv, norm_natCast] using hreal
  have hdiv : Tendsto (fun N : ℕ => s / (N : ℂ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul s
  have hone : Tendsto (fun N : ℕ => 1 + s / (N : ℂ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hdiv
  have hlog : Tendsto (fun N : ℕ => -Complex.log (1 + s / (N : ℂ))) atTop (𝓝 0) := by
    have h := hone.clog Complex.one_mem_slitPlane
    simpa [Complex.log_one] using h.neg
  have heq :
      (fun N : ℕ => (Real.log N : ℂ) - Complex.log ((N : ℂ) + s)) =ᶠ[atTop]
        (fun N : ℕ => -Complex.log (1 + s / (N : ℂ))) := by
    filter_upwards [eventually_ne_atTop 0] with N hN
    have hNposR : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_iff_ne_zero.mpr hN)
    have hNneC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    have hmul : (1 + s / (N : ℂ)) * (N : ℂ) = (N : ℂ) + s := by
      field_simp [hNneC]
    have hx : 1 + s / (N : ℂ) ≠ 0 := by
      intro hzero
      have hpos : 0 < (((N : ℂ) + s).re) := by
        simp
        linarith
      rw [← hmul, hzero] at hpos
      norm_num at hpos
    rw [← hmul]
    change (Real.log (N : ℝ) : ℂ) -
        Complex.log ((1 + s / (N : ℂ)) * ((N : ℝ) : ℂ)) =
      -Complex.log (1 + s / (N : ℂ))
    rw [Complex.log_mul_ofReal (N : ℝ) hNposR (1 + s / (N : ℂ)) hx]
    rw [Complex.ofReal_log hNposR.le]
    ring
  exact hlog.congr' heq.symm

private lemma tendsto_inv_nat_add (s : ℂ) :
    Tendsto (fun N : ℕ => (((N : ℂ) + s)⁻¹)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv]
  apply Tendsto.inv_tendsto_atTop
  exact tendsto_atTop_mono (fun N : ℕ => by
    have h := norm_sub_norm_le (N : ℂ) (-s)
    rw [sub_neg_eq_add, norm_neg, norm_natCast] at h
    exact h) (tendsto_atTop_add_const_right atTop (-‖s‖) tendsto_natCast_atTop_atTop)

/-- First-order Binet identity for `digamma` on the right half-plane. -/
theorem digamma_eq_log_sub_half_inv_add_integral {s : ℂ} (hs : 0 < s.re) :
    digamma s = Complex.log s - s⁻¹ / 2 +
      ∫ t in Set.Ioi (0 : ℝ), digammaBinetRemainderKernel s t := by
  let C : ℂ := Complex.log s - s⁻¹ / 2
  let K : ℕ → ℂ := fun N => (((N : ℂ) + s)⁻¹)
  have hdig := tendsto_log_sub_sum_inv_add_of_re_pos hs
  have hlogdiff := tendsto_log_nat_sub_log_nat_add hs
  have hK : Tendsto K atTop (𝓝 0) := by
    simpa [K] using tendsto_inv_nat_add s
  have hint : Tendsto
      (fun N : ℕ => ∫ t in (0 : ℝ)..(N : ℝ), digammaBinetRemainderKernel s t)
      atTop (𝓝 (∫ t in Set.Ioi (0 : ℝ), digammaBinetRemainderKernel s t)) := by
    exact intervalIntegral_tendsto_integral_Ioi (μ := volume) (a := (0 : ℝ))
      (integrableOn_digammaBinetRemainderKernel hs)
      (show Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop from tendsto_natCast_atTop_atTop)
  have hC : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
  have h1 : Tendsto
      (fun N : ℕ => ((Real.log N : ℂ) - Complex.log ((N : ℂ) + s)) + C)
      atTop (𝓝 (0 + C)) := hlogdiff.add hC
  have h2 : Tendsto
      (fun N : ℕ => ((Real.log N : ℂ) - Complex.log ((N : ℂ) + s)) + C - K N / 2)
      atTop (𝓝 (0 + C - 0 / 2)) := h1.sub (hK.div_const 2)
  have hseq_lim : Tendsto
      (fun N : ℕ => ((Real.log N : ℂ) - Complex.log ((N : ℂ) + s)) + C - K N / 2 +
        ∫ t in (0 : ℝ)..(N : ℝ), digammaBinetRemainderKernel s t)
      atTop (𝓝 (C + ∫ t in Set.Ioi (0 : ℝ), digammaBinetRemainderKernel s t)) := by
    have h3 := h2.add hint
    simpa [C, K] using h3
  have hseq_eq :
      (fun N : ℕ => (Real.log N : ℂ) -
        ∑ m ∈ Finset.range (N + 1), (s + m)⁻¹) =
      (fun N : ℕ => ((Real.log N : ℂ) - Complex.log ((N : ℂ) + s)) + C - K N / 2 +
        ∫ t in (0 : ℝ)..(N : ℝ), digammaBinetRemainderKernel s t) := by
    funext N
    rw [sum_range_succ_resolvent_eq s N]
    rw [sum_Ioc_resolvent_eq_log_boundary_sub_integral_firstOrder hs N]
    simp [C, K]
    ring_nf
  rw [hseq_eq] at hdig
  have hlim := tendsto_nhds_unique hdig hseq_lim
  simpa [C] using hlim

/--
The positive second-Binet formula follows from the already proved first-order Binet identity
once the positive kernel integral is identified with the negative sawtooth remainder.
-/
theorem digamma_binet_second_of_kernel_eq_neg_remainder {z : ℂ} (hz : 0 < z.re)
    (hkernel :
      ∫ t in Set.Ioi (0 : ℝ), digammaBinetKernel z t =
        -∫ t in Set.Ioi (0 : ℝ), digammaBinetRemainderKernel z t) :
    digamma z =
      Complex.log z - z⁻¹ / 2 -
        ∫ t in Set.Ioi (0 : ℝ), digammaBinetKernel z t := by
  rw [digamma_eq_log_sub_half_inv_add_integral hz]
  rw [hkernel]
  ring

/--
Sharp full-norm digamma bound, conditional on the positive second-Binet identity.
This isolates the remaining analytic identity from the completed kernel estimate.
-/
theorem digamma_second_order_full_norm_of_binet_kernel_identity {z : ℂ}
    (hz : (1 / 4 : ℝ) ≤ z.re)
    (hbinet :
      digamma z =
        Complex.log z - z⁻¹ / 2 -
          ∫ t in Set.Ioi (0 : ℝ), digammaBinetKernel z t) :
    ‖digamma z - (Complex.log z - z⁻¹ / 2)‖ ≤ 1 / (6 * ‖z‖ ^ 2) := by
  have hdiff :
      digamma z - (Complex.log z - z⁻¹ / 2) =
        -∫ t in Set.Ioi (0 : ℝ), digammaBinetKernel z t := by
    rw [hbinet]
    ring
  rw [hdiff, norm_neg]
  exact norm_integral_digammaBinetKernel_le hz

/--
Sharp full-norm digamma bound reduced to the single missing positive-kernel bridge.
-/
theorem digamma_second_order_full_norm_of_kernel_eq_neg_remainder {z : ℂ}
    (hz : (1 / 4 : ℝ) ≤ z.re)
    (hkernel :
      ∫ t in Set.Ioi (0 : ℝ), digammaBinetKernel z t =
        -∫ t in Set.Ioi (0 : ℝ), digammaBinetRemainderKernel z t) :
    ‖digamma z - (Complex.log z - z⁻¹ / 2)‖ ≤ 1 / (6 * ‖z‖ ^ 2) := by
  have hzpos : 0 < z.re := by linarith
  exact digamma_second_order_full_norm_of_binet_kernel_identity hz
    (digamma_binet_second_of_kernel_eq_neg_remainder hzpos hkernel)

private lemma integrableOn_lorentzian_shift {x y : ℝ} (hy : y ≠ 0) :
    IntegrableOn (fun t : ℝ => (1 / ((t + x) ^ 2 + y ^ 2) : ℝ))
      (Set.Ioi (0 : ℝ)) volume := by
  have hscaled : Integrable (fun u : ℝ => ((1 + (u / y) ^ 2)⁻¹ : ℝ)) volume := by
    simpa using (integrable_inv_one_add_sq.comp_div hy)
  have hshift : Integrable (fun t : ℝ => ((1 + ((t + x) / y) ^ 2)⁻¹ : ℝ)) volume := by
    simpa [add_comm] using hscaled.comp_add_right x
  have hconst : Integrable
      (fun t : ℝ => (y⁻¹ ^ 2) * ((1 + ((t + x) / y) ^ 2)⁻¹ : ℝ)) volume :=
    hshift.const_mul (y⁻¹ ^ 2)
  refine hconst.integrableOn.congr_fun
    (g := fun t : ℝ => (1 / ((t + x) ^ 2 + y ^ 2) : ℝ)) ?_ measurableSet_Ioi
  intro t _ht
  rw [inv_pow]
  field_simp [hy]
  ring

private lemma half_vertical_inv_half_re {x y : ℝ} (hxy : x ^ 2 + y ^ 2 ≠ 0) :
    (((((x : ℂ) + (y : ℂ) * I) / (2 : ℂ))⁻¹ / (2 : ℂ)).re) =
      x / (x ^ 2 + y ^ 2) := by
  have hnorm : ((((x : ℂ) + (y : ℂ) * I) / (2 : ℂ))⁻¹ / (2 : ℂ)) =
      (((x : ℂ) + (y : ℂ) * I)⁻¹) := by
    by_cases hz : ((x : ℂ) + (y : ℂ) * I) = 0
    · simp [hz]
    · field_simp [hz]
  rw [hnorm, Complex.inv_re]
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  field_simp [hxy]

private lemma abs_log_half_vertical_sub_le {x y : ℝ} (hy : y ≠ 0) :
    |(Complex.log (((x : ℂ) + (y : ℂ) * I) / (2 : ℂ))).re - Real.log (|y| / 2)| ≤
      x ^ 2 / (2 * y ^ 2) := by
  have hnorm : ‖(((x : ℂ) + (y : ℂ) * I) / (2 : ℂ))‖ =
      Real.sqrt ((x ^ 2 + y ^ 2) / 4) := by
    calc
      ‖(((x : ℂ) + (y : ℂ) * I) / (2 : ℂ))‖
          = Real.sqrt (‖(((x : ℂ) + (y : ℂ) * I) / (2 : ℂ))‖ ^ 2) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ = Real.sqrt ((x ^ 2 + y ^ 2) / 4) := by
            congr 1
            rw [← Complex.normSq_eq_norm_sq]
            simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
              Complex.mul_im]
            ring
  have hsqrt : Real.sqrt ((x ^ 2 + y ^ 2) / 4) =
      (|y| / 2) * Real.sqrt (1 + x ^ 2 / y ^ 2) := by
    have hleft : 0 ≤ Real.sqrt ((x ^ 2 + y ^ 2) / 4) := Real.sqrt_nonneg _
    have hright : 0 ≤ (|y| / 2) * Real.sqrt (1 + x ^ 2 / y ^ 2) := by positivity
    have hsqs : Real.sqrt ((x ^ 2 + y ^ 2) / 4) ^ 2 =
        ((|y| / 2) * Real.sqrt (1 + x ^ 2 / y ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt]
      · rw [mul_pow, Real.sq_sqrt]
        · rw [div_pow, sq_abs]
          field_simp [hy]
          ring
        · positivity
      · positivity
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsqs) with h | h
    · exact h
    · nlinarith
  have hlogeq : (Complex.log (((x : ℂ) + (y : ℂ) * I) / (2 : ℂ))).re -
      Real.log (|y| / 2) = (1 / 2 : ℝ) * Real.log (1 + x ^ 2 / y ^ 2) := by
    rw [Complex.log_re, hnorm, hsqrt]
    have hbasepos : 0 < |y| / 2 := by positivity
    have hargpos : 0 < 1 + x ^ 2 / y ^ 2 := by positivity
    rw [Real.log_mul hbasepos.ne' (ne_of_gt (Real.sqrt_pos.2 hargpos))]
    rw [Real.log_sqrt hargpos.le]
    ring
  rw [hlogeq]
  have hfrac : 0 ≤ x ^ 2 / y ^ 2 := by positivity
  have hone : (1 : ℝ) ≤ 1 + x ^ 2 / y ^ 2 := by linarith
  have hnonneg : 0 ≤ (1 / 2 : ℝ) * Real.log (1 + x ^ 2 / y ^ 2) := by
    exact mul_nonneg (by norm_num) (Real.log_nonneg hone)
  rw [abs_of_nonneg hnonneg]
  exact half_log_one_add_sq_div_le hy

private lemma abs_re_inv_sq_le {a b : ℝ} (hb : b ≠ 0) :
    |(((((a : ℂ) + (b : ℂ) * I)⁻¹) ^ (2 : ℕ)).re)| ≤
      1 / (a ^ 2 + b ^ 2) := by
  have hdenpos : 0 < a ^ 2 + b ^ 2 := by
    have hbpos : 0 < b ^ 2 := sq_pos_of_ne_zero hb
    nlinarith [sq_nonneg a]
  have hformula : (((((a : ℂ) + (b : ℂ) * I)⁻¹) ^ (2 : ℕ)).re) =
      (a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2) ^ 2 := by
    rw [pow_two]
    simp [Complex.inv_re, Complex.inv_im, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]
    field_simp [ne_of_gt hdenpos]
  have habs : |a ^ 2 - b ^ 2| ≤ a ^ 2 + b ^ 2 := by
    rw [abs_sub_le_iff]
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  rw [hformula]
  rw [abs_div, abs_pow, abs_of_pos hdenpos]
  calc
    |a ^ 2 - b ^ 2| / (a ^ 2 + b ^ 2) ^ 2
        ≤ (a ^ 2 + b ^ 2) / (a ^ 2 + b ^ 2) ^ 2 := by
          exact div_le_div_of_nonneg_right habs (sq_nonneg _)
    _ = 1 / (a ^ 2 + b ^ 2) := by
          field_simp [ne_of_gt hdenpos]

private lemma abs_re_digammaBinetRemainderKernel_half_vertical_le {x y t : ℝ}
    (hy : y ≠ 0) :
    |(digammaBinetRemainderKernel (((x : ℂ) + (y : ℂ) * I) / (2 : ℂ)) t).re| ≤
      (1 / 2 : ℝ) * (1 / ((t + x / 2) ^ 2 + (y / 2) ^ 2)) := by
  have hy2 : y / 2 ≠ 0 := by
    intro h
    have : y = 0 := by linarith
    exact hy this
  have hinv := abs_re_inv_sq_le (a := t + x / 2) (b := y / 2) hy2
  rw [digammaBinetRemainderKernel]
  have hshift : ((t : ℂ) + (((x : ℂ) + (y : ℂ) * I) / (2 : ℂ))) =
      (((t + x / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I) := by
    apply Complex.ext
    · simp [Complex.mul_re]
    · simp [Complex.mul_im]
  rw [hshift]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [abs_mul]
  have hB1 := norm_fract_sub_half_le t
  rw [norm_real, Real.norm_eq_abs] at hB1
  exact mul_le_mul hB1 hinv (abs_nonneg _) (by norm_num)

private lemma integral_firstOrder_remainder_half_vertical_le {x y : ℝ} (hx : 0 < x)
    (hy : y ≠ 0) :
    |(∫ t in Set.Ioi (0 : ℝ),
        digammaBinetRemainderKernel (((x : ℂ) + (y : ℂ) * I) / (2 : ℂ)) t).re| ≤
      |y|⁻¹ * Real.arctan (|y| / x) := by
  let s : ℂ := (((x : ℂ) + (y : ℂ) * I) / (2 : ℂ))
  have hsre : 0 < s.re := by
    dsimp [s]
    simp [Complex.mul_re]
    linarith
  have hkernel_int : Integrable (fun t : ℝ => digammaBinetRemainderKernel s t)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrableOn_digammaBinetRemainderKernel hsre
  have hre := Complex.reCLM.integral_comp_comm hkernel_int
  change (∫ t in Set.Ioi (0 : ℝ), (digammaBinetRemainderKernel s t).re) =
      (∫ t in Set.Ioi (0 : ℝ), digammaBinetRemainderKernel s t).re at hre
  rw [← hre]
  have habs := MeasureTheory.abs_integral_le_integral_abs
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (f := fun t : ℝ => (digammaBinetRemainderKernel s t).re)
  refine le_trans habs ?_
  have hlor_int : Integrable
      (fun t : ℝ => (1 / 2 : ℝ) * (1 / ((t + x / 2) ^ 2 + (y / 2) ^ 2)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    exact (integrableOn_lorentzian_shift (x := x / 2) (y := y / 2) (by
      intro h
      have : y = 0 := by linarith
      exact hy this)).const_mul (1 / 2 : ℝ)
  have hmono : ∫ t in Set.Ioi (0 : ℝ), |(digammaBinetRemainderKernel s t).re| ≤
      ∫ t in Set.Ioi (0 : ℝ), (1 / 2 : ℝ) *
        (1 / ((t + x / 2) ^ 2 + (y / 2) ^ 2)) := by
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => abs_nonneg ((digammaBinetRemainderKernel s t).re))
      hlor_int
      (by
        filter_upwards with t
        dsimp [s]
        exact abs_re_digammaBinetRemainderKernel_half_vertical_le (x := x) (y := y)
          (t := t) hy)
  refine le_trans hmono ?_
  have hfun : (fun t : ℝ => (1 / 2 : ℝ) *
      (1 / ((t + x / 2) ^ 2 + (y / 2) ^ 2))) =
      fun t : ℝ => (1 / 2 : ℝ) *
        (1 / ((t + x / 2) ^ 2 + (|y| / 2) ^ 2)) := by
    funext t
    rw [div_pow, div_pow, sq_abs]
  rw [hfun]
  rw [MeasureTheory.integral_const_mul]
  have hI := integral_Ioi_shifted_inv_sq_add_sq_eq_arctan
    (x := x / 2) (y := |y| / 2) (by linarith) (by positivity)
  rw [hI]
  field_simp [hx.ne', abs_pos.mpr hy]
  norm_num

/--
Kadiri vertical real-part bound for the digamma term at `(x + iy) / 2`.
This is the Prop. 2.2 shape: the logarithmic split contributes the quadratic term,
and the first-order Binet remainder contributes the arctangent Lorentzian tail.
-/
theorem re_digamma_half_vertical_bound {x y : ℝ} (hx : 0 < x) (hy : y ≠ 0) :
    |(digamma (((x : ℂ) + (y : ℂ) * I) / (2 : ℂ))).re -
        (Real.log (|y| / 2) - x / (x ^ 2 + y ^ 2))| ≤
      |y|⁻¹ * Real.arctan (|y| / x) + x ^ 2 / (2 * y ^ 2) := by
  let s : ℂ := (((x : ℂ) + (y : ℂ) * I) / (2 : ℂ))
  have hsre : 0 < s.re := by
    dsimp [s]
    simp [Complex.mul_re]
    linarith
  have hbinet := digamma_eq_log_sub_half_inv_add_integral hsre
  have hxy : x ^ 2 + y ^ 2 ≠ 0 := by
    have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
    nlinarith [sq_nonneg x]
  have hinv : (s⁻¹ / 2).re = x / (x ^ 2 + y ^ 2) := by
    simpa [s] using half_vertical_inv_half_re (x := x) (y := y) hxy
  have heq : (digamma s).re - (Real.log (|y| / 2) - x / (x ^ 2 + y ^ 2)) =
      ((Complex.log s).re - Real.log (|y| / 2)) +
        (∫ t in Set.Ioi (0 : ℝ), digammaBinetRemainderKernel s t).re := by
    rw [hbinet]
    simp only [Complex.add_re, Complex.sub_re]
    rw [hinv]
    ring
  rw [heq]
  calc
    |(Complex.log s).re - Real.log (|y| / 2) +
        (∫ t in Set.Ioi (0 : ℝ), digammaBinetRemainderKernel s t).re|
        ≤ |(Complex.log s).re - Real.log (|y| / 2)| +
          |(∫ t in Set.Ioi (0 : ℝ), digammaBinetRemainderKernel s t).re| :=
            abs_add_le _ _
    _ ≤ x ^ 2 / (2 * y ^ 2) + |y|⁻¹ * Real.arctan (|y| / x) := by
          exact add_le_add
            (by simpa [s] using abs_log_half_vertical_sub_le (x := x) (y := y) hy)
            (by
              simpa [s] using
                (integral_firstOrder_remainder_half_vertical_le (x := x) (y := y) hx hy))
    _ ≤ |y|⁻¹ * Real.arctan (|y| / x) + x ^ 2 / (2 * y ^ 2) := by
          rw [add_comm]

/--
Boundary-corrected second-order Binet identity for `digamma` on the right half-plane.
The `-s⁻² / 12` term is the fixed lower-endpoint Euler-Maclaurin boundary term.
-/
theorem digamma_eq_log_sub_half_inv_sub_inv_sq_add_integral {s : ℂ} (hs : 0 < s.re) :
    digamma s = Complex.log s - s⁻¹ / 2 - (s⁻¹ ^ (2 : ℕ)) / 12 +
      ∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t := by
  let C : ℂ := Complex.log s - s⁻¹ / 2 - (s⁻¹ ^ (2 : ℕ)) / 12
  let K : ℕ → ℂ := fun N => (((N : ℂ) + s)⁻¹)
  have hdig := tendsto_log_sub_sum_inv_add_of_re_pos hs
  have hlogdiff := tendsto_log_nat_sub_log_nat_add hs
  have hK : Tendsto K atTop (𝓝 0) := by
    simpa [K] using tendsto_inv_nat_add s
  have hint : Tendsto
      (fun N : ℕ => ∫ t in (0 : ℝ)..(N : ℝ), digammaBinetSecondOrderRemainderKernel s t)
      atTop (𝓝 (∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t)) := by
    exact intervalIntegral_tendsto_integral_Ioi (μ := volume) (a := (0 : ℝ))
      (integrableOn_digammaBinetSecondOrderRemainderKernel hs)
      (show Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop from tendsto_natCast_atTop_atTop)
  have hC : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
  have h1 : Tendsto
      (fun N : ℕ => ((Real.log N : ℂ) - Complex.log ((N : ℂ) + s)) + C)
      atTop (𝓝 (0 + C)) := hlogdiff.add hC
  have h2 : Tendsto
      (fun N : ℕ => ((Real.log N : ℂ) - Complex.log ((N : ℂ) + s)) + C - K N / 2)
      atTop (𝓝 (0 + C - 0 / 2)) := h1.sub (hK.div_const 2)
  have h3 : Tendsto
      (fun N : ℕ => ((Real.log N : ℂ) - Complex.log ((N : ℂ) + s)) + C - K N / 2 +
        (K N ^ (2 : ℕ)) / 12)
      atTop (𝓝 (0 + C - 0 / 2 + (0 ^ (2 : ℕ)) / 12)) :=
    h2.add ((hK.pow 2).div_const 12)
  have hseq_lim : Tendsto
      (fun N : ℕ => ((Real.log N : ℂ) - Complex.log ((N : ℂ) + s)) + C - K N / 2 +
        (K N ^ (2 : ℕ)) / 12 +
        ∫ t in (0 : ℝ)..(N : ℝ), digammaBinetSecondOrderRemainderKernel s t)
      atTop (𝓝 (C + ∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t)) := by
    have h4 := h3.add hint
    simpa [C, K] using h4
  have hseq_eq :
      (fun N : ℕ => (Real.log N : ℂ) -
        ∑ m ∈ Finset.range (N + 1), (s + m)⁻¹) =
      (fun N : ℕ => ((Real.log N : ℂ) - Complex.log ((N : ℂ) + s)) + C - K N / 2 +
        (K N ^ (2 : ℕ)) / 12 +
        ∫ t in (0 : ℝ)..(N : ℝ), digammaBinetSecondOrderRemainderKernel s t) := by
    funext N
    rw [sum_range_succ_resolvent_eq s N]
    rw [sum_Ioc_resolvent_eq_log_boundary_sub_integral hs N]
    simp [C, K]
    ring_nf
  rw [hseq_eq] at hdig
  have hlim := tendsto_nhds_unique hdig hseq_lim
  simpa [C] using hlim

/-- Norm bound for the corrected second-order Binet remainder in the right half-plane. -/
theorem norm_digamma_sub_log_sub_half_inv_add_inv_sq_le {s : ℂ} (hs : 0 < s.re) :
    ‖digamma s - (Complex.log s - s⁻¹ / 2 - (s⁻¹ ^ (2 : ℕ)) / 12)‖ ≤
      1 / (12 * s.re ^ 2) := by
  have h := digamma_eq_log_sub_half_inv_sub_inv_sq_add_integral (s := s) hs
  calc
    ‖digamma s - (Complex.log s - s⁻¹ / 2 - (s⁻¹ ^ (2 : ℕ)) / 12)‖
        = ‖∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t‖ := by
          rw [h]
          ring_nf
    _ ≤ 1 / (12 * s.re ^ 2) :=
          norm_integral_digammaBinetSecondOrderRemainderKernel_le hs

/-- Recombine the first- and second-order Binet identities by cancelling their common digamma term. -/
theorem neg_inv_sq_div_twelve_add_integral_secondOrder_eq_integral_firstOrder {s : ℂ}
    (hs : 0 < s.re) :
    -(s⁻¹ ^ (2 : ℕ)) / 12 + ∫ t in Set.Ioi (0 : ℝ),
        digammaBinetSecondOrderRemainderKernel s t =
      ∫ t in Set.Ioi (0 : ℝ), digammaBinetRemainderKernel s t := by
  have h1 := digamma_eq_log_sub_half_inv_add_integral (s := s) hs
  have h2 := digamma_eq_log_sub_half_inv_sub_inv_sq_add_integral (s := s) hs
  have h := h2.symm.trans h1
  linear_combination h

/-- Pointwise domination of the second-order kernel by the shifted norm-cube. -/
lemma norm_digammaBinetSecondOrderRemainderKernel_le_norm_cube {s : ℂ} (t : ℝ) :
    ‖digammaBinetSecondOrderRemainderKernel s t‖ ≤
      (1 / 6 : ℝ) * ‖(t : ℂ) + s‖⁻¹ ^ (3 : ℕ) := by
  calc
    ‖digammaBinetSecondOrderRemainderKernel s t‖
        = 2 * ‖bernoulli2PeriodizedHalf t‖ * ‖(t : ℂ) + s‖⁻¹ ^ (3 : ℕ) := by
          rw [digammaBinetSecondOrderRemainderKernel, norm_mul, norm_mul, norm_pow, norm_inv]
          norm_num
    _ ≤ 2 * (1 / 12 : ℝ) * ‖(t : ℂ) + s‖⁻¹ ^ (3 : ℕ) := by
          gcongr
          exact norm_bernoulli2PeriodizedHalf_le t
    _ = (1 / 6 : ℝ) * ‖(t : ℂ) + s‖⁻¹ ^ (3 : ℕ) := by
          ring

/-- Vertical-line pointwise decay for the norm-cube tail. -/
lemma norm_add_inv_cube_le_vertical_square {s : ℂ} {t : ℝ} (hs : 0 < s.re)
    (him : s.im ≠ 0) (ht : 0 < t) :
    ‖(t : ℂ) + s‖⁻¹ ^ (3 : ℕ) ≤ |s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ)) := by
  have hpos : 0 < t + s.re := by linarith
  have hnorm_x : t + s.re ≤ ‖(t : ℂ) + s‖ := by
    have h := Complex.re_le_norm ((t : ℂ) + s)
    simpa [add_comm, add_left_comm, add_assoc] using h
  have hnorm_pos : 0 < ‖(t : ℂ) + s‖ := lt_of_lt_of_le hpos hnorm_x
  have hypos : 0 < |s.im| := abs_pos.mpr him
  have hnorm_y : |s.im| ≤ ‖(t : ℂ) + s‖ := by
    have h := Complex.abs_im_le_norm ((t : ℂ) + s)
    simpa using h
  have hinv_y : ‖(t : ℂ) + s‖⁻¹ ≤ |s.im|⁻¹ := inv_anti₀ hypos hnorm_y
  have hinv_x : ‖(t : ℂ) + s‖⁻¹ ≤ (t + s.re)⁻¹ := inv_anti₀ hpos hnorm_x
  have hsq : ‖(t : ℂ) + s‖⁻¹ ^ (2 : ℕ) ≤ (t + s.re)⁻¹ ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ (inv_nonneg.mpr hnorm_pos.le) hinv_x 2
  have hpow_eq : (t + s.re) ^ (-(2 : ℝ)) = (t + s.re)⁻¹ ^ (2 : ℕ) := by
    rw [Real.rpow_neg hpos.le, Real.rpow_two, inv_pow]
  calc
    ‖(t : ℂ) + s‖⁻¹ ^ (3 : ℕ)
        = ‖(t : ℂ) + s‖⁻¹ * ‖(t : ℂ) + s‖⁻¹ ^ (2 : ℕ) := by ring
    _ ≤ |s.im|⁻¹ * ((t + s.re)⁻¹ ^ (2 : ℕ)) := by
      exact mul_le_mul hinv_y hsq (pow_nonneg (inv_nonneg.mpr hnorm_pos.le) 2)
        (inv_nonneg.mpr hypos.le)
    _ = |s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ)) := by rw [hpow_eq]

/-- The vertical square majorant is integrable on `(0, ∞)`. -/
lemma integrableOn_digammaBinetVerticalSquareMajorant {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => |s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ)))
      (Set.Ioi (0 : ℝ)) volume := by
  have hmaj_base := integrableOn_digammaBinetRemainderMajorant (σ := s.re) hs
  have h := hmaj_base.const_mul (2 * |s.im|⁻¹)
  change Integrable (fun t : ℝ => |s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ)))
    (volume.restrict (Set.Ioi (0 : ℝ)))
  change Integrable
    (fun t : ℝ => (2 * |s.im|⁻¹) * ((1 / 2 : ℝ) * (t + s.re) ^ (-(2 : ℝ))))
    (volume.restrict (Set.Ioi (0 : ℝ))) at h
  convert h using 1
  ext t
  ring

/-- Evaluation of the vertical square majorant integral. -/
lemma integral_Ioi_digammaBinetVerticalSquareMajorant {s : ℂ} (hs : 0 < s.re)
    (him : s.im ≠ 0) :
    ∫ t in Set.Ioi (0 : ℝ), |s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ)) =
      1 / (s.re * |s.im|) := by
  have hbase := integral_Ioi_digammaBinetRemainderMajorant (σ := s.re) hs
  calc
    ∫ t in Set.Ioi (0 : ℝ), |s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ))
        = (2 * |s.im|⁻¹) *
            ∫ t in Set.Ioi (0 : ℝ), (1 / 2 : ℝ) * (t + s.re) ^ (-(2 : ℝ)) := by
          rw [← MeasureTheory.integral_const_mul]
          congr 1
          ext t
          ring
    _ = 1 / (s.re * |s.im|) := by
          rw [hbase]
          field_simp [ne_of_gt hs, ne_of_gt (abs_pos.mpr him)]

/-- Integral tail bound with vertical decay. -/
lemma integral_Ioi_norm_add_inv_cube_le_vertical {s : ℂ} (hs : 0 < s.re)
    (him : s.im ≠ 0) :
    ∫ t in Set.Ioi (0 : ℝ), ‖(t : ℂ) + s‖⁻¹ ^ (3 : ℕ) ≤
      1 / (s.re * |s.im|) := by
  have hmaj := integrableOn_digammaBinetVerticalSquareMajorant (s := s) hs
  have hmono :
      ∫ t in Set.Ioi (0 : ℝ), ‖(t : ℂ) + s‖⁻¹ ^ (3 : ℕ) ≤
        ∫ t in Set.Ioi (0 : ℝ), |s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ)) := by
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) 3)
      hmaj
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        exact norm_add_inv_cube_le_vertical_square hs him ht)
  exact hmono.trans_eq (integral_Ioi_digammaBinetVerticalSquareMajorant hs him)

/-- Norm bound for the second-order kernel integral with vertical decay. -/
lemma norm_integral_digammaBinetSecondOrderRemainderKernel_le_vertical {s : ℂ}
    (hs : 0 < s.re) (him : s.im ≠ 0) :
    ‖∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t‖ ≤
      1 / (s.re * |s.im|) := by
  have hnorm := MeasureTheory.norm_integral_le_integral_norm
    (μ := volume.restrict (Set.Ioi (0 : ℝ))) (f := digammaBinetSecondOrderRemainderKernel s)
  have hmaj : IntegrableOn
      (fun t : ℝ => (1 / 6 : ℝ) * (|s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ))))
      (Set.Ioi (0 : ℝ)) volume :=
    (integrableOn_digammaBinetVerticalSquareMajorant (s := s) hs).const_mul (1 / 6 : ℝ)
  have hmono :
      ∫ t in Set.Ioi (0 : ℝ), ‖digammaBinetSecondOrderRemainderKernel s t‖ ≤
        ∫ t in Set.Ioi (0 : ℝ), (1 / 6 : ℝ) *
          (|s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ))) := by
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => norm_nonneg (digammaBinetSecondOrderRemainderKernel s t))
      hmaj
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        calc
          ‖digammaBinetSecondOrderRemainderKernel s t‖
              ≤ (1 / 6 : ℝ) * ‖(t : ℂ) + s‖⁻¹ ^ (3 : ℕ) :=
                norm_digammaBinetSecondOrderRemainderKernel_le_norm_cube t
          _ ≤ (1 / 6 : ℝ) * (|s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ))) := by
            exact mul_le_mul_of_nonneg_left
              (norm_add_inv_cube_le_vertical_square hs him ht) (by norm_num))
  have hval :
      ∫ t in Set.Ioi (0 : ℝ), (1 / 6 : ℝ) *
          (|s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ)))
        ≤ 1 / (s.re * |s.im|) := by
    calc
      ∫ t in Set.Ioi (0 : ℝ), (1 / 6 : ℝ) *
          (|s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ)))
          = (1 / 6 : ℝ) *
              ∫ t in Set.Ioi (0 : ℝ), |s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ)) := by
            rw [MeasureTheory.integral_const_mul]
      _ = (1 / 6 : ℝ) * (1 / (s.re * |s.im|)) := by
            rw [integral_Ioi_digammaBinetVerticalSquareMajorant hs him]
      _ ≤ 1 / (s.re * |s.im|) := by
            have hden : 0 < s.re * |s.im| := mul_pos hs (abs_pos.mpr him)
            have hone : 0 ≤ 1 / (s.re * |s.im|) := one_div_nonneg.mpr hden.le
            nlinarith
  exact hnorm.trans (hmono.trans hval)

/-- Norm bound for the second-order kernel integral with the explicit `1/6` vertical constant. -/
lemma norm_integral_secondOrderKernel_le_vertical_sharp {s : ℂ} (hs : 0 < s.re)
    (him : s.im ≠ 0) :
    ‖∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t‖ ≤
      (1 / 6 : ℝ) / (s.re * |s.im|) := by
  have hnorm := MeasureTheory.norm_integral_le_integral_norm
    (μ := volume.restrict (Set.Ioi (0 : ℝ))) (f := digammaBinetSecondOrderRemainderKernel s)
  have hmaj : IntegrableOn
      (fun t : ℝ => (1 / 6 : ℝ) * (|s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ))))
      (Set.Ioi (0 : ℝ)) volume :=
    (integrableOn_digammaBinetVerticalSquareMajorant (s := s) hs).const_mul (1 / 6 : ℝ)
  have hmono :
      ∫ t in Set.Ioi (0 : ℝ), ‖digammaBinetSecondOrderRemainderKernel s t‖ ≤
        ∫ t in Set.Ioi (0 : ℝ), (1 / 6 : ℝ) *
          (|s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ))) := by
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => norm_nonneg (digammaBinetSecondOrderRemainderKernel s t))
      hmaj
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        calc
          ‖digammaBinetSecondOrderRemainderKernel s t‖
              ≤ (1 / 6 : ℝ) * ‖(t : ℂ) + s‖⁻¹ ^ (3 : ℕ) :=
                norm_digammaBinetSecondOrderRemainderKernel_le_norm_cube t
          _ ≤ (1 / 6 : ℝ) * (|s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ))) := by
            exact mul_le_mul_of_nonneg_left
              (norm_add_inv_cube_le_vertical_square hs him ht) (by norm_num))
  calc
    ‖∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t‖
        ≤ ∫ t in Set.Ioi (0 : ℝ), ‖digammaBinetSecondOrderRemainderKernel s t‖ := hnorm
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), (1 / 6 : ℝ) *
          (|s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ))) := hmono
    _ = (1 / 6 : ℝ) / (s.re * |s.im|) := by
      rw [MeasureTheory.integral_const_mul]
      rw [integral_Ioi_digammaBinetVerticalSquareMajorant hs him]
      ring

/--
Pointwise real-part decay for the inverse-square resolvent on a vertical line.
Writing `w = a + ib`, this is the elementary bound
`|Re(w⁻²)| ≤ 1 / (2 a |b|)`.
-/
lemma abs_re_inv_sq_le_vertical_two {a b : ℝ} (ha : 0 < a) (hb : b ≠ 0) :
    |(((((a : ℂ) + (b : ℂ) * I)⁻¹) ^ (2 : ℕ)).re)| ≤
      (1 / 2 : ℝ) / (a * |b|) := by
  have hdenpos : 0 < a ^ 2 + b ^ 2 := by
    have hbpos : 0 < b ^ 2 := sq_pos_of_ne_zero hb
    nlinarith [sq_nonneg a]
  have hformula : (((((a : ℂ) + (b : ℂ) * I)⁻¹) ^ (2 : ℕ)).re) =
      (a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2) ^ 2 := by
    rw [pow_two]
    simp [Complex.inv_re, Complex.inv_im, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im]
    field_simp [ne_of_gt hdenpos]
  have habs : |a ^ 2 - b ^ 2| ≤ a ^ 2 + b ^ 2 := by
    rw [abs_sub_le_iff]
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  have hfirst : |(((((a : ℂ) + (b : ℂ) * I)⁻¹) ^ (2 : ℕ)).re)| ≤
      1 / (a ^ 2 + b ^ 2) := by
    rw [hformula]
    rw [abs_div, abs_pow, abs_of_pos hdenpos]
    calc
      |a ^ 2 - b ^ 2| / (a ^ 2 + b ^ 2) ^ 2
          ≤ (a ^ 2 + b ^ 2) / (a ^ 2 + b ^ 2) ^ 2 := by
            exact div_le_div_of_nonneg_right habs (sq_nonneg _)
      _ = 1 / (a ^ 2 + b ^ 2) := by
            field_simp [ne_of_gt hdenpos]
  have htwo : 2 * a * |b| ≤ a ^ 2 + b ^ 2 := by
    have hsq : 0 ≤ (a - |b|) ^ 2 := sq_nonneg (a - |b|)
    nlinarith [sq_abs b]
  have htwopos : 0 < 2 * a * |b| := by positivity
  have hsecond : 1 / (a ^ 2 + b ^ 2) ≤ 1 / (2 * a * |b|) := by
    simpa [one_div] using inv_anti₀ htwopos htwo
  calc
    |(((((a : ℂ) + (b : ℂ) * I)⁻¹) ^ (2 : ℕ)).re)|
        ≤ 1 / (a ^ 2 + b ^ 2) := hfirst
    _ ≤ 1 / (2 * a * |b|) := hsecond
    _ = (1 / 2 : ℝ) / (a * |b|) := by ring

/--
AM-GM sharpened vertical-line pointwise decay for the norm-cube tail.
Compared with `norm_add_inv_cube_le_vertical_square`, this saves a factor `1 / 2`.
-/
lemma norm_add_inv_cube_le_vertical_square_half {s : ℂ} {t : ℝ} (hs : 0 < s.re)
    (him : s.im ≠ 0) (ht : 0 < t) :
    ‖(t : ℂ) + s‖⁻¹ ^ (3 : ℕ) ≤
      (1 / 2 : ℝ) * (|s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ))) := by
  have hpos : 0 < t + s.re := by linarith
  have hnorm_x : t + s.re ≤ ‖(t : ℂ) + s‖ := by
    have h := Complex.re_le_norm ((t : ℂ) + s)
    simpa [add_comm, add_left_comm, add_assoc] using h
  have hnorm_pos : 0 < ‖(t : ℂ) + s‖ := lt_of_lt_of_le hpos hnorm_x
  have hypos : 0 < |s.im| := abs_pos.mpr him
  have hinv_x : ‖(t : ℂ) + s‖⁻¹ ≤ (t + s.re)⁻¹ := inv_anti₀ hpos hnorm_x
  have hnorm_sq : 2 * (t + s.re) * |s.im| ≤ ‖(t : ℂ) + s‖ ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re, Complex.add_im,
      Complex.ofReal_im]
    have hsq : 0 ≤ (t + s.re - |s.im|) ^ 2 := sq_nonneg (t + s.re - |s.im|)
    nlinarith [sq_abs s.im]
  have htwopos : 0 < 2 * (t + s.re) * |s.im| := by positivity
  have hsq_inv : ‖(t : ℂ) + s‖⁻¹ ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * ((t + s.re)⁻¹ * |s.im|⁻¹) := by
    calc
      ‖(t : ℂ) + s‖⁻¹ ^ (2 : ℕ)
          = (‖(t : ℂ) + s‖ ^ (2 : ℕ))⁻¹ := by rw [← inv_pow]
      _ ≤ (2 * (t + s.re) * |s.im|)⁻¹ := inv_anti₀ htwopos hnorm_sq
      _ = (1 / 2 : ℝ) * ((t + s.re)⁻¹ * |s.im|⁻¹) := by
            field_simp [ne_of_gt hpos, ne_of_gt hypos]
  have hpow_eq : (t + s.re) ^ (-(2 : ℝ)) = (t + s.re)⁻¹ ^ (2 : ℕ) := by
    rw [Real.rpow_neg hpos.le, Real.rpow_two, inv_pow]
  calc
    ‖(t : ℂ) + s‖⁻¹ ^ (3 : ℕ)
        = ‖(t : ℂ) + s‖⁻¹ * ‖(t : ℂ) + s‖⁻¹ ^ (2 : ℕ) := by ring
    _ ≤ (t + s.re)⁻¹ *
          ((1 / 2 : ℝ) * ((t + s.re)⁻¹ * |s.im|⁻¹)) := by
            exact mul_le_mul hinv_x hsq_inv
              (pow_nonneg (inv_nonneg.mpr hnorm_pos.le) 2)
              (inv_nonneg.mpr hpos.le)
    _ = (1 / 2 : ℝ) * (|s.im|⁻¹ * ((t + s.re)⁻¹ ^ (2 : ℕ))) := by ring
    _ = (1 / 2 : ℝ) * (|s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ))) := by rw [hpow_eq]

/-- Norm bound for the second-order kernel integral with the sharpened `1/12` constant. -/
lemma norm_integral_secondOrderKernel_le_vertical_target {s : ℂ} (hs : 0 < s.re)
    (him : s.im ≠ 0) :
    ‖∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t‖ ≤
      (1 / 12 : ℝ) / (s.re * |s.im|) := by
  have hnorm := MeasureTheory.norm_integral_le_integral_norm
    (μ := volume.restrict (Set.Ioi (0 : ℝ))) (f := digammaBinetSecondOrderRemainderKernel s)
  have hmaj : IntegrableOn
      (fun t : ℝ => (1 / 12 : ℝ) * (|s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ))))
      (Set.Ioi (0 : ℝ)) volume :=
    (integrableOn_digammaBinetVerticalSquareMajorant (s := s) hs).const_mul (1 / 12 : ℝ)
  have hmono :
      ∫ t in Set.Ioi (0 : ℝ), ‖digammaBinetSecondOrderRemainderKernel s t‖ ≤
        ∫ t in Set.Ioi (0 : ℝ), (1 / 12 : ℝ) *
          (|s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ))) := by
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => norm_nonneg (digammaBinetSecondOrderRemainderKernel s t))
      hmaj
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        calc
          ‖digammaBinetSecondOrderRemainderKernel s t‖
              ≤ (1 / 6 : ℝ) * ‖(t : ℂ) + s‖⁻¹ ^ (3 : ℕ) :=
                norm_digammaBinetSecondOrderRemainderKernel_le_norm_cube t
          _ ≤ (1 / 6 : ℝ) *
                ((1 / 2 : ℝ) * (|s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ)))) := by
                  exact mul_le_mul_of_nonneg_left
                    (norm_add_inv_cube_le_vertical_square_half hs him ht) (by norm_num)
          _ = (1 / 12 : ℝ) * (|s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ))) := by ring)
  calc
    ‖∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t‖
        ≤ ∫ t in Set.Ioi (0 : ℝ), ‖digammaBinetSecondOrderRemainderKernel s t‖ := hnorm
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), (1 / 12 : ℝ) *
          (|s.im|⁻¹ * (t + s.re) ^ (-(2 : ℝ))) := hmono
    _ = (1 / 12 : ℝ) / (s.re * |s.im|) := by
          rw [MeasureTheory.integral_const_mul]
          rw [integral_Ioi_digammaBinetVerticalSquareMajorant hs him]
          ring

/-- Boundary real-part bound for the second-order Binet correction. -/
lemma abs_re_neg_inv_sq_div_twelve_le_vertical_target {s : ℂ} (hs : 0 < s.re)
    (him : s.im ≠ 0) :
    |((-(s⁻¹ ^ (2 : ℕ)) / (12 : ℂ)).re)| ≤
      (1 / 24 : ℝ) / (s.re * |s.im|) := by
  have hsq : |((s⁻¹ ^ (2 : ℕ)).re)| ≤ (1 / 2 : ℝ) / (s.re * |s.im|) := by
    have hs_eq : ((s.re : ℂ) + (s.im : ℂ) * I) = s := Complex.re_add_im s
    rw [← hs_eq]
    simpa [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] using
      (abs_re_inv_sq_le_vertical_two (a := s.re) (b := s.im) hs him)
  calc
    |((-(s⁻¹ ^ (2 : ℕ)) / (12 : ℂ)).re)|
        = |((s⁻¹ ^ (2 : ℕ)).re)| / 12 := by
          rw [Complex.div_re, Complex.neg_re]
          norm_num
          rw [abs_div, abs_neg]
          norm_num
          ring
    _ ≤ ((1 / 2 : ℝ) / (s.re * |s.im|)) / 12 := by
          exact div_le_div_of_nonneg_right hsq (by norm_num)
    _ = (1 / 24 : ℝ) / (s.re * |s.im|) := by ring

/-- Boundary term bound for the second-order Binet correction. -/
lemma norm_neg_inv_sq_div_twelve_le_vertical {s : ℂ} (hs : 0 < s.re)
    (him : s.im ≠ 0) :
    ‖-(s⁻¹ ^ (2 : ℕ)) / (12 : ℂ)‖ ≤ 1 / (s.re * |s.im|) := by
  have hxnorm : s.re ≤ ‖s‖ := Complex.re_le_norm s
  have hnorm_pos : 0 < ‖s‖ := lt_of_lt_of_le hs hxnorm
  have hypos : 0 < |s.im| := abs_pos.mpr him
  have hynorm : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hinv_x : ‖s‖⁻¹ ≤ s.re⁻¹ := inv_anti₀ hs hxnorm
  have hinv_y : ‖s‖⁻¹ ≤ |s.im|⁻¹ := inv_anti₀ hypos hynorm
  have hsq : ‖s‖⁻¹ ^ (2 : ℕ) ≤ s.re⁻¹ * |s.im|⁻¹ := by
    calc
      ‖s‖⁻¹ ^ (2 : ℕ) = ‖s‖⁻¹ * ‖s‖⁻¹ := by ring
      _ ≤ s.re⁻¹ * |s.im|⁻¹ := by
        exact mul_le_mul hinv_x hinv_y (inv_nonneg.mpr hnorm_pos.le) (inv_nonneg.mpr hs.le)
  have hprod_nonneg : 0 ≤ s.re⁻¹ * |s.im|⁻¹ := by
    exact mul_nonneg (inv_nonneg.mpr hs.le) (inv_nonneg.mpr hypos.le)
  have hdiv : s.re⁻¹ * |s.im|⁻¹ / 12 ≤ s.re⁻¹ * |s.im|⁻¹ := by
    nlinarith
  calc
    ‖-(s⁻¹ ^ (2 : ℕ)) / (12 : ℂ)‖
        = ‖s‖⁻¹ ^ (2 : ℕ) / 12 := by
          rw [norm_div, norm_neg, norm_pow, norm_inv]
          norm_num
    _ ≤ (s.re⁻¹ * |s.im|⁻¹) / 12 := div_le_div_of_nonneg_right hsq (by norm_num)
    _ ≤ s.re⁻¹ * |s.im|⁻¹ := hdiv
    _ = 1 / (s.re * |s.im|) := by
      field_simp [ne_of_gt hs, ne_of_gt hypos]

/-- Boundary term bound with the explicit `/12` vertical constant. -/
lemma norm_neg_inv_sq_div_twelve_le_vertical_sharp {s : ℂ} (hs : 0 < s.re)
    (him : s.im ≠ 0) :
    ‖-(s⁻¹ ^ (2 : ℕ)) / (12 : ℂ)‖ ≤ (1 / 12 : ℝ) / (s.re * |s.im|) := by
  have hxnorm : s.re ≤ ‖s‖ := Complex.re_le_norm s
  have hnorm_pos : 0 < ‖s‖ := lt_of_lt_of_le hs hxnorm
  have hypos : 0 < |s.im| := abs_pos.mpr him
  have hynorm : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hinv_x : ‖s‖⁻¹ ≤ s.re⁻¹ := inv_anti₀ hs hxnorm
  have hinv_y : ‖s‖⁻¹ ≤ |s.im|⁻¹ := inv_anti₀ hypos hynorm
  have hsq : ‖s‖⁻¹ ^ (2 : ℕ) ≤ s.re⁻¹ * |s.im|⁻¹ := by
    calc
      ‖s‖⁻¹ ^ (2 : ℕ) = ‖s‖⁻¹ * ‖s‖⁻¹ := by ring
      _ ≤ s.re⁻¹ * |s.im|⁻¹ := by
        exact mul_le_mul hinv_x hinv_y (inv_nonneg.mpr hnorm_pos.le) (inv_nonneg.mpr hs.le)
  calc
    ‖-(s⁻¹ ^ (2 : ℕ)) / (12 : ℂ)‖
        = ‖s‖⁻¹ ^ (2 : ℕ) / 12 := by
          rw [norm_div, norm_neg, norm_pow, norm_inv]
          norm_num
    _ ≤ (s.re⁻¹ * |s.im|⁻¹) / 12 := div_le_div_of_nonneg_right hsq (by norm_num)
    _ = (1 / 12 : ℝ) / (s.re * |s.im|) := by
      field_simp [ne_of_gt hs, ne_of_gt hypos]

/-- Absolute real-part vertical bound for the corrected second-order Binet remainder. -/
theorem re_neg_inv_sq_div_twelve_add_integral_secondOrder_le_quarter {s : ℂ}
    (hs : 0 < s.re) (him : s.im ≠ 0) :
    |(-(s⁻¹ ^ (2 : ℕ)) / 12 +
        ∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t).re| ≤
      (1 / 4 : ℝ) / (s.re * |s.im|) := by
  let boundary : ℂ := -(s⁻¹ ^ (2 : ℕ)) / (12 : ℂ)
  let tail : ℂ := ∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t
  have hre : |(boundary + tail).re| ≤ ‖boundary + tail‖ := Complex.abs_re_le_norm _
  have htri : ‖boundary + tail‖ ≤ ‖boundary‖ + ‖tail‖ := norm_add_le _ _
  have hboundary : ‖boundary‖ ≤ (1 / 12 : ℝ) / (s.re * |s.im|) := by
    simpa [boundary] using norm_neg_inv_sq_div_twelve_le_vertical_sharp hs him
  have htail : ‖tail‖ ≤ (1 / 6 : ℝ) / (s.re * |s.im|) := by
    simpa [tail] using norm_integral_secondOrderKernel_le_vertical_sharp hs him
  have hsum : ‖boundary‖ + ‖tail‖ ≤ (1 / 4 : ℝ) / (s.re * |s.im|) := by
    calc
      ‖boundary‖ + ‖tail‖
          ≤ (1 / 12 : ℝ) / (s.re * |s.im|) + (1 / 6 : ℝ) / (s.re * |s.im|) :=
            add_le_add hboundary htail
      _ = (1 / 4 : ℝ) / (s.re * |s.im|) := by ring
  exact hre.trans (htri.trans hsum)

/--
Absolute real-part vertical bound for the corrected second-order Binet remainder.
The explicit target constant is `1 / 8`, below `1635 / 10000`.
-/
theorem re_neg_inv_sq_div_twelve_add_integral_secondOrder_le_target {s : ℂ}
    (hs : 0 < s.re) (him : s.im ≠ 0) :
    |(-(s⁻¹ ^ (2 : ℕ)) / 12 +
        ∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t).re| ≤
      (1 / 8 : ℝ) / (s.re * |s.im|) := by
  let boundary : ℂ := -(s⁻¹ ^ (2 : ℕ)) / (12 : ℂ)
  let tail : ℂ := ∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t
  have hre : |(boundary + tail).re| ≤ |boundary.re| + |tail.re| := by
    rw [Complex.add_re]
    exact abs_add_le boundary.re tail.re
  have hboundary : |boundary.re| ≤ (1 / 24 : ℝ) / (s.re * |s.im|) := by
    simpa [boundary] using abs_re_neg_inv_sq_div_twelve_le_vertical_target hs him
  have htail : |tail.re| ≤ (1 / 12 : ℝ) / (s.re * |s.im|) := by
    exact (Complex.abs_re_le_norm tail).trans
      (by simpa [tail] using norm_integral_secondOrderKernel_le_vertical_target hs him)
  have hsum : |boundary.re| + |tail.re| ≤ (1 / 8 : ℝ) / (s.re * |s.im|) := by
    calc
      |boundary.re| + |tail.re|
          ≤ (1 / 24 : ℝ) / (s.re * |s.im|) +
              (1 / 12 : ℝ) / (s.re * |s.im|) := add_le_add hboundary htail
      _ = (1 / 8 : ℝ) / (s.re * |s.im|) := by ring
  exact hre.trans hsum

/--
Combined real-part bound for the second-order Binet correction on vertical lines.
The relaxed explicit constant is `2`.
-/
theorem re_digamma_vertical_second_order_bound {s : ℂ} (hs : 0 < s.re)
    (him : s.im ≠ 0) (_hle : s.re ≤ |s.im|) :
    ((-(s⁻¹ ^ (2 : ℕ)) / (12 : ℂ) +
        ∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t).re) ≤
      2 / (s.re * |s.im|) := by
  let boundary : ℂ := -(s⁻¹ ^ (2 : ℕ)) / (12 : ℂ)
  let tail : ℂ := ∫ t in Set.Ioi (0 : ℝ), digammaBinetSecondOrderRemainderKernel s t
  have hre : (boundary + tail).re ≤ ‖boundary + tail‖ := Complex.re_le_norm _
  have htri : ‖boundary + tail‖ ≤ ‖boundary‖ + ‖tail‖ := norm_add_le _ _
  have hboundary : ‖boundary‖ ≤ 1 / (s.re * |s.im|) := by
    simpa [boundary] using norm_neg_inv_sq_div_twelve_le_vertical hs him
  have htail : ‖tail‖ ≤ 1 / (s.re * |s.im|) := by
    simpa [tail] using norm_integral_digammaBinetSecondOrderRemainderKernel_le_vertical hs him
  have hsum : ‖boundary‖ + ‖tail‖ ≤ 2 / (s.re * |s.im|) := by
    calc
      ‖boundary‖ + ‖tail‖ ≤ 1 / (s.re * |s.im|) + 1 / (s.re * |s.im|) :=
        add_le_add hboundary htail
      _ = 2 / (s.re * |s.im|) := by ring
  exact hre.trans (htri.trans hsum)

end Complex
