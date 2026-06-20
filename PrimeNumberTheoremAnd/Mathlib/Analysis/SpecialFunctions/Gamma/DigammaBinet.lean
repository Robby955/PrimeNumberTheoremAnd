/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
public import PrimeNumberTheoremAnd.EulerMaclaurin2

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.Integral
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
  have hcomp' : HasDerivAt (fun u : ℝ => (((u : ℂ) + s)⁻¹))
      (-(((t : ℂ) + s) ^ (2 : ℕ))⁻¹) t := by
    have hval : ((ContinuousLinearMap.restrictScalars ℝ
        (ContinuousLinearMap.toSpanSingleton ℂ (-(((t : ℂ) + s) ^ (2 : ℕ))⁻¹))) 1)
        = -(((t : ℂ) + s) ^ (2 : ℕ))⁻¹ := by
      simp [ContinuousLinearMap.toSpanSingleton_apply]
    rw [← hval]
    exact hcomp
  exact hcomp'.congr_deriv (by rw [inv_pow])

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
    have hsq' : HasDerivAt (fun z : ℂ => -(z⁻¹) ^ (2 : ℕ))
        (-((2 : ℂ) * (((t : ℂ) + s)⁻¹) ^ (2 - 1) * -(((t : ℂ) + s)⁻¹) ^ (2 : ℕ)))
        ((t : ℂ) + s) := hsq
    refine hsq'.congr_deriv ?_
    norm_num [pow_succ, pow_zero]
    ring
  have hcomp := hpow.comp t hlin
  have heq' : (fun y : ℝ => deriv (fun u : ℝ => (((u : ℂ) + s)⁻¹)) y) =ᶠ[nhds t]
      ((fun z : ℂ => -(z⁻¹) ^ (2 : ℕ)) ∘ fun y : ℝ => (y : ℂ) + s) := by
    filter_upwards [heq] with y hy
    rw [hy]
    simp [Function.comp, inv_pow]
  have hres := hcomp.congr_of_eventuallyEq heq'
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
    exact (hlog.comp t hinner).congr_deriv (by rw [mul_one])
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
    (him : s.im ≠ 0) :
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
