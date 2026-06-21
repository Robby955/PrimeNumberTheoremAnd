/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import PrimeNumberTheoremAnd.Backlund.ZeroCountCrude
import PrimeNumberTheoremAnd.ZetaBounds
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.CriticalLineDecay
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.PhragmenLindelof
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
On the `σ = 1` edge, the in-tree Euler-Maclaurin estimate gives
`|ζ(1+it)| ≤ C log |t|` for some fixed positive constant.
-/
theorem zeta_one_line_le_const_mul_log :
    ∃ C > 0, ∀ t : ℝ, 3 < |t| →
      ‖riemannZeta ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Real.log |t| := by
  obtain ⟨A, hA, C, hC, hζ⟩ := ZetaUpperBnd
  refine ⟨C, hC, ?_⟩
  intro t ht
  have hlog_pos : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hσ : (1 : ℝ) ∈ Set.Icc (1 - A / Real.log |t|) 2 := by
    constructor
    · have hdiv_nonneg : 0 ≤ A / Real.log |t| := div_nonneg hA.1.le hlog_pos.le
      linarith
    · norm_num
  simpa using hζ 1 t ht hσ

noncomputable def backlundA (s : ℂ) : ℂ := (s - 1) * riemannZeta s

private lemma sin_pi_one_add_mul_I (y : ℝ) :
    Complex.sin ((Real.pi : ℂ) * ((1 : ℂ) + (y : ℂ) * Complex.I)) =
      -((Real.sinh (Real.pi * y) : ℝ) : ℂ) * Complex.I := by
  have harg : (Real.pi : ℂ) * ((1 : ℂ) + (y : ℂ) * Complex.I) =
      (Real.pi : ℂ) + ((Real.pi * y : ℝ) : ℂ) * Complex.I := by
    norm_num [Complex.ofReal_mul]
    ring_nf
  rw [harg]
  simp [Complex.sin_add, Complex.sin_pi, Complex.cos_pi, Complex.sin_mul_I,
    Complex.cos_mul_I, Complex.ofReal_sinh]

private lemma gamma_pure_imag_norm_sq_pos {y : ℝ} (hy : 0 < y) :
    ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ ^ 2 =
      Real.pi / (y * Real.sinh (Real.pi * y)) := by
  let z : ℂ := (y : ℂ) * Complex.I
  have hz_ne : z ≠ 0 := by
    simp [z, hy.ne']
  have hconj : (starRingEnd ℂ) z = -z := by
    simp [z]
  have hsin : Complex.sin ((Real.pi : ℂ) * ((1 : ℂ) + z)) =
      -((Real.sinh (Real.pi * y) : ℝ) : ℂ) * Complex.I := by
    simpa [z] using sin_pi_one_add_mul_I y
  have hleft :
      Complex.Gamma ((1 : ℂ) + z) * Complex.Gamma (1 - ((1 : ℂ) + z)) =
        z * ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) := by
    have hΓadd : Complex.Gamma (z + 1) = z * Complex.Gamma z :=
      Complex.Gamma_add_one z hz_ne
    calc
      Complex.Gamma ((1 : ℂ) + z) * Complex.Gamma (1 - ((1 : ℂ) + z))
          = (z * Complex.Gamma z) * Complex.Gamma (-z) := by
            rw [show (1 : ℂ) + z = z + 1 by ring, hΓadd]
            ring_nf
      _ = (z * Complex.Gamma z) * (starRingEnd ℂ) (Complex.Gamma z) := by
            rw [← hconj, Complex.Gamma_conj]
      _ = z * (Complex.Gamma z * (starRingEnd ℂ) (Complex.Gamma z)) := by ring
      _ = z * ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have href := Complex.Gamma_mul_Gamma_one_sub ((1 : ℂ) + z)
  rw [hleft, hsin] at href
  have hsinh_pos : 0 < Real.sinh (Real.pi * y) := by
    rw [Real.sinh_eq]
    have harg : -(Real.pi * y) < Real.pi * y := by nlinarith [Real.pi_pos, hy]
    have hexp : Real.exp (-(Real.pi * y)) < Real.exp (Real.pi * y) := Real.exp_lt_exp.mpr harg
    nlinarith
  have href' : ((y * ‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) * Complex.I =
      ((Real.pi / Real.sinh (Real.pi * y) : ℝ) : ℂ) * Complex.I := by
    unfold z at href
    calc
      ((y * ‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) * Complex.I
          = ((y : ℂ) * Complex.I) * ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) := by
              push_cast
              ring
      _ = (Real.pi : ℂ) / (-((Real.sinh (Real.pi * y) : ℝ) : ℂ) * Complex.I) := href
      _ = ((Real.pi / Real.sinh (Real.pi * y) : ℝ) : ℂ) * Complex.I := by
              field_simp [Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr hsinh_pos.ne']
              simp
  have hcomplex := mul_right_cancel₀ Complex.I_ne_zero href'
  have hreal : y * ‖Complex.Gamma z‖ ^ 2 = Real.pi / Real.sinh (Real.pi * y) :=
    Complex.ofReal_injective hcomplex
  have hy_ne : y ≠ 0 := hy.ne'
  calc
    ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ ^ 2
        = (y * ‖Complex.Gamma z‖ ^ 2) / y := by
          simp [z]
          field_simp [hy_ne]
    _ = (Real.pi / Real.sinh (Real.pi * y)) / y := by rw [hreal]
    _ = Real.pi / (y * Real.sinh (Real.pi * y)) := by ring

private lemma gamma_pure_imag_norm_sq {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma ((t : ℂ) * Complex.I)‖ ^ 2 =
      Real.pi / (|t| * Real.sinh (Real.pi * |t|)) := by
  by_cases hpos : 0 < t
  · simpa [abs_of_pos hpos] using gamma_pure_imag_norm_sq_pos hpos
  · have hneg : t < 0 := lt_of_le_of_ne (le_of_not_gt hpos) ht
    have habs_pos : 0 < |t| := abs_pos.mpr ht
    have harg : (t : ℂ) * Complex.I = (starRingEnd ℂ) (((|t| : ℝ) : ℂ) * Complex.I) := by
      simp [abs_of_neg hneg]
    have hnorm : ‖Complex.Gamma ((t : ℂ) * Complex.I)‖ =
        ‖Complex.Gamma (((|t| : ℝ) : ℂ) * Complex.I)‖ := by
      rw [harg, Complex.Gamma_conj]
      simp
    rw [hnorm]
    simpa using gamma_pure_imag_norm_sq_pos habs_pos

private lemma gammaReal_vertical_norm_sq {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gammaℝ ((t : ℂ) * Complex.I)‖ ^ 2 =
      Real.pi / ((|t| / 2) * Real.sinh (Real.pi * (|t| / 2))) := by
  have ht2_ne : t / 2 ≠ 0 := by exact div_ne_zero ht two_ne_zero
  have hpow : ‖(Real.pi : ℂ) ^ (-((t : ℂ) * Complex.I) / 2)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.I_re]
  have harg : ((t : ℂ) * Complex.I) / 2 = (((t / 2 : ℝ) : ℂ) * Complex.I) := by
    norm_num [Complex.ofReal_div]
    ring
  rw [Complex.Gammaℝ_def, norm_mul, mul_pow, hpow]
  norm_num
  rw [harg]
  convert gamma_pure_imag_norm_sq ht2_ne using 1
  · rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

private lemma gammaReal_one_sub_vertical_norm_sq (t : ℝ) :
    ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I)‖ ^ 2 =
      1 / Real.cosh (Real.pi * (t / 2)) := by
  have hpow : ‖(Real.pi : ℂ) ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ =
      Real.pi ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re]
    norm_num
  have harg : ((1 : ℂ) - (t : ℂ) * Complex.I) / 2 =
      (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I) := by
    norm_num [Complex.ofReal_div]
    ring
  rw [Complex.Gammaℝ_def, norm_mul, mul_pow, hpow, harg]
  rw [Complex.gamma_half_vertical_norm_sq]
  have hcosh : Real.cosh (Real.pi * (-t / 2)) = Real.cosh (Real.pi * (t / 2)) := by
    rw [show Real.pi * (-t / 2) = -(Real.pi * (t / 2)) by ring, Real.cosh_neg]
  rw [hcosh]
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hcosh_pos : 0 < Real.cosh (Real.pi * (t / 2)) := Real.cosh_pos _
  rw [Real.rpow_neg hpi_pos.le]
  have hpi_half_sq : (Real.pi ^ (1 / 2 : ℝ)) ^ 2 = Real.pi := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hpi_pos.le
  field_simp [hpi_pos.ne', hcosh_pos.ne', hpi_half_sq]
  exact hpi_half_sq.symm

private lemma sinh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.sinh x := by
  rw [Real.sinh_eq]
  have hexp : Real.exp (-x) < Real.exp x := Real.exp_lt_exp.mpr (by linarith)
  nlinarith

private lemma sinh_le_cosh_of_nonneg {x : ℝ} (_hx : 0 ≤ x) : Real.sinh x ≤ Real.cosh x := by
  rw [Real.sinh_eq, Real.cosh_eq]
  nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

private lemma cosh_mul_half_abs (t : ℝ) :
    Real.cosh (Real.pi * (t / 2)) = Real.cosh (Real.pi * (|t| / 2)) := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · have hneg : t < 0 := lt_of_not_ge ht
    rw [abs_of_neg hneg]
    have harg : Real.pi * (t / 2) = -(Real.pi * (-t / 2)) := by ring
    rw [harg, Real.cosh_neg]

private lemma gammaReal_one_sub_vertical_div_vertical_norm_sq_le {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
        Complex.Gammaℝ ((t : ℂ) * Complex.I)‖ ^ 2 ≤ |t| / (2 * Real.pi) := by
  have ht_abs_pos : 0 < |t| := abs_pos.mpr ht
  have hx_pos : 0 < Real.pi * (|t| / 2) := by positivity
  have hsinh_pos : 0 < Real.sinh (Real.pi * (|t| / 2)) := sinh_pos_of_pos hx_pos
  have hcosh_pos : 0 < Real.cosh (Real.pi * (|t| / 2)) := Real.cosh_pos _
  have hcosh_t_pos : 0 < Real.cosh (Real.pi * (t / 2)) := Real.cosh_pos _
  have hsinh_le_cosh : Real.sinh (Real.pi * (|t| / 2)) ≤
      Real.cosh (Real.pi * (|t| / 2)) := sinh_le_cosh_of_nonneg hx_pos.le
  rw [norm_div, div_pow]
  rw [gammaReal_one_sub_vertical_norm_sq, gammaReal_vertical_norm_sq ht]
  rw [cosh_mul_half_abs]
  field_simp [Real.pi_pos.ne', hsinh_pos.ne', hcosh_pos.ne', hcosh_t_pos.ne']
  have hsinh_le_cosh' : Real.sinh (Real.pi * |t| / 2) ≤
      Real.cosh (Real.pi * |t| / 2) := by
    have harg : Real.pi * (|t| / 2) = Real.pi * |t| / 2 := by ring
    simpa [harg] using hsinh_le_cosh
  linarith

private lemma gammaReal_one_sub_vertical_div_vertical_norm_le {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
        Complex.Gammaℝ ((t : ℂ) * Complex.I)‖ ≤ Real.sqrt (|t| / (2 * Real.pi)) := by
  refine (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp ?_
  rw [Real.sq_sqrt]
  · exact gammaReal_one_sub_vertical_div_vertical_norm_sq_le ht
  · positivity

private lemma riemannZeta_vertical_eq_one_sub_mul_gammaRatio {t : ℝ} (ht : t ≠ 0) :
    riemannZeta ((t : ℂ) * Complex.I) =
      riemannZeta ((1 : ℂ) - (t : ℂ) * Complex.I) *
        (Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
          Complex.Gammaℝ ((t : ℂ) * Complex.I)) := by
  let s : ℂ := (t : ℂ) * Complex.I
  have hs_ne : s ≠ 0 := by simp [s, ht]
  have hw_ne : (1 : ℂ) - s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  have hΓw : Complex.Gammaℝ ((1 : ℂ) - s) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp [s]
  have hζs := riemannZeta_def_of_ne_zero (s := s) hs_ne
  have hζw := riemannZeta_def_of_ne_zero (s := (1 : ℂ) - s) hw_ne
  have hcompleted_w : completedRiemannZeta ((1 : ℂ) - s) =
      riemannZeta ((1 : ℂ) - s) * Complex.Gammaℝ ((1 : ℂ) - s) := by
    rw [hζw]
    field_simp [hΓw]
  calc
    riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s := hζs
    _ = completedRiemannZeta ((1 : ℂ) - s) / Complex.Gammaℝ s := by
      rw [completedRiemannZeta_one_sub]
    _ = (riemannZeta ((1 : ℂ) - s) * Complex.Gammaℝ ((1 : ℂ) - s)) /
          Complex.Gammaℝ s := by rw [hcompleted_w]
    _ = riemannZeta ((1 : ℂ) - s) *
          (Complex.Gammaℝ ((1 : ℂ) - s) / Complex.Gammaℝ s) := by ring

private lemma norm_vertical_sub_one_eq_norm_one_add_vertical (t : ℝ) :
    ‖(t : ℂ) * Complex.I - 1‖ = ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]

theorem backlundA_zero_line_le_const_mul_log_sqrt :
    ∃ C > 0, ∀ t : ℝ, 3 < |t| →
      ‖backlundA ((t : ℂ) * Complex.I)‖ ≤
        C * ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ * Real.log |t| *
          Real.sqrt (|t| / (2 * Real.pi)) := by
  obtain ⟨C, hC, hζline⟩ := zeta_one_line_le_const_mul_log
  refine ⟨C, hC, ?_⟩
  intro t ht
  have ht_ne : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    norm_num at ht
  have hζsym := riemannZeta_vertical_eq_one_sub_mul_gammaRatio ht_ne
  have hζline_t : ‖riemannZeta ((1 : ℂ) - (t : ℂ) * Complex.I)‖ ≤ C * Real.log |t| := by
    have h := hζline (-t) (by simpa [abs_neg] using ht)
    simpa [sub_eq_add_neg, neg_mul] using h
  have hgamma := gammaReal_one_sub_vertical_div_vertical_norm_le ht_ne
  have hlog_pos : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hClog_nonneg : 0 ≤ C * Real.log |t| := mul_nonneg hC.le hlog_pos.le
  unfold backlundA
  rw [hζsym]
  calc
    ‖(((t : ℂ) * Complex.I) - 1) *
        (riemannZeta ((1 : ℂ) - (t : ℂ) * Complex.I) *
          (Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
            Complex.Gammaℝ ((t : ℂ) * Complex.I)))‖
        ≤ ‖((t : ℂ) * Complex.I) - 1‖ *
            (‖riemannZeta ((1 : ℂ) - (t : ℂ) * Complex.I)‖ *
              ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
                Complex.Gammaℝ ((t : ℂ) * Complex.I)‖) := by
          calc
            ‖(((t : ℂ) * Complex.I) - 1) *
                (riemannZeta ((1 : ℂ) - (t : ℂ) * Complex.I) *
                  (Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
                    Complex.Gammaℝ ((t : ℂ) * Complex.I)))‖
                ≤ ‖((t : ℂ) * Complex.I) - 1‖ *
                    ‖riemannZeta ((1 : ℂ) - (t : ℂ) * Complex.I) *
                      (Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
                        Complex.Gammaℝ ((t : ℂ) * Complex.I))‖ := norm_mul_le _ _
            _ ≤ ‖((t : ℂ) * Complex.I) - 1‖ *
                    (‖riemannZeta ((1 : ℂ) - (t : ℂ) * Complex.I)‖ *
                      ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
                        Complex.Gammaℝ ((t : ℂ) * Complex.I)‖) := by
              exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ‖((t : ℂ) * Complex.I) - 1‖ *
            ((C * Real.log |t|) * Real.sqrt (|t| / (2 * Real.pi))) := by
          gcongr
    _ = C * ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ * Real.log |t| *
          Real.sqrt (|t| / (2 * Real.pi)) := by
          rw [norm_vertical_sub_one_eq_norm_one_add_vertical]
          ring

private lemma sqrt_abs_div_two_pi_le_two_pi_neg_half_mul_norm_one_add_vertical (t : ℝ) :
    Real.sqrt (|t| / (2 * Real.pi)) ≤
      (2 * Real.pi) ^ (-(1 / 2 : ℝ)) *
        ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ^ (1 / 2 : ℝ) := by
  let R : ℝ := ‖(1 : ℂ) + (t : ℂ) * Complex.I‖
  have hbase_pos : 0 < 2 * Real.pi := by positivity
  have hbase_nonneg : 0 ≤ 2 * Real.pi := hbase_pos.le
  have hR_nonneg : 0 ≤ R := norm_nonneg _
  have habs_le_R : |t| ≤ R := by
    have h := Complex.abs_im_le_norm ((1 : ℂ) + (t : ℂ) * Complex.I)
    simpa [R, Complex.add_im, Complex.mul_im] using h
  refine (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp ?_
  rw [Real.sq_sqrt]
  · have hbase_half_sq : ((2 * Real.pi) ^ (1 / 2 : ℝ)) ^ 2 = 2 * Real.pi := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sq_sqrt hbase_nonneg
    have hbase_neg_half_sq : ((2 * Real.pi) ^ (-(1 / 2 : ℝ))) ^ 2 = (2 * Real.pi)⁻¹ := by
      rw [Real.rpow_neg hbase_nonneg]
      field_simp [hbase_pos.ne', hbase_half_sq]
      exact hbase_half_sq.symm
    have hR_half_sq : (R ^ (1 / 2 : ℝ)) ^ 2 = R := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sq_sqrt hR_nonneg
    rw [mul_pow, hbase_neg_half_sq, hR_half_sq]
    field_simp [hbase_pos.ne']
    nlinarith
  · positivity

theorem backlundA_zero_line_le_const_mul_log :
    ∃ C > 0, ∀ t : ℝ, 3 < |t| →
      ‖backlundA ((t : ℂ) * Complex.I)‖ ≤
        C * ((2 * Real.pi) ^ (-(1 / 2 : ℝ)) *
          ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) * Real.log |t|) := by
  obtain ⟨C, hC, hA⟩ := backlundA_zero_line_le_const_mul_log_sqrt
  refine ⟨C, hC, ?_⟩
  intro t ht
  have h := hA t ht
  have hlog_pos : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hsqrt := sqrt_abs_div_two_pi_le_two_pi_neg_half_mul_norm_one_add_vertical t
  let R : ℝ := ‖(1 : ℂ) + (t : ℂ) * Complex.I‖
  have hR_pos : 0 < R := by
    apply norm_pos_iff.mpr
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
  calc
    ‖backlundA ((t : ℂ) * Complex.I)‖
        ≤ C * R * Real.log |t| * Real.sqrt (|t| / (2 * Real.pi)) := by
          simpa [R] using h
    _ ≤ C * R * Real.log |t| *
          ((2 * Real.pi) ^ (-(1 / 2 : ℝ)) * R ^ (1 / 2 : ℝ)) := by
          gcongr
    _ = C * ((2 * Real.pi) ^ (-(1 / 2 : ℝ)) * R ^ (3 / 2 : ℝ) * Real.log |t|) := by
          have hR_pow : R * R ^ (1 / 2 : ℝ) = R ^ (3 / 2 : ℝ) := by
            calc
              R * R ^ (1 / 2 : ℝ) = R ^ (1 : ℝ) * R ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
              _ = R ^ ((1 : ℝ) + 1 / 2) := by rw [← Real.rpow_add hR_pos]
              _ = R ^ (3 / 2 : ℝ) := by norm_num
          calc
            C * R * Real.log |t| *
                ((2 * Real.pi) ^ (-(1 / 2 : ℝ)) * R ^ (1 / 2 : ℝ))
                = C * (2 * Real.pi) ^ (-(1 / 2 : ℝ)) *
                    (R * R ^ (1 / 2 : ℝ)) * Real.log |t| := by ring
            _ = C * (2 * Real.pi) ^ (-(1 / 2 : ℝ)) *
                    R ^ (3 / 2 : ℝ) * Real.log |t| := by rw [hR_pow]
            _ = C * ((2 * Real.pi) ^ (-(1 / 2 : ℝ)) *
                    R ^ (3 / 2 : ℝ) * Real.log |t|) := by ring

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

/-- Rotated shifted base for the two-edge Backlund convexity normalizer. -/
noncomputable def rotatedShiftedBase (Q : ℝ) (z : ℂ) : ℂ :=
  -Complex.I * ((Q : ℂ) + z)

theorem rotatedShiftedBase_im (Q : ℝ) (z : ℂ) :
    (rotatedShiftedBase Q z).im = -(Q + z.re) := by
  simp [rotatedShiftedBase, Complex.mul_im]

theorem rotatedShiftedBase_norm (Q : ℝ) (z : ℂ) :
    ‖rotatedShiftedBase Q z‖ = ‖(Q : ℂ) + z‖ := by
  simp [rotatedShiftedBase]

/-- On a positive shifted vertical strip, the rotated base misses the log branch cut. -/
theorem rotatedShiftedBase_mem_slitPlane_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (0 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    rotatedShiftedBase Q z ∈ Complex.slitPlane := by
  refine Or.inr ?_
  have hzre : σ₀ ≤ z.re := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.1
  have hpos : (0 : ℝ) < Q + z.re := by nlinarith
  rw [rotatedShiftedBase_im]
  exact neg_ne_zero.mpr hpos.ne'

theorem rotatedShiftedBase_ne_zero_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (0 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    rotatedShiftedBase Q z ≠ 0 :=
  Complex.slitPlane_ne_zero (rotatedShiftedBase_mem_slitPlane_on_verticalClosedStrip hQ hz)

/-- The principal log of the rotated base is nonzero on a positive shifted strip. -/
theorem rotatedShiftedBase_log_ne_zero_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (0 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    Complex.log (rotatedShiftedBase Q z) ≠ 0 := by
  intro hlog
  have hbase_ne := rotatedShiftedBase_ne_zero_on_verticalClosedStrip hQ hz
  have hbase_one : rotatedShiftedBase Q z = 1 := by
    calc
      rotatedShiftedBase Q z = Complex.exp (Complex.log (rotatedShiftedBase Q z)) := by
        rw [Complex.exp_log hbase_ne]
      _ = 1 := by simp [hlog]
  have him := congrArg Complex.im hbase_one
  have hzre : σ₀ ≤ z.re := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.1
  have hpos : (0 : ℝ) < Q + z.re := by nlinarith
  rw [rotatedShiftedBase_im] at him
  simp at him
  nlinarith

/-- Complex-linear exponent interpolating two real edge powers. -/
noncomputable def twoEdgeExponent (σ₀ σ₁ α₀ α₁ : ℝ) (z : ℂ) : ℂ :=
  (α₀ : ℂ) + (((α₁ - α₀) / (σ₁ - σ₀) : ℝ) : ℂ) * (z - (σ₀ : ℂ))

/-- The rotated two-edge log-power normalizer. -/
noncomputable def rotatedShiftedLogPowerTwoEdgeNormalizer
    (Q σ₀ σ₁ α₀ α₁ : ℝ) (z : ℂ) : ℂ :=
  rotatedShiftedBase Q z ^ twoEdgeExponent σ₀ σ₁ α₀ α₁ z *
    Complex.log (rotatedShiftedBase Q z)

theorem rotatedShiftedLogPowerTwoEdgeNormalizer_ne_zero_on_verticalClosedStrip
    {Q σ₀ σ₁ α₀ α₁ : ℝ} {z : ℂ} (hQ : (0 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    rotatedShiftedLogPowerTwoEdgeNormalizer Q σ₀ σ₁ α₀ α₁ z ≠ 0 := by
  unfold rotatedShiftedLogPowerTwoEdgeNormalizer
  refine mul_ne_zero ?_ ?_
  · rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (rotatedShiftedBase_ne_zero_on_verticalClosedStrip hQ hz)
  · exact rotatedShiftedBase_log_ne_zero_on_verticalClosedStrip hQ hz

/--
The rotated two-edge normalizer is differentiable on positive shifted vertical strips.
This packages the branch-control part of the weighted PL route.
-/
theorem rotatedShiftedLogPowerTwoEdgeNormalizer_diffContOnCl_on_verticalStrip
    {Q σ₀ σ₁ α₀ α₁ : ℝ} (hσ : σ₀ < σ₁) (hQ : (0 : ℝ) < Q + σ₀) :
    DiffContOnCl ℂ (rotatedShiftedLogPowerTwoEdgeNormalizer Q σ₀ σ₁ α₀ α₁)
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁) := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [verticalStrip_closure_eq_verticalClosedStrip hσ.ne]
  unfold rotatedShiftedLogPowerTwoEdgeNormalizer rotatedShiftedBase twoEdgeExponent
  have hbase : DifferentiableOn ℂ (fun z : ℂ => -Complex.I * ((Q : ℂ) + z))
      (Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) := by
    fun_prop
  have hexponent : DifferentiableOn ℂ
      (fun z : ℂ =>
        (α₀ : ℂ) + (((α₁ - α₀) / (σ₁ - σ₀) : ℝ) : ℂ) * (z - (σ₀ : ℂ)))
      (Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) := by
    fun_prop
  exact
    (hbase.cpow hexponent
      (fun z hz => rotatedShiftedBase_mem_slitPlane_on_verticalClosedStrip
        (Q := Q) (σ₀ := σ₀) (σ₁ := σ₁) hQ hz)).mul
    (hbase.clog
      (fun z hz => rotatedShiftedBase_mem_slitPlane_on_verticalClosedStrip
        (Q := Q) (σ₀ := σ₀) (σ₁ := σ₁) hQ hz))

theorem twoEdgeExponent_re (σ₀ σ₁ α₀ α₁ : ℝ) (z : ℂ) :
    (twoEdgeExponent σ₀ σ₁ α₀ α₁ z).re =
      α₀ + ((α₁ - α₀) / (σ₁ - σ₀)) * (z.re - σ₀) := by
  simp only [twoEdgeExponent, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.sub_re, Complex.sub_im, zero_mul, sub_zero]

theorem twoEdgeExponent_im (σ₀ σ₁ α₀ α₁ : ℝ) (z : ℂ) :
    (twoEdgeExponent σ₀ σ₁ α₀ α₁ z).im =
      ((α₁ - α₀) / (σ₁ - σ₀)) * z.im := by
  simp only [twoEdgeExponent, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.sub_im, Complex.sub_re, zero_add, zero_mul]
  ring

theorem twoEdgeExponent_re_eq_interp {σ₀ σ₁ α₀ α₁ : ℝ} (hσ : σ₀ < σ₁)
    (z : ℂ) :
    (twoEdgeExponent σ₀ σ₁ α₀ α₁ z).re =
      α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
        α₁ * ((z.re - σ₀) / (σ₁ - σ₀)) := by
  rw [twoEdgeExponent_re]
  have hσne : σ₁ - σ₀ ≠ 0 := sub_ne_zero.mpr hσ.ne'
  field_simp [hσne]
  ring

/--
On the upper half of a positive shifted strip with decreasing edge exponents,
the rotated two-edge normalizer has exactly the polynomial-log size needed for
the Backlund convexity read-off.
-/
theorem rotatedShiftedLogPowerTwoEdgeNormalizer_norm_le_of_upperHalf
    {Q σ₀ σ₁ α₀ α₁ : ℝ} {z : ℂ} (hσ : σ₀ < σ₁)
    (hQ : (0 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)
    (hα : α₁ ≤ α₀) (hz_im : 0 ≤ z.im) :
    ‖rotatedShiftedLogPowerTwoEdgeNormalizer Q σ₀ σ₁ α₀ α₁ z‖ ≤
      ‖rotatedShiftedBase Q z‖ ^
        (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
          α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
        ‖Complex.log (rotatedShiftedBase Q z)‖ := by
  have hbase_ne := rotatedShiftedBase_ne_zero_on_verticalClosedStrip hQ hz
  have hzre : σ₀ ≤ z.re := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.1
  have hbase_im_neg : (rotatedShiftedBase Q z).im < 0 := by
    rw [rotatedShiftedBase_im]
    nlinarith
  have harg_nonpos : Complex.arg (rotatedShiftedBase Q z) ≤ 0 :=
    (Complex.arg_neg_iff.mpr hbase_im_neg).le
  have hcoef_nonpos : (α₁ - α₀) / (σ₁ - σ₀) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hα) (sub_nonneg.mpr hσ.le)
  have him_nonpos : (twoEdgeExponent σ₀ σ₁ α₀ α₁ z).im ≤ 0 := by
    rw [twoEdgeExponent_im]
    exact mul_nonpos_of_nonpos_of_nonneg hcoef_nonpos hz_im
  have hprod_nonneg :
      0 ≤ Complex.arg (rotatedShiftedBase Q z) *
        (twoEdgeExponent σ₀ σ₁ α₀ α₁ z).im :=
    mul_nonneg_of_nonpos_of_nonpos harg_nonpos him_nonpos
  have hexp_ge_one :
      (1 : ℝ) ≤ Real.exp (Complex.arg (rotatedShiftedBase Q z) *
        (twoEdgeExponent σ₀ σ₁ α₀ α₁ z).im) :=
    by simpa using Real.exp_le_exp.mpr hprod_nonneg
  have hpow_nonneg :
      0 ≤ ‖rotatedShiftedBase Q z‖ ^
        (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
          α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) :=
    Real.rpow_nonneg (norm_nonneg _) _
  unfold rotatedShiftedLogPowerTwoEdgeNormalizer
  rw [norm_mul, Complex.norm_cpow_of_ne_zero hbase_ne,
    twoEdgeExponent_re_eq_interp hσ]
  have hdiv_le :
      ‖rotatedShiftedBase Q z‖ ^
          (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
            α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) /
        Real.exp (Complex.arg (rotatedShiftedBase Q z) *
          (twoEdgeExponent σ₀ σ₁ α₀ α₁ z).im)
        ≤
      ‖rotatedShiftedBase Q z‖ ^
          (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
            α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) := by
    rw [div_le_iff₀ (Real.exp_pos _)]
    simpa using mul_le_mul_of_nonneg_left hexp_ge_one hpow_nonneg
  exact mul_le_mul_of_nonneg_right hdiv_le (norm_nonneg _)

/--
Phragmen-Lindelöf growth and uniform boundary control imply boundedness of the
norm on the corresponding closed vertical strip.
-/
theorem bddAbove_norm_on_verticalClosedStrip_of_phragmen_lindelof {g : ℂ → ℂ}
    {σ₀ σ₁ C : ℝ}
    (hd : DiffContOnCl ℂ g (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁))
    (hgrowth : ∃ c < Real.pi / (σ₁ - σ₀), ∃ B,
      g =O[Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo σ₀ σ₁)]
        fun z => Real.exp (B * Real.exp (c * |z.im|)))
    (hleft : ∀ z : ℂ, z.re = σ₀ → ‖g z‖ ≤ C)
    (hright : ∀ z : ℂ, z.re = σ₁ → ‖g z‖ ≤ C) :
    BddAbove (Set.image (fun z => ‖g z‖)
      (Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)) := by
  refine ⟨C, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact PhragmenLindelof.vertical_strip
    (f := g) (a := σ₀) (b := σ₁) (z := z)
    (by simpa [Complex.HadamardThreeLines.verticalStrip] using hd)
    hgrowth hleft hright
    (by simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.1)
    (by simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.2)

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

/--
Hadamard three-lines with the concrete shifted log-power normalizer and real
exponent weights.
-/
theorem log_phragmen_lindelof_shiftedLogPower {f : ℂ → ℂ}
    {Q σ₀ σ₁ C₀ C₁ α β : ℝ} {z : ℂ} (hσ : σ₀ < σ₁)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)
    (hQ : (1 : ℝ) < Q + σ₀)
    (hd : DiffContOnCl ℂ
      (fun w => f w / shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w)
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁))
    (hB : BddAbove (Set.image
      (fun w => ‖f w / shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w‖)
      (Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)))
    (hleft : ∀ w : ℂ, w.re = σ₀ →
      ‖f w‖ ≤ C₀ * (‖(Q : ℂ) + w‖ ^ α * ‖Complex.log ((Q : ℂ) + w)‖ ^ β))
    (hright : ∀ w : ℂ, w.re = σ₁ →
      ‖f w‖ ≤ C₁ * (‖(Q : ℂ) + w‖ ^ α * ‖Complex.log ((Q : ℂ) + w)‖ ^ β)) :
    ‖f z‖ ≤
      (C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
        C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀))) *
        (‖(Q : ℂ) + z‖ ^ α * ‖Complex.log ((Q : ℂ) + z)‖ ^ β) := by
  have hmain := log_phragmen_lindelof_normalized
    (f := f) (normalizer := shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ))
    (hσ := hσ) hz
    (fun w hw => shiftedLogPowerNormalizer_ne_zero_on_verticalClosedStrip
      (α : ℂ) (β : ℂ) hQ hw)
    hd hB
    (fun w hw => by
      simpa [norm_shiftedLogPowerNormalizer_ofReal] using hleft w hw)
    (fun w hw => by
      simpa [norm_shiftedLogPowerNormalizer_ofReal] using hright w hw)
  simpa [norm_shiftedLogPowerNormalizer_ofReal] using hmain

/--
Log-augmented Phragmen-Lindelöf in a vertical strip with shifted log-power
weights. The normalized quotient is controlled by the usual PL growth condition,
so no closed-strip boundedness hypothesis is required.
-/
theorem log_phragmen_lindelof {f : ℂ → ℂ}
    {Q σ₀ σ₁ C₀ C₁ α β : ℝ} {z : ℂ} (hσ : σ₀ < σ₁)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)
    (hQ : (1 : ℝ) < Q + σ₀)
    (hd : DiffContOnCl ℂ
      (fun w => f w / shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w)
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁))
    (hgrowth : ∃ c < Real.pi / (σ₁ - σ₀), ∃ B,
      (fun w => f w / shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w)
        =O[Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            Filter.principal (Complex.re ⁻¹' Set.Ioo σ₀ σ₁)]
          fun w => Real.exp (B * Real.exp (c * |w.im|)))
    (hleft : ∀ w : ℂ, w.re = σ₀ →
      ‖f w‖ ≤ C₀ * (‖(Q : ℂ) + w‖ ^ α * ‖Complex.log ((Q : ℂ) + w)‖ ^ β))
    (hright : ∀ w : ℂ, w.re = σ₁ →
      ‖f w‖ ≤ C₁ * (‖(Q : ℂ) + w‖ ^ α * ‖Complex.log ((Q : ℂ) + w)‖ ^ β)) :
    ‖f z‖ ≤
      (C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
        C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀))) *
        (‖(Q : ℂ) + z‖ ^ α * ‖Complex.log ((Q : ℂ) + z)‖ ^ β) := by
  let g : ℂ → ℂ := fun w => f w / shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w
  have hleft_g : ∀ w : ℂ, w.re = σ₀ → ‖g w‖ ≤ C₀ := by
    intro w hw
    have hwstrip : w ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁ := by
      simp [Complex.HadamardThreeLines.verticalClosedStrip, hw, hσ.le]
    have hnorm_pos : 0 < ‖shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w‖ :=
      norm_pos_iff.mpr (shiftedLogPowerNormalizer_ne_zero_on_verticalClosedStrip
        (Q := Q) (σ₀ := σ₀) (σ₁ := σ₁) (α := (α : ℂ)) (β := (β : ℂ)) hQ hwstrip)
    change ‖f w / shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w‖ ≤ C₀
    rw [norm_div]
    exact (div_le_iff₀ hnorm_pos).2 (by
      simpa [norm_shiftedLogPowerNormalizer_ofReal] using hleft w hw)
  have hright_g : ∀ w : ℂ, w.re = σ₁ → ‖g w‖ ≤ C₁ := by
    intro w hw
    have hwstrip : w ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁ := by
      simp [Complex.HadamardThreeLines.verticalClosedStrip, hw, hσ.le]
    have hnorm_pos : 0 < ‖shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w‖ :=
      norm_pos_iff.mpr (shiftedLogPowerNormalizer_ne_zero_on_verticalClosedStrip
        (Q := Q) (σ₀ := σ₀) (σ₁ := σ₁) (α := (α : ℂ)) (β := (β : ℂ)) hQ hwstrip)
    change ‖f w / shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w‖ ≤ C₁
    rw [norm_div]
    exact (div_le_iff₀ hnorm_pos).2 (by
      simpa [norm_shiftedLogPowerNormalizer_ofReal] using hright w hw)
  have hB : BddAbove (Set.image
      (fun w => ‖f w / shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w‖)
      (Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)) := by
    simpa [g] using
      bddAbove_norm_on_verticalClosedStrip_of_phragmen_lindelof
        (g := g) (σ₀ := σ₀) (σ₁ := σ₁) (C := max C₀ C₁)
        (by simpa [g] using hd)
        (by simpa [g] using hgrowth)
        (fun w hw => (hleft_g w hw).trans (le_max_left C₀ C₁))
        (fun w hw => (hright_g w hw).trans (le_max_right C₀ C₁))
  exact log_phragmen_lindelof_shiftedLogPower
    (f := f) (Q := Q) (σ₀ := σ₀) (σ₁ := σ₁)
    (C₀ := C₀) (C₁ := C₁) (α := α) (β := β)
    hσ hz hQ hd hB hleft hright

/--
Two-edge Phragmen-Lindelöf with a rotated log-power normalizer. The geometric
read-off from the rotated normalizer is derived for decreasing edge powers on
the upper half-strip.
-/
theorem log_phragmen_lindelof_shiftedLogPower_twoEdge {f : ℂ → ℂ}
    {Q σ₀ σ₁ C₀ C₁ α₀ α₁ k : ℝ} {z : ℂ} (hσ : σ₀ < σ₁)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)
    (hQ : (0 : ℝ) < Q + σ₀) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hα : α₁ ≤ α₀) (hz_im : 0 ≤ z.im) (hk : (1 : ℝ) ≤ k)
    (hd : DiffContOnCl ℂ
      (fun w => f w / rotatedShiftedLogPowerTwoEdgeNormalizer Q σ₀ σ₁ α₀ α₁ w)
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁))
    (hgrowth : ∃ c < Real.pi / (σ₁ - σ₀), ∃ B,
      (fun w => f w / rotatedShiftedLogPowerTwoEdgeNormalizer Q σ₀ σ₁ α₀ α₁ w)
        =O[Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            Filter.principal (Complex.re ⁻¹' Set.Ioo σ₀ σ₁)]
          fun w => Real.exp (B * Real.exp (c * |w.im|)))
    (hleft : ∀ w : ℂ, w.re = σ₀ →
      ‖f w‖ ≤ C₀ * ‖rotatedShiftedLogPowerTwoEdgeNormalizer Q σ₀ σ₁ α₀ α₁ w‖)
    (hright : ∀ w : ℂ, w.re = σ₁ →
      ‖f w‖ ≤ C₁ * ‖rotatedShiftedLogPowerTwoEdgeNormalizer Q σ₀ σ₁ α₀ α₁ w‖) :
    ‖f z‖ ≤
      (C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
        C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀))) *
        k * (‖rotatedShiftedBase Q z‖ ^
          (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
            α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
          ‖Complex.log (rotatedShiftedBase Q z)‖) := by
  let normalizer : ℂ → ℂ :=
    rotatedShiftedLogPowerTwoEdgeNormalizer Q σ₀ σ₁ α₀ α₁
  let g : ℂ → ℂ := fun w => f w / normalizer w
  have hnormalizer :
      ∀ w ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁, normalizer w ≠ 0 := by
    intro w hw
    exact rotatedShiftedLogPowerTwoEdgeNormalizer_ne_zero_on_verticalClosedStrip hQ hw
  have hleft_g : ∀ w : ℂ, w.re = σ₀ → ‖g w‖ ≤ C₀ := by
    intro w hw
    have hwstrip : w ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁ := by
      simp [Complex.HadamardThreeLines.verticalClosedStrip, hw, hσ.le]
    have hnorm_pos : 0 < ‖normalizer w‖ := norm_pos_iff.mpr (hnormalizer w hwstrip)
    change ‖f w / normalizer w‖ ≤ C₀
    rw [norm_div]
    exact (div_le_iff₀ hnorm_pos).2 (by simpa [normalizer] using hleft w hw)
  have hright_g : ∀ w : ℂ, w.re = σ₁ → ‖g w‖ ≤ C₁ := by
    intro w hw
    have hwstrip : w ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁ := by
      simp [Complex.HadamardThreeLines.verticalClosedStrip, hw, hσ.le]
    have hnorm_pos : 0 < ‖normalizer w‖ := norm_pos_iff.mpr (hnormalizer w hwstrip)
    change ‖f w / normalizer w‖ ≤ C₁
    rw [norm_div]
    exact (div_le_iff₀ hnorm_pos).2 (by simpa [normalizer] using hright w hw)
  have hB : BddAbove (Set.image (fun w => ‖f w / normalizer w‖)
      (Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)) := by
    simpa [g, normalizer] using
      bddAbove_norm_on_verticalClosedStrip_of_phragmen_lindelof
        (g := g) (σ₀ := σ₀) (σ₁ := σ₁) (C := max C₀ C₁)
        (by simpa [g, normalizer] using hd)
        (by simpa [g, normalizer] using hgrowth)
        (fun w hw => (hleft_g w hw).trans (le_max_left C₀ C₁))
        (fun w hw => (hright_g w hw).trans (le_max_right C₀ C₁))
  have hmain := log_phragmen_lindelof_normalized
    (f := f) (normalizer := normalizer) (hσ := hσ) hz
    hnormalizer hd hB hleft hright
  have hinterp_nonneg :
      0 ≤ C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
        C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀)) := by
    exact mul_nonneg (Real.rpow_nonneg hC₀ _) (Real.rpow_nonneg hC₁ _)
  have hgeom :
      ‖normalizer z‖ ≤
        k * (‖rotatedShiftedBase Q z‖ ^
          (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
            α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
          ‖Complex.log (rotatedShiftedBase Q z)‖) := by
    have hgeom_one :=
      rotatedShiftedLogPowerTwoEdgeNormalizer_norm_le_of_upperHalf
        (Q := Q) (σ₀ := σ₀) (σ₁ := σ₁) (α₀ := α₀) (α₁ := α₁)
        (z := z) hσ hQ hz hα hz_im
    have htarget_nonneg :
        0 ≤ ‖rotatedShiftedBase Q z‖ ^
          (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
            α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
          ‖Complex.log (rotatedShiftedBase Q z)‖ := by
      exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)
    exact hgeom_one.trans (by
      calc
        ‖rotatedShiftedBase Q z‖ ^
            (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
              α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
            ‖Complex.log (rotatedShiftedBase Q z)‖
            ≤ 1 * (‖rotatedShiftedBase Q z‖ ^
              (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
                α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
              ‖Complex.log (rotatedShiftedBase Q z)‖) := by rw [one_mul]
        _ ≤ k * (‖rotatedShiftedBase Q z‖ ^
              (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
                α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
              ‖Complex.log (rotatedShiftedBase Q z)‖) := by
            exact mul_le_mul_of_nonneg_right hk htarget_nonneg)
  calc
    ‖f z‖ ≤
        (C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
          C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀))) * ‖normalizer z‖ := hmain
    _ ≤
        (C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
          C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀))) *
          (k * (‖rotatedShiftedBase Q z‖ ^
            (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
              α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
            ‖Complex.log (rotatedShiftedBase Q z)‖)) := by
          exact mul_le_mul_of_nonneg_left (by simpa [normalizer] using hgeom) hinterp_nonneg
    _ =
        (C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
          C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀))) *
          k * (‖rotatedShiftedBase Q z‖ ^
            (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
              α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
            ‖Complex.log (rotatedShiftedBase Q z)‖) := by ring

/--
The fixed shifted log-power quotient for the entire zeta surrogate has the
analytic side conditions needed by the PL shell on the strip `0 < re z < 1`.
-/
theorem zetaSurrogate_shiftedLogPower_PL_inputs {Q : ℝ} (hQ : (1 : ℝ) < Q) :
    (∀ w ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1,
      shiftedLogPowerNormalizer Q ((5 / 4 : ℝ) : ℂ) (1 : ℂ) w ≠ 0) ∧
    DiffContOnCl ℂ
      (fun w => zetaSurrogate w /
        shiftedLogPowerNormalizer Q ((5 / 4 : ℝ) : ℂ) (1 : ℂ) w)
      (Complex.HadamardThreeLines.verticalStrip 0 1) := by
  have hσ : (0 : ℝ) < 1 := by norm_num
  have hQstrip : (1 : ℝ) < Q + (0 : ℝ) := by simpa using hQ
  constructor
  · intro w hw
    exact shiftedLogPowerNormalizer_ne_zero_on_verticalClosedStrip
      ((5 / 4 : ℝ) : ℂ) (1 : ℂ) hQstrip hw
  · have hsurrogate : DiffContOnCl ℂ zetaSurrogate
        (Complex.HadamardThreeLines.verticalStrip 0 1) :=
      zetaSurrogate_differentiable.diffContOnCl
    have hnormalizer : DiffContOnCl ℂ
        (shiftedLogPowerNormalizer Q ((5 / 4 : ℝ) : ℂ) (1 : ℂ))
        (Complex.HadamardThreeLines.verticalStrip 0 1) :=
      shiftedLogPowerNormalizer_diffContOnCl_on_verticalStrip
        ((5 / 4 : ℝ) : ℂ) (1 : ℂ) hσ hQstrip
    have hnormalizer_inv : DiffContOnCl ℂ
        (fun w =>
          (shiftedLogPowerNormalizer Q ((5 / 4 : ℝ) : ℂ) (1 : ℂ) w)⁻¹)
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
      refine hnormalizer.inv ?_
      intro w hw
      rw [verticalStrip_closure_eq_verticalClosedStrip hσ.ne] at hw
      exact shiftedLogPowerNormalizer_ne_zero_on_verticalClosedStrip
        ((5 / 4 : ℝ) : ℂ) (1 : ℂ) hQstrip hw
    simpa [div_eq_mul_inv, mul_comm] using hnormalizer_inv.smul hsurrogate

end Backlund
