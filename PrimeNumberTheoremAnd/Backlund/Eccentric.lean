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

theorem backlundA_conj (z : ℂ) :
    backlundA (star z) = star (backlundA z) := by
  simp [backlundA, riemannZeta_conj]

/--
Backlund's real-part auxiliary
`F_N(z) = (A(z+iT)^N + A(z-iT)^N)/2`.
-/
noncomputable def backlundF (N : ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (backlundA (z + (T : ℂ) * Complex.I) ^ N +
      backlundA (z - (T : ℂ) * Complex.I) ^ N)

theorem backlundF_real_eq_re (N : ℕ) (σ T : ℝ) :
    backlundF N T (σ : ℂ) =
      ((backlundA ((σ : ℂ) + (T : ℂ) * Complex.I) ^ N).re : ℂ) := by
  have hreflect :
      (σ : ℂ) - (T : ℂ) * Complex.I =
        star ((σ : ℂ) + (T : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp [Complex.add_re, Complex.sub_re, Complex.mul_re]
    · simp [Complex.add_im, Complex.sub_im, Complex.mul_im]
  unfold backlundF
  rw [hreflect, backlundA_conj]
  rw [← star_pow]
  let w : ℂ := backlundA ((σ : ℂ) + (T : ℂ) * Complex.I) ^ N
  change (1 / 2 : ℂ) * (w + star w) = (w.re : ℂ)
  apply Complex.ext
  · simp [Complex.mul_re, Complex.add_re]
    ring
  · simp [Complex.mul_im, Complex.add_im]

theorem backlundF_real_eq_zero_iff (N : ℕ) (σ T : ℝ) :
    backlundF N T (σ : ℂ) = 0 ↔
      (backlundA ((σ : ℂ) + (T : ℂ) * Complex.I) ^ N).re = 0 := by
  rw [backlundF_real_eq_re]
  exact Complex.ofReal_eq_zero

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

private lemma log_abs_im_le_norm_log {z : ℂ} {t : ℝ}
    (him : z.im = t) (ht : (1 : ℝ) < |t|) :
    Real.log |t| ≤ ‖Complex.log z‖ := by
  have him_le_norm : |t| ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    simpa [him] using h
  have hlog_le : Real.log |t| ≤ Real.log ‖z‖ :=
    Real.log_le_log (by linarith) him_le_norm
  have hlog_norm_le : Real.log ‖z‖ ≤ ‖Complex.log z‖ := by
    rw [← Complex.log_re]
    exact le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  exact hlog_le.trans hlog_norm_le

private lemma norm_one_add_vertical_le_norm_shifted_vertical {Q t : ℝ}
    (hQ : (1 : ℝ) ≤ Q) :
    ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  nlinarith

theorem zetaSurrogate_zero_line_le_const_mul_shiftedLog {Q : ℝ} (hQ : (1 : ℝ) < Q) :
    ∃ C > 0, ∀ t : ℝ, 3 < |t| →
      ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤
        C * (‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖) := by
  obtain ⟨C, hC, hA⟩ := backlundA_zero_line_le_const_mul_log
  let C₀ : ℝ := C * (2 * Real.pi) ^ (-(1 / 2 : ℝ))
  have hfactor_pos : (0 : ℝ) < (2 * Real.pi) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  refine ⟨C₀, by positivity, ?_⟩
  intro t ht
  have ht_ne : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    norm_num at ht
  have hsurrogate_eq : zetaSurrogate ((t : ℂ) * Complex.I) =
      backlundA ((t : ℂ) * Complex.I) := by
    have hs : (t : ℂ) * Complex.I ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
    simp [zetaSurrogate, backlundA, hs]
  have hR_le :
      ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) ≤
        ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _)
      (norm_one_add_vertical_le_norm_shifted_vertical hQ.le) (by norm_num)
  have hlog_le :
      Real.log |t| ≤ ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖ :=
    log_abs_im_le_norm_log
      (z := (Q : ℂ) + (t : ℂ) * Complex.I) (t := t) (by simp) (by linarith)
  have hlog_nonneg : 0 ≤ Real.log |t| := (Real.log_pos (by linarith)).le
  have htarget_pow_nonneg :
      0 ≤ ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hprod_le :
      ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) * Real.log |t| ≤
        ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖ :=
    mul_le_mul hR_le hlog_le hlog_nonneg htarget_pow_nonneg
  rw [hsurrogate_eq]
  calc
    ‖backlundA ((t : ℂ) * Complex.I)‖
        ≤ C * ((2 * Real.pi) ^ (-(1 / 2 : ℝ)) *
          ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) * Real.log |t|) := hA t ht
    _ = C₀ * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          Real.log |t|) := by ring
    _ ≤ C₀ * (‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖) := by
        exact mul_le_mul_of_nonneg_left hprod_le (by positivity)

theorem zetaSurrogate_one_line_le_const_mul_shiftedLog {Q : ℝ} (_hQ : (1 : ℝ) < Q) :
    ∃ C > 0, ∀ t : ℝ, 3 < |t| →
      ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) := by
  obtain ⟨C, hC, hζ⟩ := zeta_one_line_le_const_mul_log
  refine ⟨C, hC, ?_⟩
  intro t ht
  have ht_ne : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    norm_num at ht
  have hs : ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [ht_ne] at him
  have hsurrogate_eq :
      zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I) =
        ((t : ℂ) * Complex.I) * riemannZeta ((1 : ℂ) + (t : ℂ) * Complex.I) := by
    rw [zetaSurrogate, if_neg hs]
    ring
  have him_le :
      |t| ≤ ‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ := by
    have h := Complex.abs_im_le_norm (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
    simpa [Complex.add_im, Complex.mul_im] using h
  have hlog_le :
      Real.log |t| ≤ ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
    log_abs_im_le_norm_log
      (z := ((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) (t := t) (by simp) (by linarith)
  have hlog_nonneg : 0 ≤ Real.log |t| := (Real.log_pos (by linarith)).le
  have hnorm_nonneg : 0 ≤ ‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ := norm_nonneg _
  have hprod_le :
      |t| * Real.log |t| ≤
        ‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
    mul_le_mul him_le hlog_le hlog_nonneg hnorm_nonneg
  have hnorm_t : ‖(t : ℂ) * Complex.I‖ = |t| := by simp
  rw [hsurrogate_eq, norm_mul]
  have hζt := hζ t ht
  calc
    ‖(t : ℂ) * Complex.I‖ * ‖riemannZeta ((1 : ℂ) + (t : ℂ) * Complex.I)‖
        = |t| * ‖riemannZeta ((1 : ℂ) + (t : ℂ) * Complex.I)‖ := by rw [hnorm_t]
    _ ≤ |t| * (C * Real.log |t|) := by
          exact mul_le_mul_of_nonneg_left hζt (abs_nonneg t)
    _ = C * (|t| * Real.log |t|) := by ring
    _ ≤ C * (‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) := by
        exact mul_le_mul_of_nonneg_left hprod_le hC.le

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

theorem zetaSurrogate_zero_line_le_const_mul_shiftedLog_global {Q : ℝ}
    (hQ : (1 : ℝ) < Q) :
    ∃ C > 0, ∀ t : ℝ,
      ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤
        C * (‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖) := by
  obtain ⟨Chigh, hChigh, hhigh⟩ :=
    zetaSurrogate_zero_line_le_const_mul_shiftedLog hQ
  let D : ℝ → ℝ := fun t =>
    ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
      ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖
  have hD_pos : ∀ t : ℝ, 0 < D t := by
    intro t
    have hbase_re : (1 : ℝ) < (((Q : ℂ) + (t : ℂ) * Complex.I).re) := by
      simp [Complex.add_re, Complex.mul_re]
      linarith
    have hbase_ne : ((Q : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp [Complex.add_re, Complex.mul_re] at hre
      linarith
    have hpow_pos :
        0 < ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr hbase_ne) _
    have hlog_pos :
        0 < ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖ :=
      norm_pos_iff.mpr (log_ne_zero_of_one_lt_re hbase_re)
    exact mul_pos hpow_pos hlog_pos
  have hratio_cont : ContinuousOn
      (fun t : ℝ => ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ / D t)
      (Set.Icc (-3 : ℝ) 3) := by
    have hpath_cont : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by fun_prop
    have hnum_cont : Continuous fun t : ℝ => ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ :=
      (zetaSurrogate_differentiable.continuous.comp hpath_cont).norm
    have hshift_cont : Continuous fun t : ℝ => (Q : ℂ) + (t : ℂ) * Complex.I := by fun_prop
    have hpow_cont : Continuous fun t : ℝ =>
        ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) :=
      hshift_cont.norm.rpow_const (fun t => by
        have hne : ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ≠ 0 := by
          apply norm_ne_zero_iff.mpr
          intro h
          have hre := congrArg Complex.re h
          simp [Complex.add_re, Complex.mul_re] at hre
          linarith
        exact Or.inl hne)
    have hlog_cont : Continuous fun t : ℝ =>
        Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I) := by
      refine hshift_cont.clog ?_
      intro t
      refine Or.inl ?_
      simp [Complex.add_re, Complex.mul_re]
      linarith
    have hD_cont : Continuous D := by
      change Continuous (fun t : ℝ =>
        ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖)
      exact hpow_cont.mul hlog_cont.norm
    exact hnum_cont.continuousOn.div hD_cont.continuousOn
      (fun t _ => ne_of_gt (hD_pos t))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hratio_cont
  let C : ℝ := max Chigh (M + 1)
  refine ⟨C, lt_of_lt_of_le hChigh (le_max_left _ _), ?_⟩
  intro t
  by_cases ht : (3 : ℝ) < |t|
  · exact (hhigh t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left Chigh (M + 1))
        (le_of_lt (hD_pos t)))
  · have habs : |t| ≤ (3 : ℝ) := le_of_not_gt ht
    have htIcc : t ∈ Set.Icc (-3 : ℝ) 3 := by
      simpa [Set.mem_Icc] using (abs_le.mp habs)
    have hratio_le_M :
        ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ / D t ≤ M := by
      exact (le_abs_self _).trans (hM t htIcc)
    have hmain :
        ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤ M * D t :=
      (div_le_iff₀ (hD_pos t)).mp hratio_le_M
    have hM_le_C : M ≤ C := by
      calc
        M ≤ M + 1 := by linarith
        _ ≤ C := le_max_right _ _
    exact hmain.trans (mul_le_mul_of_nonneg_right hM_le_C (le_of_lt (hD_pos t)))

theorem zetaSurrogate_one_line_le_const_mul_shiftedLog_global {Q : ℝ}
    (hQ : (1 : ℝ) < Q) :
    ∃ C > 0, ∀ t : ℝ,
      ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) := by
  obtain ⟨Chigh, hChigh, hhigh⟩ :=
    zetaSurrogate_one_line_le_const_mul_shiftedLog hQ
  let D : ℝ → ℝ := fun t =>
    ‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
      ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
  have hD_pos : ∀ t : ℝ, 0 < D t := by
    intro t
    have hbase_re : (1 : ℝ) <
        ((((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re) := by
      simp [Complex.add_re, Complex.mul_re]
      linarith
    have hbase_ne : (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp [Complex.add_re, Complex.mul_re] at hre
      linarith
    have hnorm_pos :
        0 < ‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ :=
      norm_pos_iff.mpr hbase_ne
    have hlog_pos :
        0 < ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
      norm_pos_iff.mpr (log_ne_zero_of_one_lt_re hbase_re)
    exact mul_pos hnorm_pos hlog_pos
  have hratio_cont : ContinuousOn
      (fun t : ℝ => ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ / D t)
      (Set.Icc (-3 : ℝ) 3) := by
    have hpath_cont : Continuous fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I := by fun_prop
    have hnum_cont : Continuous fun t : ℝ =>
        ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ :=
      (zetaSurrogate_differentiable.continuous.comp hpath_cont).norm
    have hshift_cont : Continuous fun t : ℝ =>
        ((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by fun_prop
    have hlog_cont : Continuous fun t : ℝ =>
        Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
      refine hshift_cont.clog ?_
      intro t
      refine Or.inl ?_
      simp [Complex.add_re, Complex.mul_re]
      linarith
    have hD_cont : Continuous D := by
      change Continuous (fun t : ℝ =>
        ‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
      exact hshift_cont.norm.mul hlog_cont.norm
    exact hnum_cont.continuousOn.div hD_cont.continuousOn
      (fun t _ => ne_of_gt (hD_pos t))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hratio_cont
  let C : ℝ := max Chigh (M + 1)
  refine ⟨C, lt_of_lt_of_le hChigh (le_max_left _ _), ?_⟩
  intro t
  by_cases ht : (3 : ℝ) < |t|
  · exact (hhigh t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left Chigh (M + 1))
        (le_of_lt (hD_pos t)))
  · have habs : |t| ≤ (3 : ℝ) := le_of_not_gt ht
    have htIcc : t ∈ Set.Icc (-3 : ℝ) 3 := by
      simpa [Set.mem_Icc] using (abs_le.mp habs)
    have hratio_le_M :
        ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ / D t ≤ M := by
      exact (le_abs_self _).trans (hM t htIcc)
    have hmain :
        ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * D t :=
      (div_le_iff₀ (hD_pos t)).mp hratio_le_M
    have hM_le_C : M ≤ C := by
      calc
        M ≤ M + 1 := by linarith
        _ ≤ C := le_max_right _ _
    exact hmain.trans (mul_le_mul_of_nonneg_right hM_le_C (le_of_lt (hD_pos t)))

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

/-- Reflected product used in the midpoint convexity step. -/
noncomputable def midpointReflectedProduct (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z * star (f ((1 : ℂ) - star z))

/-- Constant-exponent majorant for the midpoint reflected-product route. -/
noncomputable def midpointReflectedProductMajorant (Q C₀ C₁ : ℝ) (z : ℂ) : ℂ :=
  ((C₀ * C₁ : ℝ) : ℂ) *
    (((Q : ℂ) + z) ^ (((3 / 2 : ℝ) : ℂ)) *
      (((Q + 1 : ℝ) : ℂ) - z) *
      Complex.log ((Q : ℂ) + z) *
      Complex.log ((((Q + 1 : ℝ) : ℂ) - z)))

theorem zetaSurrogate_conj (z : ℂ) :
    zetaSurrogate (star z) = star (zetaSurrogate z) := by
  by_cases hz : z = 1
  · subst hz
    simp [zetaSurrogate]
  · have hstar : star z ≠ 1 := by
      intro h
      have h' := congrArg (starRingEnd ℂ) h
      exact hz (by simpa [Complex.conj_conj] using h')
    rw [zetaSurrogate, if_neg hstar]
    rw [show zetaSurrogate z = (z - 1) * riemannZeta z by simp [zetaSurrogate, hz]]
    simp [riemannZeta_conj]

theorem midpointReflectedProduct_zetaSurrogate_eq (z : ℂ) :
    midpointReflectedProduct zetaSurrogate z =
      zetaSurrogate z * zetaSurrogate ((1 : ℂ) - z) := by
  unfold midpointReflectedProduct
  have harg : (1 : ℂ) - star z = star ((1 : ℂ) - z) := by
    simp
  rw [harg, zetaSurrogate_conj]
  simp

/-- Reflected shifted base `Q + 1 - z` stays off the log branch cut on a strip. -/
theorem reflectedShifted_mem_slitPlane_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (0 : ℝ) < Q + 1 - σ₁)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    (((Q + 1 : ℝ) : ℂ) - z) ∈ Complex.slitPlane := by
  refine Or.inl ?_
  have hzre : z.re ≤ σ₁ := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.2
  have hpos : (0 : ℝ) < Q + 1 - z.re := by nlinarith
  simpa [Complex.sub_re] using hpos

theorem reflectedShifted_log_ne_zero_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (1 : ℝ) < Q + 1 - σ₁)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    Complex.log ((((Q + 1 : ℝ) : ℂ) - z)) ≠ 0 := by
  apply log_ne_zero_of_one_lt_re
  have hzre : z.re ≤ σ₁ := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.2
  have hpos : (1 : ℝ) < Q + 1 - z.re := by nlinarith
  simpa [Complex.sub_re] using hpos

theorem reflectedShifted_log_mem_slitPlane_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (1 : ℝ) < Q + 1 - σ₁)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    Complex.log ((((Q + 1 : ℝ) : ℂ) - z)) ∈ Complex.slitPlane := by
  refine Or.inl ?_
  rw [Complex.log_re]
  apply Real.log_pos
  have hzre : z.re ≤ σ₁ := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.2
  have hpos : (1 : ℝ) < ((((Q + 1 : ℝ) : ℂ) - z).re) := by
    simp [Complex.sub_re]
    nlinarith
  exact lt_of_lt_of_le hpos (Complex.re_le_norm _)

theorem reflectedShifted_log_diffContOnCl_on_verticalStrip {Q σ₀ σ₁ : ℝ}
    (hσ : σ₀ < σ₁) (hQ : (0 : ℝ) < Q + 1 - σ₁) :
    DiffContOnCl ℂ (fun z : ℂ => Complex.log ((((Q + 1 : ℝ) : ℂ) - z)))
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁) := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [verticalStrip_closure_eq_verticalClosedStrip hσ.ne]
  exact ((differentiableOn_const (((Q + 1 : ℝ) : ℂ))).sub differentiableOn_id).clog
    (fun z hz => reflectedShifted_mem_slitPlane_on_verticalClosedStrip hQ hz)

theorem midpointReflectedProductMajorant_ne_zero_on_verticalClosedStrip
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : C₀ ≠ 0) (hC₁ : C₁ ≠ 0)
    {z : ℂ} (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) :
    midpointReflectedProductMajorant Q C₀ C₁ z ≠ 0 := by
  unfold midpointReflectedProductMajorant
  refine mul_ne_zero ?_ ?_
  · exact_mod_cast mul_ne_zero hC₀ hC₁
  · refine mul_ne_zero ?_ ?_
    · refine mul_ne_zero ?_ ?_
      · refine mul_ne_zero ?_ ?_
        · rw [Complex.cpow_ne_zero_iff]
          exact Or.inl (Complex.slitPlane_ne_zero
            (shifted_mem_slitPlane_on_verticalClosedStrip
              (Q := Q) (σ₀ := 0) (σ₁ := 1) (by linarith) hz))
        · exact Complex.slitPlane_ne_zero
            (reflectedShifted_mem_slitPlane_on_verticalClosedStrip
              (Q := Q) (σ₀ := 0) (σ₁ := 1) (by linarith) hz)
      · exact shifted_log_ne_zero_on_verticalClosedStrip
          (Q := Q) (σ₀ := 0) (σ₁ := 1) (by linarith) hz
    · exact reflectedShifted_log_ne_zero_on_verticalClosedStrip
        (Q := Q) (σ₀ := 0) (σ₁ := 1) (by linarith) hz

private lemma norm_ge_of_re_ge {z : ℂ} {A : ℝ} (hz : A ≤ z.re) :
    A ≤ ‖z‖ :=
  hz.trans (Complex.re_le_norm z)

private lemma log_le_norm_log_of_re_ge {z : ℂ} {A : ℝ} (hA : (1 : ℝ) < A)
    (hz : A ≤ z.re) :
    Real.log A ≤ ‖Complex.log z‖ := by
  have hA_norm : A ≤ ‖z‖ := norm_ge_of_re_ge hz
  have hlog_le : Real.log A ≤ Real.log ‖z‖ :=
    Real.log_le_log (by linarith) hA_norm
  have hlog_norm_le : Real.log ‖z‖ ≤ ‖Complex.log z‖ := by
    rw [← Complex.log_re]
    exact le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  exact hlog_le.trans hlog_norm_le

theorem midpointReflectedProductMajorant_norm_lower_on_verticalClosedStrip
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    {z : ℂ} (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) :
    (C₀ * C₁) * (Q ^ (5 / 2 : ℝ) * (Real.log Q) ^ 2) ≤
      ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ := by
  let qz : ℂ := (Q : ℂ) + z
  let rz : ℂ := (((Q + 1 : ℝ) : ℂ) - z)
  have hzleft : (0 : ℝ) ≤ z.re := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.1
  have hzright : z.re ≤ (1 : ℝ) := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.2
  have hqz_re : Q ≤ qz.re := by
    simp [qz, Complex.add_re]
    linarith
  have hrz_re : Q ≤ rz.re := by
    simp [rz, Complex.sub_re]
    linarith
  have hqz_ne : qz ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [qz, Complex.add_re] at hre
    linarith
  have hqnorm : Q ≤ ‖qz‖ := norm_ge_of_re_ge hqz_re
  have hrnorm : Q ≤ ‖rz‖ := norm_ge_of_re_ge hrz_re
  have hqlog : Real.log Q ≤ ‖Complex.log qz‖ :=
    log_le_norm_log_of_re_ge hQ hqz_re
  have hrlog : Real.log Q ≤ ‖Complex.log rz‖ :=
    log_le_norm_log_of_re_ge hQ hrz_re
  have hlogQ_nonneg : 0 ≤ Real.log Q := (Real.log_pos hQ).le
  have hqpow :
      Q ^ (3 / 2 : ℝ) ≤ ‖qz‖ ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hqnorm (by norm_num)
  have hcore :
      Q ^ (3 / 2 : ℝ) * Q * (Real.log Q * Real.log Q) ≤
        ‖qz‖ ^ (3 / 2 : ℝ) * ‖rz‖ *
          (‖Complex.log qz‖ * ‖Complex.log rz‖) := by
    have hright_nonneg : 0 ≤ ‖qz‖ ^ (3 / 2 : ℝ) * ‖rz‖ :=
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)
    exact mul_le_mul
      (mul_le_mul hqpow hrnorm (by linarith : (0 : ℝ) ≤ Q)
        (Real.rpow_nonneg (norm_nonneg _) _))
      (mul_le_mul hqlog hrlog hlogQ_nonneg (norm_nonneg _))
      (mul_nonneg hlogQ_nonneg hlogQ_nonneg) hright_nonneg
  have hnorm_eq :
      ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ =
        (C₀ * C₁) * (‖qz‖ ^ (3 / 2 : ℝ) * ‖rz‖ *
          (‖Complex.log qz‖ * ‖Complex.log rz‖)) := by
    have hcpow :
        ‖qz ^ (((3 / 2 : ℝ) : ℂ))‖ = ‖qz‖ ^ (3 / 2 : ℝ) := by
      rw [Complex.norm_cpow_of_ne_zero hqz_ne]
      norm_num
    unfold midpointReflectedProductMajorant
    change
      ‖((C₀ * C₁ : ℝ) : ℂ) *
        (qz ^ (((3 / 2 : ℝ) : ℂ)) * rz *
          Complex.log qz * Complex.log rz)‖ =
        (C₀ * C₁) * (‖qz‖ ^ (3 / 2 : ℝ) * ‖rz‖ *
          (‖Complex.log qz‖ * ‖Complex.log rz‖))
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hcpow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (mul_pos hC₀ hC₁)]
    ring
  rw [hnorm_eq]
  calc
    (C₀ * C₁) * (Q ^ (5 / 2 : ℝ) * (Real.log Q) ^ 2)
        = (C₀ * C₁) * (Q ^ (3 / 2 : ℝ) * Q *
            (Real.log Q * Real.log Q)) := by
          have hQpow : Q ^ (5 / 2 : ℝ) = Q ^ (3 / 2 : ℝ) * Q := by
            rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add (by linarith : 0 < Q)]
            rw [Real.rpow_one]
          rw [hQpow, pow_two]
    _ ≤ (C₀ * C₁) * (‖qz‖ ^ (3 / 2 : ℝ) * ‖rz‖ *
          (‖Complex.log qz‖ * ‖Complex.log rz‖)) := by
          exact mul_le_mul_of_nonneg_left hcore (mul_nonneg hC₀.le hC₁.le)

theorem zetaSurrogate_midpointReflectedProduct_norm_le_exp_quadratic :
    ∃ C > 0, ∀ z : ℂ,
      ‖midpointReflectedProduct zetaSurrogate z‖ ≤
        Real.exp (C * ((1 + ‖z‖) ^ (2 : ℝ) +
          (1 + ‖(1 : ℂ) - star z‖) ^ (2 : ℝ))) := by
  obtain ⟨C, hCpos, hC⟩ := zetaSurrogate_log_growth
  have hnorm : ∀ z : ℂ,
      ‖zetaSurrogate z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (2 : ℝ)) :=
    Real.norm_le_exp_mul_rpow_of_log_growth
      (f := zetaSurrogate) (r := fun z : ℂ => 1 + ‖z‖)
      (C := C) (ρ := (3 / 2 : ℝ)) (τ := (2 : ℝ))
      hCpos.le (fun z => by linarith [norm_nonneg z]) (by norm_num) hC
  refine ⟨C, hCpos, fun z => ?_⟩
  unfold midpointReflectedProduct
  rw [norm_mul, norm_star]
  calc
    ‖zetaSurrogate z‖ * ‖zetaSurrogate ((1 : ℂ) - star z)‖
        ≤ Real.exp (C * (1 + ‖z‖) ^ (2 : ℝ)) *
            Real.exp (C * (1 + ‖(1 : ℂ) - star z‖) ^ (2 : ℝ)) :=
          mul_le_mul (hnorm z) (hnorm ((1 : ℂ) - star z))
            (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (C * ((1 + ‖z‖) ^ (2 : ℝ) +
          (1 + ‖(1 : ℂ) - star z‖) ^ (2 : ℝ))) := by
          rw [← Real.exp_add]
          ring_nf

theorem zetaSurrogate_midpointReflectedProduct_quotient_norm_le_exp_quadratic
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    ∃ C > 0, ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1,
      ‖midpointReflectedProduct zetaSurrogate z /
          midpointReflectedProductMajorant Q C₀ C₁ z‖ ≤
        Real.exp (C * ((1 + ‖z‖) ^ (2 : ℝ) +
          (1 + ‖(1 : ℂ) - star z‖) ^ (2 : ℝ))) /
          ((C₀ * C₁) * (Q ^ (5 / 2 : ℝ) * (Real.log Q) ^ 2)) := by
  obtain ⟨C, hCpos, hC⟩ := zetaSurrogate_midpointReflectedProduct_norm_le_exp_quadratic
  refine ⟨C, hCpos, fun z hz => ?_⟩
  set D : ℝ := (C₀ * C₁) * (Q ^ (5 / 2 : ℝ) * (Real.log Q) ^ 2)
  have hDpos : 0 < D := by
    have hlog : 0 < Real.log Q := Real.log_pos hQ
    have hpow : 0 < Q ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    dsimp [D]
    positivity
  have hden :
      D ≤ ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ := by
    simpa [D] using midpointReflectedProductMajorant_norm_lower_on_verticalClosedStrip
      hQ hC₀ hC₁ hz
  rw [norm_div]
  calc
    ‖midpointReflectedProduct zetaSurrogate z‖ /
        ‖midpointReflectedProductMajorant Q C₀ C₁ z‖
        ≤ ‖midpointReflectedProduct zetaSurrogate z‖ / D :=
          div_le_div_of_nonneg_left (norm_nonneg _) hDpos hden
    _ ≤ Real.exp (C * ((1 + ‖z‖) ^ (2 : ℝ) +
          (1 + ‖(1 : ℂ) - star z‖) ^ (2 : ℝ))) / D :=
          div_le_div_of_nonneg_right (hC z) hDpos.le

private lemma one_add_norm_le_two_mul_exp_abs_im_of_re_mem_Ioo {z : ℂ}
    (hz : z.re ∈ Set.Ioo (0 : ℝ) 1) :
    1 + ‖z‖ ≤ 2 * Real.exp |z.im| := by
  have hz_re_icc : z.re ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨by linarith [hz.1], le_of_lt hz.2⟩
  have hnorm : ‖z‖ ≤ |z.im| + 1 := by
    calc ‖z‖
        = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := by rw [Complex.re_add_im]
      _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |z.re| + |z.im| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, Complex.norm_real]
          simp only [norm_eq_abs, mul_one]
      _ ≤ 1 + |z.im| := by
          have hre : |z.re| ≤ 1 := abs_le.mpr hz_re_icc
          linarith
      _ = |z.im| + 1 := by ring
  calc
    1 + ‖z‖ ≤ |z.im| + 2 := by linarith
    _ ≤ 2 * (1 + |z.im|) := by nlinarith [abs_nonneg z.im]
    _ ≤ 2 * Real.exp |z.im| :=
        mul_le_mul_of_nonneg_left
          (by simpa [add_comm] using Real.add_one_le_exp |z.im|) (by norm_num)

private lemma reflected_quadratic_le_eight_exp_two_abs_im {z : ℂ}
    (hz : z.re ∈ Set.Ioo (0 : ℝ) 1) :
    (1 + ‖z‖) ^ (2 : ℝ) + (1 + ‖(1 : ℂ) - star z‖) ^ (2 : ℝ) ≤
      8 * Real.exp (2 * |z.im|) := by
  have hz_ref : ((1 : ℂ) - star z).re ∈ Set.Ioo (0 : ℝ) 1 := by
    simp only [RCLike.star_def, Complex.sub_re, Complex.one_re, Complex.conj_re,
      Set.mem_Ioo, sub_pos, sub_lt_self_iff]
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hz_bound := one_add_norm_le_two_mul_exp_abs_im_of_re_mem_Ioo hz
  have href_bound :=
    one_add_norm_le_two_mul_exp_abs_im_of_re_mem_Ioo hz_ref
  have href_bound' :
      1 + ‖(1 : ℂ) - star z‖ ≤ 2 * Real.exp |z.im| := by
    simpa [Complex.sub_im] using href_bound
  have hpos_z : 0 ≤ 1 + ‖z‖ := by positivity
  have hpos_ref : 0 ≤ 1 + ‖(1 : ℂ) - star z‖ := by positivity
  have hexp_pos : 0 < Real.exp |z.im| := Real.exp_pos _
  have hz_sq :
      (1 + ‖z‖) ^ 2 ≤ (2 * Real.exp |z.im|) ^ 2 := by
    nlinarith
  have href_sq :
      (1 + ‖(1 : ℂ) - star z‖) ^ 2 ≤ (2 * Real.exp |z.im|) ^ 2 := by
    nlinarith
  have hexp_sq : (2 * Real.exp |z.im|) ^ 2 = 4 * Real.exp (2 * |z.im|) := by
    rw [sq, show 2 * |z.im| = |z.im| + |z.im| by ring, Real.exp_add]
    ring
  rw [Real.rpow_two, Real.rpow_two]
  nlinarith

theorem zetaSurrogate_midpointReflectedProduct_PL_growth
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    ∃ c < Real.pi / ((1 : ℝ) - 0), ∃ B,
      (fun z => midpointReflectedProduct zetaSurrogate z /
          midpointReflectedProductMajorant Q C₀ C₁ z)
        =O[Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            Filter.principal (Complex.re ⁻¹' Set.Ioo 0 1)]
          fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
  obtain ⟨C, hCpos, hC⟩ :=
    zetaSurrogate_midpointReflectedProduct_quotient_norm_le_exp_quadratic
      hQ hC₀ hC₁
  set D : ℝ := (C₀ * C₁) * (Q ^ (5 / 2 : ℝ) * (Real.log Q) ^ 2)
  have hDpos : 0 < D := by
    have hlog : 0 < Real.log Q := Real.log_pos hQ
    have hpow : 0 < Q ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    dsimp [D]
    positivity
  refine ⟨2, by
    have htwo_lt_pi : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
    simpa using htwo_lt_pi, 8 * C, ?_⟩
  apply Asymptotics.IsBigO.of_bound D⁻¹
  filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self
    (Complex.re ⁻¹' Set.Ioo (0 : ℝ) 1))] with z hzstrip
  have hzre : z.re ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa using hzstrip
  have hzclosed : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using
      (show z.re ∈ Set.Icc (0 : ℝ) 1 from ⟨le_of_lt hzre.1, le_of_lt hzre.2⟩)
  have hquot := hC z hzclosed
  have hquad := reflected_quadratic_le_eight_exp_two_abs_im hzre
  have hexp_le :
      Real.exp (C * ((1 + ‖z‖) ^ (2 : ℝ) +
          (1 + ‖(1 : ℂ) - star z‖) ^ (2 : ℝ))) ≤
        Real.exp ((8 * C) * Real.exp (2 * |z.im|)) := by
    refine Real.exp_le_exp.2 ?_
    have hexp_nonneg : 0 ≤ Real.exp (2 * |z.im|) := (Real.exp_pos _).le
    nlinarith
  calc
    ‖midpointReflectedProduct zetaSurrogate z /
        midpointReflectedProductMajorant Q C₀ C₁ z‖
        ≤ Real.exp (C * ((1 + ‖z‖) ^ (2 : ℝ) +
          (1 + ‖(1 : ℂ) - star z‖) ^ (2 : ℝ))) / D := by
          simpa [D] using hquot
    _ ≤ Real.exp ((8 * C) * Real.exp (2 * |z.im|)) / D :=
          div_le_div_of_nonneg_right hexp_le hDpos.le
    _ = D⁻¹ * ‖Real.exp ((8 * C) * Real.exp (2 * |z.im|))‖ := by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          ring

theorem midpointReflectedProductMajorant_diffContOnCl_on_verticalStrip
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) :
    DiffContOnCl ℂ (midpointReflectedProductMajorant Q C₀ C₁)
      (Complex.HadamardThreeLines.verticalStrip 0 1) := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [verticalStrip_closure_eq_verticalClosedStrip (by norm_num : (0 : ℝ) ≠ 1)]
  unfold midpointReflectedProductMajorant
  have hpow : DifferentiableOn ℂ (fun z : ℂ => ((Q : ℂ) + z) ^ (((3 / 2 : ℝ) : ℂ)))
      (Complex.HadamardThreeLines.verticalClosedStrip 0 1) :=
    ((differentiableOn_const (Q : ℂ)).add differentiableOn_id).cpow_const
      (fun z hz => shifted_mem_slitPlane_on_verticalClosedStrip
        (Q := Q) (σ₀ := 0) (σ₁ := 1) (by linarith) hz)
  have hlinear : DifferentiableOn ℂ (fun z : ℂ => (((Q + 1 : ℝ) : ℂ) - z))
      (Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    fun_prop
  have hlog : DifferentiableOn ℂ (fun z : ℂ => Complex.log ((Q : ℂ) + z))
      (Complex.HadamardThreeLines.verticalClosedStrip 0 1) :=
    ((differentiableOn_const (Q : ℂ)).add differentiableOn_id).clog
      (fun z hz => shifted_mem_slitPlane_on_verticalClosedStrip
        (Q := Q) (σ₀ := 0) (σ₁ := 1) (by linarith) hz)
  have hreflectedLog : DifferentiableOn ℂ
      (fun z : ℂ => Complex.log ((((Q + 1 : ℝ) : ℂ) - z)))
      (Complex.HadamardThreeLines.verticalClosedStrip 0 1) :=
    ((differentiableOn_const (((Q + 1 : ℝ) : ℂ))).sub differentiableOn_id).clog
      (fun z hz => reflectedShifted_mem_slitPlane_on_verticalClosedStrip
        (Q := Q) (σ₀ := 0) (σ₁ := 1) (by linarith) hz)
  exact (differentiableOn_const (((C₀ * C₁ : ℝ) : ℂ))).mul
    (((hpow.mul hlinear).mul hlog).mul hreflectedLog)

theorem zetaSurrogate_midpointReflectedProduct_PL_inputs
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : C₀ ≠ 0) (hC₁ : C₁ ≠ 0) :
    (∀ w ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1,
      midpointReflectedProductMajorant Q C₀ C₁ w ≠ 0) ∧
    DiffContOnCl ℂ
      (fun w => midpointReflectedProduct zetaSurrogate w /
        midpointReflectedProductMajorant Q C₀ C₁ w)
      (Complex.HadamardThreeLines.verticalStrip 0 1) := by
  constructor
  · intro w hw
    exact midpointReflectedProductMajorant_ne_zero_on_verticalClosedStrip hQ hC₀ hC₁ hw
  · have hσ : (0 : ℝ) < 1 := by norm_num
    have hsurrogate : DiffContOnCl ℂ zetaSurrogate
        (Complex.HadamardThreeLines.verticalStrip 0 1) :=
      zetaSurrogate_differentiable.diffContOnCl
    have hreflectArg : DiffContOnCl ℂ (fun w : ℂ => (1 : ℂ) - w)
        (Complex.HadamardThreeLines.verticalStrip 0 1) :=
      ((differentiable_const (1 : ℂ)).sub differentiable_id).diffContOnCl
    have hreflectSurrogate : DiffContOnCl ℂ (fun w : ℂ => zetaSurrogate ((1 : ℂ) - w))
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
      simpa [Function.comp_def] using
        zetaSurrogate_differentiable.comp_diffContOnCl hreflectArg
    have hnumerator : DiffContOnCl ℂ
        (fun w : ℂ => zetaSurrogate w * zetaSurrogate ((1 : ℂ) - w))
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
      simpa [smul_eq_mul] using hsurrogate.smul hreflectSurrogate
    have hmajorant : DiffContOnCl ℂ (midpointReflectedProductMajorant Q C₀ C₁)
        (Complex.HadamardThreeLines.verticalStrip 0 1) :=
      midpointReflectedProductMajorant_diffContOnCl_on_verticalStrip hQ
    have hmajorant_inv : DiffContOnCl ℂ
        (fun w => (midpointReflectedProductMajorant Q C₀ C₁ w)⁻¹)
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
      refine hmajorant.inv ?_
      intro w hw
      rw [verticalStrip_closure_eq_verticalClosedStrip hσ.ne] at hw
      exact midpointReflectedProductMajorant_ne_zero_on_verticalClosedStrip hQ hC₀ hC₁ hw
    have hquot : DiffContOnCl ℂ
        (fun w => (zetaSurrogate w * zetaSurrogate ((1 : ℂ) - w)) /
          midpointReflectedProductMajorant Q C₀ C₁ w)
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        hmajorant_inv.smul hnumerator
    simpa [midpointReflectedProduct_zetaSurrogate_eq] using hquot

private theorem one_sub_star_midline (t : ℝ) :
    (1 : ℂ) - star ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
      (1 / 2 : ℂ) + (t : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
    norm_num
  · simp [Complex.sub_im, Complex.add_im, Complex.mul_im]

theorem midpointReflectedProduct_norm_midline (f : ℂ → ℂ) (t : ℝ) :
    ‖midpointReflectedProduct f ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ =
      ‖f ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  unfold midpointReflectedProduct
  rw [one_sub_star_midline]
  simp [pow_two]

theorem midpointReflectedProductMajorant_norm_midline
    {Q C₀ C₁ t : ℝ} (hQ : (1 : ℝ) < Q) :
    ‖midpointReflectedProductMajorant Q C₀ C₁
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ =
      |C₀| * |C₁| *
        ‖(Q : ℂ) + ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ (5 / 2 : ℝ) *
        ‖Complex.log ((Q : ℂ) + ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2 := by
  let z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  let qz : ℂ := (Q : ℂ) + z
  have hqz_re : (0 : ℝ) < qz.re := by
    simp [qz, z, Complex.add_re, Complex.mul_re]
    linarith
  have hqz_ne : qz ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [h] at hqz_re
    simp at hqz_re
  have hreflect : (((Q + 1 : ℝ) : ℂ) - z) = star qz := by
    apply Complex.ext
    · simp [qz, z, Complex.sub_re, Complex.add_re, Complex.mul_re]
      ring_nf
    · simp [qz, z, Complex.sub_im, Complex.add_im, Complex.mul_im]
  have harg_ne : qz.arg ≠ Real.pi := by
    intro harg
    have harg' := Complex.arg_eq_pi_iff.mp harg
    linarith
  have hlog_conj : Complex.log (star qz) = star (Complex.log qz) := by
    simpa using Complex.log_conj qz harg_ne
  have hcpow :
      ‖qz ^ (((3 / 2 : ℝ) : ℂ) : ℂ)‖ = ‖qz‖ ^ (3 / 2 : ℝ) := by
    rw [Complex.norm_cpow_of_ne_zero hqz_ne]
    simp
  unfold midpointReflectedProductMajorant
  simp only [z, qz] at *
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hcpow, hreflect, hlog_conj]
  simp only [norm_star]
  have hqz_pos : 0 < ‖qz‖ := norm_pos_iff.mpr hqz_ne
  have hpow : ‖qz‖ ^ (3 / 2 : ℝ) * ‖qz‖ = ‖qz‖ ^ (5 / 2 : ℝ) := by
    calc
      ‖qz‖ ^ (3 / 2 : ℝ) * ‖qz‖ =
          ‖qz‖ ^ (3 / 2 : ℝ) * ‖qz‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ‖qz‖ ^ ((3 / 2 : ℝ) + 1) := by rw [← Real.rpow_add hqz_pos]
      _ = ‖qz‖ ^ (5 / 2 : ℝ) := by norm_num
  rw [hpow]
  simp [qz, z, pow_two, mul_comm, mul_left_comm, mul_assoc]

theorem midpointReflectedProductMajorant_norm_left_boundary
    {Q C₀ C₁ t : ℝ} (hQ : (1 : ℝ) < Q) :
    ‖midpointReflectedProductMajorant Q C₀ C₁ ((t : ℂ) * Complex.I)‖ =
      |C₀| * |C₁| *
        (‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖) *
        (‖((Q + 1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖) := by
  let z : ℂ := (t : ℂ) * Complex.I
  let qz : ℂ := (Q : ℂ) + z
  have hqz_re : (0 : ℝ) < qz.re := by
    simp [qz, z, Complex.add_re, Complex.mul_re]
    linarith
  have hqz_ne : qz ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [h] at hqz_re
    simp at hqz_re
  have hreflect :
      (((Q + 1 : ℝ) : ℂ) - z) =
        ((Q + 1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [z, Complex.sub_re, Complex.add_re, Complex.mul_re]
    · simp [z, Complex.sub_im, Complex.add_im, Complex.mul_im]
  have hcpow :
      ‖qz ^ (((3 / 2 : ℝ) : ℂ) : ℂ)‖ = ‖qz‖ ^ (3 / 2 : ℝ) := by
    rw [Complex.norm_cpow_of_ne_zero hqz_ne]
    simp
  unfold midpointReflectedProductMajorant
  simp only [z, qz] at *
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hcpow, hreflect]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem midpointReflectedProductMajorant_norm_right_boundary
    {Q C₀ C₁ t : ℝ} (hQ : (1 : ℝ) < Q) :
    ‖midpointReflectedProductMajorant Q C₀ C₁ ((1 : ℂ) + (t : ℂ) * Complex.I)‖ =
      |C₀| * |C₁| *
        (‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) *
        (‖(Q : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖ *
          ‖Complex.log ((Q : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖) := by
  let z : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I
  let qz : ℂ := (Q : ℂ) + z
  have hqz_re : (0 : ℝ) < qz.re := by
    simp [qz, z, Complex.add_re, Complex.mul_re]
    linarith
  have hqz_ne : qz ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [h] at hqz_re
    simp at hqz_re
  have hqz_eq :
      qz = ((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    simp [qz, z]
    ring
  have hreflect :
      (((Q + 1 : ℝ) : ℂ) - z) =
        (Q : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [z, Complex.sub_re, Complex.add_re, Complex.mul_re]
    · simp [z, Complex.sub_im, Complex.add_im, Complex.mul_im]
  have hcpow :
      ‖qz ^ (((3 / 2 : ℝ) : ℂ) : ℂ)‖ = ‖qz‖ ^ (3 / 2 : ℝ) := by
    rw [Complex.norm_cpow_of_ne_zero hqz_ne]
    simp
  unfold midpointReflectedProductMajorant
  simp only [z, qz] at *
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hcpow, hqz_eq, hreflect]
  simp [mul_comm, mul_left_comm, mul_assoc]

private lemma rpow_three_halves_mul_le_swap {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    a ^ (3 / 2 : ℝ) * b ≤ b ^ (3 / 2 : ℝ) * a := by
  have hhalf : a ^ (1 / 2 : ℝ) ≤ b ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow ha.le hab (by norm_num)
  have ha32 : a ^ (3 / 2 : ℝ) = a * a ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ha]
    rw [Real.rpow_one]
  have hb32 : b ^ (3 / 2 : ℝ) = b * b ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hb]
    rw [Real.rpow_one]
  rw [ha32, hb32]
  nlinarith [mul_nonneg ha.le hb.le, hhalf]

theorem zetaSurrogate_midpointReflectedProduct_left_boundary_le_one_of_edge_bounds
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hzero : ∀ t : ℝ,
      ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤
        C₀ * (‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖))
    (hone : ∀ t : ℝ,
      ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C₁ * (‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)) :
    ∀ t : ℝ,
      ‖midpointReflectedProduct zetaSurrogate ((t : ℂ) * Complex.I) /
        midpointReflectedProductMajorant Q C₀ C₁ ((t : ℂ) * Complex.I)‖ ≤ 1 := by
  intro t
  let D₀ : ℝ :=
    ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
      ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖
  let D₁ : ℝ :=
    ‖((Q + 1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖ *
      ‖Complex.log (((Q + 1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖
  have hD₀_nonneg : 0 ≤ D₀ := by
    exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)
  have hD₁_nonneg : 0 ≤ D₁ := by
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hzero_t : ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤ C₀ * D₀ := by
    simpa [D₀] using hzero t
  have hone_neg_t :
      ‖zetaSurrogate ((1 : ℂ) - (t : ℂ) * Complex.I)‖ ≤ C₁ * D₁ := by
    have h := hone (-t)
    simpa [D₁, sub_eq_add_neg, neg_mul] using h
  have hnum :
      ‖midpointReflectedProduct zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤
        (C₀ * D₀) * (C₁ * D₁) := by
    rw [midpointReflectedProduct_zetaSurrogate_eq, norm_mul]
    exact mul_le_mul hzero_t hone_neg_t
      (norm_nonneg _) (mul_nonneg hC₀.le hD₀_nonneg)
  have hmaj_norm :
      ‖midpointReflectedProductMajorant Q C₀ C₁ ((t : ℂ) * Complex.I)‖ =
        (C₀ * D₀) * (C₁ * D₁) := by
    rw [midpointReflectedProductMajorant_norm_left_boundary (Q := Q) (C₀ := C₀)
      (C₁ := C₁) (t := t) hQ]
    rw [abs_of_pos hC₀, abs_of_pos hC₁]
    ring
  have hzstrip :
      ((t : ℂ) * Complex.I) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, Complex.mul_re]
  have hmajorant_pos :
      0 < ‖midpointReflectedProductMajorant Q C₀ C₁ ((t : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr
      (midpointReflectedProductMajorant_ne_zero_on_verticalClosedStrip hQ hC₀.ne'
        hC₁.ne' hzstrip)
  rw [norm_div]
  exact (div_le_iff₀ hmajorant_pos).2 (by simpa [hmaj_norm] using hnum)

theorem zetaSurrogate_midpointReflectedProduct_left_boundary_le_one_of_re_eq_zero
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hzero : ∀ t : ℝ,
      ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤
        C₀ * (‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖))
    (hone : ∀ t : ℝ,
      ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C₁ * (‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)) :
    ∀ w : ℂ, w.re = 0 →
      ‖midpointReflectedProduct zetaSurrogate w /
        midpointReflectedProductMajorant Q C₀ C₁ w‖ ≤ 1 := by
  intro w hw
  have hw_eq : w = (w.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [hw, Complex.mul_re]
    · simp [Complex.mul_im]
  rw [hw_eq]
  exact zetaSurrogate_midpointReflectedProduct_left_boundary_le_one_of_edge_bounds
    hQ hC₀ hC₁ hzero hone w.im

theorem zetaSurrogate_midpointReflectedProduct_right_boundary_le_one_of_edge_bounds
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hzero : ∀ t : ℝ,
      ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤
        C₀ * (‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖))
    (hone : ∀ t : ℝ,
      ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C₁ * (‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)) :
    ∀ t : ℝ,
      ‖midpointReflectedProduct zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I) /
        midpointReflectedProductMajorant Q C₀ C₁ ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 := by
  intro t
  let R₀ : ℝ := ‖(Q : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖
  let L₀ : ℝ := ‖Complex.log ((Q : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖
  let R₁ : ℝ := ‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖
  let L₁ : ℝ := ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
  have hR₀_pos : 0 < R₀ := by
    apply norm_pos_iff.mpr
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re] at hre
    linarith
  have hR₁_pos : 0 < R₁ := by
    apply norm_pos_iff.mpr
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re] at hre
    linarith
  have hR₀_le_R₁ : R₀ ≤ R₁ := by
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]
    nlinarith
  have hpower_swap : R₀ ^ (3 / 2 : ℝ) * R₁ ≤ R₁ ^ (3 / 2 : ℝ) * R₀ :=
    rpow_three_halves_mul_le_swap hR₀_pos hR₁_pos hR₀_le_R₁
  have hlog_nonneg : 0 ≤ L₀ * L₁ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hswap :
      (R₁ * L₁) * (R₀ ^ (3 / 2 : ℝ) * L₀) ≤
        (R₁ ^ (3 / 2 : ℝ) * L₁) * (R₀ * L₀) := by
    calc
      (R₁ * L₁) * (R₀ ^ (3 / 2 : ℝ) * L₀)
          = (R₀ ^ (3 / 2 : ℝ) * R₁) * (L₀ * L₁) := by ring
      _ ≤ (R₁ ^ (3 / 2 : ℝ) * R₀) * (L₀ * L₁) := by
          exact mul_le_mul_of_nonneg_right hpower_swap hlog_nonneg
      _ = (R₁ ^ (3 / 2 : ℝ) * L₁) * (R₀ * L₀) := by ring
  have hone_t : ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      C₁ * (R₁ * L₁) := by
    simpa [R₁, L₁] using hone t
  have hzero_neg_t : ‖zetaSurrogate (((-t : ℝ) : ℂ) * Complex.I)‖ ≤
      C₀ * (R₀ ^ (3 / 2 : ℝ) * L₀) := by
    simpa [R₀, L₀] using hzero (-t)
  have hsecond :
      ‖zetaSurrogate ((1 : ℂ) - ((1 : ℂ) + (t : ℂ) * Complex.I))‖ =
        ‖zetaSurrogate (((-t : ℝ) : ℂ) * Complex.I)‖ := by
    have harg :
        (1 : ℂ) - ((1 : ℂ) + (t : ℂ) * Complex.I) =
          ((-t : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [Complex.mul_re]
      · simp [Complex.mul_im]
    rw [harg]
  have hnum :
      ‖midpointReflectedProduct zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (C₁ * (R₁ * L₁)) * (C₀ * (R₀ ^ (3 / 2 : ℝ) * L₀)) := by
    rw [midpointReflectedProduct_zetaSurrogate_eq, norm_mul, hsecond]
    exact mul_le_mul hone_t hzero_neg_t (norm_nonneg _)
      (mul_nonneg hC₁.le (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hmaj_norm :
      ‖midpointReflectedProductMajorant Q C₀ C₁
          ((1 : ℂ) + (t : ℂ) * Complex.I)‖ =
        (C₀ * C₁) * ((R₁ ^ (3 / 2 : ℝ) * L₁) * (R₀ * L₀)) := by
    rw [midpointReflectedProductMajorant_norm_right_boundary (Q := Q) (C₀ := C₀)
      (C₁ := C₁) (t := t) hQ]
    rw [abs_of_pos hC₀, abs_of_pos hC₁]
    simp [R₀, L₀, R₁, L₁, mul_comm, mul_left_comm, mul_assoc]
  have hnum_le_major :
      ‖midpointReflectedProduct zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        ‖midpointReflectedProductMajorant Q C₀ C₁
          ((1 : ℂ) + (t : ℂ) * Complex.I)‖ := by
    refine hnum.trans ?_
    rw [hmaj_norm]
    calc
      (C₁ * (R₁ * L₁)) * (C₀ * (R₀ ^ (3 / 2 : ℝ) * L₀))
          = (C₀ * C₁) * ((R₁ * L₁) * (R₀ ^ (3 / 2 : ℝ) * L₀)) := by ring
      _ ≤ (C₀ * C₁) * ((R₁ ^ (3 / 2 : ℝ) * L₁) * (R₀ * L₀)) := by
          exact mul_le_mul_of_nonneg_left hswap (mul_nonneg hC₀.le hC₁.le)
  have hzstrip :
      ((1 : ℂ) + (t : ℂ) * Complex.I) ∈
        Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, Complex.add_re, Complex.mul_re]
  have hmajorant_pos :
      0 < ‖midpointReflectedProductMajorant Q C₀ C₁
        ((1 : ℂ) + (t : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr
      (midpointReflectedProductMajorant_ne_zero_on_verticalClosedStrip hQ hC₀.ne'
        hC₁.ne' hzstrip)
  rw [norm_div]
  exact (div_le_iff₀ hmajorant_pos).2 (by simpa [one_mul] using hnum_le_major)

theorem zetaSurrogate_midpointReflectedProduct_right_boundary_le_one_of_re_eq_one
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hzero : ∀ t : ℝ,
      ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤
        C₀ * (‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖))
    (hone : ∀ t : ℝ,
      ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C₁ * (‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)) :
    ∀ w : ℂ, w.re = 1 →
      ‖midpointReflectedProduct zetaSurrogate w /
        midpointReflectedProductMajorant Q C₀ C₁ w‖ ≤ 1 := by
  intro w hw
  have hw_eq : w = (1 : ℂ) + (w.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [hw, Complex.add_re, Complex.mul_re]
    · simp [Complex.add_im, Complex.mul_im]
  rw [hw_eq]
  exact zetaSurrogate_midpointReflectedProduct_right_boundary_le_one_of_edge_bounds
    hQ hC₀ hC₁ hzero hone w.im

theorem zetaSurrogate_midpointReflectedProduct_boundary_controls {Q : ℝ} (hQ : (1 : ℝ) < Q) :
    ∃ C₀ > 0, ∃ C₁ > 0,
      (∀ w : ℂ, w.re = 0 →
        ‖midpointReflectedProduct zetaSurrogate w /
          midpointReflectedProductMajorant Q C₀ C₁ w‖ ≤ 1) ∧
      (∀ w : ℂ, w.re = 1 →
        ‖midpointReflectedProduct zetaSurrogate w /
          midpointReflectedProductMajorant Q C₀ C₁ w‖ ≤ 1) := by
  obtain ⟨C₀, hC₀, hzero⟩ := zetaSurrogate_zero_line_le_const_mul_shiftedLog_global hQ
  obtain ⟨C₁, hC₁, hone⟩ := zetaSurrogate_one_line_le_const_mul_shiftedLog_global hQ
  refine ⟨C₀, hC₀, C₁, hC₁, ?_, ?_⟩
  · exact zetaSurrogate_midpointReflectedProduct_left_boundary_le_one_of_re_eq_zero
      hQ hC₀ hC₁ hzero hone
  · exact zetaSurrogate_midpointReflectedProduct_right_boundary_le_one_of_re_eq_one
      hQ hC₀ hC₁ hzero hone

/--
Midpoint reflected-product Phragmen-Lindelöf core. Once the reflected quotient
has PL growth and unit boundary control on the two strip edges, its midpoint
specialization bounds the square of the original function by the midpoint
majorant.
-/
theorem midpoint_reflectedProduct_norm_sq_le_majorant_of_verticalStrip {f : ℂ → ℂ}
    {Q C₀ C₁ t : ℝ}
    (hmajorant :
      midpointReflectedProductMajorant Q C₀ C₁
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hd : DiffContOnCl ℂ
      (fun w => midpointReflectedProduct f w /
        midpointReflectedProductMajorant Q C₀ C₁ w)
      (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hgrowth : ∃ c < Real.pi / ((1 : ℝ) - 0), ∃ B,
      (fun w => midpointReflectedProduct f w /
        midpointReflectedProductMajorant Q C₀ C₁ w)
        =O[Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            Filter.principal (Complex.re ⁻¹' Set.Ioo 0 1)]
          fun w => Real.exp (B * Real.exp (c * |w.im|)))
    (hleft : ∀ w : ℂ, w.re = 0 →
      ‖midpointReflectedProduct f w / midpointReflectedProductMajorant Q C₀ C₁ w‖ ≤ 1)
    (hright : ∀ w : ℂ, w.re = 1 →
      ‖midpointReflectedProduct f w / midpointReflectedProductMajorant Q C₀ C₁ w‖ ≤ 1) :
    ‖f ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 ≤
      ‖midpointReflectedProductMajorant Q C₀ C₁
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
  let z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have hzre : z.re = (1 / 2 : ℝ) := by
    simp [z, Complex.add_re, Complex.mul_re]
  have hzleft : (0 : ℝ) ≤ z.re := by
    rw [hzre]
    norm_num
  have hzright : z.re ≤ (1 : ℝ) := by
    rw [hzre]
    norm_num
  have hquot :
      ‖midpointReflectedProduct f z / midpointReflectedProductMajorant Q C₀ C₁ z‖ ≤
        (1 : ℝ) :=
    PhragmenLindelof.vertical_strip
      (f := fun w => midpointReflectedProduct f w /
        midpointReflectedProductMajorant Q C₀ C₁ w)
      (a := 0) (b := 1) (C := 1) (z := z)
      hd hgrowth hleft hright hzleft hzright
  have hmajorant_pos :
      0 < ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ :=
    norm_pos_iff.mpr (by simpa [z] using hmajorant)
  have hproduct :
      ‖midpointReflectedProduct f z‖ ≤
        ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ := by
    rw [norm_div] at hquot
    have hmul :
        ‖midpointReflectedProduct f z‖ ≤
          (1 : ℝ) * ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ :=
      (div_le_iff₀ hmajorant_pos).mp (by simpa using hquot)
    simpa [one_mul] using hmul
  rw [show z = (1 / 2 : ℂ) + (t : ℂ) * Complex.I by rfl] at hproduct
  rw [midpointReflectedProduct_norm_midline] at hproduct
  exact hproduct

theorem zetaSurrogate_midpoint_norm_sq_le_majorant {Q : ℝ} (hQ : (1 : ℝ) < Q) :
    ∃ C₀ > 0, ∃ C₁ > 0,
      ∀ t : ℝ,
        ‖zetaSurrogate ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 ≤
          ‖midpointReflectedProductMajorant Q C₀ C₁
            ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
  obtain ⟨C₀, hC₀, C₁, hC₁, hleft, hright⟩ :=
    zetaSurrogate_midpointReflectedProduct_boundary_controls hQ
  obtain ⟨hnonzero, hd⟩ :=
    zetaSurrogate_midpointReflectedProduct_PL_inputs hQ hC₀.ne' hC₁.ne'
  refine ⟨C₀, hC₀, C₁, hC₁, ?_⟩
  intro t
  have hzmid :
      ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ∈
        Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, Complex.add_re, Complex.mul_re]
    norm_num
  exact midpoint_reflectedProduct_norm_sq_le_majorant_of_verticalStrip
    (f := zetaSurrogate) (Q := Q) (C₀ := C₀) (C₁ := C₁) (t := t)
    (hnonzero _ hzmid) hd
    (zetaSurrogate_midpointReflectedProduct_PL_growth hQ hC₀ hC₁)
    hleft hright

theorem A_critical_line_quarter_log {Q : ℝ} (hQ : (1 : ℝ) < Q) :
    ∃ k₁ > 0,
      ∀ t : ℝ,
        ‖backlundA ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          k₁ * (‖(Q : ℂ) + ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ (5 / 4 : ℝ) *
            ‖Complex.log ((Q : ℂ) + ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))‖) := by
  obtain ⟨C₀, hC₀, C₁, hC₁, hsquare⟩ :=
    zetaSurrogate_midpoint_norm_sq_le_majorant (Q := Q) hQ
  let k₁ : ℝ := Real.sqrt (C₀ * C₁)
  refine ⟨k₁, by positivity, ?_⟩
  intro t
  let z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  let R : ℝ := ‖(Q : ℂ) + z‖
  let L : ℝ := ‖Complex.log ((Q : ℂ) + z)‖
  have hRpos : 0 < R := by
    apply norm_pos_iff.mpr
    intro h
    have hre := congrArg Complex.re h
    simp [z, Complex.add_re, Complex.mul_re] at hre
    linarith
  have hLpos : 0 < L := by
    apply norm_pos_iff.mpr
    exact log_ne_zero_of_one_lt_re (by simp [z, Complex.add_re, Complex.mul_re]; linarith)
  have hksq : k₁ ^ 2 = C₀ * C₁ := by
    simpa [k₁] using Real.sq_sqrt (mul_nonneg hC₀.le hC₁.le)
  have hRpow :
      (R ^ (5 / 4 : ℝ)) ^ 2 = R ^ (5 / 2 : ℝ) := by
    rw [sq, ← Real.rpow_add hRpos]
    norm_num
  have hmajorant_norm :
      ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ =
        C₀ * C₁ * R ^ (5 / 2 : ℝ) * L ^ 2 := by
    rw [show z = (1 / 2 : ℂ) + (t : ℂ) * Complex.I by rfl]
    rw [midpointReflectedProductMajorant_norm_midline (Q := Q) (C₀ := C₀)
      (C₁ := C₁) (t := t) hQ]
    rw [abs_of_pos hC₀, abs_of_pos hC₁]
  have htarget_sq :
      ‖zetaSurrogate z‖ ^ 2 ≤
        (k₁ * (R ^ (5 / 4 : ℝ) * L)) ^ 2 := by
    have hsquare' :
        ‖zetaSurrogate z‖ ^ 2 ≤ ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ := by
      simpa [z] using hsquare t
    calc
      ‖zetaSurrogate z‖ ^ 2
          ≤ ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ := hsquare'
      _ = C₀ * C₁ * R ^ (5 / 2 : ℝ) * L ^ 2 := hmajorant_norm
      _ = (k₁ * (R ^ (5 / 4 : ℝ) * L)) ^ 2 := by
          rw [mul_pow, mul_pow, hksq, hRpow]
          ring
  have htarget_nonneg : 0 ≤ k₁ * (R ^ (5 / 4 : ℝ) * L) := by
    positivity
  have hsurrogate_le :
      ‖zetaSurrogate z‖ ≤ k₁ * (R ^ (5 / 4 : ℝ) * L) :=
    (sq_le_sq₀ (norm_nonneg _) htarget_nonneg).mp htarget_sq
  have hz_ne : z ≠ 1 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp [z, Complex.add_re, Complex.mul_re] at hre
  have hsurrogate_eq : zetaSurrogate z = backlundA z := by
    simp [zetaSurrogate, backlundA, hz_ne]
  rw [show ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = z by rfl]
  rw [← hsurrogate_eq]
  simpa [R, L] using hsurrogate_le

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
