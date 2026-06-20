import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Trigonometric
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaBinet
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Vertical Gamma decay on fixed strips

This file collects reusable Gamma/digamma estimates used by the Kadiri
horizontal route.  The statements here are independent of the Kadiri zero-set
and partial-fraction packaging.
-/

open Real

namespace Complex

/-! ## Critical-line Gamma decay -/

private lemma sin_pi_half_add_mul_I (τ : ℝ) :
    Complex.sin (Real.pi * (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)) =
      (Real.cosh (Real.pi * τ) : ℂ) := by
  have harg : (Real.pi : ℂ) * (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)
      = (Real.pi / 2 : ℂ) + ((Real.pi * τ : ℝ) : ℂ) * I := by
    norm_num [Complex.ofReal_div, Complex.ofReal_mul]
    ring_nf
  rw [harg]
  simp [Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.cos_mul_I,
    Complex.sin_mul_I, Complex.ofReal_cosh]

/-- Exact critical-line identity:
`‖Γ(1/2+iτ)‖² = π / cosh(πτ)`. -/
theorem gamma_half_vertical_norm_sq (τ : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * τ) := by
  let z : ℂ := ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I
  have hconj : (starRingEnd ℂ) z = 1 - z := by
    apply Complex.ext <;> norm_num [z, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im]
  have hleft :
      Complex.Gamma z * Complex.Gamma (1 - z) = ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hconj, Complex.Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsin : Complex.sin (Real.pi * z) = (Real.cosh (Real.pi * τ) : ℂ) := by
    simpa [z] using sin_pi_half_add_mul_I τ
  have hcomplex :
      ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) =
        ((Real.pi / Real.cosh (Real.pi * τ) : ℝ) : ℂ) := by
    calc
      ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ)
          = Complex.Gamma z * Complex.Gamma (1 - z) := hleft.symm
      _ = (Real.pi : ℂ) / Complex.sin (Real.pi * z) := Complex.Gamma_mul_Gamma_one_sub z
      _ = ((Real.pi / Real.cosh (Real.pi * τ) : ℝ) : ℂ) := by
        simp [hsin, Complex.ofReal_div]
  simpa [z] using Complex.ofReal_injective hcomplex

private lemma exp_abs_div_two_le_cosh (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    nlinarith [Real.exp_pos x, Real.exp_pos (-x)]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

private lemma gamma_half_vertical_norm_sq_le_exp (τ : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤
      2 * Real.pi * Real.exp (-(Real.pi * |τ|)) := by
  rw [gamma_half_vertical_norm_sq]
  have hxabs : |Real.pi * τ| = Real.pi * |τ| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hcosh_lower : Real.exp (Real.pi * |τ|) / 2 ≤ Real.cosh (Real.pi * τ) := by
    simpa [hxabs] using exp_abs_div_two_le_cosh (Real.pi * τ)
  have hden_pos : 0 < Real.exp (Real.pi * |τ|) / 2 := by positivity
  have hinv : (Real.cosh (Real.pi * τ))⁻¹ ≤ (Real.exp (Real.pi * |τ|) / 2)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hden_pos hcosh_lower
  have hinv_eval : (Real.exp (Real.pi * |τ|) / 2)⁻¹ =
      2 * Real.exp (-(Real.pi * |τ|)) := by
    rw [div_eq_mul_inv, mul_inv_rev]
    rw [inv_inv, ← Real.exp_neg]
  calc
    Real.pi / Real.cosh (Real.pi * τ) = Real.pi * (Real.cosh (Real.pi * τ))⁻¹ := by ring
    _ ≤ Real.pi * (Real.exp (Real.pi * |τ|) / 2)⁻¹ := by
      exact mul_le_mul_of_nonneg_left hinv Real.pi_pos.le
    _ = 2 * Real.pi * Real.exp (-(Real.pi * |τ|)) := by
      rw [hinv_eval]
      ring

/-- Critical-line Gamma decay:
`‖Γ(1/2+iτ)‖ ≤ √(2π) exp(-π|τ|/2)`. -/
theorem gamma_half_vertical_norm_le_exp (τ : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤
      Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2)) := by
  refine (sq_le_sq₀ (norm_nonneg _) ?_).mp ?_
  · positivity
  have hrhs_sq :
      (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2))) ^ 2 =
        2 * Real.pi * Real.exp (-(Real.pi * |τ|)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [hrhs_sq]
  exact gamma_half_vertical_norm_sq_le_exp τ

/-! ## Log-norm derivative and vertical-line digamma control -/

/-- `d/du log‖g u‖ = Re(g'/g)` when `g u ≠ 0` (`g : ℝ → ℂ`). -/
theorem hasDerivAt_log_norm {g : ℝ → ℂ} {g' : ℂ} {u : ℝ}
    (h : HasDerivAt g g' u) (hne : g u ≠ 0) :
    HasDerivAt (fun x => Real.log ‖g x‖) (g' / g u).re u := by
  have hre : HasDerivAt (fun x => (g x).re) g'.re u :=
    (Complex.reCLM.hasFDerivAt).comp_hasDerivAt u h
  have him : HasDerivAt (fun x => (g x).im) g'.im u :=
    (Complex.imCLM.hasFDerivAt).comp_hasDerivAt u h
  have hnsq : HasDerivAt (fun x => Complex.normSq (g x))
      (g'.re * (g u).re + (g u).re * g'.re + (g'.im * (g u).im + (g u).im * g'.im)) u := by
    have h1 : HasDerivAt (fun x => (g x).re * (g x).re)
        (g'.re * (g u).re + (g u).re * g'.re) u := hre.mul hre
    have h2 : HasDerivAt (fun x => (g x).im * (g x).im)
        (g'.im * (g u).im + (g u).im * g'.im) u := him.mul him
    have hsum := h1.add h2
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards with x
    simp only [Pi.add_apply, Complex.normSq_apply]
  have hpos : 0 < Complex.normSq (g u) := Complex.normSq_pos.mpr hne
  have hlog : HasDerivAt (fun x => Real.log (Complex.normSq (g x)))
      ((g'.re * (g u).re + (g u).re * g'.re + (g'.im * (g u).im + (g u).im * g'.im))
        / Complex.normSq (g u)) u := by
    have := hnsq.log (ne_of_gt hpos)
    simpa [div_eq_mul_inv] using this
  have hhalf : HasDerivAt (fun x => Real.log ‖g x‖)
      ((1 / 2) * ((g'.re * (g u).re + (g u).re * g'.re
          + (g'.im * (g u).im + (g u).im * g'.im)) / Complex.normSq (g u))) u := by
    have := hlog.const_mul (1 / 2 : ℝ)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards with x
    rw [show ‖g x‖ = Real.sqrt (Complex.normSq (g x)) by
        rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)],
      Real.log_sqrt (Complex.normSq_nonneg _)]
    ring
  refine hhalf.congr_deriv ?_
  rw [Complex.div_re, Complex.normSq_apply]
  field_simp
  ring

private def vline (τ : ℝ) : ℝ → ℂ := fun u => (u : ℂ) + (τ : ℂ) * I

private theorem vline_re (τ u : ℝ) : (vline τ u).re = u := by
  simp [vline, Complex.add_re, Complex.mul_re]

private theorem vline_im (τ u : ℝ) : (vline τ u).im = τ := by
  simp [vline, Complex.add_im, Complex.mul_im]

private theorem hasDerivAt_vline (τ u : ℝ) : HasDerivAt (vline τ) 1 u :=
  ((hasDerivAt_id u).ofReal_comp).add_const ((τ : ℂ) * I)

private theorem gamma_vline_ne_zero {τ u : ℝ} (hu : 0 < u) :
    Complex.Gamma (vline τ u) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hm
  have hre : (vline τ u).re = -(m : ℝ) := by rw [hm]; simp
  rw [vline_re] at hre
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

private theorem digamma_eq_logDeriv {τ u : ℝ} :
    (deriv Complex.Gamma (vline τ u) * 1 / Complex.Gamma (vline τ u))
      = Complex.digamma (vline τ u) := by
  rw [mul_one, Complex.digamma_def, logDeriv_apply]

/-- The log-norm of Γ along a vertical line has derivative `Re ψ(u + iτ)`. -/
theorem hasDerivAt_log_norm_gamma {τ u : ℝ} (hu : 0 < u) :
    HasDerivAt
      (fun x : ℝ => Real.log ‖Complex.Gamma ((x : ℂ) + (τ : ℂ) * I)‖)
      (Complex.digamma ((u : ℂ) + (τ : ℂ) * I)).re u := by
  change HasDerivAt (fun x : ℝ => Real.log ‖Complex.Gamma (vline τ x)‖)
    (Complex.digamma (vline τ u)).re u
  have hΓdiff : DifferentiableAt ℂ Complex.Gamma (vline τ u) := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have hre : (vline τ u).re = -(m : ℝ) := by rw [hm]; simp
    rw [vline_re] at hre
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hcomp : HasDerivAt (fun x : ℝ => Complex.Gamma (vline τ x))
      (deriv Complex.Gamma (vline τ u) * 1) u := by
    have h := (hΓdiff.hasDerivAt).scomp u (hasDerivAt_vline τ u)
    exact h.congr_deriv (by rw [one_smul, mul_one])
  have hne : Complex.Gamma (vline τ u) ≠ 0 := gamma_vline_ne_zero hu
  have := hasDerivAt_log_norm hcomp hne
  rwa [digamma_eq_logDeriv] at this

private theorem continuousOn_digamma_vline {τ a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u : ℝ => Complex.digamma (vline τ u)) (Set.Icc a b) := by
  intro u hu
  have hupos : 0 < u := lt_of_lt_of_le ha hu.1
  have hre : 0 < (vline τ u).re := by rw [vline_re]; exact hupos
  have hcd : ContinuousAt Complex.digamma (vline τ u) :=
    Complex.continuousAt_digamma_of_re_pos hre
  have hvc : ContinuousAt (vline τ) u := by
    apply Continuous.continuousAt
    unfold vline
    exact (Complex.continuous_ofReal.add continuous_const)
  exact (hcd.comp hvc).continuousWithinAt

private theorem re_digamma_vline_le_log_norm_add_four {u τ : ℝ}
    (hu : (1 / 2 : ℝ) ≤ u) (hτ : (1 : ℝ) ≤ |τ|) :
    (Complex.digamma (vline τ u)).re ≤ Real.log ‖vline τ u‖ + 4 := by
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hτne : τ ≠ 0 := by
    intro h
    rw [h] at hτ
    norm_num at hτ
  let z : ℂ := vline τ u
  have hzre : z.re = u := by simp [z, vline_re]
  have hzim : z.im = τ := by simp [z, vline_im]
  have hs : 0 < z.re := by rw [hzre]; exact hupos
  have him : z.im ≠ 0 := by rw [hzim]; exact hτne
  let corr : ℂ := -(z⁻¹ ^ (2 : ℕ)) / (12 : ℂ) +
    ∫ t in Set.Ioi (0 : ℝ), Complex.digammaBinetSecondOrderRemainderKernel z t
  have hcorr : corr.re ≤ 2 / (u * |τ|) := by
    have h := Complex.re_digamma_vertical_second_order_bound (s := z) hs him
    simpa [corr, hzre, hzim] using h
  have hinv_nonneg : 0 ≤ (z⁻¹ / (2 : ℂ)).re := by
    rw [Complex.div_re, Complex.inv_re]
    simp only [Complex.re_ofNat, Complex.normSq_ofNat, Complex.inv_im, Complex.im_ofNat, mul_zero,
      zero_div, add_zero]
    dsimp [z, vline]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_self, add_zero, Complex.normSq_apply, Complex.add_im, zero_add,
      mul_one]
    have hden : 0 < u * u + τ * τ := by nlinarith [mul_pos hupos hupos, sq_nonneg τ]
    field_simp [hden.ne']
    nlinarith [hupos, hden]
  have hcorr4 : corr.re ≤ 4 := by
    have hden_ge : (1 / 2 : ℝ) ≤ u * |τ| := by
      nlinarith [hu, hτ]
    have hinv : 1 / (u * |τ|) ≤ 1 / (1 / 2 : ℝ) := by
      exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden_ge
    have h2div : 2 / (u * |τ|) ≤ 4 := by
      have hmul := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
      norm_num at hmul
      simpa [div_eq_mul_inv] using hmul
    exact hcorr.trans h2div
  have hbinet_re : (Complex.digamma z).re =
      (Complex.log z).re - (z⁻¹ / (2 : ℂ)).re + corr.re := by
    rw [Complex.digamma_eq_log_sub_half_inv_sub_inv_sq_add_integral (s := z) hs]
    simp [corr, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    ring
  calc
    (Complex.digamma (vline τ u)).re = (Complex.digamma z).re := rfl
    _ = (Complex.log z).re - (z⁻¹ / (2 : ℂ)).re + corr.re := hbinet_re
    _ ≤ Real.log ‖z‖ + 4 := by
      rw [Complex.log_re]
      linarith
    _ = Real.log ‖vline τ u‖ + 4 := rfl

private theorem re_digamma_vline_le_log_base_add_const {A u τ : ℝ} (hA0 : 0 ≤ A)
    (hu : u ∈ Set.Icc (1 / 2 : ℝ) (A + 1)) (hτ : (1 : ℝ) ≤ |τ|) :
    (Complex.digamma (vline τ u)).re ≤
      Real.log (|τ| + 2) + (Real.log (A + 3) + 4) := by
  have hdig := re_digamma_vline_le_log_norm_add_four hu.1 hτ
  have hu_nonneg : 0 ≤ u := le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hu.1
  have hnorm_le_abs : ‖vline τ u‖ ≤ |(vline τ u).re| + |(vline τ u).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  have hnorm_le_sum : ‖vline τ u‖ ≤ u + |τ| := by
    calc
      ‖vline τ u‖ ≤ |(vline τ u).re| + |(vline τ u).im| := hnorm_le_abs
      _ = |u| + |τ| := by rw [vline_re, vline_im]
      _ = u + |τ| := by rw [abs_of_nonneg hu_nonneg]
  have hnorm_pos : 0 < ‖vline τ u‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hi := congrArg Complex.im hz
    rw [vline_im] at hi
    have hi0 : τ = 0 := by simpa using hi
    have : |τ| = 0 := by simp [hi0]
    linarith
  have hsum_le_prod : u + |τ| ≤ (A + 3) * (|τ| + 2) := by
    nlinarith [hu.2, hA0, abs_nonneg τ]
  have hnorm_le_prod : ‖vline τ u‖ ≤ (A + 3) * (|τ| + 2) :=
    hnorm_le_sum.trans hsum_le_prod
  have hlog_norm :
      Real.log ‖vline τ u‖ ≤ Real.log (|τ| + 2) + Real.log (A + 3) := by
    calc
      Real.log ‖vline τ u‖ ≤ Real.log ((A + 3) * (|τ| + 2)) :=
        Real.log_le_log hnorm_pos hnorm_le_prod
      _ = Real.log (A + 3) + Real.log (|τ| + 2) := by
        rw [Real.log_mul]
        · positivity
        · positivity
      _ = Real.log (|τ| + 2) + Real.log (A + 3) := by ring
  linarith

/-! ## Vertical Gamma bounds on fixed strips -/

/-- Vertical Gamma decay with sharp `u - 1/2` power. -/
theorem gamma_vertical_decay_add {A : ℝ} (hA0 : 0 ≤ A) :
    ∃ CΓ : ℝ, 0 ≤ CΓ ∧
      ∀ σ' τ : ℝ, σ' ∈ Set.Icc (1 / 2 : ℝ) (A + 1) → (1 : ℝ) ≤ |τ| →
        ‖Complex.Gamma ((σ' : ℂ) + (τ : ℂ) * I)‖ ≤
          CΓ * (|τ| + 2) ^ (σ' - 1 / 2) *
            Real.exp (-(Real.pi * |τ| / 2)) := by
  set K : ℝ := Real.log (A + 3) + 4 with hK_def
  set CΓ : ℝ := Real.sqrt (2 * Real.pi) * Real.exp ((A + 1 / 2) * K) with hCΓ_def
  have hK0 : 0 ≤ K := by
    have hlog_nonneg : 0 ≤ Real.log (A + 3) := Real.log_nonneg (by linarith)
    linarith [hK_def, hlog_nonneg]
  refine ⟨CΓ, by positivity, fun σ' τ hσ' hτ => ?_⟩
  obtain ⟨hσ'lo, hσ'hi⟩ := hσ'
  set L : ℝ := Real.log (|τ| + 2) with hL_def
  have hbase_pos : 0 < |τ| + 2 := by linarith [abs_nonneg τ]
  set F : ℝ → ℝ := fun u => Real.log ‖Complex.Gamma (vline τ u)‖ with hF_def
  set G : ℝ → ℝ := fun u => (Complex.digamma (vline τ u)).re with hG_def
  have hderiv : ∀ u ∈ Set.uIcc (1 / 2 : ℝ) σ', HasDerivAt F (G u) u := by
    intro u hu
    rw [Set.uIcc_of_le hσ'lo] at hu
    have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu.1
    change HasDerivAt (fun x : ℝ => Real.log ‖Complex.Gamma ((x : ℂ) + (τ : ℂ) * I)‖)
      (Complex.digamma ((u : ℂ) + (τ : ℂ) * I)).re u
    exact hasDerivAt_log_norm_gamma hupos
  have hGcont : ContinuousOn G (Set.uIcc (1 / 2 : ℝ) σ') := by
    rw [Set.uIcc_of_le hσ'lo]
    exact (Complex.continuous_re.comp_continuousOn (continuousOn_digamma_vline (by norm_num)))
  have hint : IntervalIntegrable G MeasureTheory.volume (1 / 2 : ℝ) σ' :=
    hGcont.intervalIntegrable
  have hFTC : ∫ u in (1 / 2 : ℝ)..σ', G u = F σ' - F (1 / 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hGub : ∀ u ∈ Set.Icc (1 / 2 : ℝ) σ', G u ≤ L + K := by
    intro u hu
    have huA : u ∈ Set.Icc (1 / 2 : ℝ) (A + 1) := ⟨hu.1, le_trans hu.2 hσ'hi⟩
    have h := re_digamma_vline_le_log_base_add_const hA0 huA hτ
    rw [hG_def, hL_def, hK_def]
    linarith
  have hintbd : ∫ u in (1 / 2 : ℝ)..σ', G u ≤ (σ' - 1 / 2) * (L + K) := by
    have hmono : ∫ u in (1 / 2 : ℝ)..σ', G u ≤ ∫ _ in (1 / 2 : ℝ)..σ', (L + K) :=
      intervalIntegral.integral_mono_on hσ'lo hint intervalIntegrable_const hGub
    rwa [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hbase : F (1 / 2) ≤
      Real.log (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2))) := by
    rw [hF_def]
    have hΓhalf : ‖Complex.Gamma (vline τ (1 / 2))‖ ≤
        Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2)) := by
      have h := gamma_half_vertical_norm_le_exp τ
      have heq : vline τ (1 / 2) = ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I := rfl
      rw [heq, show -(Real.pi * |τ| / 2) = -(Real.pi * |τ|) / 2 by ring]
      simpa [neg_div] using h
    have hΓhalf_pos : 0 < ‖Complex.Gamma (vline τ (1 / 2))‖ :=
      norm_pos_iff.mpr (gamma_vline_ne_zero (by norm_num))
    exact Real.log_le_log hΓhalf_pos hΓhalf
  have hσ'sub : (σ' - 1 / 2) ≤ (A + 1 / 2) := by linarith
  have hFσ'_bd : F σ' ≤
      Real.log (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2))) +
        (σ' - 1 / 2) * L + (A + 1 / 2) * K := by
    have hFeq : F σ' = F (1 / 2) + ∫ u in (1 / 2 : ℝ)..σ', G u := by rw [hFTC]; ring
    rw [hFeq]
    have hKstep : (σ' - 1 / 2) * K ≤ (A + 1 / 2) * K :=
      mul_le_mul_of_nonneg_right hσ'sub hK0
    calc
      F (1 / 2) + ∫ u in (1 / 2 : ℝ)..σ', G u
          ≤ F (1 / 2) + (σ' - 1 / 2) * (L + K) := by linarith [hintbd]
      _ ≤ Real.log (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2))) +
            (σ' - 1 / 2) * L + (A + 1 / 2) * K := by linarith [hbase, hKstep]
  have hΓσ'_pos : 0 < ‖Complex.Gamma ((σ' : ℂ) + (τ : ℂ) * I)‖ := by
    apply norm_pos_iff.mpr
    apply Complex.Gamma_ne_zero
    intro m hm
    have hre : ((σ' : ℂ) + (τ : ℂ) * I).re = -(m : ℝ) := by rw [hm]; simp
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] at hre
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    norm_num at hre
    linarith
  have hF_eq_target : F σ' = Real.log ‖Complex.Gamma ((σ' : ℂ) + (τ : ℂ) * I)‖ := by
    rw [hF_def]
    rfl
  have hRHS_pos : 0 <
      CΓ * (|τ| + 2) ^ (σ' - 1 / 2) * Real.exp (-(Real.pi * |τ| / 2)) := by
    have hpow : 0 < (|τ| + 2) ^ (σ' - 1 / 2) := Real.rpow_pos_of_pos hbase_pos _
    positivity
  have hlogRHS :
      Real.log (CΓ * (|τ| + 2) ^ (σ' - 1 / 2) *
          Real.exp (-(Real.pi * |τ| / 2))) =
        Real.log (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2))) +
          (σ' - 1 / 2) * L + (A + 1 / 2) * K := by
    have hsqrtexp_pos : 0 < Real.sqrt (2 * Real.pi) *
        Real.exp (-(Real.pi * |τ| / 2)) := by positivity
    have hpow_pos : 0 < (|τ| + 2) ^ (σ' - 1 / 2) :=
      Real.rpow_pos_of_pos hbase_pos _
    rw [show CΓ * (|τ| + 2) ^ (σ' - 1 / 2) *
          Real.exp (-(Real.pi * |τ| / 2)) =
        (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2))) *
          ((|τ| + 2) ^ (σ' - 1 / 2) * Real.exp ((A + 1 / 2) * K)) by
          rw [hCΓ_def]
          ring]
    rw [Real.log_mul hsqrtexp_pos.ne' (mul_ne_zero hpow_pos.ne' (Real.exp_pos _).ne')]
    rw [Real.log_mul hpow_pos.ne' (Real.exp_pos _).ne']
    rw [Real.log_rpow hbase_pos, hL_def]
    simp
    ring
  have hloglog :
      Real.log ‖Complex.Gamma ((σ' : ℂ) + (τ : ℂ) * I)‖ ≤
        Real.log (CΓ * (|τ| + 2) ^ (σ' - 1 / 2) *
          Real.exp (-(Real.pi * |τ| / 2))) := by
    rw [hlogRHS, ← hF_eq_target]
    exact hFσ'_bd
  exact (Real.log_le_log_iff hΓσ'_pos hRHS_pos).mp hloglog

/-- Loose vertical Gamma decay with an unspecified fixed polynomial power. -/
theorem gamma_vertical_loose_bound_add {A : ℝ} (hA0 : 0 ≤ A) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ σ' τ : ℝ, σ' ∈ Set.Icc (1 / 2 : ℝ) (A + 1) → (1 : ℝ) ≤ |τ| →
      ‖Complex.Gamma ((σ' : ℂ) + (τ : ℂ) * I)‖ ≤
        Real.sqrt (2 * Real.pi) * (|τ| + 2) ^ d * Real.exp (-(Real.pi * |τ| / 2)) := by
  obtain ⟨C, hC0, hCbd⟩ :=
    Complex.exists_norm_digamma_le_log (a := (1 / 2 : ℝ)) (b := A + 1) (by norm_num)
  refine ⟨C * (A + 1 / 2), by positivity, fun σ' τ hσ' hτ => ?_⟩
  obtain ⟨hσ'lo, hσ'hi⟩ := hσ'
  set L : ℝ := Real.log (|τ| + 2) with hL_def
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [abs_nonneg τ])
  have hbase_pos : 0 < |τ| + 2 := by linarith [abs_nonneg τ]
  set F : ℝ → ℝ := fun u => Real.log ‖Complex.Gamma (vline τ u)‖ with hF_def
  set G : ℝ → ℝ := fun u => (Complex.digamma (vline τ u)).re with hG_def
  have hderiv : ∀ u ∈ Set.uIcc (1 / 2 : ℝ) σ', HasDerivAt F (G u) u := by
    intro u hu
    rw [Set.uIcc_of_le hσ'lo] at hu
    have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu.1
    change HasDerivAt (fun x : ℝ => Real.log ‖Complex.Gamma ((x : ℂ) + (τ : ℂ) * I)‖)
      (Complex.digamma ((u : ℂ) + (τ : ℂ) * I)).re u
    exact hasDerivAt_log_norm_gamma hupos
  have hGcont : ContinuousOn G (Set.uIcc (1 / 2 : ℝ) σ') := by
    rw [Set.uIcc_of_le hσ'lo]
    exact (Complex.continuous_re.comp_continuousOn (continuousOn_digamma_vline (by norm_num)))
  have hint : IntervalIntegrable G MeasureTheory.volume (1 / 2 : ℝ) σ' :=
    hGcont.intervalIntegrable
  have hFTC : ∫ u in (1 / 2 : ℝ)..σ', G u = F σ' - F (1 / 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hGub : ∀ u ∈ Set.Icc (1 / 2 : ℝ) σ', G u ≤ C * L := by
    intro u hu
    have hre : (vline τ u).re = u := vline_re τ u
    have him : (vline τ u).im = τ := vline_im τ u
    have h1 : G u ≤ ‖Complex.digamma (vline τ u)‖ := by
      rw [hG_def]; exact (Complex.re_le_norm _)
    have h2 : ‖Complex.digamma (vline τ u)‖ ≤ C * Real.log (|(vline τ u).im| + 2) :=
      hCbd (vline τ u) (by rw [hre]; exact hu.1) (by rw [hre]; linarith [hu.2, hσ'hi])
    rw [him] at h2
    calc G u ≤ ‖Complex.digamma (vline τ u)‖ := h1
      _ ≤ C * Real.log (|τ| + 2) := h2
      _ = C * L := by rw [hL_def]
  have hintbd : ∫ u in (1 / 2 : ℝ)..σ', G u ≤ (σ' - 1 / 2) * (C * L) := by
    have hmono : ∫ u in (1 / 2 : ℝ)..σ', G u ≤ ∫ _ in (1 / 2 : ℝ)..σ', (C * L) :=
      intervalIntegral.integral_mono_on hσ'lo hint (intervalIntegrable_const) hGub
    rwa [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hbase : F (1 / 2) ≤ Real.log (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2))) := by
    rw [hF_def]
    have hΓhalf : ‖Complex.Gamma (vline τ (1 / 2))‖ ≤
        Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2)) := by
      have h := gamma_half_vertical_norm_le_exp τ
      have heq : vline τ (1 / 2) = ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I := rfl
      rw [heq, show -(Real.pi * |τ| / 2) = -(Real.pi * |τ|) / 2 by ring]
      simpa [neg_div] using h
    have hΓhalf_pos : 0 < ‖Complex.Gamma (vline τ (1 / 2))‖ :=
      norm_pos_iff.mpr (gamma_vline_ne_zero (by norm_num))
    exact Real.log_le_log hΓhalf_pos hΓhalf
  have hσ'sub : (σ' - 1 / 2) ≤ (A + 1 / 2) := by linarith
  have hFσ'_bd : F σ' ≤ Real.log (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2)))
      + (A + 1 / 2) * (C * L) := by
    have hFeq : F σ' = F (1 / 2) + ∫ u in (1 / 2 : ℝ)..σ', G u := by rw [hFTC]; ring
    rw [hFeq]
    have hstep : (σ' - 1 / 2) * (C * L) ≤ (A + 1 / 2) * (C * L) :=
      mul_le_mul_of_nonneg_right hσ'sub (by positivity)
    calc F (1 / 2) + ∫ u in (1 / 2 : ℝ)..σ', G u
        ≤ F (1 / 2) + (σ' - 1 / 2) * (C * L) := by linarith [hintbd]
      _ ≤ Real.log (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2)))
            + (A + 1 / 2) * (C * L) := by linarith [hbase, hstep]
  have hΓσ'_pos : 0 < ‖Complex.Gamma ((σ' : ℂ) + (τ : ℂ) * I)‖ := by
    apply norm_pos_iff.mpr
    apply Complex.Gamma_ne_zero
    intro m hm
    have hre : ((σ' : ℂ) + (τ : ℂ) * I).re = -(m : ℝ) := by rw [hm]; simp
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] at hre
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    norm_num at hre
    linarith
  have hF_eq_target : F σ' = Real.log ‖Complex.Gamma ((σ' : ℂ) + (τ : ℂ) * I)‖ := by
    rw [hF_def]
    change Real.log ‖Complex.Gamma (vline τ σ')‖ =
      Real.log ‖Complex.Gamma ((σ' : ℂ) + (τ : ℂ) * I)‖
    rfl
  set d : ℝ := C * (A + 1 / 2) with hd_def
  have hRHS_pos : 0 < Real.sqrt (2 * Real.pi) * (|τ| + 2) ^ d * Real.exp (-(Real.pi * |τ| / 2)) := by
    have h1 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have h2 : 0 < (|τ| + 2) ^ d := Real.rpow_pos_of_pos hbase_pos d
    positivity
  have hlogRHS : Real.log (Real.sqrt (2 * Real.pi) * (|τ| + 2) ^ d * Real.exp (-(Real.pi * |τ| / 2)))
      = Real.log (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2))) + (A + 1 / 2) * (C * L) := by
    rw [show Real.sqrt (2 * Real.pi) * (|τ| + 2) ^ d * Real.exp (-(Real.pi * |τ| / 2))
        = (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2))) * (|τ| + 2) ^ d by ring,
      Real.log_mul (by
        have h1 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
        positivity) (by positivity), Real.log_rpow hbase_pos, hd_def, hL_def]
    ring
  have hloglog : Real.log ‖Complex.Gamma ((σ' : ℂ) + (τ : ℂ) * I)‖
      ≤ Real.log (Real.sqrt (2 * Real.pi) * (|τ| + 2) ^ d * Real.exp (-(Real.pi * |τ| / 2))) := by
    rw [hlogRHS, ← hF_eq_target]; exact hFσ'_bd
  exact (Real.log_le_log_iff hΓσ'_pos hRHS_pos).mp hloglog

end Complex
