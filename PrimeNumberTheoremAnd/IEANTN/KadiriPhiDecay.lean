import Mathlib.Analysis.Fourier.FourierTransformDeriv
import PrimeNumberTheoremAnd.IEANTN.KadiriHorizontalPVCanonical

/-!
# Kadiri condition-B Phi decay surface

This sidecar makes the condition-B-to-weighted-L1 step public for the horizontal
route.  It also records the elementary norm estimate extracted from one
Fourier integration-by-parts identity, and keeps the FinalBound/canonical-PV
assembly reachable from this file.
-/

namespace Kadiri

open MeasureTheory Complex Filter Asymptotics
open scoped Topology FourierTransform

noncomputable section

/-- Condition-B decay gives weighted integrability throughout the horizontal
strip `-a <= sigma <= 1+a`.  This is the L1 input used before applying Fourier
integration by parts to `phi(y) * exp(sigma*y)`. -/
theorem kadiriConditionB_weightedStripIntegrable_of_continuous {φ : ℝ → ℂ}
    (hφ : Continuous φ) {b a σ : ℝ}
    (hφ_decay : (fun x : ℝ => φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ => Real.exp (-(1 / 2 + b) * |x|))
    (hab : a < b) (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    Integrable (fun y : ℝ => φ y * exp ((σ : ℂ) * (y : ℂ))) := by
  let F : ℝ → ℂ := fun y => φ y * exp ((σ : ℂ) * (y : ℂ))
  have hF_cont : Continuous F := by
    dsimp [F]
    fun_prop
  have hF_loc : LocallyIntegrable F volume := hF_cont.locallyIntegrable
  have hshape : ∀ x : ℝ,
      ‖F x‖ =
        Real.exp ((σ - 1 / 2) * x) * ‖φ x * exp ((x : ℂ) / 2)‖ := by
    intro x
    dsimp [F]
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
    have hσ_re : (((σ : ℂ) * (x : ℂ))).re = σ * x := by
      norm_num [Complex.mul_re]
    have hhalf_re : (((x : ℂ) / 2)).re = x / 2 := by
      norm_num
    rw [hσ_re, hhalf_re]
    calc
      ‖φ x‖ * Real.exp (σ * x)
          = (Real.exp ((σ - 1 / 2) * x) * Real.exp (x / 2)) * ‖φ x‖ := by
            rw [← Real.exp_add]
            ring_nf
      _ = Real.exp ((σ - 1 / 2) * x) * (Real.exp (x / 2) * ‖φ x‖) := by ring
      _ = Real.exp ((σ - 1 / 2) * x) * (‖φ x‖ * Real.exp (x / 2)) := by ring
  have htop_decay := hφ_decay.mono
    (show Filter.atTop ≤ Filter.cocompact ℝ from atTop_le_cocompact)
  have hbot_decay := hφ_decay.mono
    (show Filter.atBot ≤ Filter.cocompact ℝ from atBot_le_cocompact)
  have htop :
      F =O[Filter.atTop] fun x : ℝ => Real.exp ((σ - 1 - b) * x) := by
    rw [Asymptotics.isBigO_iff] at htop_decay ⊢
    obtain ⟨C, hC⟩ := htop_decay
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_gt_atTop (0 : ℝ)] with x hxC hxpos
    rw [hshape]
    calc
      Real.exp ((σ - 1 / 2) * x) * ‖φ x * exp ((x : ℂ) / 2)‖
          ≤ Real.exp ((σ - 1 / 2) * x) *
              (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
            exact mul_le_mul_of_nonneg_left hxC (Real.exp_nonneg _)
      _ = C * ‖Real.exp ((σ - 1 - b) * x)‖ := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
              abs_of_pos (Real.exp_pos _), abs_of_pos hxpos]
            calc
              Real.exp ((σ - 1 / 2) * x) *
                    (C * Real.exp (-(1 / 2 + b) * x))
                  = C * (Real.exp ((σ - 1 / 2) * x) *
                      Real.exp (-(1 / 2 + b) * x)) := by ring_nf
              _ = C * Real.exp ((σ - 1 / 2) * x + (-(1 / 2 + b) * x)) := by
                    rw [Real.exp_add]
              _ = C * Real.exp ((σ - 1 - b) * x) := by ring_nf
  have hbot :
      F =O[Filter.atBot] fun x : ℝ => Real.exp ((σ + b) * x) := by
    rw [Asymptotics.isBigO_iff] at hbot_decay ⊢
    obtain ⟨C, hC⟩ := hbot_decay
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_lt_atBot (0 : ℝ)] with x hxC hxneg
    rw [hshape]
    calc
      Real.exp ((σ - 1 / 2) * x) * ‖φ x * exp ((x : ℂ) / 2)‖
          ≤ Real.exp ((σ - 1 / 2) * x) *
              (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
            exact mul_le_mul_of_nonneg_left hxC (Real.exp_nonneg _)
      _ = C * ‖Real.exp ((σ + b) * x)‖ := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
              abs_of_pos (Real.exp_pos _), abs_of_neg hxneg]
            calc
              Real.exp ((σ - 1 / 2) * x) *
                    (C * Real.exp (-(1 / 2 + b) * -x))
                  = C * (Real.exp ((σ - 1 / 2) * x) *
                      Real.exp (-(1 / 2 + b) * -x)) := by ring_nf
              _ = C * Real.exp ((σ - 1 / 2) * x + (-(1 / 2 + b) * -x)) := by
                    rw [Real.exp_add]
              _ = C * Real.exp ((σ + b) * x) := by ring_nf
  have htop_int :
      IntegrableAtFilter (fun x : ℝ => Real.exp ((σ - 1 - b) * x))
        Filter.atTop volume := by
    refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
    convert exp_neg_integrableOn_Ioi 0
      (show 0 < 1 + b - σ by linarith [hσ.2, hab]) using 1
    ext x
    congr 1
    ring
  have hbot_int :
      IntegrableAtFilter (fun x : ℝ => Real.exp ((σ + b) * x))
        Filter.atBot volume := by
    rw [← Filter.map_neg_atTop, measurableEmbedding_neg.integrableAtFilter_iff_comap]
    have hvol : (volume : Measure ℝ).comap Neg.neg = volume := by
      convert (MeasurableEquiv.neg ℝ).map_symm.symm using 1
      simp
    rw [hvol, Function.comp_def]
    refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
    convert exp_neg_integrableOn_Ioi 0
      (show 0 < σ + b by linarith [hσ.1, hab]) using 1
    ext x
    congr 1
    ring
  exact hF_loc.integrable_of_isBigO_atBot_atTop hbot hbot_int htop htop_int

/-- ContDiff wrapper for the public weighted-integrability lemma. -/
theorem kadiriConditionB_weightedStripIntegrable {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b a σ : ℝ}
    (hφ_decay : (fun x : ℝ => φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ => Real.exp (-(1 / 2 + b) * |x|))
    (hab : a < b) (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    Integrable (fun y : ℝ => φ y * exp ((σ : ℂ) * (y : ℂ))) :=
  kadiriConditionB_weightedStripIntegrable_of_continuous hφ.continuous hφ_decay hab hσ

/-- Condition-B derivative decay gives the matching weighted-L1 input for
`deriv phi`. -/
theorem kadiriConditionB_weightedDerivStripIntegrable {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b a σ : ℝ}
    (hφ'_decay : (fun x : ℝ => deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ => Real.exp (-(1 / 2 + b) * |x|))
    (hab : a < b) (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    Integrable (fun y : ℝ => deriv φ y * exp ((σ : ℂ) * (y : ℂ))) :=
  kadiriConditionB_weightedStripIntegrable_of_continuous
    (φ := fun y => deriv φ y) (hφ.continuous_deriv (by norm_num))
    hφ'_decay hab hσ

/-- Differentiability of the exponentially weighted line source. -/
theorem kadiriConditionB_weightedLineDifferentiable {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (σ : ℝ) :
    Differentiable ℝ (fun y : ℝ => φ y * exp ((σ : ℂ) * (y : ℂ))) := by
  intro y
  have hlinear :
      DifferentiableAt ℝ (fun y : ℝ => (σ : ℂ) * (y : ℂ)) y := by
    exact ((hasDerivAt_id y).ofReal_comp.const_mul (σ : ℂ)).differentiableAt
  exact ((hφ.differentiable (by norm_num)) y).mul hlinear.cexp

/-- Pointwise derivative of the exponentially weighted line source. -/
theorem kadiriConditionB_weightedLine_deriv_eq {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (σ y : ℝ) :
    deriv (fun x : ℝ => φ x * exp ((σ : ℂ) * (x : ℂ))) y =
      deriv φ y * exp ((σ : ℂ) * (y : ℂ)) +
        (σ : ℂ) * (φ y * exp ((σ : ℂ) * (y : ℂ))) := by
  have hexp :
      HasDerivAt (fun x : ℝ => exp ((σ : ℂ) * (x : ℂ)))
        ((σ : ℂ) * exp ((σ : ℂ) * (y : ℂ))) y := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (((hasDerivAt_id y).ofReal_comp.const_mul (σ : ℂ)).cexp)
  have hφy : HasDerivAt φ (deriv φ y) y :=
    ((hφ.differentiable (by norm_num)) y).hasDerivAt
  have hmul := hφy.mul hexp
  simpa [mul_add, mul_assoc, mul_comm, mul_left_comm] using hmul.deriv

/-- Condition B gives integrability of the derivative of the weighted line
source, the precondition for the Fourier/IBP decay step. -/
theorem kadiriConditionB_weightedLineDerivIntegrable {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b a σ : ℝ}
    (hφ_decay : (fun x : ℝ => φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ => Real.exp (-(1 / 2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ => deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ => Real.exp (-(1 / 2 + b) * |x|))
    (hab : a < b) (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    Integrable (deriv (fun y : ℝ => φ y * exp ((σ : ℂ) * (y : ℂ)))) := by
  have hbase :
      Integrable (fun y : ℝ => φ y * exp ((σ : ℂ) * (y : ℂ))) :=
    kadiriConditionB_weightedStripIntegrable hφ hφ_decay hab hσ
  have hbase_scaled :
      Integrable (fun y : ℝ => (σ : ℂ) *
        (φ y * exp ((σ : ℂ) * (y : ℂ)))) := by
    simpa [smul_eq_mul] using hbase.const_mul (σ : ℂ)
  have hderiv :
      Integrable (fun y : ℝ => deriv φ y * exp ((σ : ℂ) * (y : ℂ))) :=
    kadiriConditionB_weightedDerivStripIntegrable hφ hφ'_decay hab hσ
  have hsum :
      Integrable (fun y : ℝ =>
        deriv φ y * exp ((σ : ℂ) * (y : ℂ)) +
          (σ : ℂ) * (φ y * exp ((σ : ℂ) * (y : ℂ)))) :=
    hderiv.add hbase_scaled
  refine MeasureTheory.Integrable.congr hsum ?_
  filter_upwards with y
  rw [kadiriConditionB_weightedLine_deriv_eq hφ σ y]

/-- Whole-line Fourier integration by parts for the `exp (i T y)` kernel.
This is the exact identity used before applying the elementary norm bound. -/
theorem kadiri_fourier_exp_i_mul_ibp {g : ℝ → ℂ} {T : ℝ}
    (hT : T ≠ 0) (hg : Integrable g) (hg_diff : Differentiable ℝ g)
    (hg_deriv : Integrable (deriv g)) :
    (∫ y : ℝ, g y * exp (((T * y : ℝ) : ℂ) * I))
      = (I / (T : ℂ)) * ∫ y : ℝ, deriv g y * exp (((T * y : ℝ) : ℂ) * I) := by
  let u : ℝ := -T / (2 * Real.pi)
  have hfourier := congr_fun (Real.fourier_deriv (f := g) hg hg_diff hg_deriv) u
  have hphase : ∀ y : ℝ,
      Complex.exp ((↑(-2 * Real.pi * y * u) : ℂ) * I) =
        Complex.exp (((T * y : ℝ) : ℂ) * I) := by
    intro y
    congr 1
    dsimp [u]
    norm_num [Real.pi_ne_zero]
    field_simp [Real.pi_ne_zero]
  have hF_g : 𝓕 g u = ∫ y : ℝ, g y * exp (((T * y : ℝ) : ℂ) * I) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [hphase y]
    simp [smul_eq_mul, mul_comm]
  have hF_deriv :
      𝓕 (deriv g) u = ∫ y : ℝ, deriv g y * exp (((T * y : ℝ) : ℂ) * I) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [hphase y]
    simp [smul_eq_mul, mul_comm]
  have hcoef : (2 * ↑Real.pi * I * (u : ℂ)) = -((T : ℂ) * I) := by
    dsimp [u]
    norm_num [Real.pi_ne_zero]
    field_simp [Real.pi_ne_zero]
  rw [hF_deriv, hF_g, hcoef] at hfourier
  have hT_complex : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  rw [hfourier]
  simp [smul_eq_mul]
  field_simp [hT_complex]
  simp only [I_sq, neg_mul, one_mul, neg_neg]
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  ring_nf

/-- Norm estimate extracted from a Fourier integration-by-parts identity.  The
identity itself is the analytic IBP step; this lemma turns it into the
`1 / |T|` L1 bound used by the horizontal route. -/
theorem norm_fourier_le_integral_norm_div {g g' : ℝ → ℂ} {T : ℝ}
    (hT : T ≠ 0)
    (hibp : (∫ y : ℝ, g y * exp (((T * y : ℝ) : ℂ) * I))
        = ((I / (T : ℂ)) *
            ∫ y : ℝ, g' y * exp (((T * y : ℝ) : ℂ) * I))) :
    ‖∫ y : ℝ, g y * exp (((T * y : ℝ) : ℂ) * I)‖
      ≤ (∫ y : ℝ, ‖g' y * exp (((T * y : ℝ) : ℂ) * I)‖) / |T| := by
  have hT_abs : |T| ≠ 0 := abs_ne_zero.mpr hT
  calc
    ‖∫ y : ℝ, g y * exp (((T * y : ℝ) : ℂ) * I)‖
        = ‖(I / (T : ℂ)) *
            ∫ y : ℝ, g' y * exp (((T * y : ℝ) : ℂ) * I)‖ := by
          rw [hibp]
    _ = ‖I / (T : ℂ)‖ *
          ‖∫ y : ℝ, g' y * exp (((T * y : ℝ) : ℂ) * I)‖ := by
          rw [norm_mul]
    _ ≤ ‖I / (T : ℂ)‖ *
          (∫ y : ℝ, ‖g' y * exp (((T * y : ℝ) : ℂ) * I)‖) := by
          exact mul_le_mul_of_nonneg_left
            (MeasureTheory.norm_integral_le_integral_norm
              (fun y : ℝ => g' y * exp (((T * y : ℝ) : ℂ) * I)))
            (norm_nonneg _)
    _ = (∫ y : ℝ, ‖g' y * exp (((T * y : ℝ) : ℂ) * I)‖) / |T| := by
          rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_div,
            inv_mul_eq_div]

/-- Compatibility alias for the Fourier norm estimate, named with the absolute
denominator in the theorem surface. -/
theorem norm_fourier_le_integral_norm_div_abs {g g' : ℝ → ℂ} {T : ℝ}
    (hT : T ≠ 0)
    (hibp : (∫ y : ℝ, g y * exp (((T * y : ℝ) : ℂ) * I))
        = ((I / (T : ℂ)) *
            ∫ y : ℝ, g' y * exp (((T * y : ℝ) : ℂ) * I))) :
    ‖∫ y : ℝ, g y * exp (((T * y : ℝ) : ℂ) * I)‖
      ≤ (∫ y : ℝ, ‖g' y * exp (((T * y : ℝ) : ℂ) * I)‖) / |T| :=
  norm_fourier_le_integral_norm_div hT hibp

/-- Condition-B weighted-line form of the Fourier/IBP norm estimate.  This is
the local `1 / |T|` input for the horizontal `Φ` decay on
`σ ∈ [-a, 1+a]`. -/
theorem kadiriConditionB_weightedLine_fourier_norm_le_deriv_integral_div_abs
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) {b a σ T : ℝ}
    (hT : T ≠ 0)
    (hφ_decay : (fun x : ℝ => φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ => Real.exp (-(1 / 2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ => deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ => Real.exp (-(1 / 2 + b) * |x|))
    (hab : a < b) (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    ‖∫ y : ℝ,
        (φ y * exp ((σ : ℂ) * (y : ℂ))) *
          exp (((T * y : ℝ) : ℂ) * I)‖
      ≤ (∫ y : ℝ,
          ‖deriv (fun x : ℝ => φ x * exp ((σ : ℂ) * (x : ℂ))) y *
            exp (((T * y : ℝ) : ℂ) * I)‖) / |T| :=
  norm_fourier_le_integral_norm_div_abs
    (g := fun y : ℝ => φ y * exp ((σ : ℂ) * (y : ℂ)))
    (g' := deriv (fun x : ℝ => φ x * exp ((σ : ℂ) * (x : ℂ)))) hT
    (kadiri_fourier_exp_i_mul_ibp hT
      (kadiriConditionB_weightedStripIntegrable hφ hφ_decay hab hσ)
      (kadiriConditionB_weightedLineDifferentiable hφ σ)
      (kadiriConditionB_weightedLineDerivIntegrable
        hφ hφ_decay hφ'_decay hab hσ))

/-- Rewrite the top horizontal transform value as a weighted Fourier integral. -/
theorem kadiriHorizontalPhi_top_eq_weightedLineFourier {φ : ℝ → ℂ} (σ T : ℝ) :
    kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)) =
      ∫ y : ℝ,
        (φ y * exp ((σ : ℂ) * (y : ℂ))) *
          exp (((T * y : ℝ) : ℂ) * I) := by
  unfold kadiriHorizontalPhi kadiriTopHorizontalPoint
  apply integral_congr_ae
  filter_upwards with y
  calc
    φ y * exp (- -((σ : ℂ) + (T : ℂ) * I) * (y : ℂ))
        = φ y * exp ((σ : ℂ) * (y : ℂ) + ((T * y : ℝ) : ℂ) * I) := by
            congr 2
            rw [Complex.ofReal_mul]
            ring
    _ = φ y * (exp ((σ : ℂ) * (y : ℂ)) *
          exp (((T * y : ℝ) : ℂ) * I)) := by
            rw [exp_add]
    _ = (φ y * exp ((σ : ℂ) * (y : ℂ))) *
          exp (((T * y : ℝ) : ℂ) * I) := by
            ring

/-- Rewrite the bottom horizontal transform value as a weighted Fourier
integral with frequency `-T`. -/
theorem kadiriHorizontalPhi_bot_eq_weightedLineFourier {φ : ℝ → ℂ} (σ T : ℝ) :
    kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)) =
      ∫ y : ℝ,
        (φ y * exp ((σ : ℂ) * (y : ℂ))) *
          exp ((((-T) * y : ℝ) : ℂ) * I) := by
  unfold kadiriHorizontalPhi kadiriBotHorizontalPoint
  apply integral_congr_ae
  filter_upwards with y
  calc
    φ y * exp (- -((σ : ℂ) + ((-T : ℝ) : ℂ) * I) * (y : ℂ))
        = φ y * exp ((σ : ℂ) * (y : ℂ) + (((-T) * y : ℝ) : ℂ) * I) := by
            congr 2
            rw [Complex.ofReal_mul]
            ring
    _ = φ y * (exp ((σ : ℂ) * (y : ℂ)) *
          exp ((((-T) * y : ℝ) : ℂ) * I)) := by
            rw [exp_add]
    _ = (φ y * exp ((σ : ℂ) * (y : ℂ))) *
          exp ((((-T) * y : ℝ) : ℂ) * I) := by
            ring

/-- Pointwise top-segment `Φ` estimate from condition-B weighted-line
Fourier/IBP. Uniformity in `σ` is the later constant-extraction step. -/
theorem kadiriHorizontalPhi_top_norm_le_weightedLine_deriv_integral_div_abs
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) {b a σ T : ℝ}
    (hT : T ≠ 0)
    (hφ_decay : (fun x : ℝ => φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ => Real.exp (-(1 / 2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ => deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ => Real.exp (-(1 / 2 + b) * |x|))
    (hab : a < b) (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    ‖kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))‖
      ≤ (∫ y : ℝ,
          ‖deriv (fun x : ℝ => φ x * exp ((σ : ℂ) * (x : ℂ))) y *
            exp (((T * y : ℝ) : ℂ) * I)‖) / |T| := by
  rw [kadiriHorizontalPhi_top_eq_weightedLineFourier]
  exact kadiriConditionB_weightedLine_fourier_norm_le_deriv_integral_div_abs
    hφ hT hφ_decay hφ'_decay hab hσ

/-- Pointwise bottom-segment `Φ` estimate from condition-B weighted-line
Fourier/IBP. Uniformity in `σ` is the later constant-extraction step. -/
theorem kadiriHorizontalPhi_bot_norm_le_weightedLine_deriv_integral_div_abs
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) {b a σ T : ℝ}
    (hT : T ≠ 0)
    (hφ_decay : (fun x : ℝ => φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ => Real.exp (-(1 / 2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ => deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ => Real.exp (-(1 / 2 + b) * |x|))
    (hab : a < b) (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    ‖kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))‖
      ≤ (∫ y : ℝ,
          ‖deriv (fun x : ℝ => φ x * exp ((σ : ℂ) * (x : ℂ))) y *
            exp ((((-T) * y : ℝ) : ℂ) * I)‖) / |T| := by
  rw [kadiriHorizontalPhi_bot_eq_weightedLineFourier]
  have hneg : -T ≠ 0 := neg_ne_zero.mpr hT
  simpa [abs_neg] using
    (kadiriConditionB_weightedLine_fourier_norm_le_deriv_integral_div_abs
      hφ hneg hφ_decay hφ'_decay hab hσ)

/-- The C1 transform-decay contract includes the plain transform-decay
contract. -/
theorem kadiriHorizontalPhiDecayBound_of_phiPrimeDecay {φ : ℝ → ℂ} {a : ℝ}
    (hΦ : KadiriHorizontalPhiPrimeDecayBound φ a) :
    KadiriHorizontalPhiDecayBound φ a := by
  rcases hΦ with ⟨A0, _A1, hA0, _hA1, hΦ⟩
  refine ⟨A0, hA0, ?_⟩
  filter_upwards [hΦ] with T hT
  rcases hT with ⟨hT_abs, htop, hbot⟩
  exact ⟨le_trans (by norm_num : (1 : ℝ) ≤ 2) hT_abs,
    (fun σ hσ => (htop σ hσ).1),
    (fun σ hσ => (hbot σ hσ).1)⟩

/-- FinalBound plus the Phi/PV C1 route input gives the canonical PV package.
This alias keeps the condition-B sidecar as the capstone import surface. -/
def kadiriHorizontalPVPackage_of_finalBound_and_phiDecay
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hΦ : KadiriHorizontalPhiC1DecayBound φ a) :
    KadiriHorizontalPVPackage φ a :=
  kadiriHorizontalPVPackage_of_finalBound_and_phiC1Decay ha hΦ

/-- Top canonical PV vanishing from FinalBound and the Phi/PV C1 route input. -/
theorem kadiri_thm_3_1_q1_top_horizontal_pv_vanishes_of_finalBound_and_phiDecay
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hΦ : KadiriHorizontalPhiC1DecayBound φ a) :
    Filter.Tendsto (kadiriTopHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_top_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_finalBound_and_phiDecay ha hΦ)

/-- Bottom canonical PV vanishing from FinalBound and the Phi/PV C1 route input. -/
theorem kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes_of_finalBound_and_phiDecay
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hΦ : KadiriHorizontalPhiC1DecayBound φ a) :
    Filter.Tendsto (kadiriBotHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_finalBound_and_phiDecay ha hΦ)

end

end Kadiri
