import PrimeNumberTheoremAnd.Defs
import PrimeNumberTheoremAnd.PerronFormula

namespace Kadiri

open MeasureTheory Complex
open Asymptotics
open ArithmeticFunction hiding log
open Filter
open scoped Topology
open scoped FourierTransform

lemma kadiri_laplace_strip_weight_integrable_of_continuous {ψ : ℝ → ℂ}
    (hψ : Continuous ψ) {b : ℝ}
    (hψ_decay : (fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a σ : ℝ} (ha : 0 < a) (hab : a < b) (hσlo : -a ≤ σ) (hσhi : σ ≤ 1 / 2) :
    Integrable (fun y : ℝ => exp ((σ : ℂ) * (y : ℂ)) * ψ y) := by
  let F : ℝ → ℂ := fun y => exp ((σ : ℂ) * (y : ℂ)) * ψ y
  have hF_cont : Continuous F := by
    dsimp [F]
    fun_prop
  have hF_loc : LocallyIntegrable F volume := hF_cont.locallyIntegrable
  have hshape : ∀ x : ℝ,
      ‖F x‖ = Real.exp ((σ - 1 / 2) * x) * ‖ψ x * exp ((x : ℂ) / 2)‖ := by
    intro x
    dsimp [F]
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
    have h1 : ((↑σ * ↑x) : ℂ).re = σ * x := by
      norm_num [Complex.mul_re]
    have h2 : ((x : ℂ) / 2).re = x / 2 := by
      norm_num
    rw [h1, h2]
    calc
      Real.exp (σ * x) * ‖ψ x‖
          = (Real.exp ((σ - 1 / 2) * x) * Real.exp (x / 2)) * ‖ψ x‖ := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
      _ = Real.exp ((σ - 1 / 2) * x) * (‖ψ x‖ * Real.exp (x / 2)) := by
            ring_nf
  have htop_decay := hψ_decay.mono (show Filter.atTop ≤ Filter.cocompact ℝ from
    atTop_le_cocompact)
  have hbot_decay := hψ_decay.mono (show Filter.atBot ≤ Filter.cocompact ℝ from
    atBot_le_cocompact)
  have htop : F =O[Filter.atTop] fun x : ℝ => Real.exp ((σ - 1 - b) * x) := by
    rw [Asymptotics.isBigO_iff] at htop_decay ⊢
    obtain ⟨C, hC⟩ := htop_decay
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_gt_atTop (0 : ℝ)] with x hxC hxpos
    rw [hshape]
    calc
      Real.exp ((σ - 1 / 2) * x) * ‖ψ x * exp ((x : ℂ) / 2)‖
          ≤ Real.exp ((σ - 1 / 2) * x) *
              (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
            exact mul_le_mul_of_nonneg_left hxC (Real.exp_nonneg _)
      _ = C * ‖Real.exp ((σ - 1 - b) * x)‖ := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
              abs_of_pos (Real.exp_pos _), abs_of_pos hxpos]
            calc
              Real.exp ((σ - 1 / 2) * x) * (C * Real.exp (-(1 / 2 + b) * x))
                  = C * (Real.exp ((σ - 1 / 2) * x) *
                      Real.exp (-(1 / 2 + b) * x)) := by ring_nf
              _ = C * Real.exp ((σ - 1 / 2) * x + (-(1 / 2 + b) * x)) := by
                    rw [Real.exp_add]
              _ = C * Real.exp ((σ - 1 - b) * x) := by ring_nf
  have hbot : F =O[Filter.atBot] fun x : ℝ => Real.exp ((σ + b) * x) := by
    rw [Asymptotics.isBigO_iff] at hbot_decay ⊢
    obtain ⟨C, hC⟩ := hbot_decay
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_lt_atBot (0 : ℝ)] with x hxC hxneg
    rw [hshape]
    calc
      Real.exp ((σ - 1 / 2) * x) * ‖ψ x * exp ((x : ℂ) / 2)‖
          ≤ Real.exp ((σ - 1 / 2) * x) *
              (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
            exact mul_le_mul_of_nonneg_left hxC (Real.exp_nonneg _)
      _ = C * ‖Real.exp ((σ + b) * x)‖ := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
              abs_of_pos (Real.exp_pos _), abs_of_neg hxneg]
            calc
              Real.exp ((σ - 1 / 2) * x) * (C * Real.exp (-(1 / 2 + b) * -x))
                  = C * (Real.exp ((σ - 1 / 2) * x) *
                      Real.exp (-(1 / 2 + b) * -x)) := by ring_nf
              _ = C * Real.exp ((σ - 1 / 2) * x + (-(1 / 2 + b) * -x)) := by
                    rw [Real.exp_add]
              _ = C * Real.exp ((σ + b) * x) := by ring_nf
  have htop_int : IntegrableAtFilter (fun x : ℝ => Real.exp ((σ - 1 - b) * x))
      Filter.atTop volume := by
    refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
    convert exp_neg_integrableOn_Ioi 0 (show 0 < 1 + b - σ by linarith) using 1
    ext x
    ring_nf
  have hbot_int : IntegrableAtFilter (fun x : ℝ => Real.exp ((σ + b) * x))
      Filter.atBot volume := by
    rw [← Filter.map_neg_atTop, measurableEmbedding_neg.integrableAtFilter_iff_comap]
    have hvol : (volume : Measure ℝ).comap Neg.neg = volume := by
      change (volume : Measure ℝ).comap (MeasurableEquiv.neg ℝ) = volume
      rw [← MeasurableEquiv.map_symm]
      simp
    rw [hvol, Function.comp_def]
    refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
    convert exp_neg_integrableOn_Ioi 0 (show 0 < σ + b by linarith) using 1
    ext x
    ring_nf
  exact hF_loc.integrable_of_isBigO_atBot_atTop hbot hbot_int htop htop_int

lemma kadiri_laplace_exp_abs_moment_integrable_of_continuous {ψ : ℝ → ℂ}
    (hψ : Continuous ψ) {b δ : ℝ} (hδb : δ < b)
    (hψ_decay : (fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    Integrable (fun y : ℝ => ‖(y : ℂ)‖ * ‖ψ y‖ * Real.exp (δ * |y|)) := by
  let F : ℝ → ℝ := fun y => ‖(y : ℂ)‖ * ‖ψ y‖ * Real.exp (δ * |y|)
  have hF_cont : Continuous F := by
    dsimp [F]
    fun_prop
  have hF_loc : LocallyIntegrable F volume := hF_cont.locallyIntegrable
  have hshape : ∀ x : ℝ,
      F x = ‖(x : ℂ)‖ * Real.exp (δ * |x| - x / 2) *
        ‖ψ x * exp ((x : ℂ) / 2)‖ := by
    intro x
    dsimp [F]
    rw [norm_mul, Complex.norm_exp]
    have hxre : ((x : ℂ) / 2).re = x / 2 := by norm_num
    rw [hxre]
    rw [mul_assoc, Real.exp_sub, div_eq_mul_inv, mul_assoc]
    field_simp [Real.exp_ne_zero]
  have htop_decay := hψ_decay.mono (show Filter.atTop ≤ Filter.cocompact ℝ from
    atTop_le_cocompact)
  have hbot_decay := hψ_decay.mono (show Filter.atBot ≤ Filter.cocompact ℝ from
    atBot_le_cocompact)
  have htop : F =O[Filter.atTop]
      fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(1 + b - δ) * x) := by
    rw [Asymptotics.isBigO_iff] at htop_decay ⊢
    obtain ⟨C, hC⟩ := htop_decay
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_gt_atTop (0 : ℝ)] with x hxC hxpos
    have hxnorm : ‖x‖ = x := by rw [Real.norm_eq_abs, abs_of_pos hxpos]
    rw [hshape, abs_of_pos hxpos, Complex.norm_real, hxnorm]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ x * Real.exp (δ * x - x / 2) * ‖ψ x * exp ((x : ℂ) / 2)‖)]
    calc
      x * Real.exp (δ * x - x / 2) * ‖ψ x * exp ((x : ℂ) / 2)‖
          ≤ x * Real.exp (δ * x - x / 2) *
              (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
            gcongr
      _ = C * ‖x ^ (1 : ℝ) * Real.exp (-(1 + b - δ) * x)‖ := by
            rw [abs_of_pos hxpos]
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            rw [Real.rpow_one, abs_of_pos (mul_pos hxpos (Real.exp_pos _))]
            calc
              x * Real.exp (δ * x - x / 2) *
                    (C * Real.exp (-(1 / 2 + b) * x))
                  = C * (x * (Real.exp (δ * x - x / 2) *
                    Real.exp (-(1 / 2 + b) * x))) := by ring
              _ = C * (x * Real.exp (-(1 + b - δ) * x)) := by
                    rw [← Real.exp_add]
                    ring_nf
  have hbot : F =O[Filter.atBot]
      fun x : ℝ => (-x) ^ (1 : ℝ) * Real.exp ((b - δ) * x) := by
    rw [Asymptotics.isBigO_iff] at hbot_decay ⊢
    obtain ⟨C, hC⟩ := hbot_decay
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_lt_atBot (0 : ℝ)] with x hxC hxneg
    have hnegpos : 0 < -x := by linarith
    have hxnorm : ‖x‖ = -x := by rw [Real.norm_eq_abs, abs_of_neg hxneg]
    rw [hshape, abs_of_neg hxneg, Complex.norm_real, hxnorm]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (-x) * Real.exp (δ * -x - x / 2) * ‖ψ x * exp ((x : ℂ) / 2)‖)]
    calc
      (-x) * Real.exp (δ * -x - x / 2) * ‖ψ x * exp ((x : ℂ) / 2)‖
          ≤ (-x) * Real.exp (δ * -x - x / 2) *
              (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
            gcongr
      _ = C * ‖(-x) ^ (1 : ℝ) * Real.exp ((b - δ) * x)‖ := by
            rw [abs_of_neg hxneg]
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            rw [Real.rpow_one, abs_of_pos (mul_pos hnegpos (Real.exp_pos _))]
            calc
              (-x) * Real.exp (δ * -x - x / 2) *
                    (C * Real.exp (-(1 / 2 + b) * -x))
                  = C * ((-x) * (Real.exp (δ * -x - x / 2) *
                    Real.exp (-(1 / 2 + b) * -x))) := by ring
              _ = C * ((-x) * Real.exp ((b - δ) * x)) := by
                    rw [← Real.exp_add]
                    ring_nf
  have htop_int : IntegrableAtFilter
      (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(1 + b - δ) * x)) Filter.atTop volume := by
    refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
    simpa [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := 1) (p := 1) (b := 1 + b - δ) (by norm_num) (by norm_num) (by linarith)
  have hbot_int : IntegrableAtFilter
      (fun x : ℝ => (-x) ^ (1 : ℝ) * Real.exp ((b - δ) * x)) Filter.atBot volume := by
    rw [← Filter.map_neg_atTop, measurableEmbedding_neg.integrableAtFilter_iff_comap]
    have hvol : (volume : Measure ℝ).comap Neg.neg = volume := by
      change (volume : Measure ℝ).comap (MeasurableEquiv.neg ℝ) = volume
      rw [← MeasurableEquiv.map_symm]
      simp
    rw [hvol, Function.comp_def]
    refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
    convert
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := 1) (p := 1) (b := b - δ) (by norm_num) (by norm_num) (by linarith)) using 1
    ext x
    rw [Real.rpow_one, Real.rpow_one]
    ring_nf
  exact hF_loc.integrable_of_isBigO_atBot_atTop hbot hbot_int htop htop_int

lemma kadiri_laplace_exp_abs_moment_integrable {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b δ : ℝ} (hδb : δ < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    Integrable (fun y : ℝ => ‖(y : ℂ)‖ * ‖φ y‖ * Real.exp (δ * |y|)) :=
  kadiri_laplace_exp_abs_moment_integrable_of_continuous hφ.continuous hδb hφ_decay

lemma kadiri_laplace_exp_hasDerivAt_zero {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    HasDerivAt
      (fun s : ℂ => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)
      (∫ y : ℝ, φ y * (y : ℂ) ∂volume) 0 := by
  let δ : ℝ := b / 2
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδb : δ < b := by dsimp [δ]; linarith
  let F : ℂ → ℝ → ℂ := fun s y => φ y * exp (s * (y : ℂ))
  let F' : ℂ → ℝ → ℂ := fun s y => φ y * ((y : ℂ) * exp (s * (y : ℂ)))
  let bound : ℝ → ℝ := fun y => ‖(y : ℂ)‖ * ‖φ y‖ * Real.exp (δ * |y|)
  have hF_meas : ∀ᶠ s in 𝓝 (0 : ℂ), AEStronglyMeasurable (F s) volume := by
    exact Eventually.of_forall fun s => by
      dsimp [F]
      exact (hφ.continuous.mul (continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  have hF_int : Integrable (F 0) volume := by
    have hbase : Integrable (fun y : ℝ => exp (((0 : ℝ) : ℂ) * (y : ℂ)) * φ y) :=
      kadiri_laplace_strip_weight_integrable_of_continuous
        (ψ := φ) hφ.continuous hφ_decay
        (a := b / 2) (σ := 0) (by positivity) (by linarith) (by linarith) (by norm_num)
    refine hbase.congr ?_
    filter_upwards with y
    dsimp [F]
    simp [mul_comm]
  have hF'_meas : AEStronglyMeasurable (F' 0) volume := by
    dsimp [F']
    exact (hφ.continuous.mul ((continuous_ofReal.mul (continuous_exp.comp (by fun_prop))))).aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂volume, ∀ s ∈ Metric.ball (0 : ℂ) δ, ‖F' s y‖ ≤ bound y := by
    filter_upwards with y s hs
    dsimp [F', bound]
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have hre : (s * (y : ℂ)).re = s.re * y := by norm_num [Complex.mul_re]
    rw [hre]
    have hmul_abs : s.re * y ≤ |s.re| * |y| := by
      calc
        s.re * y ≤ |s.re * y| := le_abs_self _
        _ = |s.re| * |y| := by rw [abs_mul]
    have hre_le : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
    have hnorm_lt : ‖s‖ < δ := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hs
    have hnorm_le : ‖s‖ ≤ δ := le_of_lt hnorm_lt
    have hle : s.re * y ≤ δ * |y| := by
      calc
        s.re * y ≤ |s.re| * |y| := hmul_abs
        _ ≤ ‖s‖ * |y| := mul_le_mul_of_nonneg_right hre_le (abs_nonneg y)
        _ ≤ δ * |y| := mul_le_mul_of_nonneg_right hnorm_le (abs_nonneg y)
    have hexp : Real.exp (s.re * y) ≤ Real.exp (δ * |y|) :=
      Real.exp_le_exp.mpr hle
    calc
      ‖φ y‖ * (‖(y : ℂ)‖ * Real.exp (s.re * y))
          ≤ ‖φ y‖ * (‖(y : ℂ)‖ * Real.exp (δ * |y|)) := by
            gcongr
      _ = ‖(y : ℂ)‖ * ‖φ y‖ * Real.exp (δ * |y|) := by ring
  have hbound_int : Integrable bound volume :=
    kadiri_laplace_exp_abs_moment_integrable hφ hδb hφ_decay
  have h_diff : ∀ᵐ y ∂volume, ∀ s ∈ Metric.ball (0 : ℂ) δ,
      HasDerivAt (fun w : ℂ => F w y) (F' s y) s := by
    filter_upwards with y s _hs
    dsimp [F, F']
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (((hasDerivAt_id s).mul_const (y : ℂ)).cexp.const_mul (φ y))
  have hderiv :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (x₀ := (0 : ℂ)) (s := Metric.ball (0 : ℂ) δ)
      (bound := bound) (μ := volume) (Metric.ball_mem_nhds (0 : ℂ) hδpos)
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  have hInt :
      (∫ y : ℝ, φ y * (y : ℂ) ∂volume) = ∫ y : ℝ, F' 0 y ∂volume := by
    apply integral_congr_ae
    filter_upwards with y
    dsimp [F']
    simp [Complex.exp_zero]
  rw [hInt]
  change HasDerivAt (fun s : ℂ => ∫ y : ℝ, F s y ∂volume)
    (∫ y : ℝ, F' 0 y ∂volume) 0
  exact hderiv

lemma kadiri_laplace_exp_zero_sub_div_isBigO_one {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    (fun s : ℂ =>
        ((∫ y : ℝ, φ y * exp ((0 : ℂ) * (y : ℂ)) ∂volume) -
          (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)) / s)
      =O[𝓝[≠] (0 : ℂ)] (fun _ : ℂ => (1 : ℂ)) := by
  let f : ℂ → ℂ := fun s => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume
  have hderiv := kadiri_laplace_exp_hasDerivAt_zero hφ hb hφ_decay
  have hslopeO : slope f 0 =O[𝓝[≠] (0 : ℂ)] (fun _ : ℂ => (1 : ℂ)) :=
    hderiv.tendsto_slope.isBigO_one ℂ
  refine hslopeO.neg_left.congr' ?_ .rfl
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  dsimp [f]
  simp [slope, div_eq_mul_inv, sub_eq_add_neg]
  ring

lemma kadiri_laplace_exp_integral_sub_div_isBigO_one {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    (fun s : ℂ =>
        ((∫ y : ℝ, φ y ∂volume) -
          (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)) / s)
      =O[𝓝[≠] (0 : ℂ)] (fun _ : ℂ => (1 : ℂ)) := by
  have hO := kadiri_laplace_exp_zero_sub_div_isBigO_one hφ hb hφ_decay
  have hzero :
      (∫ y : ℝ, φ y * exp ((0 : ℂ) * (y : ℂ)) ∂volume) =
        ∫ y : ℝ, φ y ∂volume := by
    apply integral_congr_ae
    filter_upwards with y
    simp
  refine hO.congr' ?_ .rfl
  filter_upwards with s
  rw [hzero]

lemma kadiri_laplace_exp_interval_moment_integrable_of_continuous {ψ : ℝ → ℂ}
    (hψ : Continuous ψ) {b lo hi : ℝ} (hlo : -b < lo) (hhi : hi < 1 + b)
    (hlohi : lo ≤ hi)
    (hψ_decay : (fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    Integrable (fun y : ℝ =>
      ‖(y : ℂ)‖ * ‖ψ y‖ * (Real.exp (lo * y) + Real.exp (hi * y))) := by
  let F : ℝ → ℝ := fun y =>
    ‖(y : ℂ)‖ * ‖ψ y‖ * (Real.exp (lo * y) + Real.exp (hi * y))
  have hF_cont : Continuous F := by
    dsimp [F]
    fun_prop
  have hF_loc : LocallyIntegrable F volume := hF_cont.locallyIntegrable
  have hshape : ∀ x : ℝ,
      F x =
        ‖(x : ℂ)‖ *
          (Real.exp ((lo - 1 / 2) * x) + Real.exp ((hi - 1 / 2) * x)) *
            ‖ψ x * exp ((x : ℂ) / 2)‖ := by
    intro x
    dsimp [F]
    have hxre : ((x : ℂ) / 2).re = x / 2 := by norm_num
    have hψexp : ‖ψ x * exp ((x : ℂ) / 2)‖ = ‖ψ x‖ * Real.exp (x / 2) := by
      rw [norm_mul, Complex.norm_exp, hxre]
    have hloexp :
        Real.exp ((lo - 1 / 2) * x) * Real.exp (x / 2) = Real.exp (lo * x) := by
      rw [← Real.exp_add]
      ring_nf
    have hhiexp :
        Real.exp ((hi - 1 / 2) * x) * Real.exp (x / 2) = Real.exp (hi * x) := by
      rw [← Real.exp_add]
      ring_nf
    rw [hψexp]
    rw [← hloexp, ← hhiexp]
    ring
  let topBound : ℝ → ℝ := fun x =>
    x * Real.exp (-(1 + b - lo) * x) +
      x * Real.exp (-(1 + b - hi) * x)
  let botBound : ℝ → ℝ := fun x =>
    (-x) * Real.exp ((b + lo) * x) +
      (-x) * Real.exp ((b + hi) * x)
  have htop_decay := hψ_decay.mono (show Filter.atTop ≤ Filter.cocompact ℝ from
    atTop_le_cocompact)
  have hbot_decay := hψ_decay.mono (show Filter.atBot ≤ Filter.cocompact ℝ from
    atBot_le_cocompact)
  have htop : F =O[Filter.atTop] topBound := by
    rw [Asymptotics.isBigO_iff] at htop_decay ⊢
    obtain ⟨C, hC⟩ := htop_decay
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_gt_atTop (0 : ℝ)] with x hxC hxpos
    have hxnorm : ‖(x : ℂ)‖ = x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
    have hdecay :
        ‖Real.exp (-(1 / 2 + b) * |x|)‖ = Real.exp (-(1 / 2 + b) * x) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos hxpos]
    rw [hshape, hxnorm]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (by positivity :
        0 ≤ x * (Real.exp ((lo - 1 / 2) * x) + Real.exp ((hi - 1 / 2) * x)) *
          ‖ψ x * exp ((x : ℂ) / 2)‖)]
    calc
      x * (Real.exp ((lo - 1 / 2) * x) + Real.exp ((hi - 1 / 2) * x)) *
          ‖ψ x * exp ((x : ℂ) / 2)‖
          ≤ x * (Real.exp ((lo - 1 / 2) * x) + Real.exp ((hi - 1 / 2) * x)) *
              (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
            gcongr
      _ = C * ‖topBound x‖ := by
            rw [hdecay]
            have hlo_prod :
                Real.exp ((lo - 1 / 2) * x) * Real.exp (-(1 / 2 + b) * x) =
                  Real.exp (-(1 + b - lo) * x) := by
              rw [← Real.exp_add]
              ring_nf
            have hhi_prod :
                Real.exp ((hi - 1 / 2) * x) * Real.exp (-(1 / 2 + b) * x) =
                  Real.exp (-(1 + b - hi) * x) := by
              rw [← Real.exp_add]
              ring_nf
            have htopNorm :
                ‖topBound x‖ =
                  x * Real.exp (-(1 + b - lo) * x) +
                    x * Real.exp (-(1 + b - hi) * x) := by
              dsimp [topBound]
              rw [abs_of_nonneg]
              · positivity
            rw [htopNorm]
            calc
              x * (Real.exp ((lo - 1 / 2) * x) + Real.exp ((hi - 1 / 2) * x)) *
                    (C * Real.exp (-(1 / 2 + b) * x))
                  = C * (x * (Real.exp ((lo - 1 / 2) * x) *
                        Real.exp (-(1 / 2 + b) * x)) +
                      x * (Real.exp ((hi - 1 / 2) * x) *
                        Real.exp (-(1 / 2 + b) * x))) := by ring
              _ = C * (x * Real.exp (-(1 + b - lo) * x) +
                    x * Real.exp (-(1 + b - hi) * x)) := by
                    rw [hlo_prod, hhi_prod]
  have hbot : F =O[Filter.atBot] botBound := by
    rw [Asymptotics.isBigO_iff] at hbot_decay ⊢
    obtain ⟨C, hC⟩ := hbot_decay
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_lt_atBot (0 : ℝ)] with x hxC hxneg
    have hnegpos : 0 < -x := by linarith
    have hxnorm : ‖(x : ℂ)‖ = -x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hxneg]
    have hdecay :
        ‖Real.exp (-(1 / 2 + b) * |x|)‖ =
          Real.exp (-(1 / 2 + b) * (-x)) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_neg hxneg]
    rw [hshape, hxnorm]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (by positivity :
        0 ≤ (-x) * (Real.exp ((lo - 1 / 2) * x) + Real.exp ((hi - 1 / 2) * x)) *
          ‖ψ x * exp ((x : ℂ) / 2)‖)]
    calc
      (-x) * (Real.exp ((lo - 1 / 2) * x) + Real.exp ((hi - 1 / 2) * x)) *
          ‖ψ x * exp ((x : ℂ) / 2)‖
          ≤ (-x) * (Real.exp ((lo - 1 / 2) * x) + Real.exp ((hi - 1 / 2) * x)) *
              (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
            gcongr
      _ = C * ‖botBound x‖ := by
            rw [hdecay]
            have hlo_prod :
                Real.exp ((lo - 1 / 2) * x) * Real.exp (-(1 / 2 + b) * (-x)) =
                  Real.exp ((b + lo) * x) := by
              rw [← Real.exp_add]
              ring_nf
            have hhi_prod :
                Real.exp ((hi - 1 / 2) * x) * Real.exp (-(1 / 2 + b) * (-x)) =
                  Real.exp ((b + hi) * x) := by
              rw [← Real.exp_add]
              ring_nf
            have hbotNorm :
                ‖botBound x‖ =
                  (-x) * Real.exp ((b + lo) * x) +
                    (-x) * Real.exp ((b + hi) * x) := by
              dsimp [botBound]
              rw [abs_of_nonneg]
              · positivity
            rw [hbotNorm]
            calc
              (-x) * (Real.exp ((lo - 1 / 2) * x) + Real.exp ((hi - 1 / 2) * x)) *
                    (C * Real.exp (-(1 / 2 + b) * (-x)))
                  = C * ((-x) * (Real.exp ((lo - 1 / 2) * x) *
                        Real.exp (-(1 / 2 + b) * (-x))) +
                      (-x) * (Real.exp ((hi - 1 / 2) * x) *
                        Real.exp (-(1 / 2 + b) * (-x)))) := by ring
              _ = C * ((-x) * Real.exp ((b + lo) * x) +
                    (-x) * Real.exp ((b + hi) * x)) := by
                    rw [hlo_prod, hhi_prod]
  have htop_int : IntegrableAtFilter topBound Filter.atTop volume := by
    have h1 : IntegrableAtFilter
        (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(1 + b - lo) * x))
        Filter.atTop volume := by
      refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
      simpa [Real.rpow_one] using
        integrableOn_rpow_mul_exp_neg_mul_rpow
          (s := 1) (p := 1) (b := 1 + b - lo) (by norm_num) (by norm_num)
          (by linarith)
    have h2 : IntegrableAtFilter
        (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(1 + b - hi) * x))
        Filter.atTop volume := by
      refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
      simpa [Real.rpow_one] using
        integrableOn_rpow_mul_exp_neg_mul_rpow
          (s := 1) (p := 1) (b := 1 + b - hi) (by norm_num) (by norm_num)
          (by linarith)
    convert h1.add h2 using 2 <;>
      first
      | rfl
      | (funext x; simp [topBound, Real.rpow_one, mul_comm])
  have hbot_int : IntegrableAtFilter botBound Filter.atBot volume := by
    rw [← Filter.map_neg_atTop, measurableEmbedding_neg.integrableAtFilter_iff_comap]
    have hvol : (volume : Measure ℝ).comap Neg.neg = volume := by
      change (volume : Measure ℝ).comap (MeasurableEquiv.neg ℝ) = volume
      rw [← MeasurableEquiv.map_symm]
      simp
    rw [hvol, Function.comp_def]
    have h1 : IntegrableAtFilter
        (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(b + lo) * x))
        Filter.atTop volume := by
      refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
      simpa [Real.rpow_one] using
        integrableOn_rpow_mul_exp_neg_mul_rpow
          (s := 1) (p := 1) (b := b + lo) (by norm_num) (by norm_num)
          (by linarith)
    have h2 : IntegrableAtFilter
        (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(b + hi) * x))
        Filter.atTop volume := by
      refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
      simpa [Real.rpow_one] using
        integrableOn_rpow_mul_exp_neg_mul_rpow
          (s := 1) (p := 1) (b := b + hi) (by norm_num) (by norm_num)
          (by linarith)
    convert h1.add h2 using 2 <;>
      first
      | rfl
      | (simp only [botBound, Pi.add_apply, Real.rpow_one, neg_neg];
          congr 1 <;> congr 1 <;> ring_nf)
  exact hF_loc.integrable_of_isBigO_atBot_atTop hbot hbot_int htop htop_int

lemma kadiri_laplace_exp_hasDerivAt_of_kadiri_strip {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b a : ℝ} (ha : 0 < a) (hab : a < b) {s0 : ℂ}
    (hs0lo : -a ≤ s0.re) (hs0hi : s0.re ≤ 1 / 2)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    HasDerivAt
      (fun s : ℂ => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)
      (∫ y : ℝ, φ y * ((y : ℂ) * exp (s0 * (y : ℂ))) ∂volume) s0 := by
  let lo : ℝ := -((a + b) / 2)
  let hi : ℝ := 1 / 2 + b / 2
  let ε : ℝ := min (s0.re - lo) (hi - s0.re) / 2
  have hb : 0 < b := lt_trans ha hab
  have hlo_lt_s0 : lo < s0.re := by
    dsimp [lo]
    linarith
  have hs0_lt_hi : s0.re < hi := by
    dsimp [hi]
    linarith
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact half_pos (lt_min (sub_pos.mpr hlo_lt_s0) (sub_pos.mpr hs0_lt_hi))
  have hlo_bound : -b < lo := by
    dsimp [lo]
    linarith
  have hhi_bound : hi < 1 + b := by
    dsimp [hi]
    linarith
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi]
    linarith
  let F : ℂ → ℝ → ℂ := fun s y => φ y * exp (s * (y : ℂ))
  let F' : ℂ → ℝ → ℂ := fun s y => φ y * ((y : ℂ) * exp (s * (y : ℂ)))
  let bound : ℝ → ℝ := fun y =>
    ‖(y : ℂ)‖ * ‖φ y‖ * (Real.exp (lo * y) + Real.exp (hi * y))
  have hball_re_bounds :
      ∀ s ∈ Metric.ball s0 ε, lo ≤ s.re ∧ s.re ≤ hi := by
    intro s hs
    have hre_diff : |s.re - s0.re| ≤ ‖s - s0‖ := by
      simpa [sub_re] using Complex.abs_re_le_norm (s - s0)
    have hnorm_lt : ‖s - s0‖ < ε := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hs
    have hε_le_left : ε ≤ s0.re - lo := by
      dsimp [ε]
      exact (half_le_self (by positivity)).trans (min_le_left _ _)
    have hε_le_right : ε ≤ hi - s0.re := by
      dsimp [ε]
      exact (half_le_self (by positivity)).trans (min_le_right _ _)
    have hdiff_le : |s.re - s0.re| ≤ ε := le_trans hre_diff (le_of_lt hnorm_lt)
    constructor
    · have hleft := (abs_le.mp hdiff_le).1
      linarith
    · have hright := (abs_le.mp hdiff_le).2
      linarith
  have hF_meas : ∀ᶠ s in 𝓝 s0, AEStronglyMeasurable (F s) volume := by
    exact Eventually.of_forall fun s => by
      dsimp [F]
      exact (hφ.continuous.mul (continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  have hF_int : Integrable (F s0) volume := by
    have hbase : Integrable (fun y : ℝ => exp (((s0.re : ℝ) : ℂ) * (y : ℂ)) * φ y) :=
      kadiri_laplace_strip_weight_integrable_of_continuous
        (ψ := φ) hφ.continuous hφ_decay
        (a := a) (σ := s0.re) ha hab hs0lo hs0hi
    refine hbase.congr' ?_ ?_
    · dsimp [F]
      exact (hφ.continuous.mul (continuous_exp.comp (by fun_prop))).aestronglyMeasurable
    · filter_upwards with y
      dsimp [F]
      rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
      have h1 : (s0 * (y : ℂ)).re = s0.re * y := by norm_num [Complex.mul_re]
      have h2 : ((((s0.re : ℝ) : ℂ) * (y : ℂ)) : ℂ).re = s0.re * y := by norm_num
      rw [h1, h2]
      ring
  have hF'_meas : AEStronglyMeasurable (F' s0) volume := by
    dsimp [F']
    exact (hφ.continuous.mul ((continuous_ofReal.mul (continuous_exp.comp (by fun_prop))))).aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂volume, ∀ s ∈ Metric.ball s0 ε, ‖F' s y‖ ≤ bound y := by
    filter_upwards with y s hs
    obtain ⟨hslo, hshi⟩ := hball_re_bounds s hs
    dsimp [F', bound]
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have hre : (s * (y : ℂ)).re = s.re * y := by norm_num [Complex.mul_re]
    rw [hre]
    have hexp_le : Real.exp (s.re * y) ≤ Real.exp (lo * y) + Real.exp (hi * y) := by
      by_cases hy : 0 ≤ y
      · have hmul : s.re * y ≤ hi * y := mul_le_mul_of_nonneg_right hshi hy
        exact (Real.exp_le_exp.mpr hmul).trans
          (le_add_of_nonneg_left (Real.exp_nonneg _))
      · have hy' : y ≤ 0 := le_of_not_ge hy
        have hmul : s.re * y ≤ lo * y := mul_le_mul_of_nonpos_right hslo hy'
        exact (Real.exp_le_exp.mpr hmul).trans
          (le_add_of_nonneg_right (Real.exp_nonneg _))
    calc
      ‖φ y‖ * (‖(y : ℂ)‖ * Real.exp (s.re * y))
          ≤ ‖φ y‖ * (‖(y : ℂ)‖ *
              (Real.exp (lo * y) + Real.exp (hi * y))) := by
            gcongr
      _ = ‖(y : ℂ)‖ * ‖φ y‖ *
          (Real.exp (lo * y) + Real.exp (hi * y)) := by ring
  have hbound_int : Integrable bound volume :=
    kadiri_laplace_exp_interval_moment_integrable_of_continuous
      hφ.continuous hlo_bound hhi_bound hlohi hφ_decay
  have h_diff : ∀ᵐ y ∂volume, ∀ s ∈ Metric.ball s0 ε,
      HasDerivAt (fun w : ℂ => F w y) (F' s y) s := by
    filter_upwards with y s _hs
    dsimp [F, F']
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (((hasDerivAt_id s).mul_const (y : ℂ)).cexp.const_mul (φ y))
  have hderiv :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (x₀ := s0) (s := Metric.ball s0 ε)
      (bound := bound) (μ := volume) (Metric.ball_mem_nhds s0 hεpos)
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  simpa [F, F'] using hderiv

lemma kadiri_laplace_exp_differentiableOn_kadiri_strip {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b a : ℝ} (ha : 0 < a) (hab : a < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    DifferentiableOn ℂ
      (fun s : ℂ => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)
      (Set.Icc (-a) (1 / 2 : ℝ) ×ℂ Set.univ) := by
  intro s hs
  have hsre := Complex.mem_reProdIm.mp hs |>.1
  exact DifferentiableAt.differentiableWithinAt
    ((kadiri_laplace_exp_hasDerivAt_of_kadiri_strip
      hφ ha hab hsre.1 hsre.2 hφ_decay).differentiableAt)

lemma kadiri_exp_mul_hasDerivAt (sigma x : ℝ) :
    HasDerivAt (fun y : ℝ => exp ((sigma : ℂ) * (y : ℂ)))
      ((sigma : ℂ) * exp ((sigma : ℂ) * (x : ℂ))) x := by
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    ((hasDerivAt_id x).ofReal_comp.const_mul (sigma : ℂ)).cexp

lemma kadiri_laplace_strip_weight_differentiable {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (sigma : ℝ) :
    Differentiable ℝ (fun z : ℝ => exp ((sigma : ℂ) * (z : ℂ)) * φ z) := by
  intro y
  exact (kadiri_exp_mul_hasDerivAt sigma y).differentiableAt.mul
    ((hφ.differentiable (by norm_num)) y)

lemma kadiri_laplace_strip_weight_deriv_integrable
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a σ : ℝ} (ha : 0 < a) (hab : a < b) (hσlo : -a ≤ σ) (hσhi : σ ≤ 1 / 2) :
    Integrable (deriv (fun z : ℝ => exp ((σ : ℂ) * (z : ℂ)) * φ z)) := by
  let F : ℝ → ℂ := fun y => exp ((σ : ℂ) * (y : ℂ)) * φ y
  let G : ℝ → ℂ := fun y => exp ((σ : ℂ) * (y : ℂ)) * deriv φ y
  have hF_int : Integrable F :=
    kadiri_laplace_strip_weight_integrable_of_continuous
      (ψ := φ) hφ.continuous hφ_decay ha hab hσlo hσhi
  have hG_int : Integrable G :=
    kadiri_laplace_strip_weight_integrable_of_continuous
      (ψ := deriv φ) (hφ.continuous_deriv (by norm_num)) hφ'_decay ha hab hσlo hσhi
  have hsum : Integrable (fun y : ℝ => (σ : ℂ) * F y + G y) :=
    (hF_int.const_mul (σ : ℂ)).add hG_int
  refine hsum.congr ?_
  filter_upwards with y
  dsimp [F, G]
  symm
  rw [deriv_fun_mul (kadiri_exp_mul_hasDerivAt σ y).differentiableAt
    ((hφ.differentiable (by norm_num)) y)]
  rw [HasDerivAt.deriv (kadiri_exp_mul_hasDerivAt σ y)]
  ring

lemma kadiri_laplace_strip_weight_norm_le_endpoints
    {ψ : ℝ → ℂ} {a σ x : ℝ} (hσlo : -a ≤ σ) (hσhi : σ ≤ 1 / 2) :
    ‖exp ((σ : ℂ) * (x : ℂ)) * ψ x‖ ≤
      ‖exp (((-a : ℝ) : ℂ) * (x : ℂ)) * ψ x‖ +
        ‖exp (((1 / 2 : ℝ) : ℂ) * (x : ℂ)) * ψ x‖ := by
  have hnorm (τ : ℝ) :
      ‖exp ((τ : ℂ) * (x : ℂ)) * ψ x‖ = Real.exp (τ * x) * ‖ψ x‖ := by
    rw [norm_mul, Complex.norm_exp]
    have hτ : ((τ : ℂ) * (x : ℂ)).re = τ * x := by
      norm_num [Complex.mul_re]
    rw [hτ]
  by_cases hx : 0 ≤ x
  · have hcoeff : Real.exp (σ * x) ≤ Real.exp ((1 / 2 : ℝ) * x) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hσhi hx)
    rw [hnorm σ, hnorm (-a), hnorm (1 / 2 : ℝ)]
    calc
      Real.exp (σ * x) * ‖ψ x‖
          ≤ Real.exp ((1 / 2 : ℝ) * x) * ‖ψ x‖ := by
            exact mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
      _ ≤ Real.exp ((-a) * x) * ‖ψ x‖ +
          Real.exp ((1 / 2 : ℝ) * x) * ‖ψ x‖ :=
            le_add_of_nonneg_left (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))
  · have hxle : x ≤ 0 := le_of_not_ge hx
    have hcoeff : Real.exp (σ * x) ≤ Real.exp ((-a) * x) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hσlo hxle)
    rw [hnorm σ, hnorm (-a), hnorm (1 / 2 : ℝ)]
    calc
      Real.exp (σ * x) * ‖ψ x‖
          ≤ Real.exp ((-a) * x) * ‖ψ x‖ := by
            exact mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
      _ ≤ Real.exp ((-a) * x) * ‖ψ x‖ +
          Real.exp ((1 / 2 : ℝ) * x) * ‖ψ x‖ :=
            le_add_of_nonneg_right (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))

lemma kadiri_laplace_strip_deriv_integral_bounded
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ σ : ℝ, -a ≤ σ → σ ≤ 1 / 2 →
      ∫ x, ‖deriv (fun z : ℝ => exp ((σ : ℂ) * (z : ℂ)) * φ z) x‖ ∂volume ≤ D := by
  let Lφ : ℝ → ℂ := fun x => exp (((-a : ℝ) : ℂ) * (x : ℂ)) * φ x
  let Rφ : ℝ → ℂ := fun x => exp (((1 / 2 : ℝ) : ℂ) * (x : ℂ)) * φ x
  let Lφ' : ℝ → ℂ := fun x => exp (((-a : ℝ) : ℂ) * (x : ℂ)) * deriv φ x
  let Rφ' : ℝ → ℂ := fun x => exp (((1 / 2 : ℝ) : ℂ) * (x : ℂ)) * deriv φ x
  let K : ℝ := max a (1 / 2)
  let M : ℝ → ℝ := fun x => K * (‖Lφ x‖ + ‖Rφ x‖) + (‖Lφ' x‖ + ‖Rφ' x‖)
  have hK_nonneg : 0 ≤ K := by
    exact ha.le.trans (le_max_left a (1 / 2))
  have hleft_le_half : -a ≤ (1 / 2 : ℝ) := by linarith
  have hLφ_int : Integrable Lφ :=
    kadiri_laplace_strip_weight_integrable_of_continuous
      (ψ := φ) hφ.continuous hφ_decay ha hab le_rfl hleft_le_half
  have hRφ_int : Integrable Rφ :=
    kadiri_laplace_strip_weight_integrable_of_continuous
      (ψ := φ) hφ.continuous hφ_decay ha hab hleft_le_half le_rfl
  have hLφ'_int : Integrable Lφ' :=
    kadiri_laplace_strip_weight_integrable_of_continuous
      (ψ := deriv φ) (hφ.continuous_deriv (by norm_num)) hφ'_decay ha hab
      le_rfl hleft_le_half
  have hRφ'_int : Integrable Rφ' :=
    kadiri_laplace_strip_weight_integrable_of_continuous
      (ψ := deriv φ) (hφ.continuous_deriv (by norm_num)) hφ'_decay ha hab
      hleft_le_half le_rfl
  have hM_int : Integrable M := by
    have hφsum : Integrable (fun x => ‖Lφ x‖ + ‖Rφ x‖) :=
      hLφ_int.norm.add hRφ_int.norm
    have hφ'sum : Integrable (fun x => ‖Lφ' x‖ + ‖Rφ' x‖) :=
      hLφ'_int.norm.add hRφ'_int.norm
    exact (hφsum.const_mul K).add hφ'sum
  have hM_nonneg : ∀ x, 0 ≤ M x := by
    intro x
    dsimp [M]
    exact add_nonneg
      (mul_nonneg hK_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)))
      (add_nonneg (norm_nonneg _) (norm_nonneg _))
  refine ⟨∫ x, M x ∂volume, integral_nonneg hM_nonneg, ?_⟩
  intro σ hσlo hσhi
  have hσnorm : ‖(σ : ℂ)‖ ≤ K := by
    rw [norm_real, Real.norm_eq_abs]
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hKa : a ≤ K := le_max_left a (1 / 2)
      linarith
    · have hKh : (1 / 2 : ℝ) ≤ K := le_max_right a (1 / 2)
      linarith
  have hderiv_int : Integrable (deriv (fun z : ℝ => exp ((σ : ℂ) * (z : ℂ)) * φ z)) :=
    kadiri_laplace_strip_weight_deriv_integrable
      (φ := φ) hφ hφ_decay hφ'_decay ha hab hσlo hσhi
  have hpoint : ∀ x,
      ‖deriv (fun z : ℝ => exp ((σ : ℂ) * (z : ℂ)) * φ z) x‖ ≤ M x := by
    intro x
    have hderiv :
        deriv (fun z : ℝ => exp ((σ : ℂ) * (z : ℂ)) * φ z) x =
          (σ : ℂ) * (exp ((σ : ℂ) * (x : ℂ)) * φ x) +
            exp ((σ : ℂ) * (x : ℂ)) * deriv φ x := by
      rw [deriv_fun_mul (kadiri_exp_mul_hasDerivAt σ x).differentiableAt
        ((hφ.differentiable (by norm_num)) x)]
      rw [HasDerivAt.deriv (kadiri_exp_mul_hasDerivAt σ x)]
      ring
    have hφ_end := kadiri_laplace_strip_weight_norm_le_endpoints
      (ψ := φ) (a := a) (σ := σ) (x := x) hσlo hσhi
    have hφ'_end := kadiri_laplace_strip_weight_norm_le_endpoints
      (ψ := deriv φ) (a := a) (σ := σ) (x := x) hσlo hσhi
    rw [hderiv]
    dsimp [M, Lφ, Rφ, Lφ', Rφ']
    calc
      ‖(σ : ℂ) * (exp ((σ : ℂ) * (x : ℂ)) * φ x) +
          exp ((σ : ℂ) * (x : ℂ)) * deriv φ x‖
          ≤ ‖(σ : ℂ) * (exp ((σ : ℂ) * (x : ℂ)) * φ x)‖ +
              ‖exp ((σ : ℂ) * (x : ℂ)) * deriv φ x‖ := norm_add_le _ _
      _ = ‖(σ : ℂ)‖ * ‖exp ((σ : ℂ) * (x : ℂ)) * φ x‖ +
              ‖exp ((σ : ℂ) * (x : ℂ)) * deriv φ x‖ := by rw [norm_mul]
      _ ≤ K *
              (‖exp (((-a : ℝ) : ℂ) * (x : ℂ)) * φ x‖ +
                ‖exp (((1 / 2 : ℝ) : ℂ) * (x : ℂ)) * φ x‖) +
            (‖exp (((-a : ℝ) : ℂ) * (x : ℂ)) * deriv φ x‖ +
              ‖exp (((1 / 2 : ℝ) : ℂ) * (x : ℂ)) * deriv φ x‖) := by
          have hfirst :
              ‖(σ : ℂ)‖ * ‖exp ((σ : ℂ) * (x : ℂ)) * φ x‖ ≤
                K *
                  (‖exp (((-a : ℝ) : ℂ) * (x : ℂ)) * φ x‖ +
                    ‖exp (((1 / 2 : ℝ) : ℂ) * (x : ℂ)) * φ x‖) := by
            exact mul_le_mul hσnorm hφ_end (norm_nonneg _) hK_nonneg
          exact add_le_add hfirst hφ'_end
  exact integral_mono hderiv_int.norm hM_int hpoint

end Kadiri
