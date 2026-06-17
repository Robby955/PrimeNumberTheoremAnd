import PrimeNumberTheoremAnd.IEANTN.CH2.CH2
import PrimeNumberTheoremAnd.IEANTN.KadiriHadamardPVBridge

/-!
# Downstream Kadiri Theorem 3.1 assembly

This file keeps the final Kadiri Theorem 3.1 assembly downstream of
`Kadiri.lean`, so it can import the axiom-clean horizontal and Hadamard/PV
wrappers without creating an import cycle.
-/

namespace Kadiri

open Complex Filter MeasureTheory
open Asymptotics
open ArithmeticFunction hiding log
open scoped Topology Interval

noncomputable section

theorem kadiri_laplace_full_strip_weight_integrable_of_continuous {ψ : ℝ → ℂ}
    (hψ : Continuous ψ) {b σ : ℝ}
    (hσlo : -b < σ) (hσhi : σ < 1 + b)
    (hψ_decay : (fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
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
      convert (MeasurableEquiv.neg ℝ).map_symm.symm using 1
      simp
    rw [hvol, Function.comp_def]
    refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
    convert exp_neg_integrableOn_Ioi 0 (show 0 < σ + b by linarith) using 1
    ext x
    ring_nf
  exact hF_loc.integrable_of_isBigO_atBot_atTop hbot hbot_int htop htop_int

theorem kadiri_laplace_full_strip_exp_interval_moment_integrable_of_continuous
    {ψ : ℝ → ℂ} (hψ : Continuous ψ) {b lo hi : ℝ}
    (hlo : -b < lo) (hhi : hi < 1 + b) (hlohi : lo ≤ hi)
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
    have hxnorm : ‖(x : ℂ)‖ = -x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hxneg]
    have hdecay :
        ‖Real.exp (-(1 / 2 + b) * |x|)‖ =
          Real.exp (-(1 / 2 + b) * (-x)) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_neg hxneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hsum_nonneg :
        0 ≤ Real.exp ((lo - 1 / 2) * x) + Real.exp ((hi - 1 / 2) * x) :=
      add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
    have hpref_nonneg :
        0 ≤ (-x) * (Real.exp ((lo - 1 / 2) * x) +
          Real.exp ((hi - 1 / 2) * x)) :=
      mul_nonneg hxneg_nonneg hsum_nonneg
    rw [hshape, hxnorm]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hpref_nonneg (norm_nonneg _))]
    calc
      (-x) * (Real.exp ((lo - 1 / 2) * x) + Real.exp ((hi - 1 / 2) * x)) *
          ‖ψ x * exp ((x : ℂ) / 2)‖
          ≤ (-x) * (Real.exp ((lo - 1 / 2) * x) + Real.exp ((hi - 1 / 2) * x)) *
              (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
            exact mul_le_mul_of_nonneg_left hxC hpref_nonneg
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
              · exact add_nonneg
                  (mul_nonneg hxneg_nonneg (Real.exp_nonneg _))
                  (mul_nonneg hxneg_nonneg (Real.exp_nonneg _))
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
    convert h1.add h2 using 1
    ext x
    simp [topBound, Real.rpow_one, mul_comm]
  have hbot_int : IntegrableAtFilter botBound Filter.atBot volume := by
    rw [← Filter.map_neg_atTop, measurableEmbedding_neg.integrableAtFilter_iff_comap]
    have hvol : (volume : Measure ℝ).comap Neg.neg = volume := by
      convert (MeasurableEquiv.neg ℝ).map_symm.symm using 1
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
    convert h1.add h2 using 1
    ext x
    simp [botBound, Real.rpow_one, mul_comm]
    ring_nf
  exact hF_loc.integrable_of_isBigO_atBot_atTop hbot hbot_int htop htop_int

theorem kadiri_laplace_exp_hasDerivAt_of_full_strip {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b : ℝ} {s0 : ℂ}
    (hs0lo : -b < s0.re) (hs0hi : s0.re < 1 + b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    HasDerivAt
      (fun s : ℂ => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)
      (∫ y : ℝ, φ y * ((y : ℂ) * exp (s0 * (y : ℂ))) ∂volume) s0 := by
  let lo : ℝ := (-b + s0.re) / 2
  let hi : ℝ := (s0.re + (1 + b)) / 2
  let ε : ℝ := min (s0.re - lo) (hi - s0.re) / 2
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
    linarith [hlo_lt_s0.le, hs0_lt_hi.le]
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
      kadiri_laplace_full_strip_weight_integrable_of_continuous
        (ψ := φ) hφ.continuous hs0lo hs0hi hφ_decay
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
    kadiri_laplace_full_strip_exp_interval_moment_integrable_of_continuous
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

theorem kadiri_laplace_exp_continuousAt_of_full_strip {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b : ℝ} {s0 : ℂ}
    (hs0lo : -b < s0.re) (hs0hi : s0.re < 1 + b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    ContinuousAt
      (fun s : ℂ => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume) s0 :=
  (kadiri_laplace_exp_hasDerivAt_of_full_strip hφ hs0lo hs0hi hφ_decay).differentiableAt.continuousAt

private theorem kadiri_laplace_full_strip_isOpen {b : ℝ} :
    IsOpen {s : ℂ | -b < s.re ∧ s.re < 1 + b} := by
  have hleft : IsOpen {s : ℂ | (-b : ℝ) < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hright : IsOpen {s : ℂ | s.re < 1 + b} :=
    isOpen_lt Complex.continuous_re continuous_const
  simpa [Set.setOf_and] using hleft.inter hright

theorem kadiri_laplace_exp_differentiableOn_full_strip {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    DifferentiableOn ℂ
      (fun s : ℂ => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)
      {s : ℂ | -b < s.re ∧ s.re < 1 + b} := by
  intro s hs
  exact DifferentiableAt.differentiableWithinAt
    ((kadiri_laplace_exp_hasDerivAt_of_full_strip hφ hs.1 hs.2 hφ_decay).differentiableAt)

theorem kadiri_laplace_exp_analyticAt_of_full_strip {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b : ℝ} {s0 : ℂ}
    (hs0lo : -b < s0.re) (hs0hi : s0.re < 1 + b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    AnalyticAt ℂ
      (fun s : ℂ => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume) s0 := by
  exact (kadiri_laplace_exp_differentiableOn_full_strip hφ hφ_decay).analyticAt
    (kadiri_laplace_full_strip_isOpen.mem_nhds ⟨hs0lo, hs0hi⟩)

theorem kadiri_laplace_exp_meromorphicOn_full_strip {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    MeromorphicOn
      (fun s : ℂ => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)
      {s : ℂ | -b < s.re ∧ s.re < 1 + b} := by
  exact
    ((kadiri_laplace_exp_differentiableOn_full_strip hφ hφ_decay).analyticOnNhd
      kadiri_laplace_full_strip_isOpen).meromorphicOn

theorem kadiri_rectangle_subset_full_laplace_strip {a b T : ℝ}
    (ha : 0 < a) (hab : a < b) (hT : 0 ≤ T) :
    Rectangle (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
        (((1 + a : ℝ) : ℂ) + (T : ℂ) * I) ⊆
      {s : ℂ | -b < s.re ∧ s.re < 1 + b} := by
  intro s hs
  have hre :
      (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).re ≤
        (((1 + a : ℝ) : ℂ) + (T : ℂ) * I).re := by
    simp
    linarith
  have him :
      (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).im ≤
        (((1 + a : ℝ) : ℂ) + (T : ℂ) * I).im := by
    simp
    linarith
  rcases (mem_Rect hre him s).1 hs with ⟨hsre_lo, hsre_hi, _hsim_lo, _hsim_hi⟩
  constructor
  · have hleft : -b < -a := by linarith
    exact hleft.trans_le (by simpa using hsre_lo)
  · have hright : (1 + a : ℝ) < 1 + b := by linarith
    have hsre_hi' : s.re ≤ (1 + a : ℝ) := by simpa using hsre_hi
    exact hsre_hi'.trans_lt hright

private lemma tendsto_mul_self_of_sub_principal_isBigO_one
    {f : ℂ → ℂ} {p c : ℂ}
    (h : (f - fun z : ℂ => c / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    Tendsto (fun z : ℂ => (z - p) * f z) (𝓝[≠] p) (𝓝 c) := by
  have hp_tendsto :
      Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 0) := by
    simpa using
      ((continuous_id.sub continuous_const).continuousAt.continuousWithinAt.tendsto :
        Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 (p - p)))
  have hp_small :
      (fun z : ℂ => z - p) =o[𝓝[≠] p] (1 : ℂ → ℂ) :=
    (isLittleO_one_iff ℂ).2 hp_tendsto
  have hrem_tendsto :
      Tendsto
        (fun z : ℂ => (z - p) * ((f - fun w : ℂ => c / (w - p)) z))
        (𝓝[≠] p) (𝓝 0) := by
    simpa using hp_small.mul_isBigO h
  have hprincipal_eventually :
      (fun z : ℂ => (z - p) * (c / (z - p))) =ᶠ[𝓝[≠] p]
        fun _ : ℂ => c := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    field_simp [sub_ne_zero.mpr hz]
  have hprincipal_tendsto :
      Tendsto (fun z : ℂ => (z - p) * (c / (z - p))) (𝓝[≠] p) (𝓝 c) :=
    tendsto_const_nhds.congr' hprincipal_eventually.symm
  have hsum_tendsto :
      Tendsto
        (fun z : ℂ =>
          (z - p) * (c / (z - p))
            + (z - p) * ((f - fun w : ℂ => c / (w - p)) z))
        (𝓝[≠] p) (𝓝 (c + 0)) :=
    hprincipal_tendsto.add hrem_tendsto
  have hcongr :
      (fun z : ℂ => (z - p) * f z) =ᶠ[𝓝[≠] p]
        fun z : ℂ =>
          (z - p) * (c / (z - p))
            + (z - p) * ((f - fun w : ℂ => c / (w - p)) z) := by
    filter_upwards with z
    simp [Pi.sub_apply]
    ring
  simpa using hsum_tendsto.congr' hcongr.symm

private lemma residue_eq_of_sub_principal_isBigO_one
    {f : ℂ → ℂ} {p c : ℂ}
    (h : (f - fun z : ℂ => c / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    CH2.residue f p = c :=
  CH2.residue_eq_of_tendsto (tendsto_mul_self_of_sub_principal_isBigO_one h)

private lemma residue_mul_eq_of_sub_principal_isBigO_one
    {f Ψ : ℂ → ℂ} {p c : ℂ}
    (h : (f - fun z : ℂ => c / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ))
    (hΨ : ContinuousAt Ψ p) :
    CH2.residue (fun z : ℂ => f z * Ψ z) p = c * Ψ p := by
  refine CH2.residue_eq_of_tendsto ?_
  have hf := tendsto_mul_self_of_sub_principal_isBigO_one h
  have hprod := hf.mul hΨ.continuousWithinAt.tendsto
  have hcongr :
      (fun z : ℂ => (z - p) * (f z * Ψ z)) =ᶠ[𝓝[≠] p]
        fun z : ℂ => ((z - p) * f z) * Ψ z := by
    filter_upwards with z
    ring
  simpa [mul_assoc] using hprod.congr' hcongr.symm

private lemma meromorphicOrderAt_nonneg_of_isBigO_one
    {f : ℂ → ℂ} {p : ℂ} (_hf : MeromorphicAt f p)
    (hO : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    0 ≤ meromorphicOrderAt f p := by
  by_contra hnonneg
  have hneg : meromorphicOrderAt f p < 0 := lt_of_not_ge hnonneg
  have hnorm :
      Tendsto (fun z : ℂ => ‖f z‖) (𝓝[≠] p) Filter.atTop := by
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg hneg
  exact (Filter.not_isBoundedUnder_of_tendsto_atTop hnorm) hO.isBoundedUnder_le

private lemma meromorphicOrderAt_eq_neg_one_of_sub_principal_isBigO_one
    {f : ℂ → ℂ} {p c : ℂ}
    (hf : MeromorphicAt f p) (hc : c ≠ 0)
    (h : (f - fun z : ℂ => c / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    meromorphicOrderAt f p = (-1 : ℤ) := by
  let principal : ℂ → ℂ := fun z => c / (z - p)
  let rem : ℂ → ℂ := f - principal
  have hconst_mero : MeromorphicAt (fun _ : ℂ => c) p := MeromorphicAt.const c p
  have hlin_mero : MeromorphicAt (fun z : ℂ => z - p) p := by fun_prop
  have hprincipal_mero : MeromorphicAt principal p := hconst_mero.div hlin_mero
  have hrem_mero : MeromorphicAt rem p := hf.sub hprincipal_mero
  have hrem_nonneg : 0 ≤ meromorphicOrderAt rem p :=
    meromorphicOrderAt_nonneg_of_isBigO_one hrem_mero (by simpa [rem, principal] using h)
  have hprincipal_order : meromorphicOrderAt principal p = (-1 : ℤ) := by
    dsimp [principal]
    change meromorphicOrderAt ((fun _ : ℂ => c) / fun z : ℂ => z - p) p = (-1 : ℤ)
    rw [meromorphicOrderAt_div hconst_mero hlin_mero, meromorphicOrderAt_const,
      if_neg hc, meromorphicOrderAt_id_sub_const]
    norm_num
  have hlt : meromorphicOrderAt principal p < meromorphicOrderAt rem p := by
    rw [hprincipal_order]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 (by norm_num : (-1 : ℤ) < 0)) hrem_nonneg
  have hsum_order :
      meromorphicOrderAt (principal + rem) p = meromorphicOrderAt principal p :=
    meromorphicOrderAt_add_eq_left_of_lt hrem_mero hlt
  have hcongr : f =ᶠ[𝓝[≠] p] principal + rem := by
    filter_upwards with z
    dsimp [principal, rem]
    ring
  calc
    meromorphicOrderAt f p = meromorphicOrderAt (principal + rem) p :=
      meromorphicOrderAt_congr hcongr
    _ = meromorphicOrderAt principal p := hsum_order
    _ = (-1 : ℤ) := hprincipal_order

/--
At a nontrivial zero `rho`, the negative logarithmic derivative has principal
part `-ord(rho)/(s-rho)` and bounded remainder on the punctured neighborhood.
-/
theorem kadiri_neg_zeta_logDeriv_principal_part_at_nontrivialZero
    (rho : NontrivialZeros) :
    ((fun s : ℂ => -deriv riemannZeta s / riemannZeta s)
        - fun s => -((riemannZeta.order (rho : ℂ) : ℂ)) / (s - (rho : ℂ)))
      =O[𝓝[≠] (rho : ℂ)] (1 : ℂ → ℂ) := by
  have h := (kadiri_logDeriv_zeta_hadamard_pv_remainder_bound rho).neg_left
  refine h.congr ?_ (fun _ => rfl)
  intro s
  simp [Pi.sub_apply, Pi.div_apply, neg_div]
  ring

/--
The residue of `-ζ'/ζ` at a nontrivial zero is the negative zero multiplicity.
This is the residue-identification atom needed by the rectangle bridge.
-/
theorem kadiri_neg_zeta_logDeriv_residue_at_nontrivialZero
    (rho : NontrivialZeros) :
    CH2.residue (fun s : ℂ => -deriv riemannZeta s / riemannZeta s) (rho : ℂ) =
      -((riemannZeta.order (rho : ℂ) : ℂ)) := by
  exact residue_eq_of_sub_principal_isBigO_one
    (kadiri_neg_zeta_logDeriv_principal_part_at_nontrivialZero rho)

/--
After multiplication by a continuous test factor, the nontrivial-zero residue is
the negative zero multiplicity times the test factor value.
-/
theorem kadiri_neg_zeta_logDeriv_mul_residue_at_nontrivialZero
    (rho : NontrivialZeros) {Ψ : ℂ → ℂ}
    (hΨ : ContinuousAt Ψ (rho : ℂ)) :
    CH2.residue (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * Ψ s)
        (rho : ℂ) =
      -((riemannZeta.order (rho : ℂ) : ℂ)) * Ψ (rho : ℂ) := by
  exact residue_mul_eq_of_sub_principal_isBigO_one
    (kadiri_neg_zeta_logDeriv_principal_part_at_nontrivialZero rho) hΨ

private lemma kadiri_neg_zeta_logDeriv_sub_one_principal_eventually :
    ((fun s : ℂ => -deriv riemannZeta s / riemannZeta s)
        - fun s => (1 : ℂ) / (s - 1))
      =ᶠ[𝓝[≠] (1 : ℂ)]
        fun s : ℂ => -logDeriv Complex.zetaTimesSMinusOne_entire s := by
  have hH_ne_nhds :
      ∀ᶠ z in 𝓝 (1 : ℂ), Complex.zetaTimesSMinusOne_entire z ≠ 0 := by
    exact
      (Complex.zetaTimesSMinusOne_entire_differentiable.analyticAt
        (1 : ℂ)).continuousAt.eventually_ne
        (by simp [Complex.zetaTimesSMinusOne_entire_one])
  have hH_ne :
      ∀ᶠ z in 𝓝[≠] (1 : ℂ), Complex.zetaTimesSMinusOne_entire z ≠ 0 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hH_ne_nhds
  filter_upwards [self_mem_nhdsWithin, hH_ne] with z hz hHne
  have hz1 : z ≠ (1 : ℂ) := by simpa using hz
  have hEq :
      (fun w : ℂ => Complex.zetaTimesSMinusOne_entire w / (w - 1))
        =ᶠ[𝓝 z] riemannZeta := by
    filter_upwards [eventually_ne_nhds hz1] with w hw
    have hH := Complex.zetaTimesSMinusOne_entire_eq_mul_riemannZeta hw
    rw [hH]
    field_simp [sub_ne_zero.mpr hw]
  have hderiv :
      deriv (fun w : ℂ => Complex.zetaTimesSMinusOne_entire w / (w - 1)) z =
        deriv riemannZeta z :=
    hEq.deriv_eq
  have hvalue :
      Complex.zetaTimesSMinusOne_entire z / (z - 1) = riemannZeta z :=
    hEq.eq_of_nhds
  have hden_ne : z - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hz1
  have hHdiff : DifferentiableAt ℂ Complex.zetaTimesSMinusOne_entire z :=
    Complex.zetaTimesSMinusOne_entire_differentiable z
  have hden_diff : DifferentiableAt ℂ (fun w : ℂ => w - 1) z := by fun_prop
  have hlog_den : logDeriv (fun w : ℂ => w - 1) z = 1 / (z - 1) := by
    rw [logDeriv_apply]
    have hderiv_den : deriv (fun w : ℂ => w - 1) z = 1 := by simp
    rw [hderiv_den]
  have hlog_div :=
    logDeriv_div (f := Complex.zetaTimesSMinusOne_entire)
      (g := fun w : ℂ => w - 1) z hHne hden_ne hHdiff hden_diff
  rw [hlog_den] at hlog_div
  have hlog_quot :
      deriv riemannZeta z / riemannZeta z =
        logDeriv Complex.zetaTimesSMinusOne_entire z - 1 / (z - 1) := by
    rw [← hvalue, ← hderiv]
    simpa [logDeriv_apply] using hlog_div
  simp only [one_div, Pi.sub_apply]
  rw [neg_div, hlog_quot]
  ring

private lemma kadiri_one_div_sub_one_meromorphicAt_one :
    MeromorphicAt (fun s : ℂ => (1 : ℂ) / (s - 1)) (1 : ℂ) := by
  have hnum : MeromorphicAt (fun _ : ℂ => (1 : ℂ)) (1 : ℂ) :=
    MeromorphicAt.const (1 : ℂ) (1 : ℂ)
  have hden : MeromorphicAt (fun s : ℂ => s - 1) (1 : ℂ) := by
    exact (show AnalyticAt ℂ (fun s : ℂ => s - 1) (1 : ℂ) from by fun_prop).meromorphicAt
  change MeromorphicAt ((fun _ : ℂ => (1 : ℂ)) / fun s : ℂ => s - 1) (1 : ℂ)
  exact hnum.div hden

private lemma kadiri_neg_logDeriv_zetaTimesSMinusOne_meromorphicAt_one :
    MeromorphicAt (fun s : ℂ => -logDeriv Complex.zetaTimesSMinusOne_entire s) (1 : ℂ) := by
  have hH_an :
      AnalyticAt ℂ Complex.zetaTimesSMinusOne_entire (1 : ℂ) :=
    Complex.zetaTimesSMinusOne_entire_differentiable.analyticAt (1 : ℂ)
  have hder : MeromorphicAt (deriv Complex.zetaTimesSMinusOne_entire) (1 : ℂ) :=
    hH_an.deriv.meromorphicAt
  have hden : MeromorphicAt Complex.zetaTimesSMinusOne_entire (1 : ℂ) :=
    hH_an.meromorphicAt
  have hquot :
      MeromorphicAt (deriv Complex.zetaTimesSMinusOne_entire /
        Complex.zetaTimesSMinusOne_entire) (1 : ℂ) :=
    hder.div hden
  change MeromorphicAt (-(deriv Complex.zetaTimesSMinusOne_entire /
    Complex.zetaTimesSMinusOne_entire)) (1 : ℂ)
  simpa [logDeriv_apply, Pi.div_apply] using hquot.neg

/--
The negative logarithmic derivative `-ζ'/ζ` is meromorphic at the zeta pole.
The value at the pole itself is irrelevant; the proof uses the punctured
identity with `(s - 1)ζ(s)`.
-/
theorem kadiri_neg_zeta_logDeriv_meromorphicAt_one :
    MeromorphicAt (fun s : ℂ => -deriv riemannZeta s / riemannZeta s) (1 : ℂ) := by
  have hsum :
      MeromorphicAt
        ((fun s : ℂ => (1 : ℂ) / (s - 1)) +
          fun s : ℂ => -logDeriv Complex.zetaTimesSMinusOne_entire s)
        (1 : ℂ) :=
    kadiri_one_div_sub_one_meromorphicAt_one.add
      kadiri_neg_logDeriv_zetaTimesSMinusOne_meromorphicAt_one
  refine hsum.congr ?_
  filter_upwards [kadiri_neg_zeta_logDeriv_sub_one_principal_eventually] with s hs
  dsimp [Pi.sub_apply] at hs ⊢
  rw [← hs]
  ring

/-- `-ζ'/ζ` is meromorphic at every complex point. -/
theorem kadiri_neg_zeta_logDeriv_meromorphicAt (s : ℂ) :
    MeromorphicAt (fun z : ℂ => -deriv riemannZeta z / riemannZeta z) s := by
  by_cases hs : s = 1
  · subst hs
    exact kadiri_neg_zeta_logDeriv_meromorphicAt_one
  · have han : AnalyticAt ℂ riemannZeta s :=
      riemannZeta_analyticOn_compl_one s (by simpa [Set.mem_compl_iff] using hs)
    have hquot : MeromorphicAt (deriv riemannZeta / riemannZeta) s :=
      han.deriv.meromorphicAt.div han.meromorphicAt
    refine hquot.neg.congr ?_
    filter_upwards with z
    dsimp [Pi.div_apply]
    rw [neg_div]

/-- `-ζ'/ζ` is meromorphic on every set. -/
theorem kadiri_neg_zeta_logDeriv_meromorphicOn (U : Set ℂ) :
    MeromorphicOn (fun z : ℂ => -deriv riemannZeta z / riemannZeta z) U := by
  intro z _hz
  exact kadiri_neg_zeta_logDeriv_meromorphicAt z

/--
Multiplying `-ζ'/ζ` by any meromorphic test factor preserves meromorphy on the
same set. This is the `hF_mero` input for the rectangle package.
-/
theorem kadiri_neg_zeta_logDeriv_mul_meromorphicOn {Ψ : ℂ → ℂ} {U : Set ℂ}
    (hΨ : MeromorphicOn Ψ U) :
    MeromorphicOn (fun z : ℂ => (-deriv riemannZeta z / riemannZeta z) * Ψ z) U := by
  exact (kadiri_neg_zeta_logDeriv_meromorphicOn U).mul hΨ

theorem kadiri_neg_zeta_logDeriv_meromorphicOrderAt_at_nontrivialZero
    (rho : NontrivialZeros) :
    meromorphicOrderAt (fun s : ℂ => -deriv riemannZeta s / riemannZeta s)
      (rho : ℂ) = (-1 : ℤ) := by
  have hcoeff : -((riemannZeta.order (rho : ℂ) : ℂ)) ≠ 0 := by
    have hpos : 0 < riemannZeta.order (rho : ℂ) :=
      riemannZeta_order_pos_nontrivialZero rho
    exact neg_ne_zero.mpr (by exact_mod_cast ne_of_gt hpos)
  exact meromorphicOrderAt_eq_neg_one_of_sub_principal_isBigO_one
    (kadiri_neg_zeta_logDeriv_meromorphicAt (rho : ℂ)) hcoeff
    (kadiri_neg_zeta_logDeriv_principal_part_at_nontrivialZero rho)

theorem kadiri_neg_zeta_logDeriv_meromorphicOrderAt_nonneg_of_zeta_ne_zero
    {s : ℂ} (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    0 ≤ meromorphicOrderAt
      (fun z : ℂ => -deriv riemannZeta z / riemannZeta z) s := by
  have han : AnalyticAt ℂ (fun z : ℂ => -deriv riemannZeta z / riemannZeta z) s := by
    have hζ : AnalyticAt ℂ riemannZeta s :=
      riemannZeta_analyticOn_compl_one s (by simpa [Set.mem_compl_iff] using hs1)
    exact hζ.deriv.neg.div hζ hz
  exact han.meromorphicOrderAt_nonneg

theorem kadiri_rectangle_neg_zeta_logDeriv_laplace_integrand_meromorphicOn
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) {a b T : ℝ}
    (ha : 0 < a) (hab : a < b) (hT : 0 ≤ T)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    MeromorphicOn
      (fun s : ℂ =>
        (-deriv riemannZeta s / riemannZeta s) *
          (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume))
      (Rectangle (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
        (((1 + a : ℝ) : ℂ) + (T : ℂ) * I)) := by
  exact kadiri_neg_zeta_logDeriv_mul_meromorphicOn
    ((kadiri_laplace_exp_meromorphicOn_full_strip hφ hφ_decay).mono_set
      (kadiri_rectangle_subset_full_laplace_strip ha hab hT))

/--
An off-pole height excludes zeta zeros on both horizontal rectangle sides.
The lower side is reduced to the upper side by conjugation symmetry.
-/
theorem riemannZeta_ne_zero_on_horizontal_border_of_offPole
    {T σ t : ℝ} (hT : kadiriHorizontalZetaOffPoleHeight T)
    (ht : t = T ∨ t = -T) :
    riemannZeta (((σ : ℂ) + (t : ℂ) * I)) ≠ 0 := by
  rcases ht with rfl | rfl
  · exact riemannZeta_ne_zero_on_horizontal_of_offPole hT
  · intro hzero
    have hconj_zero :
        riemannZeta ((starRingEnd ℂ) (((σ : ℂ) + ((-T : ℝ) : ℂ) * I))) = 0 := by
      rw [riemannZeta_conj, hzero]
      simp
    have htop_zero : riemannZeta (((σ : ℂ) + (T : ℂ) * I)) = 0 := by
      simpa using hconj_zero
    exact (riemannZeta_ne_zero_on_horizontal_of_offPole (T := T) (σ := σ) hT)
      htop_zero

/-- There are no real zeta zeros in `(-1, 0)`. -/
theorem kadiri_riemannZeta_neg_real_Ioo_ne_zero {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    riemannZeta (((-a : ℝ) : ℂ)) ≠ 0 := by
  let w : ℂ := ((1 + a : ℝ) : ℂ)
  have hw_zeta : riemannZeta w ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    simp [w]
    linarith
  have hw_neg_nat : ∀ n : ℕ, w ≠ -↑n := by
    intro n hn
    have hre : w.re = (-(n : ℂ)).re := congrArg Complex.re hn
    simp [w] at hre
    have hnnonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
    linarith
  have hw_ne_one : w ≠ 1 := by
    intro h
    have hre : w.re = (1 : ℂ).re := congrArg Complex.re h
    simp [w] at hre
    linarith
  have hpow : (2 * ↑Real.pi : ℂ) ^ (-w) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    left
    norm_num [Complex.ofReal_ne_zero, Real.pi_ne_zero]
  have hGamma : Complex.Gamma w ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp [w]
    linarith
  have hcos : Complex.cos (↑Real.pi * w / 2) ≠ 0 := by
    rw [Complex.cos_ne_zero_iff]
    intro k hk
    have hre : (↑Real.pi * w / 2).re =
        (((2 * (k : ℂ) + 1) * ↑Real.pi / 2).re) :=
      congrArg Complex.re hk
    have hmain : 1 + a = (2 * k + 1 : ℝ) := by
      have hscaled : Real.pi * (1 + a) / 2 =
          (2 * (k : ℝ) + 1) * Real.pi / 2 := by
        simpa [w, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hre
      nlinarith [Real.pi_pos]
    have haeq : a = (2 * k : ℝ) := by linarith
    cases le_or_gt k 0 with
    | inl hk_nonpos =>
        have hkreal : (2 * k : ℝ) ≤ 0 := by
          exact_mod_cast
            (mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℤ) ≤ 2) hk_nonpos)
        linarith
    | inr hk_pos =>
        have hk_one : (1 : ℤ) ≤ k := by omega
        have hkreal : (2 : ℝ) ≤ 2 * k := by
          exact_mod_cast (mul_le_mul_of_nonneg_left hk_one (by norm_num : (0 : ℤ) ≤ 2))
        linarith
  have hfactor : 2 * (2 * ↑Real.pi : ℂ) ^ (-w) * Complex.Gamma w *
      Complex.cos (↑Real.pi * w / 2) * riemannZeta w ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpow) hGamma) hcos)
      hw_zeta
  have hfe := riemannZeta_one_sub (s := w) hw_neg_nat hw_ne_one
  have hone : 1 - w = (((-a : ℝ) : ℂ)) := by
    dsimp [w]
    apply Complex.ext <;> simp
  rw [hone] at hfe
  rw [hfe]
  exact hfactor

theorem riemannZeta_ne_zero_of_neg_one_lt_re_nonpos
    {z : ℂ} (hgt : -1 < z.re) (hle : z.re ≤ 0) :
    riemannZeta z ≠ 0 := by
  by_cases him : z.im = 0
  · by_cases hre0 : z.re = 0
    · have hz0 : z = 0 := by
        apply Complex.ext <;> simp [hre0, him]
      rw [hz0, riemannZeta_zero]
      norm_num
    · have hlt : z.re < 0 := lt_of_le_of_ne hle hre0
      let a : ℝ := -z.re
      have ha : 0 < a := by dsimp [a]; linarith
      have ha1 : a < 1 := by dsimp [a]; linarith
      have hz : z = (((-a : ℝ) : ℂ)) := by
        apply Complex.ext <;> simp [a, him]
      rw [hz]
      exact kadiri_riemannZeta_neg_real_Ioo_ne_zero ha ha1
  · exact riemannZeta_ne_zero_of_re_nonpos_im_ne_zero hle him

/--
At the zeta pole `s = 1`, the negative logarithmic derivative has principal
part `1/(s-1)` and bounded remainder on the punctured neighborhood.
-/
theorem kadiri_neg_zeta_logDeriv_principal_part_at_one :
    ((fun s : ℂ => -deriv riemannZeta s / riemannZeta s)
        - fun s => (1 : ℂ) / (s - 1))
      =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  have hH_an :
      AnalyticAt ℂ Complex.zetaTimesSMinusOne_entire (1 : ℂ) :=
    Complex.zetaTimesSMinusOne_entire_differentiable.analyticAt (1 : ℂ)
  have hderiv_bounded :
      deriv Complex.zetaTimesSMinusOne_entire =O[𝓝 (1 : ℂ)] (1 : ℂ → ℂ) :=
    hH_an.deriv.continuousAt.norm.isBoundedUnder_le.isBigO_one ℂ
  have hH_ne : Complex.zetaTimesSMinusOne_entire (1 : ℂ) ≠ 0 := by
    simp [Complex.zetaTimesSMinusOne_entire_one]
  have hinv_bounded :
      (fun s : ℂ => (Complex.zetaTimesSMinusOne_entire s)⁻¹)
        =O[𝓝 (1 : ℂ)] (1 : ℂ → ℂ) :=
    (hH_an.continuousAt.inv₀ hH_ne).norm.isBoundedUnder_le.isBigO_one ℂ
  have hlog_bounded :
      logDeriv Complex.zetaTimesSMinusOne_entire
        =O[𝓝 (1 : ℂ)] (1 : ℂ → ℂ) := by
    have hmul_bounded_raw :=
      Asymptotics.IsBigO.mul hderiv_bounded hinv_bounded
    have hmul_bounded :
        (fun s : ℂ =>
          deriv Complex.zetaTimesSMinusOne_entire s *
            (Complex.zetaTimesSMinusOne_entire s)⁻¹)
          =O[𝓝 (1 : ℂ)] (1 : ℂ → ℂ) := by
      exact hmul_bounded_raw.congr (fun _ => rfl) (fun _ => by simp)
    simpa [logDeriv_apply, Pi.div_apply, div_eq_mul_inv]
      using hmul_bounded
  have hneg_bounded :
      (fun s : ℂ => -logDeriv Complex.zetaTimesSMinusOne_entire s)
        =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) :=
    (hlog_bounded.neg_left).mono nhdsWithin_le_nhds
  exact hneg_bounded.congr'
    kadiri_neg_zeta_logDeriv_sub_one_principal_eventually.symm
    (Filter.EventuallyEq.rfl)

/-- The residue of `-ζ'/ζ` at the zeta pole `s = 1` is `1`. -/
theorem kadiri_neg_zeta_logDeriv_residue_at_one :
    CH2.residue (fun s : ℂ => -deriv riemannZeta s / riemannZeta s) (1 : ℂ) = 1 := by
  exact residue_eq_of_sub_principal_isBigO_one
    kadiri_neg_zeta_logDeriv_principal_part_at_one

theorem kadiri_neg_zeta_logDeriv_meromorphicOrderAt_one :
    meromorphicOrderAt (fun s : ℂ => -deriv riemannZeta s / riemannZeta s)
      (1 : ℂ) = (-1 : ℤ) := by
  exact meromorphicOrderAt_eq_neg_one_of_sub_principal_isBigO_one
    kadiri_neg_zeta_logDeriv_meromorphicAt_one one_ne_zero
    kadiri_neg_zeta_logDeriv_principal_part_at_one

/--
Multiplying `-ζ'/ζ` by a meromorphic factor that has no pole cannot create
higher-order poles. Candidate pole points are the zeta pole, nontrivial zeros,
or ordinary nonzero zeta points.
-/
theorem kadiri_neg_zeta_logDeriv_mul_hasSimplePolesOn_of_nonnegative_order
    {Ψ : ℂ → ℂ} {U : Set ℂ}
    (hΨ_mero : ∀ z ∈ U, MeromorphicAt Ψ z)
    (hΨ_nonneg : ∀ z ∈ U, 0 ≤ meromorphicOrderAt Ψ z)
    (hpoles :
      ∀ z ∈ U, z = (1 : ℂ) ∨
        (∃ rho : NontrivialZeros, (rho : ℂ) = z) ∨ riemannZeta z ≠ 0) :
    CH2.HasSimplePolesOn
      (fun z : ℂ => (-deriv riemannZeta z / riemannZeta z) * Ψ z) U := by
  intro z hzU
  have hbase_mero : MeromorphicAt
      (fun z : ℂ => -deriv riemannZeta z / riemannZeta z) z :=
    kadiri_neg_zeta_logDeriv_meromorphicAt z
  have hΨz_mero : MeromorphicAt Ψ z := hΨ_mero z hzU
  have hΨz_nonneg : 0 ≤ meromorphicOrderAt Ψ z := hΨ_nonneg z hzU
  have hprod_order :
      meromorphicOrderAt
          (fun z : ℂ => (-deriv riemannZeta z / riemannZeta z) * Ψ z) z =
        meromorphicOrderAt (fun z : ℂ => -deriv riemannZeta z / riemannZeta z) z +
          meromorphicOrderAt Ψ z := by
    change meromorphicOrderAt
        ((fun z : ℂ => -deriv riemannZeta z / riemannZeta z) * Ψ) z =
      meromorphicOrderAt (fun z : ℂ => -deriv riemannZeta z / riemannZeta z) z +
        meromorphicOrderAt Ψ z
    exact meromorphicOrderAt_mul hbase_mero hΨz_mero
  rw [hprod_order]
  rcases hpoles z hzU with hz_one | hz_zero | hz_ne_zero
  · subst z
    rw [kadiri_neg_zeta_logDeriv_meromorphicOrderAt_one]
    exact le_add_of_nonneg_right hΨz_nonneg
  · rcases hz_zero with ⟨rho, hρz⟩
    subst z
    rw [kadiri_neg_zeta_logDeriv_meromorphicOrderAt_at_nontrivialZero]
    exact le_add_of_nonneg_right hΨz_nonneg
  · by_cases hz_one : z = (1 : ℂ)
    · subst z
      rw [kadiri_neg_zeta_logDeriv_meromorphicOrderAt_one]
      exact le_add_of_nonneg_right hΨz_nonneg
    · have hbase_nonneg :
          0 ≤ meromorphicOrderAt
            (fun z : ℂ => -deriv riemannZeta z / riemannZeta z) z :=
        kadiri_neg_zeta_logDeriv_meromorphicOrderAt_nonneg_of_zeta_ne_zero
          hz_one hz_ne_zero
      have hsum_nonneg :
          (0 : WithTop ℤ) ≤
            meromorphicOrderAt (fun z : ℂ => -deriv riemannZeta z / riemannZeta z) z +
              meromorphicOrderAt Ψ z :=
        add_nonneg hbase_nonneg hΨz_nonneg
      exact le_trans
        (WithTop.coe_le_coe.2 (by norm_num : (-1 : ℤ) ≤ 0))
        hsum_nonneg

/-- Analytic test factors satisfy the nonnegative-order hypothesis above. -/
theorem kadiri_neg_zeta_logDeriv_mul_hasSimplePolesOn_of_analyticAt
    {Ψ : ℂ → ℂ} {U : Set ℂ}
    (hΨ : ∀ z ∈ U, AnalyticAt ℂ Ψ z)
    (hpoles :
      ∀ z ∈ U, z = (1 : ℂ) ∨
        (∃ rho : NontrivialZeros, (rho : ℂ) = z) ∨ riemannZeta z ≠ 0) :
    CH2.HasSimplePolesOn
      (fun z : ℂ => (-deriv riemannZeta z / riemannZeta z) * Ψ z) U := by
  exact kadiri_neg_zeta_logDeriv_mul_hasSimplePolesOn_of_nonnegative_order
    (fun z hz => (hΨ z hz).meromorphicAt)
    (fun z hz => (hΨ z hz).meromorphicOrderAt_nonneg)
    hpoles

private lemma ofReal_add_mul_I_ne_one_of_im_ne_zero {σ t : ℝ} (ht : t ≠ 0) :
    ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  simp [ht] at him

theorem kadiri_neg_zeta_logDeriv_mul_meromorphicOrderAt_nonneg_of_zeta_ne_zero
    {Ψ : ℂ → ℂ} {s : ℂ}
    (hΨ_mero : MeromorphicAt Ψ s)
    (hΨ_nonneg : 0 ≤ meromorphicOrderAt Ψ s)
    (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    0 ≤ meromorphicOrderAt
      (fun z : ℂ => (-deriv riemannZeta z / riemannZeta z) * Ψ z) s := by
  have hbase_mero : MeromorphicAt
      (fun z : ℂ => -deriv riemannZeta z / riemannZeta z) s :=
    kadiri_neg_zeta_logDeriv_meromorphicAt s
  change 0 ≤ meromorphicOrderAt
    ((fun z : ℂ => -deriv riemannZeta z / riemannZeta z) * Ψ) s
  rw [meromorphicOrderAt_mul hbase_mero hΨ_mero]
  exact add_nonneg
    (kadiri_neg_zeta_logDeriv_meromorphicOrderAt_nonneg_of_zeta_ne_zero hs1 hz)
    hΨ_nonneg

/--
On an off-pole horizontal side of the Kadiri rectangle, the weighted zeta
logarithmic derivative has no pole when the test factor has no pole.
-/
theorem kadiri_neg_zeta_logDeriv_mul_meromorphicOrderAt_nonneg_on_horizontal_border_of_offPole
    {Ψ : ℂ → ℂ} {T σ t : ℝ}
    (hT : kadiriHorizontalZetaOffPoleHeight T) (ht : t = T ∨ t = -T)
    (hΨ_mero : MeromorphicAt Ψ ((σ : ℂ) + (t : ℂ) * I))
    (hΨ_nonneg : 0 ≤ meromorphicOrderAt Ψ ((σ : ℂ) + (t : ℂ) * I)) :
    0 ≤ meromorphicOrderAt
      (fun z : ℂ => (-deriv riemannZeta z / riemannZeta z) * Ψ z)
      ((σ : ℂ) + (t : ℂ) * I) := by
  have ht_ne_zero : t ≠ 0 := by
    rcases ht with rfl | rfl
    · exact hT.1
    · intro hneg
      exact hT.1 (neg_eq_zero.mp hneg)
  exact kadiri_neg_zeta_logDeriv_mul_meromorphicOrderAt_nonneg_of_zeta_ne_zero
    hΨ_mero hΨ_nonneg
    (ofReal_add_mul_I_ne_one_of_im_ne_zero ht_ne_zero)
    (riemannZeta_ne_zero_on_horizontal_border_of_offPole (T := T) (σ := σ) (t := t)
      hT ht)

theorem kadiri_rectangle_neg_zeta_logDeriv_mul_pole_candidate
    {Ψ : ℂ → ℂ} {a T : ℝ} {z : ℂ}
    (ha : 0 < a) (ha1 : a < 1) (hT : 0 ≤ T)
    (hzRect : z ∈ Rectangle (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
      (((1 + a : ℝ) : ℂ) + (T : ℂ) * I))
    (hΨ_mero : MeromorphicAt Ψ z)
    (hΨ_nonneg : 0 ≤ meromorphicOrderAt Ψ z)
    (hpole : meromorphicOrderAt
      (fun z : ℂ => (-deriv riemannZeta z / riemannZeta z) * Ψ z) z < 0) :
    z = (1 : ℂ) ∨
      ∃ rho : NontrivialZeros, (rho : ℂ) = z ∧ |(rho : ℂ).im| ≤ T := by
  by_cases hz_one : z = (1 : ℂ)
  · exact Or.inl hz_one
  · have hzeta_zero : riemannZeta z = 0 := by
      by_contra hzeta_ne
      exact not_lt_of_ge
        (kadiri_neg_zeta_logDeriv_mul_meromorphicOrderAt_nonneg_of_zeta_ne_zero
          hΨ_mero hΨ_nonneg hz_one hzeta_ne)
        hpole
    have hre :
        (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).re ≤
          (((1 + a : ℝ) : ℂ) + (T : ℂ) * I).re := by
      simp
      linarith
    have him :
        (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).im ≤
          (((1 + a : ℝ) : ℂ) + (T : ℂ) * I).im := by
      simp
      linarith
    rcases (mem_Rect hre him z).1 hzRect with ⟨hz_re_left, hz_re_right, hz_im_low, hz_im_high⟩
    have hz_re_gt_neg_one : -1 < z.re := by
      have hleft : -a ≤ z.re := by simpa using hz_re_left
      linarith
    by_cases hz_re_nonpos : z.re ≤ 0
    · exact False.elim
        ((riemannZeta_ne_zero_of_neg_one_lt_re_nonpos hz_re_gt_neg_one hz_re_nonpos)
          hzeta_zero)
    · have hz_re_pos : 0 < z.re := lt_of_not_ge hz_re_nonpos
      by_cases hz_re_one_le : 1 ≤ z.re
      · exact False.elim ((riemannZeta_ne_zero_of_one_le_re hz_re_one_le) hzeta_zero)
      · have hz_re_lt_one : z.re < 1 := lt_of_not_ge hz_re_one_le
        let rho : NontrivialZeros :=
          ⟨z, ⟨hz_re_pos, hz_re_lt_one⟩, Set.mem_univ _, by
            simpa [riemannZeta.zeroes] using hzeta_zero⟩
        refine Or.inr ⟨rho, rfl, ?_⟩
        have him_abs : |z.im| ≤ T := by
          exact abs_le.mpr ⟨by simpa using hz_im_low, by simpa using hz_im_high⟩
        simpa [rho] using him_abs

theorem nontrivialZeros_abs_im_le_finite (T : ℝ) :
    ({rho : NontrivialZeros | |(rho : ℂ).im| ≤ T} : Set NontrivialZeros).Finite := by
  refine Set.Finite.subset (nontrivialZeros_abs_im_lt_finite (T + 1)) ?_
  intro rho hrho
  exact lt_of_le_of_lt hrho (lt_add_one T)

theorem kadiri_one_union_nontrivialZeros_abs_im_le_finite (T : ℝ) :
    ({z : ℂ | z = (1 : ℂ) ∨
      ∃ rho : NontrivialZeros, (rho : ℂ) = z ∧ |(rho : ℂ).im| ≤ T}).Finite := by
  let Z : Set ℂ :=
    (fun rho : NontrivialZeros => (rho : ℂ)) ''
      ({rho : NontrivialZeros | |(rho : ℂ).im| ≤ T} : Set NontrivialZeros)
  have hZ : Z.Finite := (nontrivialZeros_abs_im_le_finite T).image
    (fun rho : NontrivialZeros => (rho : ℂ))
  have hset :
      {z : ℂ | z = (1 : ℂ) ∨
        ∃ rho : NontrivialZeros, (rho : ℂ) = z ∧ |(rho : ℂ).im| ≤ T} =
        ({1} : Set ℂ) ∪ Z := by
    ext z
    constructor
    · intro hz
      rcases hz with hz_one | ⟨rho, hρz, hρT⟩
      · exact Or.inl (by simpa using hz_one)
      · exact Or.inr ⟨rho, hρT, hρz⟩
    · intro hz
      rcases hz with hz_one | ⟨rho, hρT, hρz⟩
      · exact Or.inl (by simpa using hz_one)
      · exact Or.inr ⟨rho, hρz, hρT⟩
  rw [hset]
  exact (Set.finite_singleton (1 : ℂ)).union hZ

theorem kadiri_rectangle_neg_zeta_logDeriv_mul_poles_finite
    {Ψ : ℂ → ℂ} {a T : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hT : 0 ≤ T)
    (hΨ_mero : ∀ z ∈ Rectangle (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
      (((1 + a : ℝ) : ℂ) + (T : ℂ) * I), MeromorphicAt Ψ z)
    (hΨ_nonneg : ∀ z ∈ Rectangle (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
      (((1 + a : ℝ) : ℂ) + (T : ℂ) * I), 0 ≤ meromorphicOrderAt Ψ z) :
    (Rectangle (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
      (((1 + a : ℝ) : ℂ) + (T : ℂ) * I) ∩
        {z | meromorphicOrderAt
          (fun z : ℂ => (-deriv riemannZeta z / riemannZeta z) * Ψ z) z < 0}).Finite := by
  refine Set.Finite.subset
    (kadiri_one_union_nontrivialZeros_abs_im_le_finite T) ?_
  intro z hz
  rcases hz with ⟨hzRect, hpole⟩
  exact kadiri_rectangle_neg_zeta_logDeriv_mul_pole_candidate
    ha ha1 hT hzRect (hΨ_mero z hzRect) (hΨ_nonneg z hzRect) hpole

theorem kadiri_rectangle_zeta_zero_candidate
    {a T : ℝ} {z : ℂ}
    (ha : 0 < a) (ha1 : a < 1) (hT : 0 ≤ T)
    (hzRect : z ∈ Rectangle (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
      (((1 + a : ℝ) : ℂ) + (T : ℂ) * I))
    (hzeta_zero : riemannZeta z = 0) :
    ∃ rho : NontrivialZeros, (rho : ℂ) = z ∧ |(rho : ℂ).im| ≤ T := by
  have hre :
      (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).re ≤
        (((1 + a : ℝ) : ℂ) + (T : ℂ) * I).re := by
    simp
    linarith
  have him :
      (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).im ≤
        (((1 + a : ℝ) : ℂ) + (T : ℂ) * I).im := by
    simp
    linarith
  rcases (mem_Rect hre him z).1 hzRect with ⟨hz_re_left, _hz_re_right, hz_im_low, hz_im_high⟩
  have hz_re_gt_neg_one : -1 < z.re := by
    have hleft : -a ≤ z.re := by simpa using hz_re_left
    linarith
  by_cases hz_re_nonpos : z.re ≤ 0
  · exact False.elim
      ((riemannZeta_ne_zero_of_neg_one_lt_re_nonpos hz_re_gt_neg_one hz_re_nonpos)
        hzeta_zero)
  · have hz_re_pos : 0 < z.re := lt_of_not_ge hz_re_nonpos
    by_cases hz_re_one_le : 1 ≤ z.re
    · exact False.elim ((riemannZeta_ne_zero_of_one_le_re hz_re_one_le) hzeta_zero)
    · have hz_re_lt_one : z.re < 1 := lt_of_not_ge hz_re_one_le
      let rho : NontrivialZeros :=
        ⟨z, ⟨hz_re_pos, hz_re_lt_one⟩, Set.mem_univ _, by
          simpa [riemannZeta.zeroes] using hzeta_zero⟩
      refine ⟨rho, rfl, ?_⟩
      have him_abs : |z.im| ≤ T := by
        exact abs_le.mpr ⟨by simpa using hz_im_low, by simpa using hz_im_high⟩
      simpa [rho] using him_abs

theorem kadiri_rectangle_neg_zeta_logDeriv_laplace_integrand_hasSimplePolesOn
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) {a b T : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hab : a < b) (hT : 0 ≤ T)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    CH2.HasSimplePolesOn
      (fun s : ℂ =>
        (-deriv riemannZeta s / riemannZeta s) *
          (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume))
      (Rectangle (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
        (((1 + a : ℝ) : ℂ) + (T : ℂ) * I)) := by
  refine kadiri_neg_zeta_logDeriv_mul_hasSimplePolesOn_of_analyticAt ?_ ?_
  · intro z hzRect
    have hstrip := kadiri_rectangle_subset_full_laplace_strip ha hab hT hzRect
    exact kadiri_laplace_exp_analyticAt_of_full_strip hφ hstrip.1 hstrip.2 hφ_decay
  · intro z hzRect
    by_cases hzeta_zero : riemannZeta z = 0
    · rcases kadiri_rectangle_zeta_zero_candidate ha ha1 hT hzRect hzeta_zero with
        ⟨rho, hρz, _hρT⟩
      exact Or.inr (Or.inl ⟨rho, hρz⟩)
    · exact Or.inr (Or.inr hzeta_zero)

theorem kadiri_rectangle_neg_zeta_logDeriv_laplace_integrand_poles_finite
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) {a b T : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hab : a < b) (hT : 0 ≤ T)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    (Rectangle (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
      (((1 + a : ℝ) : ℂ) + (T : ℂ) * I) ∩
        {z | meromorphicOrderAt
          (fun s : ℂ =>
            (-deriv riemannZeta s / riemannZeta s) *
              (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)) z < 0}).Finite := by
  refine kadiri_rectangle_neg_zeta_logDeriv_mul_poles_finite ha ha1 hT ?_ ?_
  · intro z hzRect
    have hstrip := kadiri_rectangle_subset_full_laplace_strip ha hab hT hzRect
    exact (kadiri_laplace_exp_analyticAt_of_full_strip hφ hstrip.1 hstrip.2 hφ_decay).meromorphicAt
  · intro z hzRect
    have hstrip := kadiri_rectangle_subset_full_laplace_strip ha hab hT hzRect
    exact (kadiri_laplace_exp_analyticAt_of_full_strip hφ hstrip.1 hstrip.2 hφ_decay).meromorphicOrderAt_nonneg

theorem kadiri_zeroes_rect_Ioo_vertical_finite (T : ℝ) :
    (riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Ioo (-T) T)).Finite := by
  refine Set.Finite.subset
    ((nontrivialZeros_abs_im_le_finite T).image fun rho : NontrivialZeros => (rho : ℂ)) ?_
  intro z hz
  rcases hz with ⟨hre, him, hzeta⟩
  let rho : NontrivialZeros :=
    ⟨z, ⟨hre.1, hre.2⟩, Set.mem_univ _, by
      simpa [riemannZeta.zeroes] using hzeta⟩
  refine ⟨rho, ?_, rfl⟩
  exact abs_le.mpr ⟨le_of_lt him.1, le_of_lt him.2⟩

theorem kadiri_sumResiduesIn_eq_finset_of_finite {F : ℂ → ℂ} {S : Set ℂ}
    (hS : S.Finite) :
    CH2.sumResiduesIn F S = ∑ z ∈ hS.toFinset, CH2.residue F z := by
  let Sfin : Finset ℂ := hS.toFinset
  change CH2.sumResiduesIn F S = ∑ z ∈ Sfin, CH2.residue F z
  rw [CH2.sumResiduesIn]
  have hS_eq : S = (Sfin : Set ℂ) := hS.coe_toFinset.symm
  rw [hS_eq, tsum_fintype, ← Finset.sum_coe_sort Sfin]
  rfl

/--
After multiplication by a continuous test factor, the residue at the zeta pole
`s = 1` is the test factor value.
-/
theorem kadiri_neg_zeta_logDeriv_mul_residue_at_one {Ψ : ℂ → ℂ}
    (hΨ : ContinuousAt Ψ (1 : ℂ)) :
    CH2.residue (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * Ψ s)
        (1 : ℂ) =
      Ψ (1 : ℂ) := by
  simpa using
    (residue_mul_eq_of_sub_principal_isBigO_one
      kadiri_neg_zeta_logDeriv_principal_part_at_one hΨ)

theorem kadiri_laplace_candidate_residue_sum
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) {b T : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    CH2.sumResiduesIn
      (fun s : ℂ =>
        (-deriv riemannZeta s / riemannZeta s) *
          (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume))
      (insert (1 : ℂ) (riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Ioo (-T) T))) =
      (∫ y : ℝ, φ y * exp ((1 : ℂ) * (y : ℂ)) ∂volume) -
        riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Ioo (-T) T)
          (fun ρ : ℂ => ∫ y : ℝ, φ y * exp (ρ * (y : ℂ)) ∂volume) := by
  classical
  let Ψ : ℂ → ℂ := fun s : ℂ => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume
  let F : ℂ → ℂ := fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * Ψ s
  let Z : Set ℂ := riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Ioo (-T) T)
  let S : Set ℂ := insert (1 : ℂ) Z
  have hZfin : Z.Finite := by
    simpa [Z] using kadiri_zeroes_rect_Ioo_vertical_finite T
  have hSfin : S.Finite := hZfin.insert (1 : ℂ)
  have hS_toFinset : hSfin.toFinset = insert (1 : ℂ) hZfin.toFinset := by
    ext z
    simp [S, Z, hZfin.mem_toFinset]
  have h1_not_Z : (1 : ℂ) ∉ hZfin.toFinset := by
    rw [hZfin.mem_toFinset]
    intro h
    have hlt : (1 : ℂ).re < (1 : ℝ) := h.1.2
    norm_num at hlt
  have hΨ_one_cont : ContinuousAt Ψ (1 : ℂ) := by
    have hlow : -b < (1 : ℂ).re := by
      norm_num
      linarith
    have hhigh : (1 : ℂ).re < 1 + b := by
      norm_num
      linarith
    exact kadiri_laplace_exp_continuousAt_of_full_strip hφ hlow hhigh hφ_decay
  have hres_one : CH2.residue F (1 : ℂ) = Ψ (1 : ℂ) := by
    simpa [F] using
      (kadiri_neg_zeta_logDeriv_mul_residue_at_one (Ψ := Ψ) hΨ_one_cont)
  have hres_zero_sum :
      ∑ z ∈ hZfin.toFinset, CH2.residue F z =
        -∑ z ∈ hZfin.toFinset, Ψ z * (riemannZeta.order z : ℂ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro z hz
    have hzZ : z ∈ Z := hZfin.mem_toFinset.mp hz
    rcases hzZ with ⟨hre, _him, hzeta⟩
    let rho : NontrivialZeros :=
      ⟨z, ⟨hre.1, hre.2⟩, Set.mem_univ _, by
        simpa [riemannZeta.zeroes] using hzeta⟩
    have hΨ_cont : ContinuousAt Ψ z := by
      have hlow : -b < z.re := by linarith [hre.1, hb]
      have hhigh : z.re < 1 + b := by linarith [hre.2, hb]
      exact kadiri_laplace_exp_continuousAt_of_full_strip hφ hlow hhigh hφ_decay
    have hres := kadiri_neg_zeta_logDeriv_mul_residue_at_nontrivialZero
      (rho := rho) (Ψ := Ψ) (by simpa [rho] using hΨ_cont)
    calc
      CH2.residue F z = -((riemannZeta.order z : ℂ)) * Ψ z := by
        simpa [F, rho] using hres
      _ = -(Ψ z * (riemannZeta.order z : ℂ)) := by ring
  have hzeroes_sum :
      riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Ioo (-T) T) Ψ =
        ∑ z ∈ hZfin.toFinset, Ψ z * (riemannZeta.order z : ℂ) := by
    simpa [Ψ, Z] using
      (riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := .Ioo (0 : ℝ) 1) (J := .Ioo (-T) T) (f := Ψ) hZfin)
  calc
    CH2.sumResiduesIn
        (fun s : ℂ =>
          (-deriv riemannZeta s / riemannZeta s) *
            (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume))
        (insert (1 : ℂ) (riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Ioo (-T) T)))
        = CH2.sumResiduesIn F S := by rfl
    _ = ∑ z ∈ hSfin.toFinset, CH2.residue F z :=
        kadiri_sumResiduesIn_eq_finset_of_finite hSfin
    _ = CH2.residue F (1 : ℂ) + ∑ z ∈ hZfin.toFinset, CH2.residue F z := by
        rw [hS_toFinset, Finset.sum_insert h1_not_Z]
    _ = Ψ (1 : ℂ) - riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Ioo (-T) T) Ψ := by
        rw [hres_one, hres_zero_sum, hzeroes_sum]
        ring
    _ = (∫ y : ℝ, φ y * exp ((1 : ℂ) * (y : ℂ)) ∂volume) -
        riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Ioo (-T) T)
          (fun ρ : ℂ => ∫ y : ℝ, φ y * exp (ρ * (y : ℂ)) ∂volume) := by
        rfl

theorem kadiri_rectangle_neg_zeta_logDeriv_laplace_integrand_no_poles_boundary
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) {a b T : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hab : a < b) (hT_nonneg : 0 ≤ T)
    (hT_off : kadiriHorizontalZetaOffPoleHeight T)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    Disjoint
      (RectangleBorder (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
        (((1 + a : ℝ) : ℂ) + (T : ℂ) * I))
      {z | meromorphicOrderAt
        (fun s : ℂ =>
          (-deriv riemannZeta s / riemannZeta s) *
            (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)) z < 0} := by
  rw [Set.disjoint_left]
  intro z hzB hzPole
  simp only [Set.mem_setOf_eq] at hzPole
  let Ψ : ℂ → ℂ :=
    fun s : ℂ => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume
  have hzRect : z ∈ Rectangle (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
      (((1 + a : ℝ) : ℂ) + (T : ℂ) * I) :=
    rectangleBorder_subset_rectangle _ _ hzB
  have hstrip := kadiri_rectangle_subset_full_laplace_strip ha hab hT_nonneg hzRect
  have hΨ_an : AnalyticAt ℂ Ψ z :=
    kadiri_laplace_exp_analyticAt_of_full_strip hφ hstrip.1 hstrip.2 hφ_decay
  have hcandidate :
      z = (1 : ℂ) ∨
        ∃ rho : NontrivialZeros, (rho : ℂ) = z ∧ |(rho : ℂ).im| ≤ T := by
    exact kadiri_rectangle_neg_zeta_logDeriv_mul_pole_candidate
      (Ψ := Ψ) ha ha1 hT_nonneg hzRect hΨ_an.meromorphicAt
      hΨ_an.meromorphicOrderAt_nonneg (by simpa [Ψ] using hzPole)
  have hleft_right :
      (-a : ℝ) ≤ (1 + a : ℝ) := by linarith
  have hbot_top :
      (-T : ℝ) ≤ T := by linarith
  simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, add_zero, sub_zero, mul_one, zero_add,
    Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Set.uIcc_of_le hleft_right, Set.uIcc_of_le hbot_top] at hzB
  rcases hzB with (((⟨hz_re, hz_im⟩ | ⟨hz_re, hz_im⟩) | ⟨hz_re, hz_im⟩) |
    ⟨hz_re, hz_im⟩)
  · rcases hcandidate with hz_one | ⟨rho, hρz, _hρT⟩
    · subst z
      exact hT_off.1 (by simpa using hz_im)
    · have hzero : riemannZeta z = 0 := by
        rw [← hρz]
        exact rho.property.2.2
      have hnonzero :
          riemannZeta (((z.re : ℂ) + ((-T : ℝ) : ℂ) * I)) ≠ 0 :=
        riemannZeta_ne_zero_on_horizontal_border_of_offPole
          (T := T) (σ := z.re) (t := -T) hT_off (Or.inr rfl)
      have hz_eq : ((z.re : ℂ) + ((-T : ℝ) : ℂ) * I) = z := by
        apply Complex.ext <;> simp [hz_im]
      exact hnonzero (by rw [hz_eq]; exact hzero)
  · rcases hcandidate with hz_one | ⟨rho, hρz, _hρT⟩
    · subst z
      simp at hz_re
      linarith
    · have hzero : riemannZeta z = 0 := by
        rw [← hρz]
        exact rho.property.2.2
      have hzeta_ne : riemannZeta z ≠ 0 := by
        apply riemannZeta_ne_zero_of_neg_one_lt_re_nonpos
        · rw [hz_re]
          linarith
        · rw [hz_re]
          linarith
      exact hzeta_ne hzero
  · rcases hcandidate with hz_one | ⟨rho, hρz, _hρT⟩
    · subst z
      simp at hz_im
      exact hT_off.1 hz_im.symm
    · have hzero : riemannZeta z = 0 := by
        rw [← hρz]
        exact rho.property.2.2
      have hnonzero :
          riemannZeta (((z.re : ℂ) + (T : ℂ) * I)) ≠ 0 :=
        riemannZeta_ne_zero_on_horizontal_border_of_offPole
          (T := T) (σ := z.re) (t := T) hT_off (Or.inl rfl)
      have hz_eq : ((z.re : ℂ) + (T : ℂ) * I) = z := by
        apply Complex.ext <;> simp [hz_im]
      exact hnonzero (by simpa [hz_eq] using hzero)
  · rcases hcandidate with hz_one | ⟨rho, hρz, _hρT⟩
    · subst z
      simp at hz_re
      linarith
    · have hzero : riemannZeta z = 0 := by
        rw [← hρz]
        exact rho.property.2.2
      have hzeta_ne : riemannZeta z ≠ 0 := by
        apply riemannZeta_ne_zero_of_one_le_re
        rw [hz_re]
        linarith
      exact hzeta_ne hzero

theorem kadiri_rectangle_poleSet_residue_sum
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) {a b T : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hab : a < b) (hT_nonneg : 0 ≤ T)
    (hT_off : kadiriHorizontalZetaOffPoleHeight T)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    CH2.sumResiduesIn
      (fun s : ℂ =>
        (-deriv riemannZeta s / riemannZeta s) *
          (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume))
      (Rectangle (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
          (((1 + a : ℝ) : ℂ) + (T : ℂ) * I) ∩
        {z | meromorphicOrderAt
          (fun s : ℂ =>
            (-deriv riemannZeta s / riemannZeta s) *
              (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)) z < 0}) =
      (∫ y : ℝ, φ y * exp ((1 : ℂ) * (y : ℂ)) ∂volume) -
        riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Ioo (-T) T)
          (fun ρ : ℂ => ∫ y : ℝ, φ y * exp (ρ * (y : ℂ)) ∂volume) := by
  classical
  let Ψ : ℂ → ℂ := fun s : ℂ => ∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume
  let F : ℂ → ℂ := fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * Ψ s
  let R : Set ℂ := Rectangle (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
    (((1 + a : ℝ) : ℂ) + (T : ℂ) * I)
  let P : Set ℂ := {z | meromorphicOrderAt F z < 0}
  let Z : Set ℂ := riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Ioo (-T) T)
  let S : Set ℂ := insert (1 : ℂ) Z
  have hb : 0 < b := lt_trans ha hab
  have hRmero : MeromorphicOn F R := by
    simpa [F, Ψ, R] using
      (kadiri_rectangle_neg_zeta_logDeriv_laplace_integrand_meromorphicOn
        hφ ha hab hT_nonneg hφ_decay)
  have hS_subset_R : S ⊆ R := by
    intro z hz
    have hre_le :
        (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).re ≤
          (((1 + a : ℝ) : ℂ) + (T : ℂ) * I).re := by
      simp
      linarith
    have him_le :
        (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).im ≤
          (((1 + a : ℝ) : ℂ) + (T : ℂ) * I).im := by
      simp
      linarith
    change z ∈ Rectangle (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
      (((1 + a : ℝ) : ℂ) + (T : ℂ) * I)
    rw [mem_Rect hre_le him_le]
    rcases hz with hz_one | hzZ
    · subst z
      simp only [ofReal_neg, neg_mul, add_re, neg_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, neg_zero, add_zero, one_re, ofReal_add,
        ofReal_one, le_add_iff_nonneg_right, add_im, neg_im, mul_im, zero_add, one_im,
        Left.neg_nonpos_iff, and_self]
      exact ⟨by linarith, ha.le, hT_nonneg⟩
    · rcases hzZ with ⟨hre, him, _hzeta⟩
      simp only [ofReal_neg, neg_mul, add_re, neg_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, neg_zero, add_zero, ofReal_add, ofReal_one,
        one_re, add_im, neg_im, mul_im, zero_add, one_im]
      exact ⟨by linarith [hre.1], by linarith [hre.2], le_of_lt him.1,
        le_of_lt him.2⟩
  have hset_eq : R ∩ P = S ∩ P := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨hzR, hzP⟩
      have hstrip := kadiri_rectangle_subset_full_laplace_strip ha hab hT_nonneg hzR
      have hΨ_an : AnalyticAt ℂ Ψ z :=
        kadiri_laplace_exp_analyticAt_of_full_strip hφ hstrip.1 hstrip.2 hφ_decay
      have hcandidate :
          z = (1 : ℂ) ∨
            ∃ rho : NontrivialZeros, (rho : ℂ) = z ∧ |(rho : ℂ).im| ≤ T := by
        exact kadiri_rectangle_neg_zeta_logDeriv_mul_pole_candidate
          (Ψ := Ψ) ha ha1 hT_nonneg hzR hΨ_an.meromorphicAt
          hΨ_an.meromorphicOrderAt_nonneg (by simpa [F, P] using hzP)
      refine ⟨?_, hzP⟩
      rcases hcandidate with hz_one | ⟨rho, hρz, hρT⟩
      · exact Or.inl hz_one
      · have hzero : riemannZeta z = 0 := by
          rw [← hρz]
          exact rho.property.2.2
        have him_abs : |z.im| ≤ T := by
          simpa [hρz] using hρT
        have him_bounds := abs_le.mp him_abs
        have him_ne_top : z.im ≠ T := by
          intro htop
          have hnonzero :
              riemannZeta (((z.re : ℂ) + (T : ℂ) * I)) ≠ 0 :=
            riemannZeta_ne_zero_on_horizontal_border_of_offPole
              (T := T) (σ := z.re) (t := T) hT_off (Or.inl rfl)
          have hz_eq : ((z.re : ℂ) + (T : ℂ) * I) = z := by
            apply Complex.ext <;> simp [htop]
          exact hnonzero (by rw [hz_eq]; exact hzero)
        have him_ne_bot : z.im ≠ -T := by
          intro hbot
          have hnonzero :
              riemannZeta (((z.re : ℂ) + ((-T : ℝ) : ℂ) * I)) ≠ 0 :=
            riemannZeta_ne_zero_on_horizontal_border_of_offPole
              (T := T) (σ := z.re) (t := -T) hT_off (Or.inr rfl)
          have hz_eq : ((z.re : ℂ) + ((-T : ℝ) : ℂ) * I) = z := by
            apply Complex.ext <;> simp [hbot]
          exact hnonzero (by rw [hz_eq]; exact hzero)
        have hz_re : z.re ∈ Set.Ioo (0 : ℝ) 1 := by
          rw [← hρz]
          exact rho.property.1
        have hz_im : z.im ∈ Set.Ioo (-T) T := by
          exact ⟨lt_of_le_of_ne him_bounds.1 him_ne_bot.symm,
            lt_of_le_of_ne him_bounds.2 him_ne_top⟩
        have hz_zero : z ∈ riemannZeta.zeroes := by
          simpa [riemannZeta.zeroes] using hzero
        exact Or.inr ⟨hz_re, hz_im, hz_zero⟩
    · intro hz
      exact ⟨hS_subset_R hz.1, hz.2⟩
  have hresidue_reduce :
      CH2.sumResiduesIn F (R ∩ P) = CH2.sumResiduesIn F S := by
    refine CH2.sumResiduesIn_inter_eq_of_set_eq (F := F) (Rn := R) (S2 := S) (P := P)
      hset_eq ?_
    intro s hsS hs_not_pole
    have hs_not_pole' : ¬ meromorphicOrderAt F s < 0 := by
      simpa [P] using hs_not_pole
    exact CH2.residue_eq_zero_of_not_pole_of_meromorphicAt
      (hRmero s (hS_subset_R hsS)) (le_of_not_gt hs_not_pole')
  calc
    CH2.sumResiduesIn
        (fun s : ℂ =>
          (-deriv riemannZeta s / riemannZeta s) *
            (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume))
        (Rectangle (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
            (((1 + a : ℝ) : ℂ) + (T : ℂ) * I) ∩
          {z | meromorphicOrderAt
            (fun s : ℂ =>
              (-deriv riemannZeta s / riemannZeta s) *
                (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)) z < 0})
        = CH2.sumResiduesIn F (R ∩ P) := by rfl
    _ = CH2.sumResiduesIn F S := hresidue_reduce
    _ = (∫ y : ℝ, φ y * exp ((1 : ℂ) * (y : ℂ)) ∂volume) -
        riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Ioo (-T) T)
          (fun ρ : ℂ => ∫ y : ℝ, φ y * exp (ρ * (y : ℂ)) ∂volume) := by
        simpa [F, Ψ, S, Z] using
          (kadiri_laplace_candidate_residue_sum
            (φ := φ) hφ (b := b) (T := T) hb hφ_decay)

theorem kadiri_rectangleIntegral_laplace_eq_residue_sum_of_offPole
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) {a b T : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hab : a < b) (hT_nonneg : 0 ≤ T)
    (hT_off : kadiriHorizontalZetaOffPoleHeight T)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    RectangleIntegral'
      (fun s : ℂ =>
        (-deriv riemannZeta s / riemannZeta s) *
          (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume))
      (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
      (((1 + a : ℝ) : ℂ) + (T : ℂ) * I) =
      (∫ y : ℝ, φ y * exp ((1 : ℂ) * (y : ℂ)) ∂volume) -
        riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Ioo (-T) T)
          (fun ρ : ℂ => ∫ y : ℝ, φ y * exp (ρ * (y : ℂ)) ∂volume) := by
  have hre :
      (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).re ≤
        (((1 + a : ℝ) : ℂ) + (T : ℂ) * I).re := by
    simp
    linarith
  have him :
      (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I).im ≤
        (((1 + a : ℝ) : ℂ) + (T : ℂ) * I).im := by
    simp
    linarith
  calc
    RectangleIntegral'
        (fun s : ℂ =>
          (-deriv riemannZeta s / riemannZeta s) *
            (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume))
        (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
        (((1 + a : ℝ) : ℂ) + (T : ℂ) * I)
        = CH2.sumResiduesIn
          (fun s : ℂ =>
            (-deriv riemannZeta s / riemannZeta s) *
              (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume))
          (Rectangle (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
              (((1 + a : ℝ) : ℂ) + (T : ℂ) * I) ∩
            {z | meromorphicOrderAt
              (fun s : ℂ =>
                (-deriv riemannZeta s / riemannZeta s) *
                  (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume)) z < 0}) := by
            exact CH2.RectangleIntegral'_eq_sumResiduesIn hre him
              (kadiri_rectangle_neg_zeta_logDeriv_laplace_integrand_meromorphicOn
                hφ ha hab hT_nonneg hφ_decay)
              (kadiri_rectangle_neg_zeta_logDeriv_laplace_integrand_no_poles_boundary
                hφ ha ha1 hab hT_nonneg hT_off hφ_decay)
              (kadiri_rectangle_neg_zeta_logDeriv_laplace_integrand_poles_finite
                hφ ha ha1 hab hT_nonneg hφ_decay)
              (kadiri_rectangle_neg_zeta_logDeriv_laplace_integrand_hasSimplePolesOn
                hφ ha ha1 hab hT_nonneg hφ_decay)
    _ = (∫ y : ℝ, φ y * exp ((1 : ℂ) * (y : ℂ)) ∂volume) -
        riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Ioo (-T) T)
          (fun ρ : ℂ => ∫ y : ℝ, φ y * exp (ρ * (y : ℂ)) ∂volume) :=
        kadiri_rectangle_poleSet_residue_sum
          hφ ha ha1 hab hT_nonneg hT_off hφ_decay

theorem kadiri_rectangleIntegral_laplace_eq_line_terms
    (φ : ℝ → ℂ) {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    RectangleIntegral'
      (fun s : ℂ =>
        (-deriv riemannZeta s / riemannZeta s) *
          (∫ y : ℝ, φ y * exp (s * (y : ℂ)) ∂volume))
      (((-a : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
      (((1 + a : ℝ) : ℂ) + (T : ℂ) * I) =
      kadiri_thm_3_1_q1_I φ a T
      - (1 / (2 * (Real.pi : ℂ))) *
        (∫ t in Set.Ioo (-T) T,
          (-deriv riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I) /
              riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I)) *
            Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I)))
      - (1 / (2 * (Real.pi : ℂ) * I)) *
        (∫ σ in Set.Ioo (-a) (1 + a),
          (-deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
              riemannZeta ((σ : ℂ) + (T : ℂ) * I)) *
            Φ (-((σ : ℂ) + (T : ℂ) * I)))
      + (1 / (2 * (Real.pi : ℂ) * I)) *
        (∫ σ in Set.Ioo (-a) (1 + a),
          (-deriv riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) /
              riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) *
            Φ (-((σ : ℂ) + ((-T : ℝ) : ℂ) * I))) := by
  have ha_le : -a ≤ 1 + a := by linarith
  have hT_le : -T ≤ T := by linarith
  rw [kadiri_thm_3_1_q1_I]
  dsimp [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral]
  simp only [ofReal_neg, neg_mul, neg_re, ofReal_re, mul_re, I_re, mul_zero,
    ofReal_im, I_im, mul_one, sub_self, neg_zero, add_zero, ofReal_add, ofReal_one,
    neg_im, mul_im, zero_add]
  rw [intervalIntegral.integral_of_le ha_le]
  rw [intervalIntegral.integral_of_le ha_le]
  rw [intervalIntegral.integral_of_le hT_le]
  rw [intervalIntegral.integral_of_le hT_le]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  field_simp [Complex.I_ne_zero]
  ring

private lemma kadiri_eq12_algebra {main left top bottom residue rect : ℂ}
    (hline : rect = main - left - top + bottom) (hrect : rect = residue) :
    main = left + top - bottom + residue := by
  rw [← hrect, hline]
  ring

theorem kadiri_thm_3_1_q1_eq_12_of_offPole {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    {T : ℝ} (hT : 0 < T) (hT_off : kadiriHorizontalZetaOffPoleHeight T) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    kadiri_thm_3_1_q1_I φ a T =
      (1 / (2 * (Real.pi : ℂ))) *
        (∫ t in Set.Ioo (-T) T,
          (-deriv riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I) /
              riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I)) *
            Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I)))
      + (1 / (2 * (Real.pi : ℂ) * I)) *
        (∫ σ in Set.Ioo (-a) (1 + a),
          (-deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
              riemannZeta ((σ : ℂ) + (T : ℂ) * I)) *
            Φ (-((σ : ℂ) + (T : ℂ) * I)))
      - (1 / (2 * (Real.pi : ℂ) * I)) *
        (∫ σ in Set.Ioo (-a) (1 + a),
          (-deriv riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) /
              riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) *
            Φ (-((σ : ℂ) + ((-T : ℝ) : ℂ) * I)))
      + Φ (-1)
      - riemannZeta.zeroes_sum (.Ioo 0 1) (.Ioo (-T) T) (fun ρ ↦ Φ (-ρ)) := by
  have hrect :=
    kadiri_rectangleIntegral_laplace_eq_residue_sum_of_offPole
      hφ ha ha1 hab hT.le hT_off hφ_decay
  have hline :=
    kadiri_rectangleIntegral_laplace_eq_line_terms φ ha hT.le
  simpa only [neg_neg, one_mul, sub_eq_add_neg, add_assoc] using
    (kadiri_eq12_algebra (hline := hline) (hrect := hrect))

theorem eventually_kadiri_thm_3_1_q1_eq_12_on_dyadicGoodHeight
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) :
    ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter
        zeroImagDyadicCumulativeCountBoundSource_of_local_window,
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      kadiri_thm_3_1_q1_I φ a T =
        (1 / (2 * (Real.pi : ℂ))) *
          (∫ t in Set.Ioo (-T) T,
            (-deriv riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I) /
                riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I)) *
              Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I)))
        + (1 / (2 * (Real.pi : ℂ) * I)) *
          (∫ σ in Set.Ioo (-a) (1 + a),
            (-deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
                riemannZeta ((σ : ℂ) + (T : ℂ) * I)) *
              Φ (-((σ : ℂ) + (T : ℂ) * I)))
        - (1 / (2 * (Real.pi : ℂ) * I)) *
          (∫ σ in Set.Ioo (-a) (1 + a),
            (-deriv riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) /
                riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) *
              Φ (-((σ : ℂ) + ((-T : ℝ) : ℂ) * I)))
        + Φ (-1)
        - riemannZeta.zeroes_sum (.Ioo 0 1) (.Ioo (-T) T) (fun ρ ↦ Φ (-ρ)) := by
  let hsrc : zeroImagDyadicCumulativeCountBoundSource :=
    zeroImagDyadicCumulativeCountBoundSource_of_local_window
  filter_upwards [eventually_kadiriDyadicGoodHeightFilter_scale hsrc,
    eventually_kadiriDyadicGoodHeightFilter_offPole hsrc] with T hscale hT_off
  obtain ⟨k, _hT_eq, hT_mem⟩ := hscale
  have hpow_pos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
  have hT_pos : 0 < T := lt_trans hpow_pos hT_mem.1
  exact kadiri_thm_3_1_q1_eq_12_of_offPole
    hφ hb hφ_decay hφ'_decay ha hab ha1 hT_pos hT_off

private theorem tendsto_tsum_subtype_of_eventually_mem
    {α : Type*} (f : α → ℂ) (p : ℝ → α → Prop)
    (hs : Summable f)
    (hp : ∀ a : α, ∀ᶠ T : ℝ in atTop, p T a) :
    Tendsto (fun T : ℝ => ∑' a : {a : α // p T a}, f a.1)
      atTop (𝓝 (∑' a, f a)) := by
  classical
  have hif : Tendsto (fun T : ℝ =>
      ∑' a : α, ({a : α | p T a}.indicator f) a)
      atTop (𝓝 (∑' a, f a)) := by
    refine tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun T a => ({a : α | p T a}.indicator f) a)
      (g := f)
      (bound := fun a => ‖f a‖) ?_ ?_ ?_
    · exact hs.norm
    · intro a
      exact tendsto_nhds_of_eventually_eq ((hp a).mono fun T hT => by
        exact Set.indicator_of_mem hT f)
    · filter_upwards with T a
      by_cases h : p T a
      · rw [Set.indicator_of_mem (show a ∈ {a : α | p T a} from h)]
      · rw [Set.indicator_of_notMem (show a ∉ {a : α | p T a} from h)]
        simp
  refine Filter.Tendsto.congr' ?_ hif
  filter_upwards with T
  rw [← tsum_subtype]
  rfl

private def kadiriVerticalZeroesAllEquiv (T : ℝ) :
    {ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.univ : Set ℝ) //
        (ρ : ℂ).im ∈ Set.Ioo (-T) T} ≃
      riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Ioo (-T) T) where
  toFun ρ := by
    refine ⟨(ρ.1 : ℂ), ?_⟩
    rcases ρ.1.property with ⟨hre, _him, hzeta⟩
    exact ⟨hre, ρ.2, hzeta⟩
  invFun ρ := by
    refine ⟨⟨(ρ : ℂ), ?_⟩, ?_⟩
    · rcases ρ.property with ⟨hre, him, hzeta⟩
      exact ⟨hre, Set.mem_univ _, hzeta⟩
    · exact ρ.property.2.1
  left_inv := by
    intro ρ
    cases ρ
    rfl
  right_inv := by
    intro ρ
    cases ρ
    rfl

theorem tendsto_kadiri_zeroes_sum_Ioo_vertical_atTop
    {φ : ℝ → ℂ}
    (hΦ_sum : Summable
      (fun ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.univ : Set ℝ) =>
        (∫ y, φ y * exp ((ρ : ℂ) * (y : ℂ)) ∂volume) *
          (riemannZeta.order (ρ : ℂ) : ℂ))) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Tendsto
      (fun T : ℝ =>
        riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Ioo (-T) T) (fun ρ ↦ Φ (-ρ)))
      atTop
      (𝓝 (riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.univ : Set ℝ)
        (fun ρ ↦ Φ (-ρ)))) := by
  classical
  dsimp
  let All := riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.univ : Set ℝ)
  let F : All → ℂ := fun ρ =>
    (∫ y, φ y * exp ((ρ : ℂ) * (y : ℂ)) ∂volume) *
      (riemannZeta.order (ρ : ℂ) : ℂ)
  let p : ℝ → All → Prop := fun T ρ => (ρ : ℂ).im ∈ Set.Ioo (-T) T
  have hF : Summable F := by
    simpa [F, All] using hΦ_sum
  have hp : ∀ ρ : All, ∀ᶠ T : ℝ in atTop, p T ρ := by
    intro ρ
    filter_upwards [Filter.eventually_gt_atTop (|((ρ : ℂ).im)| + 1)] with T hT
    have h_abs_lt : |(ρ : ℂ).im| < T := by linarith
    exact abs_lt.mp h_abs_lt
  have hsub := tendsto_tsum_subtype_of_eventually_mem F p hF hp
  have hfinite_eq : ∀ T : ℝ,
      riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Ioo (-T) T)
          (fun ρ => (∫ y, φ y * exp (-(-ρ) * (y : ℂ)) ∂volume)) =
        ∑' ρ : {ρ : All // p T ρ}, F ρ.1 := by
    intro T
    unfold riemannZeta.zeroes_sum
    calc
      (∑' ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Ioo (-T) T),
          (∫ y, φ y * exp (-(-((ρ : ℂ))) * (y : ℂ)) ∂volume) *
            (riemannZeta.order (ρ : ℂ) : ℂ))
          = ∑' ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Ioo (-T) T),
              (∫ y, φ y * exp ((ρ : ℂ) * (y : ℂ)) ∂volume) *
                (riemannZeta.order (ρ : ℂ) : ℂ) := by
              apply tsum_congr
              intro ρ
              simp
      _ = ∑' ρ : {ρ : All // p T ρ}, F ρ.1 := by
              rw [← Equiv.tsum_eq (kadiriVerticalZeroesAllEquiv T)]
              rfl
  have hfull_eq :
      riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.univ : Set ℝ)
          (fun ρ => (∫ y, φ y * exp (-(-ρ) * (y : ℂ)) ∂volume)) =
        ∑' ρ : All, F ρ := by
    unfold riemannZeta.zeroes_sum
    apply tsum_congr
    intro ρ
    simp [F, All]
  rw [hfull_eq]
  refine Filter.Tendsto.congr' ?_ hsub
  filter_upwards with T
  exact (hfinite_eq T).symm

theorem lim_I_from_pieces_explicit_on_dyadicGoodHeight
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (hΦ_sum : Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
      (∫ y, φ y * exp (ρ.val * (y : ℂ)) ∂volume) *
        (riemannZeta.order ρ.val : ℂ)))
    (hΓ_int : MeasureTheory.Integrable (fun t : ℝ ↦
      ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
        ∫ y, φ y * exp ((1 / 2 + (t : ℂ) * I) * (y : ℂ)) ∂volume)) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I φ a T)
      (kadiriDyadicGoodHeightFilter zeroImagDyadicCumulativeCountBoundSource_of_local_window)
      (nhds
        (φ 0 * ((-Real.log Real.pi : ℝ) : ℂ)
        + (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))
        + ((∫ y : ℝ, φ y)
          + (1 / (2 * (Real.pi : ℂ))) *
              ∫ t : ℝ,
                ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                  ∫ y, φ y * exp ((1 / 2 + (t : ℂ) * I) * (y : ℂ)) ∂volume)
        + (∫ y : ℝ, φ y * exp ((y : ℂ)) ∂volume)
        - riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
            (fun ρ ↦ ∫ y, φ y * exp (ρ * (y : ℂ)) ∂volume))) := by
  classical
  let L : Filter ℝ :=
    kadiriDyadicGoodHeightFilter zeroImagDyadicCumulativeCountBoundSource_of_local_window
  let left : ℝ → ℂ := fun T =>
    (1 / (2 * (Real.pi : ℂ))) *
      (∫ t in Set.Ioo (-T) T,
        (-deriv riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I) /
            riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I)) *
          (∫ y, φ y * exp ((((-a : ℝ) : ℂ) + (t : ℂ) * I) * (y : ℂ)) ∂volume))
  let top : ℝ → ℂ := fun T =>
    (1 / (2 * (Real.pi : ℂ) * I)) *
      (∫ σ in Set.Ioo (-a) (1 + a),
        (-deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (T : ℂ) * I)) *
          (∫ y, φ y * exp (((σ : ℂ) + (T : ℂ) * I) * (y : ℂ)) ∂volume))
  let bot : ℝ → ℂ := fun T =>
    (1 / (2 * (Real.pi : ℂ) * I)) *
      (∫ σ in Set.Ioo (-a) (1 + a),
        (-deriv riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) /
            riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) *
          (∫ y, φ y * exp (((σ : ℂ) + ((-T : ℝ) : ℂ) * I) * (y : ℂ)) ∂volume))
  let zsum : ℝ → ℂ := fun T =>
    riemannZeta.zeroes_sum (.Ioo 0 1) (.Ioo (-T) T)
      (fun ρ ↦ ∫ y, φ y * exp (ρ * (y : ℂ)) ∂volume)
  let zfull : ℂ :=
    riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
      (fun ρ ↦ ∫ y, φ y * exp (ρ * (y : ℂ)) ∂volume)
  let pole : ℂ := ∫ y : ℝ, φ y * exp ((y : ℂ)) ∂volume
  let l1 : ℂ := φ 0 * ((-Real.log Real.pi : ℝ) : ℂ)
  let l2 : ℂ := -∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n)
  let l3 : ℂ := (∫ y : ℝ, φ y)
    + (1 / (2 * (Real.pi : ℂ))) *
        ∫ t : ℝ,
          ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
            ∫ y, φ y * exp ((1 / 2 + (t : ℂ) * I) * (y : ℂ)) ∂volume
  have hle : L ≤ Filter.atTop := by
    simpa [L] using
      (kadiriDyadicGoodHeightFilter_le_atTop
        zeroImagDyadicCumulativeCountBoundSource_of_local_window)
  have hI_eq :
      (fun T : ℝ => kadiri_thm_3_1_q1_I φ a T)
        =ᶠ[L]
      (fun T : ℝ => left T + top T - bot T + pole - zsum T) := by
    simpa [L, left, top, bot, pole, zsum, sub_eq_add_neg, add_assoc] using
      (eventually_kadiri_thm_3_1_q1_eq_12_on_dyadicGoodHeight
        (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay
        (a := a) ha hab ha1)
  have h13L : Filter.Tendsto (fun T : ℝ => kadiri_thm_3_1_q1_I_1 φ a T)
      L (nhds l1) := by
    simpa [L, l1] using
      (kadiri_thm_3_1_q1_eq_13 hφ hb hφ_decay hφ'_decay ha hab ha1).mono_left hle
  have h14L : Filter.Tendsto (fun T : ℝ => kadiri_thm_3_1_q1_I_2 φ a T)
      L (nhds l2) := by
    simpa [L, l2] using
      (kadiri_thm_3_1_q1_eq_14 hφ hb hφ_decay hφ'_decay ha hab ha1).mono_left hle
  have h15L : Filter.Tendsto (fun T : ℝ => kadiri_thm_3_1_q1_I_3 φ a T)
      L (nhds l3) := by
    simpa [L, l3] using
      (kadiri_thm_3_1_q1_eq_15 hφ hb hφ_decay hφ'_decay ha hab ha1 hΓ_int).mono_left hle
  have hleft : Filter.Tendsto left L (nhds (l1 + l2 + l3)) := by
    have hpieces := (h13L.add h14L).add h15L
    refine Filter.Tendsto.congr' ?_ hpieces
    filter_upwards with T
    have hs := kadiri_thm_3_1_q1_shifted_eq_I123
      (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay
      (a := a) ha hab ha1 T
    simpa [left, add_assoc] using hs.symm
  have htop : Filter.Tendsto top L (nhds 0) := by
    simpa [L, top] using
      (kadiri_thm_3_1_q1_top_horizontal_vanishes_on_dyadicGoodHeight_unconditional
        (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay
        (a := a) ha hab ha1)
  have hbot : Filter.Tendsto bot L (nhds 0) := by
    simpa [L, bot] using
      (kadiri_thm_3_1_q1_bot_horizontal_vanishes_on_dyadicGoodHeight_unconditional
        (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay
        (a := a) ha hab ha1)
  have hzsum : Filter.Tendsto zsum L (nhds zfull) := by
    simpa [L, zsum, zfull] using
      (tendsto_kadiri_zeroes_sum_Ioo_vertical_atTop (φ := φ) hΦ_sum).mono_left hle
  have hrect : Filter.Tendsto
      (fun T : ℝ => left T + top T - bot T + pole - zsum T) L
      (nhds (l1 + l2 + l3 + pole - zfull)) := by
    have hbase : Filter.Tendsto (fun T : ℝ => left T + top T - bot T) L
        (nhds (l1 + l2 + l3)) := by
      simpa using (hleft.add htop).sub hbot
    simpa [sub_eq_add_neg, add_assoc] using (hbase.add_const pole).sub hzsum
  refine Filter.Tendsto.congr' ?_ hrect
  exact hI_eq.symm

theorem kadiriDyadicGoodHeightFilter_neBot
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    (kadiriDyadicGoodHeightFilter hsrc).NeBot := by
  rw [kadiriDyadicGoodHeightFilter]
  infer_instance

theorem kadiri_thm_3_1_q1_explicit_on_dyadicGoodHeight
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hΦ_sum : Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
      (∫ y, φ y * exp (ρ.val * (y : ℂ)) ∂volume) *
        (riemannZeta.order ρ.val : ℂ)))
    (hΓ_int : MeasureTheory.Integrable (fun t : ℝ ↦
      ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
        ∫ y, φ y * exp ((1 / 2 + (t : ℂ) * I) * (y : ℂ)) ∂volume)) :
    (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n)) =
      (φ 0 * ((-Real.log Real.pi : ℝ) : ℂ)
      + (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))
      + ((∫ y : ℝ, φ y)
        + (1 / (2 * (Real.pi : ℂ))) *
            ∫ t : ℝ,
              ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                ∫ y, φ y * exp ((1 / 2 + (t : ℂ) * I) * (y : ℂ)) ∂volume)
      + (∫ y : ℝ, φ y * exp ((y : ℂ)) ∂volume)
      - riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
          (fun ρ ↦ ∫ y, φ y * exp (ρ * (y : ℂ)) ∂volume)) := by
  classical
  let hsrc : zeroImagDyadicCumulativeCountBoundSource :=
    zeroImagDyadicCumulativeCountBoundSource_of_local_window
  let L : Filter ℝ := kadiriDyadicGoodHeightFilter hsrc
  haveI : L.NeBot := by
    simpa [L, hsrc] using kadiriDyadicGoodHeightFilter_neBot hsrc
  have hbmin1 : 0 < min b 1 := lt_min hb one_pos
  set a : ℝ := min b 1 / 2 with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; linarith
  have ha_lt_b : a < b := by
    rw [ha_def]
    have h : min b 1 ≤ b := min_le_left b 1
    linarith
  have ha_lt_1 : a < 1 := by
    rw [ha_def]
    have h : min b 1 ≤ 1 := min_le_right b 1
    linarith
  have hle : L ≤ Filter.atTop := by
    simpa [L, hsrc] using kadiriDyadicGoodHeightFilter_le_atTop hsrc
  have hinv : ∀ n : ℕ, 1 ≤ n →
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop (𝓝 (φ (Real.log n))) := by
    intro n hn
    exact kadiri_thm_3_1_q1_laplace_inversion_hinv
      (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay
      (a := a) ha_pos ha_lt_b ha_lt_1 (n := n) hn
  have heq11 :=
    kadiri_thm_3_1_q1_eq_11 hφ hb hφ_decay hφ'_decay ha_pos ha_lt_b ha_lt_1 hinv
  have hlim11_atTop :
      Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I φ a T) Filter.atTop
        (nhds (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) := by
    exact heq11.congr' (kadiri_thm_3_1_q1_I_eventually_eq_interval φ a).symm
  have hlim11 :
      Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I φ a T) L
        (nhds (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) :=
    hlim11_atTop.mono_left hle
  have hpieces :
      Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I φ a T) L
        (nhds
          (φ 0 * ((-Real.log Real.pi : ℝ) : ℂ)
          + (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))
          + ((∫ y : ℝ, φ y)
            + (1 / (2 * (Real.pi : ℂ))) *
                ∫ t : ℝ,
                  ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                    ∫ y, φ y * exp ((1 / 2 + (t : ℂ) * I) * (y : ℂ)) ∂volume)
          + (∫ y : ℝ, φ y * exp ((y : ℂ)) ∂volume)
          - riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
              (fun ρ ↦ ∫ y, φ y * exp (ρ * (y : ℂ)) ∂volume))) := by
    simpa [L, hsrc] using
      (lim_I_from_pieces_explicit_on_dyadicGoodHeight
        (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay
        (a := a) ha_pos ha_lt_b ha_lt_1 hΦ_sum hΓ_int)
  exact tendsto_nhds_unique hlim11 hpieces

theorem kadiri_thm_3_1_q1_on_dyadicGoodHeight
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hΦ_sum : Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
      (∫ y, φ y * exp (ρ.val * (y : ℂ)) ∂volume) *
        (riemannZeta.order ρ.val : ℂ)))
    (hΓ_int : MeasureTheory.Integrable (fun t : ℝ ↦
      ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
        ∫ y, φ y * exp ((1 / 2 + (t : ℂ) * I) * (y : ℂ)) ∂volume)) :
    let Φ : ℂ → ℂ := fun z ↦ ∫ y, φ y * exp (-z * (y : ℂ)) ∂volume
    (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n)) =
      Φ (-1) + Φ 0
        - riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) (fun ρ ↦ Φ (-ρ))
        - φ 0 * ((Real.log Real.pi : ℝ) : ℂ)
        - ∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n)
        + (1 / (2 * (Real.pi : ℂ))) *
            ∫ t : ℝ,
              ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                Φ (-(1 / 2 + (t : ℂ) * I)) := by
  intro Φ
  have h := kadiri_thm_3_1_q1_explicit_on_dyadicGoodHeight
    (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay hΦ_sum hΓ_int
  convert h using 1
  · have hΦ_neg_one : Φ (-1) = ∫ y : ℝ, φ y * exp ((y : ℂ)) ∂volume := by
      dsimp [Φ]
      simp
    have hΦ_zero : Φ 0 = ∫ y : ℝ, φ y ∂volume := by
      dsimp [Φ]
      simp
    have hzeroes :
        riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) (fun ρ ↦ Φ (-ρ)) =
          riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
            (fun ρ ↦ ∫ y, φ y * exp (ρ * (y : ℂ)) ∂volume) := by
      unfold riemannZeta.zeroes_sum
      apply tsum_congr
      intro ρ
      dsimp [Φ]
      simp
    have hgamma :
        (∫ t : ℝ,
          ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
            Φ (-(1 / 2 + (t : ℂ) * I))) =
          ∫ t : ℝ,
            ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
              ∫ y, φ y * exp ((1 / 2 + (t : ℂ) * I) * (y : ℂ)) ∂volume := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with t
      dsimp [Φ]
      simp
    rw [hΦ_neg_one, hΦ_zero, hzeroes, hgamma]
    simp_rw [show ∀ t : ℝ, (t : ℂ) * I = I * (t : ℂ) from fun t => mul_comm _ _]
    rw [show (((-Real.log Real.pi : ℝ) : ℂ)) = -(((Real.log Real.pi : ℝ) : ℂ)) by
      norm_num]
    ring

end

end Kadiri
