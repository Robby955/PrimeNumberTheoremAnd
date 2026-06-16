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

end

end Kadiri
