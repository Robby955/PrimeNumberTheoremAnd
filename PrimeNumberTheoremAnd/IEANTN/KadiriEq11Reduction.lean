import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.ExpDecay
import PrimeNumberTheoremAnd.LaplaceInversion
import PrimeNumberTheoremAnd.IEANTN.KadiriEq11Base

namespace Kadiri

open MeasureTheory Complex
open ArithmeticFunction hiding log
open Filter
open scoped Topology

noncomputable section

private lemma laplaceKernel_contDiff_paren (s : ℂ) :
    ContDiff ℝ 1 (fun y : ℝ => exp (-(s * (y : ℂ)))) := by
  have hofReal : ContDiff ℝ 1 (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hlinear : ContDiff ℝ 1 (fun y : ℝ => -(s * (y : ℂ))) := by
    simpa using
      ((contDiff_const.mul hofReal).neg :
        ContDiff ℝ 1 (fun y : ℝ => -(s * (y : ℂ))))
  exact hlinear.cexp

private lemma exp_neg_integrableAtFilter_atTop {c : ℝ} (hc : 0 < c) :
    IntegrableAtFilter (fun y : ℝ => Real.exp (-c * y)) Filter.atTop volume :=
  ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, exp_neg_integrableOn_Ioi 0 hc⟩

private lemma exp_pos_integrableAtFilter_atBot {c : ℝ} (hc : 0 < c) :
    IntegrableAtFilter (fun y : ℝ => Real.exp (c * y)) Filter.atBot volume := by
  rw [← Filter.map_neg_atTop, measurableEmbedding_neg.integrableAtFilter_iff_comap]
  have hmap : (volume : Measure ℝ).comap Neg.neg = volume := by
    change (volume : Measure ℝ).comap (MeasurableEquiv.neg ℝ) = volume
    rw [← MeasurableEquiv.map_symm]
    simp
  rw [hmap, Function.comp_def]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    exp_neg_integrableAtFilter_atTop (c := c) hc

private lemma weighted_laplace_source_norm_eq {φ : ℝ → ℂ} {a : ℝ} (y : ℝ) :
    ‖exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y‖ =
      Real.exp ((1 / 2 + a) * y) * ‖φ y * exp ((y : ℂ) / 2)‖ := by
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
  have hre1 : (-(↑(-(1 + a)) * ↑y) : ℂ).re = (1 + a) * y := by
    norm_num [Complex.mul_re]
    ring
  have hre2 : (((y : ℂ) / 2) : ℂ).re = y / 2 := by
    norm_num [Complex.div_re]
  rw [hre1, hre2]
  calc
    Real.exp ((1 + a) * y) * ‖φ y‖ = ‖φ y‖ * Real.exp ((1 + a) * y) := by
      ring
    _ = ‖φ y‖ * Real.exp (((1 / 2 + a) * y) + y / 2) := by
      congr 1
      congr 1
      ring
    _ = ‖φ y‖ * (Real.exp ((1 / 2 + a) * y) * Real.exp (y / 2)) := by
      rw [Real.exp_add]
    _ = Real.exp ((1 / 2 + a) * y) * (‖φ y‖ * Real.exp (y / 2)) := by
      ring

private lemma weighted_laplace_source_isBigO_atTop {φ : ℝ → ℂ} {a b : ℝ}
    (hdec_top : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.atTop] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    (fun y : ℝ => exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y)
        =O[Filter.atTop] fun y : ℝ => Real.exp ((a - b) * y) := by
  obtain ⟨C, hC⟩ := hdec_top.bound
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC, Filter.eventually_gt_atTop (0 : ℝ)] with y hCy hy
  rw [weighted_laplace_source_norm_eq (φ := φ) (a := a) y]
  have hnorm_decay :
      ‖Real.exp (-(1 / 2 + b) * |y|)‖ = Real.exp (-(1 / 2 + b) * |y|) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hnorm_target : ‖Real.exp ((a - b) * y)‖ = Real.exp ((a - b) * y) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hnorm_decay] at hCy
  rw [hnorm_target]
  calc
    Real.exp ((1 / 2 + a) * y) * ‖φ y * cexp (↑y / 2)‖
        ≤ Real.exp ((1 / 2 + a) * y) *
            (C * Real.exp (-(1 / 2 + b) * |y|)) := by
          exact mul_le_mul_of_nonneg_left hCy (Real.exp_nonneg _)
    _ = C * (Real.exp ((1 / 2 + a) * y) *
          Real.exp (-(1 / 2 + b) * y)) := by
      rw [abs_of_pos hy]
      ring
    _ = C * Real.exp (((1 / 2 + a) * y) + (-(1 / 2 + b) * y)) := by
      rw [Real.exp_add]
    _ = C * Real.exp ((a - b) * y) := by
      ring_nf

private lemma weighted_laplace_source_isBigO_atBot {φ : ℝ → ℂ} {a b : ℝ}
    (hdec_bot : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.atBot] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    (fun y : ℝ => exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y)
        =O[Filter.atBot] fun y : ℝ => Real.exp ((1 + a + b) * y) := by
  obtain ⟨C, hC⟩ := hdec_bot.bound
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC, Filter.eventually_lt_atBot (0 : ℝ)] with y hCy hy
  rw [weighted_laplace_source_norm_eq (φ := φ) (a := a) y]
  have hnorm_decay :
      ‖Real.exp (-(1 / 2 + b) * |y|)‖ = Real.exp (-(1 / 2 + b) * |y|) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hnorm_target :
      ‖Real.exp ((1 + a + b) * y)‖ = Real.exp ((1 + a + b) * y) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hnorm_decay] at hCy
  rw [hnorm_target]
  calc
    Real.exp ((1 / 2 + a) * y) * ‖φ y * cexp (↑y / 2)‖
        ≤ Real.exp ((1 / 2 + a) * y) *
            (C * Real.exp (-(1 / 2 + b) * |y|)) := by
          exact mul_le_mul_of_nonneg_left hCy (Real.exp_nonneg _)
    _ = C * (Real.exp ((1 / 2 + a) * y) *
          Real.exp (-(1 / 2 + b) * (-y))) := by
      rw [abs_of_neg hy]
      ring
    _ = C * Real.exp (((1 / 2 + a) * y) + (-(1 / 2 + b) * (-y))) := by
      rw [Real.exp_add]
    _ = C * Real.exp ((1 + a + b) * y) := by
      ring_nf

private lemma kadiri_laplace_source_integrable_of_decay {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    Integrable
      (fun y : ℝ =>
        exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y) := by
  have hdec :
      ((fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.atBot] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) ∧
      ((fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.atTop] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) := by
    simpa [cocompact_eq_atBot_atTop, Asymptotics.isBigO_sup] using hφ_decay
  have hloc : LocallyIntegrable
      (fun y : ℝ => exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y) volume := by
    have hcd :
        ContDiff ℝ 1
          (fun y : ℝ => exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y) :=
      (laplaceKernel_contDiff_paren (((-(1 + a) : ℝ) : ℂ))).mul hφ
    exact hcd.continuous.locallyIntegrable
  apply hloc.integrable_of_isBigO_atBot_atTop
    (g := fun y : ℝ => Real.exp ((1 + a + b) * y))
    (g' := fun y : ℝ => Real.exp ((a - b) * y))
  · exact weighted_laplace_source_isBigO_atBot (φ := φ) (a := a) (b := b) hdec.1
  · have hc : 0 < 1 + a + b := by positivity
    exact exp_pos_integrableAtFilter_atBot (c := 1 + a + b) hc
  · exact weighted_laplace_source_isBigO_atTop (φ := φ) (a := a) (b := b) hdec.2
  · have hc : 0 < b - a := sub_pos.mpr hab
    simpa [sub_eq_add_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc] using
      exp_neg_integrableAtFilter_atTop (c := b - a) hc

private lemma bounded_of_continuous_of_isBigO_exp_atBot_atTop
    {f : ℝ → ℂ} (hf_cont : Continuous f) {cTop cBot : ℝ}
    (hcTop : cTop < 0) (hcBot : 0 < cBot)
    (htop : f =O[Filter.atTop] fun y : ℝ => Real.exp (cTop * y))
    (hbot : f =O[Filter.atBot] fun y : ℝ => Real.exp (cBot * y)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, ‖f y‖ ≤ B := by
  obtain ⟨Ctop, hCtop⟩ := htop.bound
  let Ctop' : ℝ := max Ctop 0
  have hCtop'_nonneg : 0 ≤ Ctop' := le_max_right _ _
  have htop_ev : ∀ᶠ y in Filter.atTop, ‖f y‖ ≤ Ctop' := by
    filter_upwards [hCtop, Filter.eventually_ge_atTop (0 : ℝ)] with y hCy hy0
    have hnorm : ‖Real.exp (cTop * y)‖ = Real.exp (cTop * y) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hexp_le : Real.exp (cTop * y) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg hcTop.le hy0)
    calc
      ‖f y‖ ≤ Ctop * ‖Real.exp (cTop * y)‖ := hCy
      _ = Ctop * Real.exp (cTop * y) := by rw [hnorm]
      _ ≤ Ctop' * Real.exp (cTop * y) := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
      _ ≤ Ctop' * 1 := by
        exact mul_le_mul_of_nonneg_left hexp_le hCtop'_nonneg
      _ = Ctop' := by ring
  obtain ⟨Ytop, hYtop⟩ := Filter.eventually_atTop.mp htop_ev
  obtain ⟨Cbot, hCbot⟩ := hbot.bound
  let Cbot' : ℝ := max Cbot 0
  have hCbot'_nonneg : 0 ≤ Cbot' := le_max_right _ _
  have hbot_ev : ∀ᶠ y in Filter.atBot, ‖f y‖ ≤ Cbot' := by
    filter_upwards [hCbot, Filter.eventually_le_atBot (0 : ℝ)] with y hCy hy0
    have hnorm : ‖Real.exp (cBot * y)‖ = Real.exp (cBot * y) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hexp_le : Real.exp (cBot * y) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos hcBot.le hy0)
    calc
      ‖f y‖ ≤ Cbot * ‖Real.exp (cBot * y)‖ := hCy
      _ = Cbot * Real.exp (cBot * y) := by rw [hnorm]
      _ ≤ Cbot' * Real.exp (cBot * y) := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
      _ ≤ Cbot' * 1 := by
        exact mul_le_mul_of_nonneg_left hexp_le hCbot'_nonneg
      _ = Cbot' := by ring
  obtain ⟨Ybot, hYbot⟩ := Filter.eventually_atBot.mp hbot_ev
  let lo : ℝ := min Ybot Ytop
  let hi : ℝ := max Ybot Ytop
  obtain ⟨Cmid, hCmid⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc lo hi) hf_cont.continuousOn
  let B : ℝ := max Ctop' (max Cbot' (max Cmid 0))
  refine ⟨B, ?_, ?_⟩
  · exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  · intro y
    by_cases htop_case : Ytop ≤ y
    · exact (hYtop y htop_case).trans (le_max_left _ _)
    · by_cases hbot_case : y ≤ Ybot
      · exact (hYbot y hbot_case).trans
          ((le_max_left _ _).trans (le_max_right _ _))
      · have hy_gt_bot : Ybot < y := lt_of_not_ge hbot_case
        have hy_lt_top : y < Ytop := lt_of_not_ge htop_case
        have hylo : lo ≤ y :=
          (min_le_left Ybot Ytop).trans hy_gt_bot.le
        have hyhi : y ≤ hi :=
          hy_lt_top.le.trans (le_max_right Ybot Ytop)
        exact (hCmid y ⟨hylo, hyhi⟩).trans
          ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

private lemma kadiri_weighted_source_bounded_of_decay {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ)
    {b : ℝ} (hb : 0 < b)
    (hψ_decay : (fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y : ℝ, ‖exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * ψ y‖ ≤ B := by
  have hdec :
      ((fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.atBot] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) ∧
      ((fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.atTop] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) := by
    simpa [cocompact_eq_atBot_atTop, Asymptotics.isBigO_sup] using hψ_decay
  have hsource_cont :
      Continuous fun y : ℝ =>
        exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * ψ y :=
    (laplaceKernel_contDiff_paren (((-(1 + a) : ℝ) : ℂ))).continuous.mul hψ_cont
  refine bounded_of_continuous_of_isBigO_exp_atBot_atTop
    (f := fun y : ℝ => exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * ψ y)
    (cTop := a - b) (cBot := 1 + a + b)
    hsource_cont ?_ ?_ ?_ ?_
  · exact sub_neg.mpr hab
  · positivity
  · exact weighted_laplace_source_isBigO_atTop (φ := ψ) (a := a) (b := b) hdec.2
  · exact weighted_laplace_source_isBigO_atBot (φ := ψ) (a := a) (b := b) hdec.1

private lemma kadiri_weighted_source_differentiable {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {a : ℝ} :
    Differentiable ℝ
      (fun y : ℝ => exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y) :=
  ((laplaceKernel_contDiff_paren (((-(1 + a) : ℝ) : ℂ))).differentiable (by norm_num)).mul
    (hφ.differentiable (by norm_num))

private lemma kadiri_weighted_source_deriv {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {a y : ℝ} :
    deriv (fun x : ℝ => exp (-(((-(1 + a) : ℝ) : ℂ) * (x : ℂ))) * φ x) y =
      exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) *
        (((1 + a : ℝ) : ℂ) * φ y + deriv φ y) := by
  have hco : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) y := by
    simpa using (hasDerivAt_id y).ofReal_comp
  have hlin : HasDerivAt
      (fun x : ℝ => -(((-(1 + a) : ℝ) : ℂ) * (x : ℂ)))
      (((1 + a : ℝ) : ℂ)) y := by
    have hmul := hco.const_mul (((1 + a : ℝ) : ℂ))
    have hfun :
        (fun x : ℝ => -(((-(1 + a) : ℝ) : ℂ) * (x : ℂ))) =
          fun x : ℝ => ((1 + a : ℝ) : ℂ) * (x : ℂ) := by
      funext x
      have hcoef : -(((-(1 + a) : ℝ) : ℂ)) = ((1 + a : ℝ) : ℂ) := by
        norm_num
      calc
        -(((-(1 + a) : ℝ) : ℂ) * (x : ℂ))
            = -(((-(1 + a) : ℝ) : ℂ)) * (x : ℂ) := by rw [neg_mul]
        _ = ((1 + a : ℝ) : ℂ) * (x : ℂ) := by rw [hcoef]
    rw [hfun]
    simpa using hmul
  have hker : HasDerivAt
      (fun x : ℝ => exp (-(((-(1 + a) : ℝ) : ℂ) * (x : ℂ))))
      (exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * (((1 + a : ℝ) : ℂ))) y :=
    hlin.cexp
  have hphider : HasDerivAt φ (deriv φ y) y :=
    (hφ.differentiable (by norm_num)).differentiableAt.hasDerivAt
  change deriv ((fun x : ℝ => exp (-(((-(1 + a) : ℝ) : ℂ) * (x : ℂ)))) * φ) y =
    exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) *
      (((1 + a : ℝ) : ℂ) * φ y + deriv φ y)
  rw [deriv_mul hker.differentiableAt hphider.differentiableAt, hker.deriv, hphider.deriv]
  ring

private lemma kadiri_weighted_source_deriv_bound_of_decay {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ y : ℝ,
        ‖deriv (fun x : ℝ => exp (-(((-(1 + a) : ℝ) : ℂ) * (x : ℂ))) * φ x) y‖ ≤ D := by
  obtain ⟨Bφ, hBφ_nonneg, hBφ⟩ :=
    kadiri_weighted_source_bounded_of_decay
      (ψ := φ) hφ.continuous (b := b) hb hφ_decay (a := a) ha hab
  obtain ⟨Bφ', hBφ'_nonneg, hBφ'⟩ :=
    kadiri_weighted_source_bounded_of_decay
      (ψ := deriv φ) (hφ.continuous_deriv (by norm_num))
      (b := b) hb hφ'_decay (a := a) ha hab
  let D : ℝ := (1 + a) * Bφ + Bφ'
  refine ⟨D, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg (by positivity) hBφ_nonneg) hBφ'_nonneg
  · intro y
    rw [kadiri_weighted_source_deriv (φ := φ) hφ (a := a) (y := y)]
    have hsplit :
        exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) *
            (((1 + a : ℝ) : ℂ) * φ y + deriv φ y) =
          ((1 + a : ℝ) : ℂ) *
              (exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y) +
            exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * deriv φ y := by
      ring
    rw [hsplit]
    have hcoef : ‖((1 + a : ℝ) : ℂ)‖ = 1 + a := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc
      ‖((1 + a : ℝ) : ℂ) *
              (exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y) +
            exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * deriv φ y‖
          ≤ ‖((1 + a : ℝ) : ℂ) *
                (exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y)‖ +
              ‖exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * deriv φ y‖ :=
            norm_add_le _ _
      _ = (1 + a) *
              ‖exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y‖ +
            ‖exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * deriv φ y‖ := by
            rw [norm_mul, hcoef]
      _ ≤ (1 + a) * Bφ + Bφ' := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (hBφ y) (by positivity))
              (hBφ' y)

private lemma continuous_laplaceIntegral_verticalLine_add_of_integrable
    {φ : ℝ → ℂ} {σ : ℝ} (hφ_cont : Continuous φ)
    (hφ_int : Integrable (fun y : ℝ => exp (-((σ : ℂ) * (y : ℂ))) * φ y)) :
    Continuous
      (fun t : ℝ => ∫ y : ℝ, φ y * exp (-(((σ : ℂ) + (t : ℂ) * I) * (y : ℂ)))) := by
  rw [continuous_iff_continuousAt]
  intro t0
  let bound : ℝ → ℝ := fun y => ‖exp (-((σ : ℂ) * (y : ℂ))) * φ y‖
  let F : ℝ → ℝ → ℂ := fun t y =>
    φ y * exp (-(((σ : ℂ) + (t : ℂ) * I) * (y : ℂ)))
  have hbound_int : Integrable bound := by
    simpa [bound, mul_comm] using hφ_int.norm
  have hF_meas : ∀ᶠ t in 𝓝 t0, AEStronglyMeasurable (F t) volume := by
    refine Eventually.of_forall ?_
    intro t
    dsimp [F]
    exact (hφ_cont.mul (continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  have h_bound : ∀ᶠ t in 𝓝 t0, ∀ᵐ y ∂volume, ‖F t y‖ ≤ bound y := by
    refine Eventually.of_forall ?_
    intro t
    filter_upwards with y
    dsimp [F, bound]
    rw [norm_mul, norm_mul, norm_exp, norm_exp]
    have hsig : (-(↑σ * ↑y) : ℂ).re = -σ * y := by
      norm_num [Complex.mul_re]
    have ht : (-((↑σ + ↑t * I) * ↑y) : ℂ).re = -σ * y := by
      norm_num [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [hsig, ht]
    rw [mul_comm]
  have h_lim : ∀ᵐ y ∂volume, Tendsto (fun t => F t y) (𝓝 t0) (𝓝 (F t0 y)) := by
    filter_upwards with y
    dsimp [F]
    have hcont : Continuous
        (fun t : ℝ => φ y * exp (-(((σ : ℂ) + (t : ℂ) * I) * (y : ℂ)))) := by
      fun_prop
    exact hcont.continuousAt
  have h_tendsto :=
    tendsto_integral_filter_of_dominated_convergence
      (μ := volume) bound hF_meas h_bound hbound_int h_lim
  unfold ContinuousAt
  simpa [F] using h_tendsto

private def kadiriNegLine (a : ℝ) (t : ℝ) : ℂ :=
  ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)

private lemma kadiriNegLine_re (a t : ℝ) :
    (kadiriNegLine a t).re = -(1 + a) := by
  simp [kadiriNegLine]

private def kadiriPhiNegLine (φ : ℝ → ℂ) (a : ℝ) (t : ℝ) : ℂ :=
  ∫ y : ℝ, φ y * exp (-(kadiriNegLine a t * (y : ℂ)))

set_option maxHeartbeats 5000000 in
-- The Kadiri decay hypothesis unfolds slowly in this local continuity proof.
private lemma kadiri_phi_neg_line_continuous {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    Continuous (kadiriPhiNegLine φ a) := by
  have hsource := kadiri_laplace_source_integrable_of_decay
    (φ := φ) hφ (b := b) hb hφ_decay (a := a) ha hab
  convert
    continuous_laplaceIntegral_verticalLine_add_of_integrable
      (φ := φ) (σ := (-(1 + a) : ℝ)) hφ.continuous hsource
    using 2
  apply integral_congr_ae
  filter_upwards with y
  congr 2
  simp only [kadiriNegLine, ofReal_add, ofReal_neg, ofReal_one]

/-- Collapse the von Mangoldt Dirichlet series on the negative Mellin line. -/
lemma tsum_vonMangoldt_neg_mellin_line {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (∑' n : ℕ,
        (Λ n : ℂ) * (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) =
      -deriv riemannZeta (((1 + a : ℝ) : ℂ) - (t : ℂ) * I) /
        riemannZeta (((1 + a : ℝ) : ℂ) - (t : ℂ) * I) := by
  have hs : 1 < (((1 + a : ℝ) : ℂ) - (t : ℂ) * I).re := by
    simp
    linarith
  rw [← tsum_vonMangoldt_eq hs]
  refine tsum_congr fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hline :
        ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) =
          -(((1 + a : ℝ) : ℂ) - (t : ℂ) * I) := by
      ring
    rw [hline, Complex.cpow_neg, div_eq_mul_inv]

private lemma summable_vonMangoldt_neg_mellin_line {a : ℝ} (ha : 0 < a) (t : ℝ) :
    Summable fun n : ℕ =>
      (Λ n : ℂ) * (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) := by
  have hs : 1 < (((1 + a : ℝ) : ℂ) - (t : ℂ) * I).re := by
    simp
    linarith
  refine (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).congr fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn.ne']
    have hline :
        ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) =
          -(((1 + a : ℝ) : ℂ) - (t : ℂ) * I) := by
      ring
    rw [hline, Complex.cpow_neg, div_eq_mul_inv]

private lemma summable_norm_vonMangoldt_neg_mellin_line {a : ℝ} (ha : 0 < a) (t : ℝ) :
    Summable fun n : ℕ =>
      ‖(Λ n : ℂ) * (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
  (summable_vonMangoldt_neg_mellin_line ha t).norm

private lemma norm_vonMangoldt_neg_mellin_line_eq_real (a t : ℝ) (n : ℕ) :
    ‖(Λ n : ℂ) * (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)‖ =
      ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    rw [norm_mul, norm_div]
    rw [Complex.norm_natCast_cpow_of_pos hn]
    rw [Complex.norm_natCast_cpow_of_pos hn]
    have hleft :
        ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I).re = -(1 + a) := by
      simp
    have hright : (((1 + a : ℝ) : ℂ)).re = 1 + a := by simp
    rw [hleft, hright, Real.rpow_neg hnpos.le, div_eq_mul_inv]

private lemma summable_norm_vonMangoldt_real_line {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ =>
      ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖ := by
  have hs : 1 < (((1 + a : ℝ) : ℂ)).re := by
    simp
    linarith
  have hseries : Summable fun n : ℕ =>
      (Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ) := by
    refine (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).congr fun n ↦ ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn.ne']
  exact hseries.norm

private lemma kadiri_eq11_truncated_mellin_swap_core {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (T : ℝ) :
    HasSum
      (fun n : ℕ =>
        ∫ t in (-T)..T,
          ((Λ n : ℂ) *
              (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
            kadiriPhiNegLine φ a t)
      (∫ t in (-T)..T,
        (∑' n : ℕ,
            (Λ n : ℂ) *
              (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
          kadiriPhiNegLine φ a t) := by
  have hPhi_cont := kadiri_phi_neg_line_continuous
    (φ := φ) hφ (b := b) hb hφ_decay (a := a) ha hab
  have hPhi_cont_on : ContinuousOn (kadiriPhiNegLine φ a) (Set.uIcc (-T) T) :=
    hPhi_cont.continuousOn
  obtain ⟨C0, hC0⟩ := isCompact_uIcc.exists_bound_of_continuousOn hPhi_cont_on
  let C : ℝ := max C0 0
  have hC_nonneg : 0 ≤ C := le_max_right _ _
  have hC : ∀ y ∈ Set.uIcc (-T) T, ‖kadiriPhiNegLine φ a y‖ ≤ C := by
    intro y hy
    exact (hC0 y hy).trans (le_max_left _ _)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume)
    (F := fun n t =>
      ((Λ n : ℂ) *
          (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
        kadiriPhiNegLine φ a t)
    (f := fun t =>
      (∑' n : ℕ,
          (Λ n : ℂ) *
            (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
        kadiriPhiNegLine φ a t)
    (bound := fun n _t =>
      C * ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖) ?_ ?_ ?_ ?_ ?_
  · intro n
    by_cases hn : n = 0
    · simpa [hn] using
        (aestronglyMeasurable_const :
          AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
            (volume.restrict (Set.uIoc (-T) T)))
    · have hpow : Continuous fun t : ℝ =>
          (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) := by
        refine Continuous.const_cpow (by fun_prop) ?_
        exact Or.inl (Nat.cast_ne_zero.mpr hn)
      exact ((continuous_const.mul hpow).mul hPhi_cont).aestronglyMeasurable
  · intro n
    filter_upwards with y hy
    calc
      ‖((Λ n : ℂ) *
              (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (y : ℂ) * I)) *
            kadiriPhiNegLine φ a y‖
          = ‖(Λ n : ℂ) *
              (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (y : ℂ) * I)‖ *
            ‖kadiriPhiNegLine φ a y‖ := norm_mul _ _
      _ = ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖ *
            ‖kadiriPhiNegLine φ a y‖ := by
          rw [norm_vonMangoldt_neg_mellin_line_eq_real]
      _ ≤ ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖ * C := by
          exact mul_le_mul_of_nonneg_left
            (hC y (Set.uIoc_subset_uIcc hy)) (norm_nonneg _)
      _ = C * ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖ := by
          ring
  · filter_upwards with y hy
    exact (summable_norm_vonMangoldt_real_line ha).mul_left C
  · exact intervalIntegrable_const
  · filter_upwards with y hy
    exact (summable_vonMangoldt_neg_mellin_line ha y).hasSum.mul_right
      (kadiriPhiNegLine φ a y)

private lemma kadiri_eq11_truncated_mellin_swap {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (T : ℝ) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    (∑' n : ℕ,
        (Λ n : ℂ) *
          ((1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))) =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ t in (-T)..T,
          (∑' n : ℕ,
              (Λ n : ℂ) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
            Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) := by
  intro Φ
  have hcore := kadiri_eq11_truncated_mellin_swap_core
    (φ := φ) hφ (b := b) hb hφ_decay (a := a) ha hab T
  have hscaled :=
    congrArg (fun z : ℂ => (1 / (2 * (Real.pi : ℂ))) * z) hcore.tsum_eq
  calc
    (∑' n : ℕ,
        (Λ n : ℂ) *
          ((1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)))
        = (1 / (2 * (Real.pi : ℂ))) *
            (∑' n : ℕ,
              ∫ t in (-T)..T,
                ((Λ n : ℂ) *
                    (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
                  kadiriPhiNegLine φ a t) := by
          rw [← tsum_mul_left]
          refine tsum_congr fun n ↦ ?_
          calc
            (Λ n : ℂ) *
                ((1 / (2 * (Real.pi : ℂ))) *
                  ∫ t in (-T)..T,
                    Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                      (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
                = (1 / (2 * (Real.pi : ℂ))) *
                    ((Λ n : ℂ) *
                      ∫ t in (-T)..T,
                        Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                          (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) := by
                  ring
            _ = (1 / (2 * (Real.pi : ℂ))) *
                ∫ t in (-T)..T,
                  (Λ n : ℂ) *
                    (Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                      (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) := by
                  rw [intervalIntegral.integral_const_mul]
            _ = (1 / (2 * (Real.pi : ℂ))) *
                ∫ t in (-T)..T,
                  ((Λ n : ℂ) *
                      (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
                    kadiriPhiNegLine φ a t := by
                  congr 1
                  apply intervalIntegral.integral_congr
                  intro t ht
                  simp [Φ, kadiriPhiNegLine, kadiriNegLine]
                  ring
    _ = (1 / (2 * (Real.pi : ℂ))) *
        ∫ t in (-T)..T,
          (∑' n : ℕ,
              (Λ n : ℂ) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
            kadiriPhiNegLine φ a t := hscaled
    _ = (1 / (2 * (Real.pi : ℂ))) *
        ∫ t in (-T)..T,
          (∑' n : ℕ,
              (Λ n : ℂ) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
            Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro t ht
          simp [Φ, kadiriPhiNegLine, kadiriNegLine]

private lemma sin_div_error_pointwise_bound
    {g : ℝ → ℂ} {D x T u : ℝ}
    (hD : 0 ≤ D) (hgdiff : Differentiable ℝ g)
    (hderiv : ∀ y : ℝ, ‖deriv g y‖ ≤ D) :
    ‖(if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
        (g (x - u) - g x)‖ ≤ D / Real.pi := by
  by_cases hu : u = 0
  · simp [hu, div_nonneg hD Real.pi_pos.le]
  · rw [if_neg hu, norm_smul]
    have hscalar :
        ‖(Real.sin (T * u) / (Real.pi * u) : ℂ)‖ ≤ 1 / (Real.pi * |u|) := by
      rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real]
      simp only [Real.norm_eq_abs]
      rw [abs_of_pos Real.pi_pos]
      have hsin : |Real.sin (T * u)| ≤ 1 := Real.abs_sin_le_one _
      exact div_le_div_of_nonneg_right hsin
        (mul_nonneg Real.pi_pos.le (abs_nonneg u))
    have hdiff : ‖g (x - u) - g x‖ ≤ D * |u| := by
      have hmv :=
        (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
          (f := g) (C := D)
          (fun y _hy => hgdiff y)
          (fun y _hy => hderiv y)
          (x := x) (y := x - u) (by simp) (by simp)
      have hnorm : ‖(x - u) - x‖ = |u| := by
        rw [Real.norm_eq_abs]
        have hsub : (x - u) - x = -u := by ring
        rw [hsub, abs_neg]
      simpa [hnorm] using hmv
    have hupper_nonneg : 0 ≤ 1 / (Real.pi * |u|) := by positivity
    calc
      ‖(Real.sin (T * u) / (Real.pi * u) : ℂ)‖ * ‖g (x - u) - g x‖
          ≤ (1 / (Real.pi * |u|)) * (D * |u|) := by
            exact mul_le_mul hscalar hdiff (norm_nonneg _) hupper_nonneg
      _ = D / Real.pi := by
            field_simp [Real.pi_ne_zero, abs_pos.mpr hu]

private lemma sin_div_error_interval_bound
    {g : ℝ → ℂ} {D x T : ℝ}
    (hD : 0 ≤ D) (hgdiff : Differentiable ℝ g)
    (hderiv : ∀ y : ℝ, ‖deriv g y‖ ≤ D) :
    ‖∫ u in (-(1 : ℝ))..(1 : ℝ),
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
          (g (x - u) - g x)‖ ≤
      (D / Real.pi) * (volume.real (Set.Ioc (-(1 : ℝ)) (1 : ℝ))) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1 : ℝ)) ≤ 1)]
  refine norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Set.Ioc (-(1 : ℝ)) (1 : ℝ)) ?_ ?_
  · simp [Real.volume_Ioc]
  · intro u _hu
    exact sin_div_error_pointwise_bound (g := g) (D := D) (x := x) (T := T) (u := u)
      hD hgdiff hderiv

private theorem eq11_laplaceInvLineTrunc_laplaceTransformBilateral_eq_fourierInvTrunc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (sigma : ℝ) (f : ℝ → E) (x T : ℝ) :
    laplaceInvLineTrunc sigma (laplaceTransformBilateral f) x T =
      Complex.exp ((sigma : ℂ) * (x : ℂ)) •
        fourierInvTrunc
          (FourierTransform.fourier
            (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y)) x T := by
  let g : ℝ → E := fun y => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y
  unfold laplaceInvLineTrunc fourierInvTrunc
  simp_rw [laplaceTransformBilateral_eq_fourier]
  simp only [one_div, mul_inv_rev, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
    I_im, mul_one, sub_self, add_zero, neg_mul, add_im, mul_im, zero_add]
  rw [show (Real.pi⁻¹ * 2⁻¹ : ℝ) = (1 / (2 * Real.pi) : ℝ) by ring]
  change (1 / (2 * Real.pi) : ℝ) •
      ∫ t in (-T)..T, Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (x : ℂ)) •
        FourierTransform.fourier g (t / (2 * Real.pi)) =
      Complex.exp ((sigma : ℂ) * (x : ℂ)) •
        ((1 / (2 * Real.pi) : ℝ) •
          ∫ t in (-T)..T, Complex.exp (((t * x : ℝ) : ℂ) * I) •
            FourierTransform.fourier g (t / (2 * Real.pi)))
  have hsplit :
      (∫ t in (-T)..T, Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (x : ℂ)) •
          FourierTransform.fourier g (t / (2 * Real.pi))) =
        Complex.exp ((sigma : ℂ) * (x : ℂ)) •
          ∫ t in (-T)..T, Complex.exp (((t * x : ℝ) : ℂ) * I) •
            FourierTransform.fourier g (t / (2 * Real.pi)) := by
    rw [← intervalIntegral.integral_smul]
    congr with t
    rw [← smul_assoc]
    congr 1
    change Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (x : ℂ)) =
      Complex.exp ((sigma : ℂ) * (x : ℂ)) * Complex.exp (((t * x : ℝ) : ℂ) * I)
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [hsplit]
  rw [SMulCommClass.smul_comm (M := ℝ) (N := ℂ) (α := E)]

private theorem eq11_laplaceInvLineTrunc_tendsto_laplaceTransformBilateral_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (sigma : ℝ) (f : ℝ → E) {x : ℝ}
    (hlim : Filter.Tendsto
      (fun T : ℝ =>
        fourierInvTrunc
          (FourierTransform.fourier
            (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y)) x T)
      Filter.atTop
      (nhds (Complex.exp (-((sigma : ℂ) * (x : ℂ))) • f x))) :
    Filter.Tendsto
      (fun T : ℝ => laplaceInvLineTrunc sigma (laplaceTransformBilateral f) x T)
      Filter.atTop (nhds (f x)) := by
  let g : ℝ → E := fun y => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y
  have hlim' : Filter.Tendsto
      (fun T : ℝ => fourierInvTrunc (FourierTransform.fourier g) x T)
      Filter.atTop (nhds (g x)) := by
    simpa [g] using hlim
  have hscaled : Filter.Tendsto
      (fun T : ℝ =>
        Complex.exp ((sigma : ℂ) * (x : ℂ)) •
          fourierInvTrunc (FourierTransform.fourier g) x T)
      Filter.atTop (nhds (Complex.exp ((sigma : ℂ) * (x : ℂ)) • g x)) :=
    hlim'.const_smul (Complex.exp ((sigma : ℂ) * (x : ℂ)))
  have htarget : Complex.exp ((sigma : ℂ) * (x : ℂ)) • g x = f x := by
    simp [g, ← smul_assoc, ← Complex.exp_add]
  rw [htarget] at hscaled
  refine hscaled.congr' ?_
  filter_upwards with T
  exact (eq11_laplaceInvLineTrunc_laplaceTransformBilateral_eq_fourierInvTrunc
    sigma f x T).symm

private theorem eq11_exp_mul_log_of_pos_eq_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    Complex.exp (s * (Real.log x : ℂ)) = (x : ℂ) ^ s := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [Complex.ofReal_log hx.le]
  congr 1
  ring

private theorem eq11_laplaceIntegralCpowTrunc_eq_laplaceInvLineTrunc
    (sigma : ℝ) (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x) (T : ℝ) :
    laplaceIntegralCpowTrunc f sigma x T =
      laplaceInvLineTrunc sigma (laplaceTransformBilateral f) (Real.log x) T := by
  unfold laplaceIntegralCpowTrunc laplaceInvLineTrunc
  simp_rw [laplaceIntegral_eq_laplaceTransformBilateral, smul_eq_mul]
  rw [RCLike.real_smul_eq_coe_mul]
  congr 1
  · push_cast
    field_simp [Real.pi_ne_zero]
    rfl
  · apply intervalIntegral.integral_congr
    intro t _ht
    change laplaceTransformBilateral f ((sigma : ℂ) + (t : ℂ) * I) *
        (x : ℂ) ^ ((sigma : ℂ) + (t : ℂ) * I) =
      Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (Real.log x : ℂ)) *
        laplaceTransformBilateral f ((sigma : ℂ) + (t : ℂ) * I)
    rw [← eq11_exp_mul_log_of_pos_eq_cpow hx ((sigma : ℂ) + (t : ℂ) * I)]
    ring

private theorem eq11_laplaceIntegralCpowTrunc_tendsto_of_integrable_local_quotient
    (sigma : ℝ) (f : ℝ → ℂ) {x R : ℝ} (hx : 0 < x) (hR : 0 < R)
    (hg : Integrable (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y))
    (hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else
          (1 / (Real.pi * u) : ℂ) •
            (Complex.exp (-((sigma : ℂ) * ((Real.log x - u : ℝ) : ℂ))) *
                f (Real.log x - u) -
              Complex.exp (-((sigma : ℂ) * (Real.log x : ℂ))) * f (Real.log x)))
      volume (-R) R) :
    Filter.Tendsto (fun T : ℝ => laplaceIntegralCpowTrunc f sigma x T)
      Filter.atTop (nhds (f (Real.log x))) := by
  have hfourier : Filter.Tendsto
      (fun T : ℝ =>
        fourierInvTrunc
          (FourierTransform.fourier
            (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y))
          (Real.log x) T)
      Filter.atTop
      (nhds (Complex.exp (-((sigma : ℂ) * (Real.log x : ℂ))) • f (Real.log x))) := by
    exact fourierInvTrunc_tendsto_of_sinc_kernel (E := ℂ)
      (f := fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y)
      (by simpa [smul_eq_mul] using hg)
      (sinc_kernel_tendsto_of_integrable_local_quotient (E := ℂ)
        (f := fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y)
        (x := Real.log x) (R := R) (by simpa [smul_eq_mul] using hg) hR hq)
  have hline := eq11_laplaceInvLineTrunc_tendsto_laplaceTransformBilateral_eq
    (E := ℂ) sigma f (x := Real.log x) hfourier
  refine hline.congr' ?_
  filter_upwards with T
  exact (eq11_laplaceIntegralCpowTrunc_eq_laplaceInvLineTrunc sigma f hx T).symm

private lemma fourierInvTrunc_uniform_bound_of_deriv_bound
    {g : ℝ → ℂ} {B D : ℝ}
    (hg_int : Integrable g) (hgdiff : Differentiable ℝ g)
    (hg_bound : ∀ x : ℝ, ‖g x‖ ≤ B)
    (hD : 0 ≤ D) (hg_deriv : ∀ x : ℝ, ‖deriv g x‖ ≤ D) :
    ∀ᶠ T in atTop, ∀ x : ℝ,
      ‖fourierInvTrunc (FourierTransform.fourier g) x T‖ ≤
        2 * B + (D / Real.pi) * (volume.real (Set.Ioc (-(1 : ℝ)) (1 : ℝ))) +
          (1 / Real.pi) * ∫ u : ℝ, ‖g u‖ := by
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ),
    eventually_norm_intervalIntegral_sin_div_kernel_scalar_mass_le_two (R := (1 : ℝ)) zero_lt_one]
    with T hT hmass x
  have hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else (1 / (Real.pi * u) : ℂ) • (g (x - u) - g x))
      volume (-(1 : ℝ)) (1 : ℝ) := by
    exact intervalIntegrable_local_quotient_of_differentiableAt
      (E := ℂ) (f := g) (x := x) (R := (1 : ℝ)) zero_lt_one
      (hgdiff.continuous.continuousOn) (hgdiff.differentiableAt)
  have herr := intervalIntegrable_sin_div_kernel_error_of_intervalIntegrable_quotient
    (E := ℂ) (f := g) (x := x) (R := (1 : ℝ)) hq T
  have hlocal := sin_div_error_interval_bound (g := g) (D := D) (x := x) (T := T)
    hD hgdiff hg_deriv
  have hcore := norm_fourierInvTrunc_le_of_windowed_sin_div_bounds
    (E := ℂ) (f := g) hg_int (x := x) (T := T) (R := (1 : ℝ))
    (B := B) (L := (D / Real.pi) * (volume.real (Set.Ioc (-(1 : ℝ)) (1 : ℝ))))
    (M := (2 : ℝ)) hT zero_lt_one (hg_bound x) hmass herr hlocal
  simpa [mul_assoc] using hcore

private lemma laplaceIntegralCpowTrunc_norm_bound_of_fourier
    {φ : ℝ → ℂ} {sigma x T C : ℝ} (hx : 0 < x)
    (hC : ‖fourierInvTrunc
      (FourierTransform.fourier
        (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * φ y))
      (Real.log x) T‖ ≤ C) :
    ‖laplaceIntegralCpowTrunc φ sigma x T‖ ≤ Real.exp (sigma * Real.log x) * C := by
  rw [eq11_laplaceIntegralCpowTrunc_eq_laplaceInvLineTrunc sigma φ hx T]
  rw [eq11_laplaceInvLineTrunc_laplaceTransformBilateral_eq_fourierInvTrunc]
  rw [norm_smul, norm_exp]
  have hre : ((sigma : ℂ) * (Real.log x : ℂ)).re = sigma * Real.log x := by
    norm_num [Complex.mul_re]
  rw [hre]
  simpa [smul_eq_mul] using mul_le_mul_of_nonneg_left hC (Real.exp_nonneg _)

private lemma norm_exp_neg_log_eq_norm_nat_cpow {a : ℝ} {n : ℕ} (hn : 0 < n) :
    Real.exp ((-(1 + a)) * Real.log n) =
      ‖(n : ℂ) ^ ((-(1 + a : ℝ) : ℂ))‖ := by
  rw [Complex.norm_natCast_cpow_of_pos hn]
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hn)]
  congr 1
  simp
  ring

private lemma kadiri_eq11_tannery_bound {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ C : ℝ,
      ∀ᶠ T in atTop, ∀ n : ℕ,
        ‖(Λ n : ℂ) *
          ((1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              (let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
               Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)))‖ ≤
          C * ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖ := by
  let g : ℝ → ℂ := fun y : ℝ =>
    exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y
  obtain ⟨B, _hB_nonneg, hB⟩ :=
    kadiri_weighted_source_bounded_of_decay
      (ψ := φ) hφ.continuous (b := b) hb hφ_decay (a := a) ha hab
  obtain ⟨D, hD_nonneg, hD⟩ :=
    kadiri_weighted_source_deriv_bound_of_decay
      (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay (a := a) ha hab
  let C : ℝ :=
    2 * B + (D / Real.pi) * (volume.real (Set.Ioc (-(1 : ℝ)) (1 : ℝ))) +
      (1 / Real.pi) * ∫ u : ℝ, ‖g u‖
  refine ⟨C, ?_⟩
  have hg_int : Integrable g := by
    exact kadiri_laplace_source_integrable_of_decay
      (φ := φ) hφ (b := b) hb hφ_decay (a := a) ha hab
  have hgdiff : Differentiable ℝ g := by
    simpa [g] using kadiri_weighted_source_differentiable (φ := φ) hφ (a := a)
  have hg_deriv : ∀ x : ℝ, ‖deriv g x‖ ≤ D := by
    intro x
    simpa [g] using hD x
  have hfourier :=
    fourierInvTrunc_uniform_bound_of_deriv_bound
      (g := g) (B := B) (D := D) hg_int hgdiff hB hD_nonneg hg_deriv
  filter_upwards [hfourier] with T hT n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hx : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hlaplace :
        ‖laplaceIntegralCpowTrunc φ (-(1 + a)) (n : ℝ) T‖ ≤
          C * ‖(n : ℂ) ^ ((-(1 + a : ℝ) : ℂ))‖ := by
      have hTlog :
          ‖fourierInvTrunc
              (FourierTransform.fourier
                (fun y : ℝ => Complex.exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y))
              (Real.log (n : ℝ)) T‖ ≤ C := by
        simpa [C, g, norm_mul] using hT (Real.log (n : ℝ))
      have hcore := laplaceIntegralCpowTrunc_norm_bound_of_fourier
        (φ := φ) (sigma := -(1 + a)) (x := (n : ℝ)) (T := T) (C := C) hx
        hTlog
      have hpow := norm_exp_neg_log_eq_norm_nat_cpow (a := a) (n := n) hn
      calc
        ‖laplaceIntegralCpowTrunc φ (-(1 + a)) (n : ℝ) T‖
            ≤ Real.exp (-(1 + a) * Real.log ↑n) * C := hcore
        _ = C * ‖(n : ℂ) ^ ((-(1 + a : ℝ) : ℂ))‖ := by
            rw [hpow]
            ring
    have hpv_eq :
        ((1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              (let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
               Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))) =
          laplaceIntegralCpowTrunc φ (-(1 + a)) (n : ℝ) T := by
      simp [laplaceIntegralCpowTrunc, laplaceIntegral]
    rw [hpv_eq]
    calc
      ‖(Λ n : ℂ) * laplaceIntegralCpowTrunc φ (-(1 + a)) (n : ℝ) T‖
          = ‖(Λ n : ℂ)‖ *
              ‖laplaceIntegralCpowTrunc φ (-(1 + a)) (n : ℝ) T‖ := by
            rw [norm_mul]
      _ ≤ ‖(Λ n : ℂ)‖ * (C * ‖(n : ℂ) ^ ((-(1 + a : ℝ) : ℂ))‖) := by
            exact mul_le_mul_of_nonneg_left hlaplace (norm_nonneg _)
      _ = C * ‖(Λ n : ℂ) *
              (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ))‖ := by
            rw [norm_mul]
            ring
      _ = C * ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖ := by
            rw [← norm_vonMangoldt_neg_mellin_line_eq_real (a := a) (t := 0) (n := n)]
            simp

/-- Tannery exchange for the principal-value inversion terms.  This converts
pointwise PV inversion at each integer into the summed PV limit, using an
explicit summable domination bound over `n`. -/
lemma kadiri_thm_3_1_q1_eq_11_summed_pv_of_pointwise_inversion_bound
    {φ : ℝ → ℂ} {a : ℝ}
    (hinv : ∀ n : Nat, 1 ≤ n →
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop (𝓝 (φ (Real.log n))))
    {bound : ℕ → ℝ} (hbound_sum : Summable bound)
    (hbound :
      ∀ᶠ T in atTop, ∀ n : ℕ,
        ‖(Λ n : ℂ) *
          ((1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              (let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
               Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)))‖ ≤ bound n) :
    Tendsto
      (fun T : ℝ =>
        ∑' n : ℕ,
          (Λ n : ℂ) *
            ((1 / (2 * (Real.pi : ℂ))) *
              ∫ t in (-T)..T,
                (let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
                 Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                  (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))))
      atTop
      (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) := by
  refine tendsto_tsum_of_dominated_convergence
    (𝓕 := atTop)
    (f := fun T n =>
      (Λ n : ℂ) *
        ((1 / (2 * (Real.pi : ℂ))) *
          ∫ t in (-T)..T,
            (let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
             Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
              (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))))
    (g := fun n => (Λ n : ℂ) * φ (Real.log n))
    hbound_sum ?_ hbound
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simpa using (hinv n hn).const_mul (Λ n : ℂ)

/-- Positive-line reflection of the already-summed negative-line principal value.
The public reduction below proves this summed PV from pointwise inversion and a
Tannery domination bound before using this helper. -/
private lemma kadiri_eq11_pv_positive_line_of_negative_line_pv
    {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (_hab : a < b) (_ha1 : a < 1)
    (hinv :
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              (∑' n : ℕ,
                  (Λ n : ℂ) *
                    (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
                Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop
        (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n)))) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Tendsto
      (fun T : ℝ =>
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t in (-T)..T,
            (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
                riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
              Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I)))
      atTop
      (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) := by
  intro Φ
  dsimp only at hinv
  refine hinv.congr' ?_
  filter_upwards with T
  congr 1
  let F : ℝ → ℂ := fun t ↦
    (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
        riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
      Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I))
  have hneg : (∫ t in (-T)..T, F (-t)) = ∫ t in (-T)..T, F t := by
    simp [intervalIntegral.integral_comp_neg]
  rw [← hneg]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  dsimp [F]
  rw [tsum_vonMangoldt_neg_mellin_line ha t]
  have hzeta_arg :
      (((1 + a : ℝ) : ℂ) - (t : ℂ) * I) =
        (((1 + a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
    simp only [ofReal_neg]
    ring
  have hPhi_arg :
      ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) =
        -(((1 + a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
    simp only [ofReal_neg]
    ring
  rw [hzeta_arg, hPhi_arg]

/-- Principal-value reduction of Kadiri equation (11) from pointwise PV
inversion and an explicit Tannery domination bound.  The finite-window
sum/integral exchange is proved in this file, and the final vertical-line
reflection is the Dirichlet-series identity followed by `t ↦ -t`. -/
theorem kadiri_thm_3_1_q1_eq_11_pv_of_pointwise_inversion_bound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (hinv : ∀ n : Nat, 1 ≤ n →
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop (𝓝 (φ (Real.log n))))
    {bound : ℕ → ℝ} (hbound_sum : Summable bound)
    (hbound :
      ∀ᶠ T in atTop, ∀ n : ℕ,
        ‖(Λ n : ℂ) *
          ((1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              (let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
               Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)))‖ ≤ bound n) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Tendsto
      (fun T : ℝ =>
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t in (-T)..T,
            (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
                riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
              Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I)))
      atTop
      (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) := by
  intro Φ
  have hsummed :=
    kadiri_thm_3_1_q1_eq_11_summed_pv_of_pointwise_inversion_bound
      (φ := φ) (a := a) hinv hbound_sum hbound
  have hneg :
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              (∑' n : ℕ,
                  (Λ n : ℂ) *
                    (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
                Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop
        (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) := by
    dsimp only at hsummed
    refine hsummed.congr' ?_
    filter_upwards with T
    exact kadiri_eq11_truncated_mellin_swap
      (φ := φ) hφ (b := b) hb hφ_decay (a := a) ha hab T
  exact kadiri_eq11_pv_positive_line_of_negative_line_pv
    (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay (a := a) ha hab ha1 hneg

/-- Principal-value reduction with the explicit Tannery majorant expected from
the finite-height inversion bound.  The only domination input is the eventual
uniform estimate by a constant multiple of the absolutely summable von Mangoldt
line `Λ n / n^(1+a)`. -/
theorem kadiri_thm_3_1_q1_eq_11_pv_of_pointwise_inversion_tannery_bound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (hinv : ∀ n : Nat, 1 ≤ n →
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop (𝓝 (φ (Real.log n))))
    {C : ℝ}
    (hbound :
      ∀ᶠ T in atTop, ∀ n : ℕ,
        ‖(Λ n : ℂ) *
          ((1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              (let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
               Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)))‖ ≤
          C * ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Tendsto
      (fun T : ℝ =>
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t in (-T)..T,
            (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
                riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
              Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I)))
      atTop
      (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) := by
  exact kadiri_thm_3_1_q1_eq_11_pv_of_pointwise_inversion_bound
    (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay
    (a := a) ha hab ha1 hinv
    (bound := fun n : ℕ => C * ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖)
    ((summable_norm_vonMangoldt_real_line ha).mul_left C)
    hbound

/-- Principal-value reduction of Kadiri equation (11) from pointwise PV inversion.
The Tannery domination bound is discharged from the Kadiri decay hypotheses via
the finite-window Fourier/Laplace estimate. -/
theorem kadiri_thm_3_1_q1_eq_11_pv_of_pointwise_inversion
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (hinv : ∀ n : Nat, 1 ≤ n →
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop (𝓝 (φ (Real.log n)))) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Tendsto
      (fun T : ℝ =>
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t in (-T)..T,
            (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
                riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
              Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I)))
      atTop
      (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) := by
  obtain ⟨C, hC⟩ :=
    kadiri_eq11_tannery_bound
      (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay (a := a) ha hab
  exact kadiri_thm_3_1_q1_eq_11_pv_of_pointwise_inversion_tannery_bound
    (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay
    (a := a) ha hab ha1 hinv (C := C) hC

/-- Reduction of Kadiri equation (11) from the pointwise inversion identity.

The analytic exchange of the von Mangoldt sum with the Mellin integral is kept as an
explicit hypothesis. This isolates the part blocked by the concrete Fubini/Tonelli
side-condition proof while avoiding any dependency on the sorried inversion theorem in
`Kadiri.lean`. -/
theorem kadiri_thm_3_1_q1_eq_11_of_inversion {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (_hab : a < b) (_ha1 : a < 1)
    (hinv : ∀ n : Nat, 1 ≤ n →
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      (φ (Real.log n) : ℂ) =
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t : ℝ,
            Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
              (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
    (hMellinSwap :
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      (∑' n : ℕ,
          (Λ n : ℂ) *
            ((1 / (2 * (Real.pi : ℂ))) *
              ∫ t : ℝ,
                Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                  (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))) =
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t : ℝ,
            (∑' n : ℕ,
                (Λ n : ℂ) *
                  (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n)) =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ t : ℝ,
          (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
              riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
            Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) := by
  intro Φ
  dsimp only at hMellinSwap
  have hterm :
      ∀ n : ℕ,
        (Λ n : ℂ) * φ (Real.log n) =
          (Λ n : ℂ) *
            ((1 / (2 * (Real.pi : ℂ))) *
              ∫ t : ℝ,
                Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                  (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [hinv n hn]
  rw [tsum_congr hterm]
  rw [hMellinSwap]
  have hcollapse :
      (∫ t : ℝ,
          (∑' n : ℕ,
              (Λ n : ℂ) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
            Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) =
        ∫ t : ℝ,
          (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
              riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
            Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) := by
    let F : ℝ → ℂ := fun t ↦
      (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
          riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
        Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I))
    have hneg : (∫ t : ℝ, F (-t)) = ∫ t : ℝ, F t := by
      simpa using
        (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
          (Homeomorph.neg ℝ).measurableEmbedding F
    rw [← hneg]
    refine integral_congr_ae ?_
    filter_upwards with t
    dsimp [F]
    rw [tsum_vonMangoldt_neg_mellin_line ha t]
    have hzeta_arg :
        (((1 + a : ℝ) : ℂ) - (t : ℂ) * I) =
          (((1 + a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      simp only [ofReal_neg]
      ring
    have hPhi_arg :
        ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) =
          -(((1 + a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      simp only [ofReal_neg]
      ring
    rw [hzeta_arg, hPhi_arg]
  rw [hcollapse]

/-- The single-point truncated-limit inverse Laplace identity at `y = log n`
(\cite{Kadiri2005}, the displayed equation just before eq.~(11)): for `φ` of class `C¹`
with the strip decay of (B), and any `0 < a < b` with `n ≥ 1`,
$$\varphi(\log n)
   = \lim_{T \to \infty} \frac{1}{2\pi i} \int_{-(1+a)-iT}^{-(1+a)+iT}
       \Phi(s)\, n^{s}\, ds,$$
with `Φ(s) = ∫ y, φ y e^{-s y}`. This is the truncated-window Fourier/Laplace inversion
theorem from `PrimeNumberTheoremAnd.LaplaceInversion`, specialized to the contour
`σ = -(1+a)` and the point `x = n` (so `n^s = exp (s log n)`). It discharges the `hinv`
hypothesis carried by the eq.~(11) reduction lemmas above. -/
theorem kadiri_thm_3_1_q1_pointwise_inversion {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ n : Nat, 1 ≤ n →
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop (𝓝 (φ (Real.log n))) := by
  intro n hn Φ
  -- Reduce to the multiplication-form truncated inverse Laplace integral.
  have hx : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- The exponentially weighted source `g y = exp (-(σ y)) φ y` with `σ = -(1+a)`.
  set g : ℝ → ℂ :=
    fun y : ℝ => exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y with hg_def
  have hg_int : Integrable g :=
    kadiri_laplace_source_integrable_of_decay
      (φ := φ) hφ (b := b) hb hφ_decay (a := a) ha hab
  have hgdiff : Differentiable ℝ g :=
    kadiri_weighted_source_differentiable (φ := φ) hφ (a := a)
  -- Interval integrability of the local difference quotient of `g` at `x = log n`.
  have hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else
          (1 / (Real.pi * u) : ℂ) • (g (Real.log (n : ℝ) - u) - g (Real.log (n : ℝ))))
      volume (-(1 : ℝ)) (1 : ℝ) :=
    intervalIntegrable_local_quotient_of_differentiableAt
      (E := ℂ) (f := g) (x := Real.log (n : ℝ)) (R := (1 : ℝ)) zero_lt_one
      hgdiff.continuous.continuousOn hgdiff.differentiableAt
  -- The master truncated-limit inverse Laplace theorem applied with `σ = -(1+a)`,
  -- source `φ`, point `x = n`, window radius `R = 1`.
  have hmaster :=
    eq11_laplaceIntegralCpowTrunc_tendsto_of_integrable_local_quotient
      (sigma := (-(1 + a) : ℝ)) (f := φ) (x := (n : ℝ)) (R := (1 : ℝ))
      hx zero_lt_one hg_int hq
  -- The truncated integral defining `hinv` is exactly `laplaceIntegralCpowTrunc`.
  have hreindex :
      (fun T : ℝ =>
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t in (-T)..T,
            Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
              (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) =
        fun T : ℝ => laplaceIntegralCpowTrunc φ (-(1 + a)) (n : ℝ) T := by
    funext T
    simp only [Φ, laplaceIntegralCpowTrunc, laplaceIntegral]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _ht
    push_cast
    ring_nf
  -- The target value `φ (log n)` matches the master theorem's `φ (log x)` at `x = n`.
  rw [hreindex]
  simpa using hmaster

/-- The faithful truncated-limit form of Kadiri equation (11) (\cite{Kadiri2005},
Théorème 3.1, eq.~(11), arXiv math/0401238): the von Mangoldt sum is the `T → ∞`
limit of the truncated contour integral `kadiri_thm_3_1_q1_I φ a T` over the compact
segment `[1+a-iT, 1+a+iT]`.  Under the same `C¹` hypotheses as the stub
`kadiri_thm_3_1_q1_eq_11`, the only remaining analytic input is the single-point
truncated-limit Laplace inversion `hinv` (the displayed identity just before
\cite[(11)]{Kadiri2005}); the sum/integral exchange over the compact window and the
Tannery domination are discharged by this file, so no full-line `L¹` integrability is
needed.  This replaces the (mis-stated) absolute Bochner form `∫ t : ℝ` of the stub. -/
theorem kadiri_thm_3_1_q1_eq_11_truncated_limit_of_pointwise_inversion
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (hinv : ∀ n : Nat, 1 ≤ n →
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop (𝓝 (φ (Real.log n)))) :
    Tendsto (fun T : ℝ => kadiri_thm_3_1_q1_I φ a T) atTop
      (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) := by
  -- The bank reduction gives the limit for the interval-integral form `∫ t in (-T)..T`.
  have hbank :=
    kadiri_thm_3_1_q1_eq_11_pv_of_pointwise_inversion
      (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay (a := a) ha hab ha1 hinv
  dsimp only at hbank
  -- `kadiri_thm_3_1_q1_I` uses `∫ t in Set.Ioo (-T) T`; the bank uses `∫ t in (-T)..T`.
  -- For `T ≥ 0` these set integrals agree (`(-T)..T = Ioc (-T) T`, and `Ioo`/`Ioc`
  -- differ only on the null set `{T}`), so the two limits coincide eventually.
  refine hbank.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  have hTle : (-T) ≤ T := by linarith
  unfold kadiri_thm_3_1_q1_I
  dsimp only
  congr 1
  rw [intervalIntegral.integral_of_le hTle,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- The unconditional faithful truncated-limit form of Kadiri equation (11)
(\cite{Kadiri2005}, Théorème 3.1, eq.~(11)): the von Mangoldt sum is the `T → ∞` limit
of the truncated contour integral `kadiri_thm_3_1_q1_I φ a T`.  The single-point Laplace
inversion input is now supplied internally by `kadiri_thm_3_1_q1_pointwise_inversion`, so
this carries no analytic hypotheses beyond the `C¹` regularity and strip decay of `φ`. -/
theorem kadiri_thm_3_1_q1_eq_11_truncated_limit
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) :
    Tendsto (fun T : ℝ => kadiri_thm_3_1_q1_I φ a T) atTop
      (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) :=
  kadiri_thm_3_1_q1_eq_11_truncated_limit_of_pointwise_inversion
    (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay (a := a) ha hab ha1
    (kadiri_thm_3_1_q1_pointwise_inversion
      (φ := φ) hφ (b := b) hb hφ_decay (a := a) ha hab)

end

end Kadiri
