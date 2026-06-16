import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import PrimeNumberTheoremAnd.LaplaceInversion

/-!
# Kadiri Laplace inversion bridge

This file specializes the proved bilateral Laplace inversion payload to the
vertical line used in Kadiri's Theorem 3.1, q = 1.
-/

open Real Complex MeasureTheory Filter FourierTransform

noncomputable section

namespace Kadiri

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
    convert (MeasurableEquiv.neg ℝ).map_symm.symm using 1
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

/-- Kadiri's cocompact decay hypothesis gives integrability of the weighted
source on the line `σ = -(1 + a)` whenever `0 < a < b`. -/
theorem kadiri_laplace_source_integrable_of_decay {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
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

/-- The Kadiri vertical-line specialization of the proved cpow Laplace
inversion payload, still in symmetric truncated form. The remaining bridge to
`kadiri_thm_3_1_q1_laplace_inversion` is the conversion from this principal-value
limit to the full Bochner integral over `ℝ`. -/
theorem kadiri_laplace_inversion_bridge_trunc_payload {φ : ℝ → ℂ}
    {a : ℝ} (_ha : 0 < a) {n : ℕ} (hn : 1 ≤ n)
    (hg : Integrable
      (fun y : ℝ =>
        exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y))
    (hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else
          (1 / (π * u) : ℂ) •
            (exp (-(((-(1 + a) : ℝ) : ℂ) *
                  (((n : ℝ).log - u : ℝ) : ℂ))) *
                φ ((n : ℝ).log - u) -
              exp (-(((-(1 + a) : ℝ) : ℂ) * ((n : ℝ).log : ℂ))) *
                φ (n : ℝ).log))
      volume (-1) 1) :
    Tendsto
      (fun T : ℝ => laplaceIntegralCpowTrunc φ (-(1 + a)) (n : ℝ) T)
      atTop (nhds (φ (Real.log (n : ℝ)))) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hR : (0 : ℝ) < 1 := by norm_num
  exact
    laplaceIntegralCpowTrunc_tendsto_of_integrable_local_quotient
      (sigma := -(1 + a)) (f := φ) (x := (n : ℝ)) (R := 1)
      hnpos hR hg hq

/-- The same payload specialization with `laplaceIntegralCpowTrunc` expanded to
the vertical-line integral notation used in Kadiri's statement. -/
theorem kadiri_laplace_inversion_bridge_trunc_integral {φ : ℝ → ℂ}
    {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n)
    (hg : Integrable
      (fun y : ℝ =>
        exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y))
    (hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else
          (1 / (π * u) : ℂ) •
            (exp (-(((-(1 + a) : ℝ) : ℂ) *
                  (((n : ℝ).log - u : ℝ) : ℂ))) *
                φ ((n : ℝ).log - u) -
              exp (-(((-(1 + a) : ℝ) : ℂ) * ((n : ℝ).log : ℂ))) *
                φ (n : ℝ).log))
      volume (-1) 1) :
    Tendsto
      (fun T : ℝ =>
        (1 / (2 * (π : ℂ))) *
          ∫ t in (-T)..T,
            (∫ y : ℝ,
              φ y *
                exp (-((((-(1 + a) : ℝ) : ℂ) + (t : ℂ) * I)) * (y : ℂ))) *
              ((n : ℂ) ^ (((-(1 + a) : ℝ) : ℂ) + (t : ℂ) * I)))
      atTop (nhds (φ (Real.log (n : ℝ)))) := by
  have h :=
    kadiri_laplace_inversion_bridge_trunc_payload
      (φ := φ) (a := a) ha (n := n) hn hg hq
  unfold laplaceIntegralCpowTrunc laplaceIntegral at h
  refine h.congr' ?_
  filter_upwards with T
  congr 1

/-- `ContDiff ℝ 1` supplies the local quotient hypothesis required by the
principal-value payload. The global source integrability remains explicit. -/
theorem kadiri_laplace_inversion_bridge_trunc_integral_of_contDiff {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n)
    (hg : Integrable
      (fun y : ℝ =>
        exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y)) :
    Tendsto
      (fun T : ℝ =>
        (1 / (2 * (π : ℂ))) *
          ∫ t in (-T)..T,
            (∫ y : ℝ,
              φ y *
                exp (-((((-(1 + a) : ℝ) : ℂ) + (t : ℂ) * I)) * (y : ℂ))) *
              ((n : ℂ) ^ (((-(1 + a) : ℝ) : ℂ) + (t : ℂ) * I)))
      atTop (nhds (φ (Real.log (n : ℝ)))) := by
  let g : ℝ → ℂ := fun y =>
    exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y
  have hg_cd : ContDiff ℝ 1 g := by
    dsimp [g]
    exact (laplaceKernel_contDiff_paren (((-(1 + a) : ℝ) : ℂ))).mul hφ
  have hg_cont :
      ContinuousOn g (Set.Icc (Real.log (n : ℝ) - 1) (Real.log (n : ℝ) + 1)) :=
    hg_cd.continuous.continuousOn
  have hg_diff : DifferentiableAt ℝ g (Real.log (n : ℝ)) :=
    (hg_cd.differentiable one_ne_zero).differentiableAt
  have hq := intervalIntegrable_local_quotient_of_differentiableAt
    (E := ℂ) (f := g) (x := Real.log (n : ℝ)) (R := 1) (by norm_num) hg_cont hg_diff
  simpa [g] using
    kadiri_laplace_inversion_bridge_trunc_integral
      (φ := φ) (a := a) ha (n := n) hn hg hq

/-- Kadiri's q = 1 Laplace inversion bridge in the Perron-style
symmetric-truncated form. Finite-height exchanges should be made before
passing to this `Tendsto` limit. -/
theorem kadiri_laplace_inversion_bridge {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (_ha1 : a < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Tendsto
      (fun T : ℝ =>
        (1 / (2 * (π : ℂ))) *
          ∫ t in (-T)..T,
            Φ (((-(1 + a) : ℝ) : ℂ) + (t : ℂ) * I) *
              ((n : ℂ) ^ (((-(1 + a) : ℝ) : ℂ) + (t : ℂ) * I)))
      atTop (nhds (φ (Real.log n))) := by
  dsimp only
  have hg := kadiri_laplace_source_integrable_of_decay
    (φ := φ) hφ (b := b) hb hφ_decay (a := a) ha hab
  simpa using
    kadiri_laplace_inversion_bridge_trunc_integral_of_contDiff
      (φ := φ) hφ (a := a) ha (n := n) hn hg

end Kadiri
