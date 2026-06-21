import Architect
import PrimeNumberTheoremAnd.Defs
import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting
import PrimeNumberTheoremAnd.IEANTN.HadamardLogDerivative
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import PrimeNumberTheoremAnd.LaplaceInversion
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace Kadiri

open MeasureTheory Complex
open ArithmeticFunction hiding log
open Filter
open scoped Topology
open scoped FourierTransform

@[blueprint
  "kadiri-thm-3-1-q1-I-2"
  (title := "Kadiri's $I_2(T)$: the reflected Dirichlet-series piece")
  (statement := /-- Kadiri's $I_2(T)$ from \cite[p.~12]{Kadiri2005}: the reflected
  Dirichlet-series piece of the functional-equation rewrite of the $\sigma = -a$
  integral,
  $$ I_2(T) \;:=\; \frac{1}{2\pi i} \int_{-a - iT}^{-a + iT}
                  \frac{\zeta'}{\zeta}(1-s)\, \Phi(-s)\, ds. $$

  \emph{Sign:} the $+\zeta'/\zeta(1-s)$ integrand comes from substituting the
  (corrected) functional equation
  $-\zeta'/\zeta(s) = -\log\pi + \zeta'/\zeta(1-s) + \tfrac{1}{2}\{\Gamma'/\Gamma(s/2)
  + \Gamma'/\Gamma((1-s)/2)\}$ (see \ref{kadiri-thm-3-1-q1-functional-eq}) into the
  integrand of the $\sigma = -a$ integral and reading off the middle term. The paper
  states the integrand with a leading minus, which is a typo (matching the sign typo
  in the functional equation on \cite[p.~12]{Kadiri2005}). Its $T \to \infty$ limit
  is given by \ref{kadiri-thm-3-1-q1-eq-14}. -/)
  (latexEnv := "definition")]
noncomputable def kadiri_thm_3_1_q1_I_2 (φ : ℝ → ℂ) (a T : ℝ) : ℂ :=
  let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ t in Set.Ioo (-T) T,
      (deriv riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I))) *
        Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I))


private lemma kadiri_laplace_positive_line_weight_integrable_of_continuous {ψ : ℝ → ℂ}
    (hψ : Continuous ψ) {b : ℝ}
    (hψ_decay : (fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    Integrable (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) * ψ y) := by
  let F : ℝ → ℂ := fun y => exp (-((a : ℂ) * (y : ℂ))) * ψ y
  have hF_cont : Continuous F := by
    dsimp [F]
    fun_prop
  have hF_loc : LocallyIntegrable F volume := hF_cont.locallyIntegrable
  have hshape : ∀ x : ℝ,
      ‖F x‖ = Real.exp (-(a + 1 / 2) * x) * ‖ψ x * exp ((x : ℂ) / 2)‖ := by
    intro x
    dsimp [F]
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
    have h1 : (-(↑a * ↑x) : ℂ).re = -a * x := by
      norm_num [Complex.mul_re]
    have h2 : ((x : ℂ) / 2).re = x / 2 := by
      norm_num
    rw [h1, h2]
    calc
      Real.exp (-a * x) * ‖ψ x‖
          = (Real.exp (-(a + 1 / 2) * x) * Real.exp (x / 2)) * ‖ψ x‖ := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
      _ = Real.exp (-(a + 1 / 2) * x) * (‖ψ x‖ * Real.exp (x / 2)) := by ring_nf
  have htop_decay := hψ_decay.mono (show Filter.atTop ≤ Filter.cocompact ℝ from
    atTop_le_cocompact)
  have hbot_decay := hψ_decay.mono (show Filter.atBot ≤ Filter.cocompact ℝ from
    atBot_le_cocompact)
  have htop : F =O[Filter.atTop] fun x : ℝ => Real.exp (-(a + b + 1) * x) := by
    rw [Asymptotics.isBigO_iff] at htop_decay ⊢
    obtain ⟨C, hC⟩ := htop_decay
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_gt_atTop (0 : ℝ)] with x hxC hxpos
    rw [hshape]
    calc
      Real.exp (-(a + 1 / 2) * x) * ‖ψ x * exp ((x : ℂ) / 2)‖
          ≤ Real.exp (-(a + 1 / 2) * x) *
              (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
            exact mul_le_mul_of_nonneg_left hxC (Real.exp_nonneg _)
      _ = C * ‖Real.exp (-(a + b + 1) * x)‖ := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
              abs_of_pos (Real.exp_pos _), abs_of_pos hxpos]
            calc
              Real.exp (-(a + 1 / 2) * x) * (C * Real.exp (-(1 / 2 + b) * x))
                  = C * (Real.exp (-(a + 1 / 2) * x) *
                      Real.exp (-(1 / 2 + b) * x)) := by ring_nf
              _ = C * Real.exp (-(a + 1 / 2) * x + (-(1 / 2 + b) * x)) := by
                    rw [Real.exp_add]
              _ = C * Real.exp (-(a + b + 1) * x) := by ring_nf
  have hbot : F =O[Filter.atBot] fun x : ℝ => Real.exp ((b - a) * x) := by
    rw [Asymptotics.isBigO_iff] at hbot_decay ⊢
    obtain ⟨C, hC⟩ := hbot_decay
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_lt_atBot (0 : ℝ)] with x hxC hxneg
    rw [hshape]
    calc
      Real.exp (-(a + 1 / 2) * x) * ‖ψ x * exp ((x : ℂ) / 2)‖
          ≤ Real.exp (-(a + 1 / 2) * x) *
              (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
            exact mul_le_mul_of_nonneg_left hxC (Real.exp_nonneg _)
      _ = C * ‖Real.exp ((b - a) * x)‖ := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
              abs_of_pos (Real.exp_pos _), abs_of_neg hxneg]
            calc
              Real.exp (-(a + 1 / 2) * x) * (C * Real.exp (-(1 / 2 + b) * -x))
                  = C * (Real.exp (-(a + 1 / 2) * x) *
                      Real.exp (-(1 / 2 + b) * -x)) := by ring_nf
              _ = C * Real.exp (-(a + 1 / 2) * x + (-(1 / 2 + b) * -x)) := by
                    rw [Real.exp_add]
              _ = C * Real.exp ((b - a) * x) := by ring_nf
  have htop_int : IntegrableAtFilter (fun x : ℝ => Real.exp (-(a + b + 1) * x))
      Filter.atTop volume := by
    refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
    exact exp_neg_integrableOn_Ioi 0 (show 0 < a + b + 1 by linarith)
  have hbot_int : IntegrableAtFilter (fun x : ℝ => Real.exp ((b - a) * x))
      Filter.atBot volume := by
    rw [← Filter.map_neg_atTop, measurableEmbedding_neg.integrableAtFilter_iff_comap]
    have hvol : (volume : Measure ℝ).comap Neg.neg = volume := by
      change (volume : Measure ℝ).comap (MeasurableEquiv.neg ℝ) = volume
      rw [← MeasurableEquiv.map_symm]
      simp
    rw [hvol, Function.comp_def]
    refine ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, ?_⟩
    convert exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hab) using 1
    ext x
    ring_nf
  exact hF_loc.integrable_of_isBigO_atBot_atTop hbot hbot_int htop htop_int

private lemma kadiri_laplace_positive_line_weight_integrable {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    Integrable (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) * φ y) :=
  kadiri_laplace_positive_line_weight_integrable_of_continuous hφ.continuous hφ_decay ha hab

private lemma kadiri_laplace_shifted_vertical_segment_continuousOn
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a T : ℝ} (ha : 0 < a) (hab : a < b) (_ha1 : a < 1) :
    ContinuousOn
      (fun t : ℝ =>
        let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
        let s : ℂ := ((-a : ℝ) : ℂ) + (t : ℂ) * I
        Φ (-s))
      (Set.Icc (-T) T) := by
  have h_weighted :
      Integrable (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) * φ y) :=
    kadiri_laplace_positive_line_weight_integrable hφ hφ_decay ha hab
  have hcont :=
    continuous_laplaceIntegral_verticalLine_of_integrable
      (f := φ) (sigma := a) hφ.continuous h_weighted
  refine hcont.continuousOn.congr ?_
  intro t _ht
  dsimp [laplaceIntegral]
  apply integral_congr_ae
  filter_upwards with y
  apply congrArg (fun z : ℂ => φ y * exp (-z * (y : ℂ)))
  simp [sub_eq_add_neg, add_comm]


private theorem kadiri_laplaceInvLineTrunc_laplaceTransformBilateral_eq_fourierInvTrunc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (sigma : ℝ) (f : ℝ → E) (x T : ℝ) :
    laplaceInvLineTrunc sigma (laplaceTransformBilateral f) x T =
      Complex.exp ((sigma : ℂ) * (x : ℂ)) •
        fourierInvTrunc
          (𝓕 (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y)) x T := by
  let g : ℝ → E := fun y => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y
  unfold laplaceInvLineTrunc fourierInvTrunc
  simp_rw [laplaceTransformBilateral_eq_fourier]
  simp only [one_div, mul_inv_rev, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
    I_im, mul_one, sub_self, add_zero, neg_mul, add_im, mul_im, zero_add]
  rw [show (Real.pi⁻¹ * 2⁻¹ : ℝ) = (1 / (2 * Real.pi) : ℝ) by ring]
  change (1 / (2 * Real.pi) : ℝ) •
      ∫ t in (-T)..T, Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (x : ℂ)) •
        𝓕 g (t / (2 * Real.pi)) =
      Complex.exp ((sigma : ℂ) * (x : ℂ)) •
        ((1 / (2 * Real.pi) : ℝ) •
          ∫ t in (-T)..T, Complex.exp (((t * x : ℝ) : ℂ) * I) •
            𝓕 g (t / (2 * Real.pi)))
  have hsplit :
      (∫ t in (-T)..T, Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (x : ℂ)) •
          𝓕 g (t / (2 * Real.pi))) =
        Complex.exp ((sigma : ℂ) * (x : ℂ)) •
          ∫ t in (-T)..T, Complex.exp (((t * x : ℝ) : ℂ) * I) •
            𝓕 g (t / (2 * Real.pi)) := by
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

private theorem kadiri_laplaceInvLineTrunc_tendsto_laplaceTransformBilateral_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (sigma : ℝ) (f : ℝ → E) {x : ℝ}
    (hlim : Filter.Tendsto
      (fun T : ℝ =>
        fourierInvTrunc
          (𝓕 (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y)) x T)
      Filter.atTop
      (nhds (Complex.exp (-((sigma : ℂ) * (x : ℂ))) • f x))) :
    Filter.Tendsto
      (fun T : ℝ => laplaceInvLineTrunc sigma (laplaceTransformBilateral f) x T)
      Filter.atTop (nhds (f x)) := by
  let g : ℝ → E := fun y => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y
  have hlim' : Filter.Tendsto (fun T : ℝ => fourierInvTrunc (𝓕 g) x T)
      Filter.atTop (nhds (g x)) := by
    simpa [g] using hlim
  have hscaled : Filter.Tendsto
      (fun T : ℝ =>
        Complex.exp ((sigma : ℂ) * (x : ℂ)) • fourierInvTrunc (𝓕 g) x T)
      Filter.atTop (nhds (Complex.exp ((sigma : ℂ) * (x : ℂ)) • g x)) :=
    hlim'.const_smul (Complex.exp ((sigma : ℂ) * (x : ℂ)))
  have htarget : Complex.exp ((sigma : ℂ) * (x : ℂ)) • g x = f x := by
    simp [g, ← smul_assoc, ← Complex.exp_add]
  rw [htarget] at hscaled
  refine hscaled.congr' ?_
  filter_upwards with T
  exact (kadiri_laplaceInvLineTrunc_laplaceTransformBilateral_eq_fourierInvTrunc
    sigma f x T).symm

private theorem kadiri_exp_mul_log_of_pos_eq_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    Complex.exp (s * (Real.log x : ℂ)) = (x : ℂ) ^ s := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [Complex.ofReal_log hx.le]
  congr 1
  ring

private theorem kadiri_laplaceIntegralCpowTrunc_eq_laplaceInvLineTrunc
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
    rw [← kadiri_exp_mul_log_of_pos_eq_cpow hx ((sigma : ℂ) + (t : ℂ) * I)]
    ring

private theorem kadiri_laplaceIntegralCpowTrunc_tendsto_of_integrable_local_quotient
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
          (𝓕 (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y))
          (Real.log x) T)
      Filter.atTop
      (nhds (Complex.exp (-((sigma : ℂ) * (Real.log x : ℂ))) • f (Real.log x))) := by
    exact fourierInvTrunc_tendsto_of_sinc_kernel (E := ℂ)
      (f := fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y)
      (by simpa [smul_eq_mul] using hg)
      (sinc_kernel_tendsto_of_integrable_local_quotient (E := ℂ)
        (f := fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y)
        (x := Real.log x) (R := R) (by simpa [smul_eq_mul] using hg) hR hq)
  have hline := kadiri_laplaceInvLineTrunc_tendsto_laplaceTransformBilateral_eq
    (E := ℂ) sigma f (x := Real.log x) hfourier
  refine hline.congr' ?_
  filter_upwards with T
  exact (kadiri_laplaceIntegralCpowTrunc_eq_laplaceInvLineTrunc sigma f hx T).symm

private lemma kadiri_laplace_positive_line_weight_isBigO_atBot {φ : ℝ → ℂ} {b a : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    (fun x : ℝ => exp (-((a : ℂ) * (x : ℂ))) • φ x)
      =O[Filter.atBot] fun x : ℝ => Real.exp ((b - a) * x) := by
  have hshape : ∀ x : ℝ,
      ‖exp (-((a : ℂ) * (x : ℂ))) • φ x‖ =
        Real.exp (-(a + 1 / 2) * x) * ‖φ x * exp ((x : ℂ) / 2)‖ := by
    intro x
    rw [norm_smul, Complex.norm_exp, norm_mul, Complex.norm_exp]
    have h1 : (-(↑a * ↑x) : ℂ).re = -a * x := by
      norm_num [Complex.mul_re]
    have h2 : ((x : ℂ) / 2).re = x / 2 := by
      norm_num
    rw [h1, h2]
    calc
      Real.exp (-a * x) * ‖φ x‖
          = (Real.exp (-(a + 1 / 2) * x) * Real.exp (x / 2)) * ‖φ x‖ := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
      _ = Real.exp (-(a + 1 / 2) * x) * (‖φ x‖ * Real.exp (x / 2)) := by
            ring_nf
  have hbot_decay := hφ_decay.mono (show Filter.atBot ≤ Filter.cocompact ℝ from
    atBot_le_cocompact)
  rw [Asymptotics.isBigO_iff] at hbot_decay ⊢
  obtain ⟨C, hC⟩ := hbot_decay
  refine ⟨C, ?_⟩
  filter_upwards [hC, Filter.eventually_lt_atBot (0 : ℝ)] with x hxC hxneg
  rw [hshape]
  calc
    Real.exp (-(a + 1 / 2) * x) * ‖φ x * exp ((x : ℂ) / 2)‖
        ≤ Real.exp (-(a + 1 / 2) * x) *
            (C * ‖Real.exp (-(1 / 2 + b) * |x|)‖) := by
          exact mul_le_mul_of_nonneg_left hxC (Real.exp_nonneg _)
    _ = C * ‖Real.exp ((b - a) * x)‖ := by
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
            abs_of_pos (Real.exp_pos _), abs_of_neg hxneg]
          calc
            Real.exp (-(a + 1 / 2) * x) * (C * Real.exp (-(1 / 2 + b) * -x))
                = C * (Real.exp (-(a + 1 / 2) * x) *
                    Real.exp (-(1 / 2 + b) * -x)) := by ring_nf
            _ = C * Real.exp (-(a + 1 / 2) * x + (-(1 / 2 + b) * -x)) := by
                  rw [Real.exp_add]
            _ = C * Real.exp ((b - a) * x) := by ring_nf

private lemma kadiri_laplace_positive_line_nat_inv_bounded {φ : ℝ → ℂ} {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (hab : a < b) :
    ∃ B : ℝ, ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖(fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n)‖ ≤ B := by
  let F : ℝ → ℂ := fun y => exp (-((a : ℂ) * (y : ℂ))) • φ y
  have hO : F =O[Filter.atBot] fun x : ℝ => Real.exp ((b - a) * x) := by
    simpa [F] using
      kadiri_laplace_positive_line_weight_isBigO_atBot (φ := φ) (a := a) (b := b)
        hφ_decay
  have hcomp_zero :
      Filter.Tendsto (fun x : ℝ => Real.exp ((b - a) * x)) Filter.atBot (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_pos (sub_pos.mpr hab)).2 tendsto_id)
  have hF_zero : Filter.Tendsto F Filter.atBot (nhds 0) := hO.trans_tendsto hcomp_zero
  have hlogseq :
      Filter.Tendsto (fun n : ℕ => -Real.log ((n + 2 : ℕ) : ℝ))
        Filter.atTop Filter.atBot := by
    have hnat : Filter.Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
    exact tendsto_neg_atTop_atBot.comp (Real.tendsto_log_atTop.comp hnat)
  have hseq : Filter.Tendsto
      (fun n : ℕ => ‖F (-Real.log ((n + 2 : ℕ) : ℝ))‖) Filter.atTop (nhds 0) := by
    simpa using (hF_zero.comp hlogseq).norm
  obtain ⟨B, hB⟩ := hseq.bddAbove_range
  refine ⟨B, ?_⟩
  intro n hn0 hn1
  have hn2 : 2 ≤ n := (Nat.two_le_iff n).mpr ⟨hn0, hn1⟩
  have hrepr : n - 2 + 2 = n := Nat.sub_add_cancel hn2
  have hmem : ‖F (-Real.log n)‖ ∈
      Set.range (fun k : ℕ => ‖F (-Real.log ((k + 2 : ℕ) : ℝ))‖) := by
    refine ⟨n - 2, ?_⟩
    change ‖F (-Real.log (((n - 2 + 2 : ℕ) : ℝ)))‖ = ‖F (-Real.log (n : ℝ))‖
    rw [hrepr]
  exact hB hmem

private lemma norm_boundedOn_Iic_of_tendsto_atBot_zero_of_continuous {F : ℝ → ℂ}
    (hF_cont : Continuous F) (hF_zero : Filter.Tendsto F Filter.atBot (nhds 0))
    (C : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, x ≤ C → ‖F x‖ ≤ B := by
  have hsmall : ∀ᶠ x in Filter.atBot, ‖F x‖ < 1 := by
    exact hF_zero.norm.eventually (Iio_mem_nhds (show ‖(0 : ℂ)‖ < 1 by simp))
  rw [Filter.eventually_atBot] at hsmall
  obtain ⟨A, hA⟩ := hsmall
  by_cases hAC : A ≤ C
  · have hbdd : BddAbove ((fun x : ℝ => ‖F x‖) '' Set.Icc A C) :=
      isCompact_Icc.bddAbove_image hF_cont.norm.continuousOn
    obtain ⟨M, hM⟩ := hbdd
    refine ⟨max 1 M, zero_le_one.trans (le_max_left 1 M), ?_⟩
    intro x hxC
    by_cases hxA : x ≤ A
    · exact (le_of_lt (hA x hxA)).trans (le_max_left 1 M)
    · have hxI : x ∈ Set.Icc A C := ⟨le_of_not_ge hxA, hxC⟩
      have hximg : ‖F x‖ ∈ (fun x : ℝ => ‖F x‖) '' Set.Icc A C := ⟨x, hxI, rfl⟩
      exact (hM hximg).trans (le_max_right 1 M)
  · refine ⟨1, zero_le_one, ?_⟩
    intro x hxC
    exact le_of_lt (hA x (hxC.trans (le_of_not_ge hAC)))

private lemma kadiri_laplace_positive_line_weight_boundedOn_Iic_of_continuous {ψ : ℝ → ℂ}
    (hψ : Continuous ψ) {b : ℝ}
    (hψ_decay : (fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (hab : a < b) (C : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, x ≤ C →
      ‖exp (-((a : ℂ) * (x : ℂ))) • ψ x‖ ≤ B := by
  let F : ℝ → ℂ := fun x => exp (-((a : ℂ) * (x : ℂ))) • ψ x
  have hO : F =O[Filter.atBot] fun x : ℝ => Real.exp ((b - a) * x) := by
    simpa [F] using
      kadiri_laplace_positive_line_weight_isBigO_atBot (φ := ψ) (a := a) (b := b)
        hψ_decay
  have hcomp_zero :
      Filter.Tendsto (fun x : ℝ => Real.exp ((b - a) * x)) Filter.atBot (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_pos (sub_pos.mpr hab)).2 tendsto_id)
  have hF_zero : Filter.Tendsto F Filter.atBot (nhds 0) := hO.trans_tendsto hcomp_zero
  have hF_cont : Continuous F := by
    dsimp [F]
    fun_prop
  exact norm_boundedOn_Iic_of_tendsto_atBot_zero_of_continuous hF_cont hF_zero C

/-- Continuity of the bilateral Laplace integral on the positive vertical line
`re s = a`, obtained by reflecting the shifted contour statement. -/
lemma kadiri_laplace_positive_vertical_segment_continuousOn
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a T : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) :
    ContinuousOn (fun t : ℝ => laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I))
      (Set.Icc (-T) T) := by
  have hminus := kadiri_laplace_shifted_vertical_segment_continuousOn
    (φ := φ) hφ hb hφ_decay (a := a) (T := T) ha hab ha1
  have hcomp : ContinuousOn
      (fun t : ℝ =>
        (fun u : ℝ =>
          let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
          let s : ℂ := ((-a : ℝ) : ℂ) + (u : ℂ) * I
          Φ (-s)) (-t))
      (Set.Icc (-T) T) := by
    refine hminus.comp (continuous_neg.continuousOn) ?_
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine hcomp.congr ?_
  intro t _ht
  dsimp [laplaceIntegral]
  apply integral_congr_ae
  filter_upwards with y
  apply congrArg (fun z : ℂ => φ y * exp (-z * (y : ℂ)))
  norm_num
  ring_nf

private lemma kadiri_exp_neg_mul_hasDerivAt (sigma x : ℝ) :
    HasDerivAt (fun y : ℝ => exp (-((sigma : ℂ) * (y : ℂ))))
      (-(sigma : ℂ) * exp (-((sigma : ℂ) * (x : ℂ)))) x := by
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    ((hasDerivAt_id x).ofReal_comp.const_mul (-(sigma : ℂ))).cexp

private lemma kadiri_laplace_line_weight_differentiable {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (sigma : ℝ) :
    Differentiable ℝ (fun z : ℝ => exp (-((sigma : ℂ) * (z : ℂ))) * φ z) := by
  intro y
  have hofReal : DifferentiableAt ℝ (fun z : ℝ => (z : ℂ)) y :=
    Complex.ofRealCLM.differentiable.differentiableAt
  have hlin : DifferentiableAt ℝ (fun z : ℝ => -((sigma : ℂ) * (z : ℂ))) y := by
    simpa only [neg_mul] using hofReal.const_mul (-(sigma : ℂ))
  exact hlin.cexp.mul ((hφ.differentiable (by norm_num)).differentiableAt)


private lemma kadiri_laplace_positive_line_weight_deriv_boundedOn_Iic
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (hab : a < b) (C : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, x ≤ C →
      ‖deriv (fun z : ℝ => exp (-((a : ℂ) * (z : ℂ))) * φ z) x‖ ≤ D := by
  obtain ⟨Bφ, hBφ_nonneg, hBφ⟩ :=
    kadiri_laplace_positive_line_weight_boundedOn_Iic_of_continuous
      (ψ := φ) hφ.continuous hφ_decay hab C
  obtain ⟨Bφ', hBφ'_nonneg, hBφ'⟩ :=
    kadiri_laplace_positive_line_weight_boundedOn_Iic_of_continuous
      (ψ := deriv φ) (hφ.continuous_deriv (by norm_num)) hφ'_decay hab C
  refine ⟨‖(a : ℂ)‖ * Bφ + Bφ', add_nonneg (mul_nonneg (norm_nonneg _) hBφ_nonneg)
    hBφ'_nonneg, ?_⟩
  intro x hxC
  have hderiv :
      deriv (fun z : ℝ => exp (-((a : ℂ) * (z : ℂ))) * φ z) x =
        (-(a : ℂ)) * (exp (-((a : ℂ) * (x : ℂ))) * φ x) +
          exp (-((a : ℂ) * (x : ℂ))) * deriv φ x := by
    rw [deriv_fun_mul (kadiri_exp_neg_mul_hasDerivAt a x).differentiableAt
      ((hφ.differentiable (by norm_num)) x)]
    rw [HasDerivAt.deriv (kadiri_exp_neg_mul_hasDerivAt a x)]
    ring
  rw [hderiv]
  have hφx : ‖exp (-((a : ℂ) * (x : ℂ))) * φ x‖ ≤ Bφ := by
    simpa [smul_eq_mul] using hBφ x hxC
  have hφ'x : ‖exp (-((a : ℂ) * (x : ℂ))) * deriv φ x‖ ≤ Bφ' := by
    simpa [smul_eq_mul] using hBφ' x hxC
  calc
    ‖(-(a : ℂ)) * (exp (-((a : ℂ) * (x : ℂ))) * φ x) +
        exp (-((a : ℂ) * (x : ℂ))) * deriv φ x‖
        ≤ ‖(-(a : ℂ)) * (exp (-((a : ℂ) * (x : ℂ))) * φ x)‖ +
            ‖exp (-((a : ℂ) * (x : ℂ))) * deriv φ x‖ := norm_add_le _ _
    _ ≤ ‖(a : ℂ)‖ * Bφ + Bφ' := by
      have hfirst :
          ‖(-(a : ℂ)) * (exp (-((a : ℂ) * (x : ℂ))) * φ x)‖ ≤ ‖(a : ℂ)‖ * Bφ := by
        rw [norm_mul, norm_neg]
        exact mul_le_mul_of_nonneg_left hφx (norm_nonneg _)
      exact add_le_add hfirst hφ'x

private lemma kadiri_laplace_line_local_quotient_integrable {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (sigma x : ℝ) {R : ℝ} (hR : 0 < R) :
    IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else
          (1 / (Real.pi * u) : ℂ) •
            (exp (-((sigma : ℂ) * ((x - u : ℝ) : ℂ))) * φ (x - u) -
              exp (-((sigma : ℂ) * (x : ℂ))) * φ x))
      volume (-R) R := by
  let g : ℝ → ℂ := fun y => exp (-((sigma : ℂ) * (y : ℂ))) * φ y
  have hg_cont : ContinuousOn g (Set.Icc (x - R) (x + R)) := by
    dsimp [g]
    exact (Complex.continuous_exp.comp (by continuity)).continuousOn.mul
      hφ.continuous.continuousOn
  have hg_diff : DifferentiableAt ℝ g x :=
    (kadiri_laplace_line_weight_differentiable hφ sigma) x
  simpa [g] using
    intervalIntegrable_local_quotient_of_differentiableAt (E := ℂ)
      (f := g) (x := x) hR hg_cont hg_diff


/-- Principal-value Laplace inversion on the positive line `re s = a` under
Kadiri's decay hypotheses. The target point is written as a positive real `x`. -/
lemma kadiri_laplace_positive_line_pv {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b : ℝ} (_hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a x : ℝ} (ha : 0 < a) (hab : a < b) (hx : 0 < x) :
    Filter.Tendsto (fun T : ℝ => laplaceIntegralCpowTrunc φ a x T)
      Filter.atTop (nhds (φ (Real.log x))) := by
  have h_weighted :
      Integrable (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) * φ y) :=
    kadiri_laplace_positive_line_weight_integrable hφ hφ_decay ha hab
  have hq :
      IntervalIntegrable
        (fun u : ℝ =>
          if u = 0 then 0 else
            (1 / (Real.pi * u) : ℂ) •
              (exp (-((a : ℂ) * ((Real.log x - u : ℝ) : ℂ))) *
                  φ (Real.log x - u) -
                exp (-((a : ℂ) * (Real.log x : ℂ))) *
                  φ (Real.log x)))
        volume (-1) 1 := by
    simpa using kadiri_laplace_line_local_quotient_integrable
      (φ := φ) hφ a (Real.log x) (by norm_num : (0 : ℝ) < 1)
  exact kadiri_laplaceIntegralCpowTrunc_tendsto_of_integrable_local_quotient
    (sigma := a) (f := φ) (x := x) (R := 1) hx
    (by norm_num : (0 : ℝ) < 1) h_weighted hq

lemma kadiri_laplace_positive_line_pv_nat_inv {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) {n : ℕ} (hn : n ≠ 0) :
    Filter.Tendsto (fun T : ℝ => laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T)
      Filter.atTop (nhds (φ (-Real.log n))) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hx : 0 < ((n : ℝ)⁻¹) := inv_pos.mpr hnpos
  have h := kadiri_laplace_positive_line_pv
    (φ := φ) hφ hb hφ_decay ha hab hx
  simpa [Real.log_inv] using h

private lemma kadiri_vonMangoldt_nat_inv_cpow {n : ℕ} (hn : n ≠ 0) (a t : ℝ) :
    ((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
        (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) =
      (Λ n : ℂ) /
        (((n : ℝ) : ℂ) ^ (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I))) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnC : (((n : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hnpos.ne'
  have harg : (((n : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hnpos.le]
    exact Real.pi_ne_zero.symm
  change ((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
        ((((n : ℝ) : ℂ))⁻¹ ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) =
      (Λ n : ℂ) /
        (((n : ℝ) : ℂ) ^ (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)))
  rw [Complex.inv_cpow _ _ harg]
  rw [Complex.cpow_add (x := (((n : ℝ) : ℂ))) (y := (1 : ℂ))
    (z := (((a : ℝ) : ℂ) + (t : ℂ) * I))] <;> try exact hnC
  rw [Complex.cpow_add (x := (((n : ℝ) : ℂ))) (y := ((a : ℂ)))
    (z := ((t : ℂ) * I))] <;> try exact hnC
  norm_num
  field_simp [hnC]

private lemma kadiri_summable_vonMangoldt_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (Λ n : ℂ) / (n : ℂ) ^ s) := by
  refine (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]

private lemma kadiri_summable_norm_vonMangoldt_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖(Λ n : ℂ) / (n : ℂ) ^ s‖) :=
  summable_norm_iff.mpr (kadiri_summable_vonMangoldt_cpow hs)

private lemma kadiri_norm_vonMangoldt_nat_inv_cpow_coeff_eq
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ‖(Λ n : ℂ) / (((n : ℝ) : ℂ))‖ * ((n : ℝ)⁻¹) ^ a =
      ‖(Λ n : ℂ) / (n : ℂ) ^ (((1 + a : ℝ) : ℂ))‖ := by
  by_cases hn : n = 0
  · subst n
    simp [ha.ne']
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [norm_div, norm_div]
    norm_num
    have hpowcast : (n : ℂ) ^ (1 + (a : ℂ)) =
        (((n : ℝ) : ℂ)) ^ (1 + (a : ℂ)) := by
      norm_num
    rw [hpowcast]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    rw [Real.inv_rpow hnpos.le, Real.rpow_add hnpos, Real.rpow_one]
    field_simp [hnpos.ne', (Real.rpow_pos_of_pos hnpos a).ne']

private lemma kadiri_tsum_vonMangoldt_cpow_eq {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s) =
      -deriv riemannZeta s / riemannZeta s := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, LSeries]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]

private lemma kadiri_reflected_zeta_logDeriv_mul_laplace_eq_tsum
    (φ : ℝ → ℂ) {a t : ℝ} (ha : 0 < a) :
    (deriv riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I))) *
      laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I) =
    ∑' n : ℕ,
      -(((Λ n : ℂ) /
          (n : ℂ) ^ (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I))) *
        laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)) := by
  have hs : 1 < (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)).re := by
    simp [Complex.add_re, Complex.mul_re]
    linarith
  have hsum := kadiri_tsum_vonMangoldt_cpow_eq hs
  have hder :
      deriv riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) =
        -∑' n : ℕ, (Λ n : ℂ) /
          (n : ℂ) ^ (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) := by
    rw [hsum]
    ring
  rw [hder, neg_mul]
  rw [← tsum_mul_right, ← tsum_neg]

private lemma kadiri_reflected_zeta_logDeriv_mul_laplace_eq_tsum_nat_inv
    (φ : ℝ → ℂ) {a t : ℝ} (ha : 0 < a) :
    (deriv riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I))) *
      laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I) =
    ∑' n : ℕ,
      -(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
        (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
        laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)) := by
  rw [kadiri_reflected_zeta_logDeriv_mul_laplace_eq_tsum (φ := φ) ha]
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · subst n
    simp
  · rw [kadiri_vonMangoldt_nat_inv_cpow hn a t]
    norm_num

private lemma kadiri_I2_tsum_integral_term_eq_laplace_trunc
    (φ : ℝ → ℂ) (a T : ℝ) (n : ℕ) :
    (1 / (2 * (Real.pi : ℂ))) *
      ∫ t in (-T)..T,
        -(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
          laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)) =
    -(((Λ n : ℂ) / (n : ℂ)) * laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T) := by
  let c : ℂ := (Λ n : ℂ) / (n : ℂ)
  have hint :
      (∫ t in (-T)..T,
        -(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
          laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I))) =
      (-c) * ∫ t in (-T)..T,
        laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    norm_num [c]
    ring_nf
  rw [hint, laplaceIntegralCpowTrunc]
  have hcommInt :
      (∫ t in (-T)..T,
        laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I))) =
      ∫ t in (-T)..T,
        laplaceIntegral φ (((a : ℝ) : ℂ) + I * (t : ℂ)) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + I * (t : ℂ))) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    simp [mul_comm]
  rw [hcommInt]
  norm_num [c]
  ring_nf

lemma kadiri_thm_3_1_q1_I_2_eq_reflected_interval
    (φ : ℝ → ℂ) (a : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    kadiri_thm_3_1_q1_I_2 φ a T =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ t in (-T)..T,
          (deriv riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) /
              riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I))) *
            laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I) := by
  let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
  have hle : -T ≤ T := by linarith
  have hset_to_interval :
      ∫ t in Set.Ioo (-T) T,
        (deriv riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) /
            riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I))) *
          Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I)) =
        ∫ t in (-T)..T,
          (deriv riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) /
              riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I))) *
            Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I)) := by
    rw [intervalIntegral.integral_of_le hle,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hflip :
      ∫ t in (-T)..T,
        (deriv riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) /
            riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I))) *
          Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I)) =
        ∫ t in (-T)..T,
          (deriv riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) /
              riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I))) *
            Φ (((a : ℝ) : ℂ) + (t : ℂ) * I) := by
    simpa [sub_eq_add_neg, neg_mul, add_comm, add_left_comm, add_assoc] using
      (intervalIntegral.integral_comp_neg
        (fun t : ℝ =>
          (deriv riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) /
              riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I))) *
            Φ (((a : ℝ) : ℂ) + (t : ℂ) * I))
        (a := -T) (b := T))
  rw [kadiri_thm_3_1_q1_I_2]
  dsimp only
  rw [hset_to_interval, hflip]
  congr 1

private lemma kadiri_thm_3_1_q1_I_2_eq_neg_tsum_laplace_trunc_of_integral_tsum
    (φ : ℝ → ℂ) {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T)
    (hF_int : ∀ n : ℕ,
      Integrable
        (fun t : ℝ =>
          -(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
            (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
            laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)))
        (volume.restrict (Set.Ioc (-T) T)))
    (hF_sum : Summable fun n : ℕ =>
      ∫ t in Set.Ioc (-T) T,
        ‖-(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
          laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I))‖) :
    kadiri_thm_3_1_q1_I_2 φ a T =
      -∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) *
        laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T := by
  rw [kadiri_thm_3_1_q1_I_2_eq_reflected_interval φ a hT]
  have hle : -T ≤ T := by linarith
  have hrewrite :
      ∫ t in (-T)..T,
          (deriv riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) /
              riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I))) *
            laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I) =
        ∫ t in (-T)..T,
          ∑' n : ℕ,
            -(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
              (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
              laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact kadiri_reflected_zeta_logDeriv_mul_laplace_eq_tsum_nat_inv (φ := φ) ha
  rw [hrewrite, intervalIntegral.integral_of_le hle]
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (-T) T)) hF_int hF_sum
  rw [← hswap, ← tsum_mul_left]
  rw [← tsum_neg]
  refine tsum_congr fun n => ?_
  rw [← intervalIntegral.integral_of_le hle]
  simpa using (kadiri_I2_tsum_integral_term_eq_laplace_trunc φ a T n)

private lemma kadiri_I2_tsum_summand_integrable
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a T : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) (n : ℕ) :
    Integrable
      (fun t : ℝ =>
        -(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
          laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)))
      (volume.restrict (Set.Ioc (-T) T)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hbase : (((n : ℝ)⁻¹ : ℂ)) ∈ slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simp [inv_pos.mpr hnpos]
    have hexp : Continuous fun t : ℝ => (((a : ℝ) : ℂ) + (t : ℂ) * I) := by
      fun_prop
    have hpow : ContinuousOn
        (fun t : ℝ => (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)))
        (Set.Icc (-T) T) := by
      exact (continuous_const.cpow hexp (fun _ => hbase)).continuousOn
    have hlap := kadiri_laplace_positive_vertical_segment_continuousOn
      (φ := φ) hφ hb hφ_decay (a := a) (T := T) ha hab ha1
    have hcont : ContinuousOn
        (fun t : ℝ =>
          -(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
            (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
            laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)))
        (Set.Icc (-T) T) := by
      exact ((continuousOn_const.mul hpow).mul hlap).neg
    exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

private lemma kadiri_I2_tsum_summand_norm_eq
    (φ : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (n : ℕ) (t : ℝ) :
    ‖-(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
      (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
      laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I))‖ =
    ‖(Λ n : ℂ) / (n : ℂ) ^ (((1 + a : ℝ) : ℂ))‖ *
      ‖laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [norm_neg, norm_mul, norm_mul]
    have hpow :
        ‖(((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I))‖ =
          ((n : ℝ)⁻¹) ^ a := by
      rw [← Complex.ofReal_inv]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hnpos)]
      simp [Complex.add_re, Complex.mul_re]
    rw [hpow, kadiri_norm_vonMangoldt_nat_inv_cpow_coeff_eq ha n]

private lemma kadiri_I2_tsum_summable_integral_norm
    (φ : ℝ → ℂ) {a T : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ =>
      ∫ t in Set.Ioc (-T) T,
        ‖-(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
          laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I))‖ := by
  let C : ℝ :=
    ∫ t in Set.Ioc (-T) T,
      ‖laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)‖
  have hcoeff : Summable fun n : ℕ =>
      ‖(Λ n : ℂ) / (n : ℂ) ^ (((1 + a : ℝ) : ℂ))‖ := by
    apply kadiri_summable_norm_vonMangoldt_cpow
    simp [Complex.add_re]
    linarith
  refine (hcoeff.mul_right C).congr fun n => ?_
  have hnorm :
      (fun t : ℝ =>
        ‖-(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
          laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I))‖)
        =
      (fun t : ℝ =>
        ‖(Λ n : ℂ) / (n : ℂ) ^ (((1 + a : ℝ) : ℂ))‖ *
          ‖laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)‖) := by
    funext t
    exact kadiri_I2_tsum_summand_norm_eq φ ha n t
  rw [hnorm, MeasureTheory.integral_const_mul]

private lemma kadiri_thm_3_1_q1_I_2_eq_neg_tsum_laplace_trunc
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a T : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) (hT : 0 ≤ T) :
    kadiri_thm_3_1_q1_I_2 φ a T =
      -∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) *
        laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T := by
  exact kadiri_thm_3_1_q1_I_2_eq_neg_tsum_laplace_trunc_of_integral_tsum
    φ ha hT
    (fun n => kadiri_I2_tsum_summand_integrable hφ hb hφ_decay ha hab ha1 n)
    (kadiri_I2_tsum_summable_integral_norm φ ha)

private lemma kadiri_I2_weighted_laplace_trunc_tendsto_of_dominated_bound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b)
    (bound : ℕ → ℝ) (hbound_sum : Summable bound)
    (hbound : ∀ᶠ T in Filter.atTop, ∀ n : ℕ,
      ‖((Λ n : ℂ) / (n : ℂ)) *
        laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T‖ ≤ bound n) :
    Filter.Tendsto
      (fun T : ℝ =>
        ∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) *
          laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T)
      Filter.atTop
      (nhds (∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  apply tendsto_tsum_of_dominated_convergence (bound := bound)
  · exact hbound_sum
  · intro n
    by_cases hn : n = 0
    · subst n
      simp
    · exact (kadiri_laplace_positive_line_pv_nat_inv
        (φ := φ) hφ hb hφ_decay ha hab hn).const_mul ((Λ n : ℂ) / (n : ℂ))
  · exact hbound

lemma kadiri_thm_3_1_q1_eq_14_of_weighted_laplace_trunc_tendsto
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (hlim : Filter.Tendsto
      (fun T : ℝ =>
        -∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) *
          laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n)))) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  exact (kadiri_thm_3_1_q1_I_2_eq_neg_tsum_laplace_trunc
    hφ hb hφ_decay ha hab ha1 hT).symm

lemma kadiri_thm_3_1_q1_eq_14_of_weighted_laplace_trunc_dominated_bound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (bound : ℕ → ℝ) (hbound_sum : Summable bound)
    (hbound : ∀ᶠ T in Filter.atTop, ∀ n : ℕ,
      ‖((Λ n : ℂ) / (n : ℂ)) *
        laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T‖ ≤ bound n) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  have hseries := kadiri_I2_weighted_laplace_trunc_tendsto_of_dominated_bound
    hφ hb hφ_decay ha hab bound hbound_sum hbound
  exact kadiri_thm_3_1_q1_eq_14_of_weighted_laplace_trunc_tendsto
    hφ hb hφ_decay ha hab ha1 hseries.neg

lemma kadiri_thm_3_1_q1_eq_14_of_uniform_laplace_trunc_cpow_bound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (C : ℝ)
    (hbound : ∀ᶠ T in Filter.atTop, ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T‖ ≤ C * ((n : ℝ)⁻¹) ^ a) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  let bound : ℕ → ℝ :=
    fun n => C * ‖(Λ n : ℂ) / (n : ℂ) ^ (((1 + a : ℝ) : ℂ))‖
  have hbound_sum : Summable bound := by
    have hs : 1 < (((1 + a : ℝ) : ℂ)).re := by
      simp
      linarith
    exact (kadiri_summable_norm_vonMangoldt_cpow hs).mul_left C
  have hweighted : ∀ᶠ T in Filter.atTop, ∀ n : ℕ,
      ‖((Λ n : ℂ) / (n : ℂ)) *
        laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T‖ ≤ bound n := by
    filter_upwards [hbound] with T hT n
    by_cases hn : n = 0
    · subst n
      simp [bound]
    by_cases h1 : n = 1
    · subst n
      simp [bound]
    · rw [norm_mul]
      calc
        ‖(Λ n : ℂ) / (n : ℂ)‖ *
            ‖laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T‖
            ≤ ‖(Λ n : ℂ) / (n : ℂ)‖ * (C * ((n : ℝ)⁻¹) ^ a) :=
              mul_le_mul_of_nonneg_left (hT n hn h1) (norm_nonneg _)
        _ = C * (‖(Λ n : ℂ) / (n : ℂ)‖ * ((n : ℝ)⁻¹) ^ a) := by ring
        _ = C * (‖(Λ n : ℂ) / (((n : ℝ) : ℂ))‖ * ((n : ℝ)⁻¹) ^ a) := by
          norm_num
        _ = bound n := by
          rw [kadiri_norm_vonMangoldt_nat_inv_cpow_coeff_eq ha n]
  exact kadiri_thm_3_1_q1_eq_14_of_weighted_laplace_trunc_dominated_bound
    hφ hb hφ_decay ha hab ha1 bound hbound_sum hweighted

lemma kadiri_thm_3_1_q1_eq_14_of_uniform_fourier_inv_trunc_bound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (C : ℝ)
    (hbound : ∀ᶠ T in Filter.atTop, ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖fourierInvTrunc
          (𝓕 (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y))
          (-Real.log n) T‖ ≤ C) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  refine kadiri_thm_3_1_q1_eq_14_of_uniform_laplace_trunc_cpow_bound
    hφ hb hφ_decay ha hab ha1 C ?_
  filter_upwards [hbound] with T hT n hn h1
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hxpos : 0 < ((n : ℝ)⁻¹) := inv_pos.mpr hnpos
  rw [kadiri_laplaceIntegralCpowTrunc_eq_laplaceInvLineTrunc
    (sigma := a) (f := φ) (x := ((n : ℝ)⁻¹)) hxpos T]
  rw [kadiri_laplaceInvLineTrunc_laplaceTransformBilateral_eq_fourierInvTrunc]
  rw [norm_smul]
  have hlog : Real.log ((n : ℝ)⁻¹) = -Real.log n := by
    simp [Real.log_inv]
  have hscale :
      ‖exp ((a : ℂ) * (Real.log ((n : ℝ)⁻¹) : ℂ))‖ = ((n : ℝ)⁻¹) ^ a := by
    rw [kadiri_exp_mul_log_of_pos_eq_cpow hxpos (a : ℂ)]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp
  rw [hscale]
  calc
    ((n : ℝ)⁻¹) ^ a *
        ‖fourierInvTrunc
          (𝓕 (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y))
          (Real.log ((n : ℝ)⁻¹)) T‖
        = ((n : ℝ)⁻¹) ^ a *
            ‖fourierInvTrunc
              (𝓕 (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y))
              (-Real.log n) T‖ := by rw [hlog]
    _ ≤ ((n : ℝ)⁻¹) ^ a * C :=
      mul_le_mul_of_nonneg_left (hT n hn h1)
        (Real.rpow_nonneg (inv_nonneg.mpr hnpos.le) a)
    _ ≤ C * ((n : ℝ)⁻¹) ^ a := by rw [mul_comm]

/-- Local copy of the finite-window tail bound needed by the Kadiri `I_2`
bridge. It packages the imported sine-kernel tail estimate in the exact
uniform form used below. -/
private theorem kadiri_norm_sin_div_kernel_tail_le_integral_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} (hf : Integrable f) (x T : ℝ) {R : ℝ} (hR : 0 < R) :
    ‖(∫ u : ℝ,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
          f (x - u)) -
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
            f (x - u)‖ ≤
      (1 / (Real.pi * R)) * ∫ u : ℝ, ‖f u‖ := by
  let k : ℝ → E := fun u =>
    (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) • f (x - u)
  have hk : Integrable k :=
    integrable_sin_div_kernel_smul_of_integrable (E := E) hf x T
  have hle : -R ≤ R := by linarith
  have htail_eq :
      (∫ u : ℝ,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
            f (x - u)) -
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
              f (x - u) =
        ∫ u in (Set.Ioc (-R) R)ᶜ, k u := by
    rw [intervalIntegral.integral_of_le hle]
    have hdecomp := integral_add_compl (s := Set.Ioc (-R) R) measurableSet_Ioc hk
    dsimp [k] at hdecomp
    rw [← hdecomp]
    abel
  rw [htail_eq]
  let C : ℝ := 1 / (Real.pi * R)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hfx : Integrable (fun u : ℝ => f (x - u)) := hf.comp_sub_left x
  have hbound_int : Integrable (fun u : ℝ => C * ‖f (x - u)‖) :=
    hfx.norm.const_mul C
  have hmono : ∀ᵐ u ∂(volume.restrict (Set.Ioc (-R) R)ᶜ),
      ‖k u‖ ≤ C * ‖f (x - u)‖ := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc.compl] with u hucomp
    dsimp [k, C]
    have hu_not : u ∉ Set.Ioc (-R) R := by simpa using hucomp
    have hR_abs : R ≤ |u| := le_abs_of_notMem_Ioc_neg_pos hR hu_not
    have hu_ne : u ≠ 0 := by
      intro h0
      apply hu_not
      have hzmem : (0 : ℝ) ∈ Set.Ioc (-R) R := ⟨by linarith, hR.le⟩
      simpa [h0] using hzmem
    rw [if_neg hu_ne, norm_smul]
    have hscalar : ‖(Real.sin (T * u) / (Real.pi * u) : ℂ)‖ ≤ C := by
      dsimp [C]
      rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real]
      simp only [Real.norm_eq_abs]
      rw [abs_of_pos Real.pi_pos]
      have hsin : |Real.sin (T * u)| ≤ 1 := Real.abs_sin_le_one (T * u)
      have hden : Real.pi * R ≤ Real.pi * |u| :=
        mul_le_mul_of_nonneg_left hR_abs Real.pi_pos.le
      have hden_pos : 0 < Real.pi * R := mul_pos Real.pi_pos hR
      calc
        |Real.sin (T * u)| / (Real.pi * |u|) ≤ 1 / (Real.pi * |u|) := by
          exact div_le_div_of_nonneg_right hsin
            (mul_nonneg Real.pi_pos.le (abs_nonneg u))
        _ ≤ 1 / (Real.pi * R) := by
          simpa [one_div] using inv_anti₀ hden_pos hden
    exact mul_le_mul hscalar le_rfl (norm_nonneg _) hC_nonneg
  have hnorm_le : ‖∫ u in (Set.Ioc (-R) R)ᶜ, k u‖ ≤
      ∫ u in (Set.Ioc (-R) R)ᶜ, C * ‖f (x - u)‖ := by
    calc
      ‖∫ u in (Set.Ioc (-R) R)ᶜ, k u‖
          ≤ ∫ u in (Set.Ioc (-R) R)ᶜ, ‖k u‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u in (Set.Ioc (-R) R)ᶜ, C * ‖f (x - u)‖ := by
        exact integral_mono_ae (hk.norm.mono_measure Measure.restrict_le_self)
          (hbound_int.mono_measure Measure.restrict_le_self) hmono
  have hset_le : (∫ u in (Set.Ioc (-R) R)ᶜ, C * ‖f (x - u)‖) ≤
      ∫ u : ℝ, C * ‖f (x - u)‖ := by
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun _u => mul_nonneg hC_nonneg (norm_nonneg _)) hbound_int
  have htranslate : (∫ u : ℝ, C * ‖f (x - u)‖) = C * ∫ u : ℝ, ‖f u‖ := by
    rw [integral_const_mul]
    congr 1
    calc
      (∫ u : ℝ, ‖f (x - u)‖) = ∫ u : ℝ, ‖f (x + u)‖ := by
        simpa [sub_eq_add_neg] using
          integral_neg_eq_self (f := fun u : ℝ => ‖f (x + u)‖) (μ := volume)
      _ = ∫ u : ℝ, ‖f u‖ := by
        simpa using integral_add_left_eq_self (μ := volume) (fun u : ℝ => ‖f u‖) x
  exact hnorm_le.trans (hset_le.trans_eq htranslate)

/-- Finite-height Fourier-inversion bound with the mass, local window, and tail
pieces separated in the form used by equation (14). -/
private theorem kadiri_norm_fourierInvTrunc_le_of_windowed_sin_div_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Integrable f) {x T R B L M : ℝ}
    (hT : 0 ≤ T) (hR : 0 < R)
    (hfx : ‖f x‖ ≤ B)
    (hmass : ‖∫ u in (-R)..R,
      if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)‖ ≤ M)
    (herr : IntervalIntegrable
      (fun u : ℝ =>
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
          (f (x - u) - f x)) volume (-R) R)
    (hlocal : ‖∫ u in (-R)..R,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
          (f (x - u) - f x)‖ ≤ L) :
    ‖fourierInvTrunc (𝓕 f) x T‖ ≤
      M * B + L + (1 / (Real.pi * R)) * ∫ u : ℝ, ‖f u‖ := by
  let K : ℝ → ℂ := fun u =>
    if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)
  have hwhole : fourierInvTrunc (𝓕 f) x T = ∫ u : ℝ, K u • f (x - u) := by
    rw [fourierInvTrunc_fourier_eq_sinc_kernel (E := E) hf x T hT]
    simpa [K] using normalized_sinc_kernel_integral_comp_sub_left_sin_div_ae (E := E) f x T
  have hconst : IntervalIntegrable (fun u : ℝ => K u • f x) volume (-R) R := by
    simpa [K] using intervalIntegrable_sin_div_kernel_smul_const (E := E) (f x) T (-R) R
  have hsplit := intervalIntegral_sin_div_kernel_split (E := E) f x T R hconst
    (by simpa [K] using herr)
  have hwindow_bound : ‖∫ u in (-R)..R, K u • f (x - u)‖ ≤ M * B + L := by
    calc
      ‖∫ u in (-R)..R, K u • f (x - u)‖
          = ‖(∫ u in (-R)..R, K u) • f x +
              ∫ u in (-R)..R, K u • (f (x - u) - f x)‖ := by
            rw [show (∫ u in (-R)..R, K u • f (x - u)) =
                (∫ u in (-R)..R, K u) • f x +
                ∫ u in (-R)..R, K u • (f (x - u) - f x) by simpa [K] using hsplit]
      _ ≤ ‖(∫ u in (-R)..R, K u) • f x‖ +
            ‖∫ u in (-R)..R, K u • (f (x - u) - f x)‖ := norm_add_le _ _
      _ ≤ M * B + L := by
        have hM_nonneg : 0 ≤ M := le_trans (norm_nonneg _) hmass
        have hterm : ‖(∫ u in (-R)..R, K u) • f x‖ ≤ M * B := by
          rw [norm_smul]
          exact mul_le_mul (by simpa [K] using hmass) hfx (norm_nonneg _) hM_nonneg
        have hloc : ‖∫ u in (-R)..R, K u • (f (x - u) - f x)‖ ≤ L := by
          simpa [K] using hlocal
        linarith
  have htail := kadiri_norm_sin_div_kernel_tail_le_integral_norm (E := E) hf x T hR
  rw [hwhole]
  let W : E := ∫ u in (-R)..R, K u • f (x - u)
  let Tail : E := (∫ u : ℝ, K u • f (x - u)) - W
  have hdecomp : (∫ u : ℝ, K u • f (x - u)) = W + Tail := by
    dsimp [W, Tail]
    abel
  calc
    ‖∫ u : ℝ, K u • f (x - u)‖ = ‖W + Tail‖ := by rw [hdecomp]
    _ ≤ ‖W‖ + ‖Tail‖ := norm_add_le _ _
    _ ≤ (M * B + L) + (1 / (Real.pi * R)) * ∫ u : ℝ, ‖f u‖ := by
      have hW : ‖W‖ ≤ M * B + L := by simpa [W] using hwindow_bound
      have hTail : ‖Tail‖ ≤ (1 / (Real.pi * R)) * ∫ u : ℝ, ‖f u‖ := by
        dsimp [Tail, W, K]
        simpa [K] using htail
      linarith
    _ = M * B + L + (1 / (Real.pi * R)) * ∫ u : ℝ, ‖f u‖ := by ring

/-- The scalar finite-window sine-kernel mass is eventually bounded by `2`. -/
private theorem kadiri_eventually_norm_intervalIntegral_sin_div_kernel_scalar_mass_le_two
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ T in Filter.atTop,
      ‖∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)‖ ≤ 2 := by
  have hlim := tendsto_intervalIntegral_sin_div_kernel_scalar_mass hR
  have hnear : ∀ᶠ T in Filter.atTop,
      dist (∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) (1 : ℂ) < 1 :=
    hlim.eventually (Metric.ball_mem_nhds (1 : ℂ) zero_lt_one)
  filter_upwards [hnear] with T hT
  have hnorm_sub : ‖(∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) -
        (1 : ℂ)‖ < 1 := by
    simpa [dist_eq_norm] using hT
  calc
    ‖∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)‖
        = ‖(1 : ℂ) + ((∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) -
          (1 : ℂ))‖ := by
            congr 1
            abel
    _ ≤ ‖(1 : ℂ)‖ + ‖(∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) -
          (1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 := by
      have hle : ‖(∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) -
          (1 : ℂ)‖ ≤ 1 := le_of_lt hnorm_sub
      norm_num at hle ⊢
      linarith

/-- Kadiri-side bridge from windowed Fourier bounds to equation (14). It leaves
only a source bound and a local principal-value window bound as application
inputs; the mass and far-field tail are handled by `LaplaceInversion`. -/
lemma kadiri_thm_3_1_q1_eq_14_of_windowed_fourier_source_bounds
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a R B L M : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) (hR : 0 < R)
    (hsource : ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖(fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n)‖ ≤ B)
    (hmass : ∀ᶠ T in Filter.atTop,
      ‖∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)‖ ≤ M)
    (hlocal : ∀ᶠ T in Filter.atTop, ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
            ((fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n - u) -
              (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n))‖ ≤ L) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  let F : ℝ → ℂ := fun y => exp (-((a : ℂ) * (y : ℂ))) • φ y
  have hF_int : Integrable F := by
    have hF_mul :
        Integrable (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) * φ y) :=
      kadiri_laplace_positive_line_weight_integrable hφ hφ_decay ha hab
    simpa [F, smul_eq_mul] using hF_mul
  refine kadiri_thm_3_1_q1_eq_14_of_uniform_fourier_inv_trunc_bound
    hφ hb hφ_decay ha hab ha1
    (M * B + L + (1 / (Real.pi * R)) * ∫ u : ℝ, ‖F u‖) ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ), hmass, hlocal] with
    T hT hmassT hlocalT n hn h1
  have hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else (1 / (Real.pi * u) : ℂ) • (F (-Real.log n - u) -
          F (-Real.log n)))
      volume (-R) R := by
    have hq0 := kadiri_laplace_line_local_quotient_integrable
      (φ := φ) hφ a (-Real.log n) hR
    simpa [F, smul_eq_mul] using hq0
  have herr : IntervalIntegrable
      (fun u : ℝ =>
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
          (F (-Real.log n - u) - F (-Real.log n)))
      volume (-R) R :=
    intervalIntegrable_sin_div_kernel_error_of_intervalIntegrable_quotient
      (E := ℂ) hq T
  simpa [F] using
    kadiri_norm_fourierInvTrunc_le_of_windowed_sin_div_bounds (E := ℂ) hF_int hT hR
      (hsource n hn h1) hmassT herr (hlocalT n hn h1)

/-- Kadiri-side bridge from source and local-window bounds to equation (14),
with the scalar finite-window mass discharged by the sinc mass limit. -/
lemma kadiri_thm_3_1_q1_eq_14_of_windowed_fourier_source_local_bounds
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a R B L : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) (hR : 0 < R)
    (hsource : ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖(fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n)‖ ≤ B)
    (hlocal : ∀ᶠ T in Filter.atTop, ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
            ((fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n - u) -
              (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n))‖ ≤ L) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) :=
  kadiri_thm_3_1_q1_eq_14_of_windowed_fourier_source_bounds
    hφ hb hφ_decay ha hab ha1 hR hsource
    (kadiri_eventually_norm_intervalIntegral_sin_div_kernel_scalar_mass_le_two hR)
    hlocal

/-- Kadiri-side bridge from the remaining local-window bound to equation (14).
The weighted source bound and scalar mass bound are discharged here. -/
lemma kadiri_thm_3_1_q1_eq_14_of_windowed_fourier_local_bound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a R L : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) (hR : 0 < R)
    (hlocal : ∀ᶠ T in Filter.atTop, ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
            ((fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n - u) -
              (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n))‖ ≤ L) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  obtain ⟨B, hsource⟩ :=
    kadiri_laplace_positive_line_nat_inv_bounded (φ := φ) hφ_decay hab
  exact kadiri_thm_3_1_q1_eq_14_of_windowed_fourier_source_local_bounds
    hφ hb hφ_decay ha hab ha1 hR hsource hlocal

private lemma kadiri_laplace_positive_line_local_window_bound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a R : ℝ} (hab : a < b) (hR : 0 < R) :
    ∃ L : ℝ, ∀ᶠ T in Filter.atTop, ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
            ((fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n - u) -
              (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n))‖ ≤ L := by
  let C : ℝ := -Real.log (2 : ℝ) + R
  let F : ℝ → ℂ := fun y => exp (-((a : ℂ) * (y : ℂ))) • φ y
  obtain ⟨D, hD_nonneg, hD⟩ :=
    kadiri_laplace_positive_line_weight_deriv_boundedOn_Iic
      (φ := φ) hφ hφ_decay hφ'_decay hab C
  refine ⟨(D / Real.pi) * |R - (-R)|, Filter.Eventually.of_forall ?_⟩
  intro T n hn0 hn1
  have hn2 : 2 ≤ n := (Nat.two_le_iff n).mpr ⟨hn0, hn1⟩
  have hn2_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hlog_le : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) hn2_real
  let x : ℝ := -Real.log (n : ℝ)
  have hx_le : x ≤ -Real.log (2 : ℝ) := by
    dsimp [x]
    linarith
  have hxC : x ≤ C := by
    dsimp [C]
    linarith
  have hle : -R ≤ R := by linarith
  have hderiv_bound : ∀ y ∈ Set.Iic C, ‖deriv F y‖ ≤ D := by
    intro y hy
    simpa [F, smul_eq_mul] using hD y hy
  have hbound : ∀ u ∈ Set.uIoc (-R) R,
      ‖(if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
          (F (x - u) - F x)‖ ≤ D / Real.pi := by
    intro u hu
    have huIoc : u ∈ Set.Ioc (-R) R := by
      simpa [Set.uIoc_of_le hle] using hu
    have hxuC : x - u ≤ C := by
      have hneg_u_le : -u ≤ R := by linarith [huIoc.1]
      dsimp [C]
      linarith
    have hx_mem : x ∈ Set.Iic C := hxC
    have hxu_mem : x - u ∈ Set.Iic C := hxuC
    have hdiff :
        ‖F (x - u) - F x‖ ≤ D * ‖(x - u) - x‖ := by
      exact Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
        (s := Set.Iic C) (f := F) (C := D)
        (fun y _hy => by
          simpa [F, smul_eq_mul] using (kadiri_laplace_line_weight_differentiable hφ a y))
        hderiv_bound (convex_Iic C) hx_mem hxu_mem
    have hdist : ‖(x - u) - x‖ = |u| := by
      rw [Real.norm_eq_abs]
      ring_nf
      rw [abs_neg]
    have hdiff_abs : ‖F (x - u) - F x‖ ≤ D * |u| := by
      simpa [hdist] using hdiff
    have hq_bound :
        ‖(if u = 0 then 0 else (1 / (Real.pi * u) : ℂ) • (F (x - u) - F x))‖
          ≤ D / Real.pi := by
      by_cases hu0 : u = 0
      · rw [if_pos hu0]
        simpa using div_nonneg hD_nonneg Real.pi_pos.le
      · rw [if_neg hu0, norm_smul]
        have huabs_pos : 0 < |u| := abs_pos.mpr hu0
        have hscalar :
            ‖(1 / (Real.pi * u) : ℂ)‖ = 1 / (Real.pi * |u|) := by
          rw [norm_div, norm_one, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        calc
          ‖(1 / (Real.pi * u) : ℂ)‖ * ‖F (x - u) - F x‖
              = (1 / (Real.pi * |u|)) * ‖F (x - u) - F x‖ := by rw [hscalar]
          _ ≤ (1 / (Real.pi * |u|)) * (D * |u|) := by
            exact mul_le_mul_of_nonneg_left hdiff_abs
              (div_nonneg zero_le_one (mul_nonneg Real.pi_pos.le (abs_nonneg u)))
          _ = D / Real.pi := by
            field_simp [Real.pi_ne_zero, ne_of_gt huabs_pos]
    have hsin_norm : ‖(Real.sin (T * u) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_sin_le_one (T * u)
    rw [sin_div_kernel_sub_eq_sin_smul_quotient (E := ℂ) F x T u, norm_smul]
    calc
      ‖(Real.sin (T * u) : ℂ)‖ *
          ‖if u = 0 then 0 else (1 / (Real.pi * u) : ℂ) • (F (x - u) - F x)‖
          ≤ 1 * (D / Real.pi) :=
            mul_le_mul hsin_norm hq_bound (norm_nonneg _) zero_le_one
      _ = D / Real.pi := by ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -R) (b := R) (C := D / Real.pi)
    (f := fun u : ℝ =>
      (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
        (F (x - u) - F x)) hbound
  simpa [F, x] using hnorm

theorem kadiri_thm_3_1_q1_eq_14_core
    {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (_ha : 0 < a) (_hab : a < b) (_ha1 : a < 1) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  obtain ⟨L, hlocal⟩ :=
    kadiri_laplace_positive_line_local_window_bound
      (φ := φ) _hφ _hφ_decay _hφ'_decay _hab (R := 1) (by norm_num)
  exact kadiri_thm_3_1_q1_eq_14_of_windowed_fourier_local_bound
    _hφ _hb _hφ_decay _ha _hab _ha1 (R := 1) (L := L) (by norm_num) hlocal

end Kadiri
