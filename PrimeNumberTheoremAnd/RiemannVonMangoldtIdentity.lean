import PrimeNumberTheoremAnd.RectangleArgumentPrinciple
import PrimeNumberTheoremAnd.IEANTN.KadiriEq12Helpers
import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.CompletedXi
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.PhaseBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Riemann xi rectangle count

This file specializes the rectangle logarithmic-derivative identity to Riemann's
entire xi function.  The later Riemann-von-Mangoldt main-term extraction needs
phase-level Stirling estimates for `Complex.Gamma`; this file records the
divisor-counting layer that sits below that extraction.

The next analytic brick is an unwrapped log-Gamma Stirling estimate at
`z = 1 / 4 + (T / 2) * I`.  The local Gamma API currently has norm growth
bounds and the `logGammaSeq`/digamma construction, but not a reusable theorem
of the following shape, where the logarithm is the `logGammaSeq` limit branch:

`| (Filter.limUnder Filter.atTop (Complex.logGammaSeq z)).im -
    ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8
      + (T / 4) * Real.log (1 + 1 / (4 * T ^ 2))
      + (1 / 4) * Real.arctan (1 / (2 * T))) | ≤ 1 / (3 * T)`.
-/

open Complex Set BigOperators Filter Topology

noncomputable section

/-- The classical main term in the Riemann-von Mangoldt zero-counting formula. -/
def riemannVonMangoldtMainTerm (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8

/--
The unwrapped zeta log-derivative integral along the top edge used in the
Riemann-von Mangoldt bridge.

The orientation is from `2 + iT` to `1 / 2 + iT`, matching the classical
argument variation `arg ζ(1 / 2 + iT) - arg ζ(2 + iT)` but without taking
principal endpoint arguments.
-/
def riemannVonMangoldtZetaTopLogDerivIntegral (T : ℝ) : ℂ :=
  HIntegral (logDeriv riemannZeta) 2 (1 / 2) T

/--
The unwrapped zeta log-derivative integral along the classical Riemann-von
Mangoldt zeta contour: up the line `Re s = 2` from height `0` to `T`, then
left along the top edge to `1 / 2 + iT`.
-/
def riemannVonMangoldtZetaContourLogDerivIntegral (T : ℝ) : ℂ :=
  VIntegral (logDeriv riemannZeta) 2 0 T +
    riemannVonMangoldtZetaTopLogDerivIntegral T

/--
The unwrapped zeta-argument term used by the L0 Riemann-von Mangoldt bridge.

This is the contour argument contribution, not a principal `Complex.arg`
endpoint difference.
-/
def riemannVonMangoldtS (T : ℝ) : ℝ :=
  (1 / Real.pi) * (riemannVonMangoldtZetaContourLogDerivIntegral T).im

theorem riemannVonMangoldtS_eq_zetaContourLogDerivIntegral_im (T : ℝ) :
    riemannVonMangoldtS T =
      (1 / Real.pi) * (riemannVonMangoldtZetaContourLogDerivIntegral T).im :=
  rfl

theorem riemannVonMangoldtS_eq_zetaVertical_add_top_im (T : ℝ) :
    riemannVonMangoldtS T =
      (1 / Real.pi) *
        (VIntegral (logDeriv riemannZeta) 2 0 T +
          riemannVonMangoldtZetaTopLogDerivIntegral T).im :=
  rfl

/-- `N(T)` as a finite order-weighted sum over the positive-height zero window. -/
theorem riemannZeta_N_eq_toFinset_sum_order (T : ℝ) :
    riemannZeta.N T =
      ∑ ρ ∈ (Kadiri.zeroes_rect_univ_positive_height_finite T).toFinset,
        (riemannZeta.order ρ : ℝ) := by
  rw [riemannZeta.N]
  rw [zeroes_sum_eq_toFinset_sum (fun _ : ℂ => (1 : ℝ))
    (Kadiri.zeroes_rect_univ_positive_height_finite T)]
  simp

private lemma ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s ≠ 0 := by
  intro h
  exact hs (by simp [h])

private lemma ne_one_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s ≠ 1 := by
  intro h
  exact hs (by simp [h])

private lemma Gammaℝ_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    Gammaℝ s ≠ 0 := by
  rw [ne_eq, Gammaℝ_eq_zero_iff, not_exists]
  intro n hn
  exact hs (by simp [hn])

private lemma analyticAt_Gamma_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    AnalyticAt ℂ Gamma s := by
  let U : Set ℂ := {z | z.im ≠ 0}
  have hU_open : IsOpen U := by
    have hU : U = Complex.im ⁻¹' ({0}ᶜ : Set ℝ) := by
      ext z
      simp [U]
    rw [hU]
    exact isOpen_compl_singleton.preimage continuous_im
  have hdiff : DifferentiableOn ℂ Gamma U := by
    intro z hz
    exact (Complex.differentiableAt_Gamma z (fun n hn => by
      have him : z.im = 0 := by
        rw [hn]
        simp
      exact hz him)).differentiableWithinAt
  exact (hdiff.analyticOnNhd hU_open) s hs

private lemma analyticAt_Gammaℝ_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    AnalyticAt ℂ Gammaℝ s := by
  rw [show Gammaℝ = fun z ↦ (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) from
    funext Gammaℝ_def]
  refine AnalyticAt.mul ?_ ?_
  · rw [show (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2)) =
        fun z ↦ Complex.exp (Complex.log (Real.pi : ℂ) * (-z / 2)) from by
      funext z
      rw [Complex.cpow_def_of_ne_zero (by simp [Real.pi_ne_zero])]]
    fun_prop
  · have hhalf_im : (s / 2).im ≠ 0 := by
      intro h
      have h' : s.im / 2 = 0 := by
        simpa using h
      exact hs (by linarith)
    simpa [Function.comp_def] using
      AnalyticAt.comp_of_eq
        (g := Complex.Gamma) (f := fun z : ℂ => z / 2) (x := s) (y := s / 2)
        (analyticAt_Gamma_of_im_ne_zero hhalf_im)
        (analyticAt_id.div_const (c := (2 : ℂ)))
        rfl

/-- The Gamma-polynomial prefactor in `ξ(s) = G(s) ζ(s)` away from the real axis. -/
def riemannVonMangoldtXiPrefactor (s : ℂ) : ℂ :=
  s * (s - 1) * Gammaℝ s / 2

private lemma analyticAt_riemannVonMangoldtXiPrefactor_of_im_ne_zero {s : ℂ}
    (hs : s.im ≠ 0) :
    AnalyticAt ℂ riemannVonMangoldtXiPrefactor s := by
  unfold riemannVonMangoldtXiPrefactor
  exact (((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul
    (analyticAt_Gammaℝ_of_im_ne_zero hs)).div_const (c := (2 : ℂ)))

private lemma riemannVonMangoldtXiPrefactor_ne_zero_of_im_ne_zero {s : ℂ}
    (hs : s.im ≠ 0) :
    riemannVonMangoldtXiPrefactor s ≠ 0 := by
  unfold riemannVonMangoldtXiPrefactor
  exact div_ne_zero
    (mul_ne_zero
      (mul_ne_zero (ne_zero_of_im_ne_zero hs)
        (sub_ne_zero.mpr (ne_one_of_im_ne_zero hs)))
      (Gammaℝ_ne_zero_of_im_ne_zero hs))
    (by norm_num)

/--
Away from the real axis, `ξ` is `ζ` times the nonzero Gamma-polynomial factor appearing in
the completed zeta function.
-/
theorem riemannXi_eq_zeta_mul_gamma_factor_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    riemannXi s = (s * (s - 1) * Gammaℝ s / 2) * riemannZeta s := by
  have hs0 : s ≠ 0 := ne_zero_of_im_ne_zero hs
  have hs1 : s ≠ 1 := ne_one_of_im_ne_zero hs
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_im_ne_zero hs
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1]
  rw [riemannZeta_def_of_ne_zero hs0]
  field_simp [hΓ]

/--
Pointwise logarithmic-derivative split for `ξ = G ζ` away from the real axis and away
from zeros of `ζ`.
-/
theorem logDeriv_riemannXi_eq_prefactor_add_zeta_of_im_ne_zero {s : ℂ}
    (hs : s.im ≠ 0) (hzeta : riemannZeta s ≠ 0) :
    logDeriv riemannXi s =
      logDeriv riemannVonMangoldtXiPrefactor s + logDeriv riemannZeta s := by
  let G : ℂ → ℂ := riemannVonMangoldtXiPrefactor
  have hG_ne : G s ≠ 0 :=
    riemannVonMangoldtXiPrefactor_ne_zero_of_im_ne_zero hs
  have hG_diff : DifferentiableAt ℂ G s :=
    (analyticAt_riemannVonMangoldtXiPrefactor_of_im_ne_zero hs).differentiableAt
  have hzeta_diff : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta (ne_one_of_im_ne_zero hs)
  have him_nhds : ∀ᶠ z in 𝓝 s, z.im ≠ 0 :=
    (continuous_im.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hs
  have hxi_eq : riemannXi =ᶠ[𝓝 s] fun z => G z * riemannZeta z := by
    filter_upwards [him_nhds] with z hz
    simpa [G, riemannVonMangoldtXiPrefactor] using
      riemannXi_eq_zeta_mul_gamma_factor_of_im_ne_zero hz
  calc
    logDeriv riemannXi s = logDeriv (fun z => G z * riemannZeta z) s := by
      rw [logDeriv_apply, logDeriv_apply]
      rw [hxi_eq.deriv_eq, hxi_eq.eq_of_nhds]
    _ = logDeriv G s + logDeriv riemannZeta s :=
      logDeriv_mul s hG_ne hzeta hG_diff hzeta_diff

/-- Away from the real axis, `ξ` and `ζ` have the same zero set. -/
theorem riemannXi_eq_zero_iff_riemannZeta_eq_zero_of_im_ne_zero {s : ℂ}
    (hs : s.im ≠ 0) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := ne_zero_of_im_ne_zero hs
  have hs1 : s ≠ 1 := ne_one_of_im_ne_zero hs
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_im_ne_zero hs
  have hfactor : s * (s - 1) * Gammaℝ s / 2 ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hΓ) (by norm_num)
  rw [riemannXi_eq_zeta_mul_gamma_factor_of_im_ne_zero hs]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hfactor
  · intro h
    simp [h]

/-- Away from the real axis, `ξ` and `ζ` have the same meromorphic order. -/
theorem meromorphicOrderAt_riemannXi_eq_riemannZeta_of_im_ne_zero {s : ℂ}
    (hs : s.im ≠ 0) :
    meromorphicOrderAt riemannXi s = meromorphicOrderAt riemannZeta s := by
  let G : ℂ → ℂ := riemannVonMangoldtXiPrefactor
  have hG_an : AnalyticAt ℂ G s :=
    analyticAt_riemannVonMangoldtXiPrefactor_of_im_ne_zero hs
  have hG_ne : G s ≠ 0 :=
    riemannVonMangoldtXiPrefactor_ne_zero_of_im_ne_zero hs
  have him_nhds : ∀ᶠ z in 𝓝 s, z.im ≠ 0 :=
    (continuous_im.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hs
  have hxi_eq : riemannXi =ᶠ[𝓝[≠] s] fun z => G z * riemannZeta z := by
    filter_upwards [him_nhds.filter_mono nhdsWithin_le_nhds] with z hz
    simpa [G, riemannVonMangoldtXiPrefactor] using
      riemannXi_eq_zeta_mul_gamma_factor_of_im_ne_zero hz
  calc
    meromorphicOrderAt riemannXi s =
        meromorphicOrderAt (fun z => G z * riemannZeta z) s :=
      meromorphicOrderAt_congr hxi_eq
    _ = meromorphicOrderAt riemannZeta s :=
      meromorphicOrderAt_mul_of_ne_zero (f := riemannZeta) hG_an hG_ne

/-- The lower-left corner of the positive-height Riemann-von Mangoldt counting rectangle. -/
def riemannVonMangoldtCountingRectangleLower : ℂ :=
  0

/-- The upper-right corner of the positive-height Riemann-von Mangoldt counting rectangle. -/
def riemannVonMangoldtCountingRectangleUpper (T : ℝ) : ℂ :=
  (1 : ℂ) + ((T : ℝ) : ℂ) * I

private lemma riemannVonMangoldtCountingRectangle_mem_iff {T : ℝ} (hT : 0 ≤ T) {s : ℂ} :
    s ∈ Rectangle riemannVonMangoldtCountingRectangleLower
        (riemannVonMangoldtCountingRectangleUpper T) ↔
      0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T := by
  change s ∈ Rectangle (0 : ℂ) ((1 : ℂ) + ((T : ℝ) : ℂ) * I) ↔
    0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ T
  simpa using
    (mem_Rect (z := (0 : ℂ)) (w := (1 : ℂ) + ((T : ℝ) : ℂ) * I)
      (p := s) (by norm_num) (by simpa using hT))

private lemma riemannVonMangoldtCountingRectangle_not_border_im_pos {T : ℝ} (hT : 0 ≤ T)
    {s : ℂ}
    (hs_rect : s ∈ Rectangle riemannVonMangoldtCountingRectangleLower
      (riemannVonMangoldtCountingRectangleUpper T))
    (hs_not_border : s ∉ RectangleBorder riemannVonMangoldtCountingRectangleLower
      (riemannVonMangoldtCountingRectangleUpper T)) :
    0 < s.im := by
  have hs_bounds :=
    (riemannVonMangoldtCountingRectangle_mem_iff (T := T) hT).1 hs_rect
  refine lt_of_le_of_ne hs_bounds.2.2.1 ?_
  intro hzero
  apply hs_not_border
  change s ∈ RectangleBorder (0 : ℂ) ((1 : ℂ) + ((T : ℝ) : ℂ) * I)
  rw [RectangleBorder]
  exact Or.inl (Or.inl (Or.inl
    ⟨by
      simpa [Set.mem_preimage, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        (⟨hs_bounds.1, hs_bounds.2.1⟩ : s.re ∈ Set.Icc (0 : ℝ) 1),
    by simp [hzero.symm]⟩))

private lemma riemannVonMangoldtCountingRectangle_not_border_im_lt {T : ℝ} (hT : 0 ≤ T)
    {s : ℂ}
    (hs_rect : s ∈ Rectangle riemannVonMangoldtCountingRectangleLower
      (riemannVonMangoldtCountingRectangleUpper T))
    (hs_not_border : s ∉ RectangleBorder riemannVonMangoldtCountingRectangleLower
      (riemannVonMangoldtCountingRectangleUpper T)) :
    s.im < T := by
  have hs_bounds :=
    (riemannVonMangoldtCountingRectangle_mem_iff (T := T) hT).1 hs_rect
  refine lt_of_le_of_ne hs_bounds.2.2.2 ?_
  intro htop
  apply hs_not_border
  change s ∈ RectangleBorder (0 : ℂ) ((1 : ℂ) + ((T : ℝ) : ℂ) * I)
  rw [RectangleBorder]
  exact Or.inl (Or.inr
    ⟨by
      simpa [Set.mem_preimage, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        (⟨hs_bounds.1, hs_bounds.2.1⟩ : s.re ∈ Set.Icc (0 : ℝ) 1),
    by simp [htop]⟩)

private lemma riemannVonMangoldtCountingRectangle_mem_of_positive_height_zero {T : ℝ}
    {s : ℂ} (hs : s ∈ riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    s ∈ Rectangle riemannVonMangoldtCountingRectangleLower
      (riemannVonMangoldtCountingRectangleUpper T) := by
  have hT : 0 ≤ T := le_of_lt (lt_trans hs.2.1.1 hs.2.1.2)
  have hre := Kadiri.positiveHeightZero_re_mem_Ioo (T := T) ⟨s, hs⟩
  exact (riemannVonMangoldtCountingRectangle_mem_iff (T := T) hT).2
    ⟨le_of_lt hre.1, le_of_lt hre.2, le_of_lt hs.2.1.1, le_of_lt hs.2.1.2⟩

/--
For the positive-height counting rectangle, the divisor support of `ξ` is exactly the zeta
zero window used by `riemannZeta.N T`, provided `ξ` is nonzero on the rectangle border.
-/
theorem riemannXi_countingRectangle_divisor_support_eq_zeta_zeroes (T : ℝ) (hT : 0 < T)
    (hboundary :
      ∀ p ∈ RectangleBorder riemannVonMangoldtCountingRectangleLower
        (riemannVonMangoldtCountingRectangleUpper T),
        riemannXi p ≠ 0) :
    (MeromorphicOn.divisor riemannXi
        (Rectangle riemannVonMangoldtCountingRectangleLower
          (riemannVonMangoldtCountingRectangleUpper T))).support =
      riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T) := by
  classical
  ext s
  constructor
  · intro hs_support
    let R := Rectangle riemannVonMangoldtCountingRectangleLower
      (riemannVonMangoldtCountingRectangleUpper T)
    let D := MeromorphicOn.divisor riemannXi R
    have hxi_mero_R : MeromorphicOn riemannXi R := by
      intro u _hu
      exact (differentiable_riemannXi.analyticAt u).meromorphicAt
    have hs_rect : s ∈ R := D.supportWithinDomain hs_support
    have hs_not_border :
        s ∉ RectangleBorder riemannVonMangoldtCountingRectangleLower
          (riemannVonMangoldtCountingRectangleUpper T) := by
      intro hs_border
      have hs_xi_ne : riemannXi s ≠ 0 := hboundary s hs_border
      have hs_order_zero : meromorphicOrderAt riemannXi s = (0 : WithTop ℤ) := by
        rw [(differentiable_riemannXi.analyticAt s).meromorphicOrderAt_eq]
        rw [(differentiable_riemannXi.analyticAt s).analyticOrderAt_eq_zero.2 hs_xi_ne]
        simp
      have hs_div_zero : D s = 0 := by
        dsimp [D]
        rw [MeromorphicOn.divisor_apply hxi_mero_R hs_rect, hs_order_zero]
        simp
      exact hs_support hs_div_zero
    have hs_im_pos :
        0 < s.im :=
      riemannVonMangoldtCountingRectangle_not_border_im_pos (T := T) hT.le hs_rect hs_not_border
    have hs_im_lt :
        s.im < T :=
      riemannVonMangoldtCountingRectangle_not_border_im_lt (T := T) hT.le hs_rect hs_not_border
    have hs_im_ne : s.im ≠ 0 := ne_of_gt hs_im_pos
    have hs_div_ne :
        D s ≠ 0 := by
      simpa [D, Function.mem_support] using hs_support
    have hzeta_zero : riemannZeta s = 0 := by
      by_contra hzeta_ne
      have hs_ne_one : s ≠ 1 := ne_one_of_im_ne_zero hs_im_ne
      have hzeta_order_zero : meromorphicOrderAt riemannZeta s = (0 : WithTop ℤ) := by
        have han : AnalyticAt ℂ riemannZeta s :=
          riemannZeta_analyticOn_compl_one s (by simpa [Set.mem_compl_iff] using hs_ne_one)
        rw [han.meromorphicOrderAt_eq, han.analyticOrderAt_eq_zero.2 hzeta_ne]
        simp
      have hxi_order_zero : meromorphicOrderAt riemannXi s = (0 : WithTop ℤ) := by
        rw [meromorphicOrderAt_riemannXi_eq_riemannZeta_of_im_ne_zero hs_im_ne,
          hzeta_order_zero]
      have hs_div_zero : D s = 0 := by
        dsimp [D]
        rw [MeromorphicOn.divisor_apply hxi_mero_R hs_rect, hxi_order_zero]
        simp
      exact hs_div_ne hs_div_zero
    exact ⟨Set.mem_univ s, ⟨hs_im_pos, hs_im_lt⟩, hzeta_zero⟩
  · intro hs_zero
    let R := Rectangle riemannVonMangoldtCountingRectangleLower
      (riemannVonMangoldtCountingRectangleUpper T)
    let D := MeromorphicOn.divisor riemannXi R
    have hxi_mero_R : MeromorphicOn riemannXi R := by
      intro u _hu
      exact (differentiable_riemannXi.analyticAt u).meromorphicAt
    have hs_rect : s ∈ R :=
      riemannVonMangoldtCountingRectangle_mem_of_positive_height_zero (T := T) hs_zero
    have hs_im_ne : s.im ≠ 0 := ne_of_gt hs_zero.2.1.1
    have hs_zeta_order_ne : meromorphicOrderAt riemannZeta s ≠ (0 : WithTop ℤ) := by
      intro hzero_order
      let rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T) := ⟨s, hs_zero⟩
      have hpos := Kadiri.riemannZeta_order_pos_positiveHeightZero rho
      have horder_zero : riemannZeta.order s = 0 := by
        simp [riemannZeta.order, hzero_order]
      linarith
    have hs_xi_order_ne : meromorphicOrderAt riemannXi s ≠ (0 : WithTop ℤ) := by
      rwa [meromorphicOrderAt_riemannXi_eq_riemannZeta_of_im_ne_zero hs_im_ne]
    have hs_xi_order_ne_top : meromorphicOrderAt riemannXi s ≠ ⊤ := by
      rw [meromorphicOrderAt_riemannXi_eq_riemannZeta_of_im_ne_zero hs_im_ne]
      exact meromorphicOrderAt_riemannZeta_ne_top s
    rw [Function.mem_support, ne_eq]
    rw [MeromorphicOn.divisor_apply hxi_mero_R hs_rect]
    simpa [WithTop.untop₀_eq_zero] using
      (not_or.mpr ⟨hs_xi_order_ne, hs_xi_order_ne_top⟩)

/--
The ξ divisor sum over the positive-height counting rectangle equals the project's
order-weighted zero-counting function `N(T)`.
-/
theorem riemannXi_rectangle_divisor_sum_eq_riemannZeta_N (T : ℝ) (hT : 0 < T)
    (hboundary :
      ∀ p ∈ RectangleBorder riemannVonMangoldtCountingRectangleLower
        (riemannVonMangoldtCountingRectangleUpper T),
        riemannXi p ≠ 0) :
    (∑ p ∈ (divisor_support_rectangle_finite riemannXi
        riemannVonMangoldtCountingRectangleLower
        (riemannVonMangoldtCountingRectangleUpper T)).toFinset,
        (((MeromorphicOn.divisor riemannXi
          (Rectangle riemannVonMangoldtCountingRectangleLower
            (riemannVonMangoldtCountingRectangleUpper T))) p : ℤ) : ℝ)) =
      riemannZeta.N T := by
  classical
  let R := Rectangle riemannVonMangoldtCountingRectangleLower
    (riemannVonMangoldtCountingRectangleUpper T)
  let D := MeromorphicOn.divisor riemannXi R
  let hXi := divisor_support_rectangle_finite riemannXi
    riemannVonMangoldtCountingRectangleLower (riemannVonMangoldtCountingRectangleUpper T)
  let hZeta := Kadiri.zeroes_rect_univ_positive_height_finite T
  have hsupport :
      D.support = riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T) := by
    simpa [D, R] using
      riemannXi_countingRectangle_divisor_support_eq_zeta_zeroes T hT hboundary
  have hfinset : hXi.toFinset = hZeta.toFinset := by
    ext s
    rw [hXi.mem_toFinset, hZeta.mem_toFinset]
    simp [D, R, hsupport]
  rw [show (divisor_support_rectangle_finite riemannXi
        riemannVonMangoldtCountingRectangleLower
        (riemannVonMangoldtCountingRectangleUpper T)).toFinset = hZeta.toFinset by
      exact hfinset]
  rw [riemannZeta_N_eq_toFinset_sum_order T]
  refine Finset.sum_congr rfl ?_
  intro s hs_mem
  have hs_zero : s ∈ riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T) :=
    hZeta.mem_toFinset.mp hs_mem
  have hs_rect : s ∈ R :=
    riemannVonMangoldtCountingRectangle_mem_of_positive_height_zero (T := T) hs_zero
  have hs_im_ne : s.im ≠ 0 := ne_of_gt hs_zero.2.1.1
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (meromorphicOrderAt_riemannZeta_ne_top s)
  have hxi_mero_R : MeromorphicOn riemannXi R := by
    intro u _hu
    exact (differentiable_riemannXi.analyticAt u).meromorphicAt
  have horder : D s = riemannZeta.order s := by
    dsimp [D]
    rw [MeromorphicOn.divisor_apply hxi_mero_R hs_rect,
      meromorphicOrderAt_riemannXi_eq_riemannZeta_of_im_ne_zero hs_im_ne,
      riemannZeta.order, ← hn, WithTop.untop₀_coe, WithTop.untopD_coe]
  exact_mod_cast horder

/-- The normalized ξ logarithmic-derivative integral over the counting rectangle. -/
def riemannVonMangoldtXiCountingRectangleIntegral (T : ℝ) : ℂ :=
  RectangleIntegral' (logDeriv riemannXi) riemannVonMangoldtCountingRectangleLower
    (riemannVonMangoldtCountingRectangleUpper T)

def riemannVonMangoldtXiBottomIntegral : ℂ :=
  HIntegral (logDeriv riemannXi) 0 1 0

def riemannVonMangoldtXiTopIntegral (T : ℝ) : ℂ :=
  HIntegral (logDeriv riemannXi) 0 1 T

def riemannVonMangoldtXiRightIntegral (T : ℝ) : ℂ :=
  VIntegral (logDeriv riemannXi) 1 0 T

def riemannVonMangoldtXiLeftIntegral (T : ℝ) : ℂ :=
  VIntegral (logDeriv riemannXi) 0 0 T

theorem riemannVonMangoldtXiCountingRectangleIntegral_eq_edges (T : ℝ) :
    riemannVonMangoldtXiCountingRectangleIntegral T =
      (1 / (2 * Real.pi * I) : ℂ) •
        (riemannVonMangoldtXiBottomIntegral -
          riemannVonMangoldtXiTopIntegral T +
          riemannVonMangoldtXiRightIntegral T -
          riemannVonMangoldtXiLeftIntegral T) := by
  simp [riemannVonMangoldtXiCountingRectangleIntegral,
    riemannVonMangoldtXiBottomIntegral, riemannVonMangoldtXiTopIntegral,
    riemannVonMangoldtXiRightIntegral, riemannVonMangoldtXiLeftIntegral,
    riemannVonMangoldtCountingRectangleLower, riemannVonMangoldtCountingRectangleUpper,
    RectangleIntegral', RectangleIntegral]

theorem HIntegral_logDeriv_riemannXi_eq_prefactor_add_zeta_of_im_ne_zero
    {x₁ x₂ y : ℝ} (hy : y ≠ 0)
    (hzeta : ∀ x ∈ Set.uIcc x₁ x₂,
      riemannZeta ((x : ℂ) + ((y : ℝ) : ℂ) * I) ≠ 0)
    (hpref_int : IntervalIntegrable
      (fun x : ℝ => logDeriv riemannVonMangoldtXiPrefactor
        ((x : ℂ) + ((y : ℝ) : ℂ) * I)) MeasureTheory.volume x₁ x₂)
    (hzeta_int : IntervalIntegrable
      (fun x : ℝ => logDeriv riemannZeta
        ((x : ℂ) + ((y : ℝ) : ℂ) * I)) MeasureTheory.volume x₁ x₂) :
    HIntegral (logDeriv riemannXi) x₁ x₂ y =
      HIntegral (logDeriv riemannVonMangoldtXiPrefactor) x₁ x₂ y +
        HIntegral (logDeriv riemannZeta) x₁ x₂ y := by
  unfold HIntegral
  have hcongr : Set.EqOn
      (fun x : ℝ => logDeriv riemannXi ((x : ℂ) + ((y : ℝ) : ℂ) * I))
      (fun x : ℝ =>
        logDeriv riemannVonMangoldtXiPrefactor ((x : ℂ) + ((y : ℝ) : ℂ) * I) +
          logDeriv riemannZeta ((x : ℂ) + ((y : ℝ) : ℂ) * I))
      (Set.uIcc x₁ x₂) := by
    intro x hx
    have him : (((x : ℂ) + ((y : ℝ) : ℂ) * I).im) ≠ 0 := by
      simpa using hy
    exact logDeriv_riemannXi_eq_prefactor_add_zeta_of_im_ne_zero him (hzeta x hx)
  rw [intervalIntegral.integral_congr hcongr]
  exact intervalIntegral.integral_add hpref_int hzeta_int

theorem VIntegral_logDeriv_riemannXi_eq_prefactor_add_zeta_of_im_ne_zero
    {x y₁ y₂ : ℝ}
    (hy_ne : ∀ y ∈ Set.uIcc y₁ y₂, y ≠ 0)
    (hzeta : ∀ y ∈ Set.uIcc y₁ y₂,
      riemannZeta (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I) ≠ 0)
    (hpref_int : IntervalIntegrable
      (fun y : ℝ => logDeriv riemannVonMangoldtXiPrefactor
        (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I)) MeasureTheory.volume y₁ y₂)
    (hzeta_int : IntervalIntegrable
      (fun y : ℝ => logDeriv riemannZeta
        (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I)) MeasureTheory.volume y₁ y₂) :
    VIntegral (logDeriv riemannXi) x y₁ y₂ =
      VIntegral (logDeriv riemannVonMangoldtXiPrefactor) x y₁ y₂ +
        VIntegral (logDeriv riemannZeta) x y₁ y₂ := by
  unfold VIntegral
  have hcongr : Set.EqOn
      (fun y : ℝ => logDeriv riemannXi (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I))
      (fun y : ℝ =>
        logDeriv riemannVonMangoldtXiPrefactor (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I) +
          logDeriv riemannZeta (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I))
      (Set.uIcc y₁ y₂) := by
    intro y hy
    have him : ((((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I).im) ≠ 0 := by
      simpa using hy_ne y hy
    exact logDeriv_riemannXi_eq_prefactor_add_zeta_of_im_ne_zero him (hzeta y hy)
  rw [intervalIntegral.integral_congr hcongr]
  rw [intervalIntegral.integral_add hpref_int hzeta_int]
  ring

/-- The Gamma argument `1 / 4 + iT / 2` in the Riemann-von-Mangoldt main term. -/
def riemannVonMangoldtGammaPoint (T : ℝ) : ℂ :=
  (1 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I

/-- The Stirling main term for the log-Gamma phase calculation. -/
def riemannVonMangoldtGammaStirlingMain (z : ℂ) : ℂ :=
  (z - (1 / 2 : ℂ)) * Complex.log z - z + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ)

/-- The unwrapped log-Gamma branch built from the local `logGammaSeq` construction. -/
def logGammaBranch (z : ℂ) : ℂ :=
  Filter.limUnder Filter.atTop (Complex.logGammaSeq z)

/-- Riemann-von-Mangoldt spelling for the unwrapped log-Gamma branch. -/
def riemannVonMangoldtLogGammaBranch (z : ℂ) : ℂ :=
  logGammaBranch z

/-- The `logGammaSeq` branch exponentiates back to `Gamma` on the right half-plane. -/
theorem exp_logGammaBranch {z : ℂ} (hz : 0 < z.re) :
    Complex.exp (logGammaBranch z) = Complex.Gamma z := by
  have hlim :
      Tendsto (fun n : ℕ => Complex.logGammaSeq z n) atTop (𝓝 (logGammaBranch z)) :=
    (Complex.cauchySeq_logGammaSeq hz).tendsto_limUnder
  have hexp := (continuous_exp.tendsto _).comp hlim
  have hgamma_to_exp :
      Tendsto (fun n : ℕ => Complex.GammaSeq z n) atTop
        (𝓝 (Complex.exp (logGammaBranch z))) := by
    apply hexp.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact Complex.exp_logGammaSeq hz hn
  exact tendsto_nhds_unique hgamma_to_exp (Complex.GammaSeq_tendsto_Gamma z)

/-- On positive reals, the local complex branch is the real Bohr-Mollerup branch. -/
theorem logGammaBranch_ofReal_eq_realLogGamma {x : ℝ} (hx : 0 < x) :
    logGammaBranch (x : ℂ) = (Real.log (Real.Gamma x) : ℂ) := by
  have hseq : ∀ n : ℕ,
      Complex.logGammaSeq (x : ℂ) n = (Real.BohrMollerup.logGammaSeq x n : ℂ) := by
    intro n
    have hsum :
        (∑ m ∈ Finset.range (n + 1), Complex.log ((x : ℂ) + m)) =
          ((∑ m ∈ Finset.range (n + 1), Real.log (x + m)) : ℂ) := by
      refine Finset.sum_congr rfl ?_
      intro m hm
      have hxm_nonneg : 0 ≤ x + (m : ℝ) := by positivity
      rw [Complex.ofReal_log hxm_nonneg]
      simp
    rw [Complex.logGammaSeq, Real.BohrMollerup.logGammaSeq, hsum]
    norm_num
  have hcomplex :
      Tendsto (fun n : ℕ => Complex.logGammaSeq (x : ℂ) n) atTop
        (𝓝 (logGammaBranch (x : ℂ))) :=
    (Complex.cauchySeq_logGammaSeq (by simpa using hx)).tendsto_limUnder
  have hreal :
      Tendsto (fun n : ℕ => (Real.BohrMollerup.logGammaSeq x n : ℂ)) atTop
        (𝓝 ((Real.log (Real.Gamma x) : ℂ))) :=
    (continuous_ofReal.tendsto _).comp (Real.BohrMollerup.tendsto_log_gamma hx)
  exact tendsto_nhds_unique hcomplex (hreal.congr' (by
    filter_upwards with n
    exact (hseq n).symm))

/-- The unwrapped `logGammaSeq` branch has logarithmic derivative `digamma`. -/
theorem hasDerivAt_logGammaBranch {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt logGammaBranch (Complex.digamma z) z := by
  change HasDerivAt (fun w => Filter.limUnder Filter.atTop (Complex.logGammaSeq w))
    (Complex.digamma z) z
  exact Complex.hasDerivAt_logGammaSeq_limUnder hz

/-- Derivative of the Stirling main term on the right half-plane. -/
theorem hasDerivAt_riemannVonMangoldtGammaStirlingMain {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt riemannVonMangoldtGammaStirlingMain
      (Complex.log z - z⁻¹ / 2) z := by
  have hslit : z ∈ Complex.slitPlane := Or.inl hz
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hsub : HasDerivAt (fun w : ℂ => w - (1 / 2 : ℂ)) 1 z :=
    (hasDerivAt_id z).sub_const _
  have hlog : HasDerivAt Complex.log z⁻¹ z := Complex.hasDerivAt_log hslit
  have hprod := hsub.mul hlog
  have hmain :
      HasDerivAt
        (fun w : ℂ => (w - (1 / 2 : ℂ)) * Complex.log w - w +
          ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ))
        (1 * Complex.log z + (z - (1 / 2 : ℂ)) * z⁻¹ - 1) z :=
    (hprod.sub (hasDerivAt_id z)).add_const _
  convert hmain using 1
  · ext w
    simp [riemannVonMangoldtGammaStirlingMain]
  · field_simp [hz0]
    ring

/-- The Stirling remainder has derivative equal to the sharp digamma remainder. -/
theorem hasDerivAt_logGammaBranch_sub_stirlingMain {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (fun w => logGammaBranch w - riemannVonMangoldtGammaStirlingMain w)
      (Complex.digammaRem z) z := by
  have hbranch := hasDerivAt_logGammaBranch (z := z) hz
  have hmain := hasDerivAt_riemannVonMangoldtGammaStirlingMain (z := z) hz
  change HasDerivAt (logGammaBranch - riemannVonMangoldtGammaStirlingMain)
    (Complex.digammaRem z) z
  simpa [Complex.digammaRem] using hbranch.sub hmain

/-- Real derivative of the Stirling remainder along the radial ray `t ↦ t z`. -/
theorem hasDerivAt_logGammaBranch_stirlingRemainder_ray {z : ℂ}
    (hz : (1 / 4 : ℝ) ≤ z.re) {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt
      (fun u : ℝ =>
        logGammaBranch ((u : ℂ) * z) -
          riemannVonMangoldtGammaStirlingMain ((u : ℂ) * z))
      (Complex.digammaRem ((t : ℂ) * z) * z) t := by
  have hray : (1 / 4 : ℝ) ≤ (((t : ℂ) * z).re) := Complex.ray_re_ge_quarter hz ht
  have hray_pos : 0 < (((t : ℂ) * z).re) := by linarith
  have hrem := hasDerivAt_logGammaBranch_sub_stirlingMain (z := (t : ℂ) * z) hray_pos
  have hlin : HasDerivAt (fun u : ℝ => (u : ℂ) * z) z t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z
  have hcomp := HasFDerivAt.comp_hasDerivAt t (hrem.hasFDerivAt.restrictScalars ℝ) hlin
  change HasDerivAt
    ((fun w : ℂ => logGammaBranch w - riemannVonMangoldtGammaStirlingMain w) ∘
      fun u : ℝ => (u : ℂ) * z)
    (Complex.digammaRem ((t : ℂ) * z) * z) t
  simpa [Function.comp, ContinuousLinearMap.restrictScalars, mul_comm] using hcomp

/-- Real derivative of the Stirling remainder along an arbitrary complex line. -/
theorem hasDerivAt_logGammaBranch_stirlingRemainder_line {a v : ℂ} {t : ℝ}
    (hpos : 0 < (a + (t : ℂ) * v).re) :
    HasDerivAt
      (fun u : ℝ =>
        logGammaBranch (a + (u : ℂ) * v) -
          riemannVonMangoldtGammaStirlingMain (a + (u : ℂ) * v))
      (Complex.digammaRem (a + (t : ℂ) * v) * v) t := by
  have hrem := hasDerivAt_logGammaBranch_sub_stirlingMain
    (z := a + (t : ℂ) * v) hpos
  have hmul : HasDerivAt (fun u : ℝ => (u : ℂ) * v) v t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const v
  have hlin : HasDerivAt (fun u : ℝ => a + (u : ℂ) * v) v t := by
    simpa using hmul.const_add a
  have hcomp := HasFDerivAt.comp_hasDerivAt t (hrem.hasFDerivAt.restrictScalars ℝ) hlin
  change HasDerivAt
    ((fun w : ℂ => logGammaBranch w - riemannVonMangoldtGammaStirlingMain w) ∘
      fun u : ℝ => a + (u : ℂ) * v)
    (Complex.digammaRem (a + (t : ℂ) * v) * v) t
  simpa [Function.comp, ContinuousLinearMap.restrictScalars, mul_comm] using hcomp

/--
Moving the Stirling remainder along a segment costs the A1 derivative bound
times the segment length.
-/
theorem norm_logGammaBranch_stirlingRemainder_line_sub_le {a v : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hre :
      ∀ s ∈ Set.Icc (0 : ℝ) 1, (1 / 4 : ℝ) ≤ (a + (s : ℂ) * v).re)
    (hnorm : ∀ s ∈ Set.Icc (0 : ℝ) 1, ρ ≤ ‖a + (s : ℂ) * v‖) :
    ‖(logGammaBranch (a + v) -
        riemannVonMangoldtGammaStirlingMain (a + v)) -
      (logGammaBranch a - riemannVonMangoldtGammaStirlingMain a)‖ ≤
      (1 / (6 * ρ ^ 2)) * ‖v‖ := by
  let F : ℝ → ℂ := fun s =>
    logGammaBranch (a + (s : ℂ) * v) -
      riemannVonMangoldtGammaStirlingMain (a + (s : ℂ) * v)
  let F' : ℝ → ℂ := fun s => Complex.digammaRem (a + (s : ℂ) * v) * v
  have hderiv :
      ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt F (F' s) (Set.Icc (0 : ℝ) 1) s := by
    intro s hs
    have hpos : 0 < (a + (s : ℂ) * v).re := by linarith [hre s hs]
    exact (hasDerivAt_logGammaBranch_stirlingRemainder_line
      (a := a) (v := v) (t := s) hpos).hasDerivWithinAt
  have hbound :
      ∀ s ∈ Set.Ico (0 : ℝ) 1, ‖F' s‖ ≤ (1 / (6 * ρ ^ 2)) * ‖v‖ := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hs
    have hA1 := Complex.digammaRem_full_norm_bound (z := a + (s : ℂ) * v) (hre s hsIcc)
    have hmul := mul_le_mul_of_nonneg_right hA1 (norm_nonneg v)
    have hwlower : ρ ≤ ‖a + (s : ℂ) * v‖ := hnorm s hsIcc
    have hsq : ρ ^ 2 ≤ ‖a + (s : ℂ) * v‖ ^ 2 := by
      have hdiff : 0 ≤ ‖a + (s : ℂ) * v‖ - ρ := sub_nonneg.mpr hwlower
      have hsum : 0 ≤ ‖a + (s : ℂ) * v‖ + ρ := by positivity
      have hprod := mul_nonneg hdiff hsum
      nlinarith [hprod]
    have hdenle : 6 * ρ ^ 2 ≤ 6 * ‖a + (s : ℂ) * v‖ ^ 2 := by nlinarith
    have hdenpos : 0 < 6 * ρ ^ 2 := by positivity
    have hrec :
        1 / (6 * ‖a + (s : ℂ) * v‖ ^ 2) ≤ 1 / (6 * ρ ^ 2) :=
      one_div_le_one_div_of_le hdenpos hdenle
    calc
      ‖F' s‖
          = ‖Complex.digammaRem (a + (s : ℂ) * v)‖ * ‖v‖ := by
            simp [F']
      _ ≤ (1 / (6 * ‖a + (s : ℂ) * v‖ ^ 2)) * ‖v‖ := hmul
      _ ≤ (1 / (6 * ρ ^ 2)) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hrec (norm_nonneg v)
  simpa [F] using
    norm_image_sub_le_of_norm_deriv_le_segment_01' (f := F) (f' := F') hderiv hbound

/--
If the Stirling remainder tends to zero along the radial ray, then it equals the
negative integral of the digamma remainder on that ray.
-/
theorem logGammaBranch_sub_stirlingMain_eq_neg_integral_of_tendsto {z : ℂ}
    (hz : (1 / 4 : ℝ) ≤ z.re)
    (htend :
      Tendsto
        (fun t : ℝ =>
          logGammaBranch ((t : ℂ) * z) -
            riemannVonMangoldtGammaStirlingMain ((t : ℂ) * z))
        atTop (𝓝 0)) :
    logGammaBranch z - riemannVonMangoldtGammaStirlingMain z =
      -∫ t in Set.Ici (1 : ℝ), Complex.digammaRem ((t : ℂ) * z) * z := by
  let F : ℝ → ℂ := fun t =>
    logGammaBranch ((t : ℂ) * z) -
      riemannVonMangoldtGammaStirlingMain ((t : ℂ) * z)
  let F' : ℝ → ℂ := fun t => Complex.digammaRem ((t : ℂ) * z) * z
  have hderiv : ∀ t ∈ Set.Ici (1 : ℝ), HasDerivAt F (F' t) t := by
    intro t ht
    exact hasDerivAt_logGammaBranch_stirlingRemainder_ray (z := z) hz ht
  have hintIoi : MeasureTheory.IntegrableOn F' (Set.Ioi (1 : ℝ)) MeasureTheory.volume :=
    (Complex.integrableOn_digammaRem_ray (z := z) hz).mono_set Set.Ioi_subset_Ici_self
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := (1 : ℝ)) (f := F) (f' := F') (m := (0 : ℂ)) hderiv hintIoi (by simpa [F] using htend)
  have hFTC_Ici : ∫ t in Set.Ici (1 : ℝ), F' t = -F 1 := by
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    simpa using hFTC
  calc
    logGammaBranch z - riemannVonMangoldtGammaStirlingMain z = F 1 := by
      simp [F]
    _ = -∫ t in Set.Ici (1 : ℝ), F' t := by
      rw [hFTC_Ici]
      simp
    _ = -∫ t in Set.Ici (1 : ℝ), Complex.digammaRem ((t : ℂ) * z) * z := by
      rfl

/--
Conditional form of the sharp radial-ray Stirling bound. The only remaining
input is the tail limit of the `logGammaSeq` branch remainder along the ray.
-/
theorem norm_logGammaBranch_sub_stirling_le_of_tendsto {z : ℂ}
    (hz : (1 / 4 : ℝ) ≤ z.re)
    (htend :
      Tendsto
        (fun t : ℝ =>
          logGammaBranch ((t : ℂ) * z) -
            riemannVonMangoldtGammaStirlingMain ((t : ℂ) * z))
        atTop (𝓝 0)) :
    ‖logGammaBranch z - riemannVonMangoldtGammaStirlingMain z‖ ≤
      1 / (6 * ‖z‖) := by
  rw [logGammaBranch_sub_stirlingMain_eq_neg_integral_of_tendsto (z := z) hz htend]
  simpa [norm_neg] using Complex.norm_integral_rem_le (z := z) hz

private lemma log_factorial_stirling_remainder_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        Real.log (n.factorial : ℝ) -
          (((n : ℝ) + 1 / 2) * Real.log n - n + (1 / 2) * Real.log (2 * Real.pi)))
      atTop (𝓝 0) := by
  have hlogSt :
      Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) atTop
        (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (Real.sqrt_pos.2 Real.pi_pos).ne').tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi
  have hpi : Real.log (Real.sqrt Real.pi) = (1 / 2 : ℝ) * Real.log Real.pi := by
    rw [Real.log_sqrt Real.pi_pos.le]
    ring
  have hlim :
      Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi))
        atTop (𝓝 0) := by
    simpa using hlogSt.sub (tendsto_const_nhds (x := Real.log (Real.sqrt Real.pi)))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  rw [Stirling.log_stirlingSeq_formula, hpi]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnne]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_pos.ne']
  rw [Real.log_div hnne (Real.exp_pos 1).ne', Real.log_exp]
  ring

private lemma stirling_nat_shift_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        (((n : ℝ) + 1 / 2) * (Real.log ((n : ℝ) + 1) - Real.log n) - 1))
      atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ => (n : ℝ) * (1 / (n : ℝ))) atTop (𝓝 (1 : ℝ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp [Nat.cast_ne_zero.mpr hn]
  have hmain0 :=
    Real.tendsto_nat_mul_log_one_add_of_tendsto (g := fun n : ℕ => 1 / (n : ℝ)) hg
  have hmain :
      Tendsto (fun n : ℕ => (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n)) atTop
        (𝓝 (1 : ℝ)) := by
    refine hmain0.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
    have harg : 1 + 1 / (n : ℝ) = ((n : ℝ) + 1) / (n : ℝ) := by
      field_simp [hnne]
    rw [harg, Real.log_div (by positivity) hnne]
  have hdiff :
      Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) - Real.log n) atTop
        (𝓝 (0 : ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one] using Real.tendsto_log_nat_add_one_sub_log
  have hshift :
      Tendsto
        (fun n : ℕ => ((n : ℝ) + 1 / 2) * (Real.log ((n : ℝ) + 1) - Real.log n))
        atTop (𝓝 (1 : ℝ)) := by
    have hhalf := (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul hdiff
    convert hmain.add hhalf using 1
    · ext n
      ring_nf
    · ring_nf
  simpa using hshift.sub (tendsto_const_nhds (x := (1 : ℝ)))

/-- The log-Gamma branch Stirling remainder tends to zero on positive integers. -/
theorem logGammaBranch_stirling_int_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        logGammaBranch (((n + 1 : ℕ) : ℝ) : ℂ) -
          riemannVonMangoldtGammaStirlingMain (((n + 1 : ℕ) : ℝ) : ℂ))
      atTop (𝓝 0) := by
  let realRem : ℕ → ℝ := fun n =>
    Real.log (n.factorial : ℝ) -
      ((((n : ℝ) + 1 / 2) * Real.log ((n : ℝ) + 1) - ((n : ℝ) + 1) +
        (1 / 2) * Real.log (2 * Real.pi)))
  have hreal : Tendsto realRem atTop (𝓝 0) := by
    have hbase := log_factorial_stirling_remainder_tendsto_zero
    have hshift := stirling_nat_shift_tendsto_zero
    convert hbase.sub hshift using 1
    · ext n
      dsimp [realRem]
      ring_nf
    · ring_nf
  have hcomplex : Tendsto (fun n : ℕ => (realRem n : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    change Tendsto (Complex.ofReal ∘ realRem) atTop (𝓝 (0 : ℂ))
    exact (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
  refine hcomplex.congr' ?_
  filter_upwards with n
  have hx : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hx_nonneg : 0 ≤ (((n + 1 : ℕ) : ℝ)) := hx.le
  have hbranch := logGammaBranch_ofReal_eq_realLogGamma (x := (((n + 1 : ℕ) : ℝ))) hx
  have hgamma : Real.Gamma (((n + 1 : ℕ) : ℝ)) = (n.factorial : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using Real.Gamma_nat_eq_factorial n
  have hmain :
      riemannVonMangoldtGammaStirlingMain (((n + 1 : ℕ) : ℝ) : ℂ) =
        (((((n : ℝ) + 1 / 2) * Real.log ((n : ℝ) + 1) - ((n : ℝ) + 1) +
          (1 / 2) * Real.log (2 * Real.pi))) : ℂ) := by
    rw [riemannVonMangoldtGammaStirlingMain]
    rw [← Complex.ofReal_log hx_nonneg]
    push_cast
    ring
  rw [hbranch, hmain, hgamma]
  dsimp [realRem]
  push_cast
  ring

private lemma norm_logGammaBranch_stirling_real_floor_sub_le {x : ℝ}
    (hx : (1 / 4 : ℝ) ≤ x) :
    ‖(logGammaBranch (x : ℂ) - riemannVonMangoldtGammaStirlingMain (x : ℂ)) -
      (logGammaBranch (((⌊x⌋₊ + 1 : ℕ) : ℝ) : ℂ) -
        riemannVonMangoldtGammaStirlingMain (((⌊x⌋₊ + 1 : ℕ) : ℝ) : ℂ))‖ ≤
      1 / (6 * x ^ 2) := by
  let p : ℝ := ((⌊x⌋₊ + 1 : ℕ) : ℝ)
  have hxpos : 0 < x := by linarith
  have hxnonneg : 0 ≤ x := hxpos.le
  have hp_ge : x ≤ p := by
    have hlt := Nat.lt_floor_add_one x
    exact le_of_lt (by simpa [p, Nat.cast_add, Nat.cast_one] using hlt)
  have hp_sub_nonneg : 0 ≤ p - x := sub_nonneg.mpr hp_ge
  have hp_sub_le_one : p - x ≤ 1 := by
    have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hxnonneg
    dsimp only [p]
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hline := norm_logGammaBranch_stirlingRemainder_line_sub_le
    (a := (x : ℂ)) (v := ((p - x : ℝ) : ℂ)) (ρ := x) hxpos
    (by
      intro s hs
      have hs0 : 0 ≤ s := hs.1
      have hre_eq :
          ((x : ℂ) + (s : ℂ) * ((p - x : ℝ) : ℂ)).re = x + s * (p - x) := by
        simp
      rw [hre_eq]
      nlinarith [mul_nonneg hs0 hp_sub_nonneg])
    (by
      intro s hs
      have hs0 : 0 ≤ s := hs.1
      have hy_nonneg : 0 ≤ x + s * (p - x) := by
        nlinarith [mul_nonneg hs0 hp_sub_nonneg, hxnonneg]
      have hy_ge : x ≤ x + s * (p - x) := by
        nlinarith [mul_nonneg hs0 hp_sub_nonneg]
      have hpoint :
          (x : ℂ) + (s : ℂ) * ((p - x : ℝ) : ℂ) =
            ((x + s * (p - x) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hpoint, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy_nonneg]
      exact hy_ge)
  have hline' :
      ‖(logGammaBranch (p : ℂ) - riemannVonMangoldtGammaStirlingMain (p : ℂ)) -
        (logGammaBranch (x : ℂ) - riemannVonMangoldtGammaStirlingMain (x : ℂ))‖ ≤
        (1 / (6 * x ^ 2)) * ‖((p - x : ℝ) : ℂ)‖ := by
    simpa [p] using hline
  have hvnorm_le : ‖((p - x : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp_sub_nonneg]
    exact hp_sub_le_one
  have hcoef_nonneg : 0 ≤ 1 / (6 * x ^ 2) := by positivity
  calc
    ‖(logGammaBranch (x : ℂ) - riemannVonMangoldtGammaStirlingMain (x : ℂ)) -
      (logGammaBranch (((⌊x⌋₊ + 1 : ℕ) : ℝ) : ℂ) -
        riemannVonMangoldtGammaStirlingMain (((⌊x⌋₊ + 1 : ℕ) : ℝ) : ℂ))‖
        = ‖(logGammaBranch (p : ℂ) - riemannVonMangoldtGammaStirlingMain (p : ℂ)) -
          (logGammaBranch (x : ℂ) - riemannVonMangoldtGammaStirlingMain (x : ℂ))‖ := by
          rw [norm_sub_rev]
    _ ≤ (1 / (6 * x ^ 2)) * ‖((p - x : ℝ) : ℂ)‖ := hline'
    _ ≤ 1 / (6 * x ^ 2) := by
      simpa using mul_le_mul_of_nonneg_left hvnorm_le hcoef_nonneg

private lemma tendsto_one_div_six_mul_sq_atTop :
    Tendsto (fun x : ℝ => 1 / (6 * x ^ 2)) atTop (𝓝 (0 : ℝ)) := by
  have hpow : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hden : Tendsto (fun x : ℝ => 6 * x ^ 2) atTop atTop :=
    hpow.const_mul_atTop (by norm_num : (0 : ℝ) < 6)
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
  simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hone.div_atTop hden

/-- The log-Gamma branch Stirling remainder tends to zero on positive real rays. -/
theorem logGammaBranch_stirling_real_tendsto_zero :
    Tendsto
      (fun x : ℝ =>
        logGammaBranch (x : ℂ) - riemannVonMangoldtGammaStirlingMain (x : ℂ))
      atTop (𝓝 0) := by
  let R : ℂ → ℂ := fun w => logGammaBranch w - riemannVonMangoldtGammaStirlingMain w
  have hanchor :
      Tendsto (fun x : ℝ => R ((((⌊x⌋₊ + 1 : ℕ) : ℝ) : ℂ))) atTop (𝓝 0) := by
    simpa [R, Function.comp_def, Nat.cast_add, Nat.cast_one] using
      logGammaBranch_stirling_int_tendsto_zero.comp
        (tendsto_nat_floor_atTop (α := ℝ))
  have hdiff :
      Tendsto
        (fun x : ℝ => R (x : ℂ) - R ((((⌊x⌋₊ + 1 : ℕ) : ℝ) : ℂ)))
        atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_one_div_six_mul_sq_atTop
    filter_upwards [eventually_ge_atTop (1 / 4 : ℝ)] with x hx
    simpa [R] using norm_logGammaBranch_stirling_real_floor_sub_le (x := x) hx
  simpa [R] using hdiff.add hanchor

/-- The log-Gamma branch Stirling remainder tends to zero along every radial ray in `Re ≥ 1/4`. -/
theorem logGammaBranch_stirling_ray_tendsto_zero {z : ℂ}
    (hz : (1 / 4 : ℝ) ≤ z.re) :
    Tendsto
      (fun t : ℝ =>
        logGammaBranch ((t : ℂ) * z) -
          riemannVonMangoldtGammaStirlingMain ((t : ℂ) * z))
      atTop (𝓝 0) := by
  let R : ℂ → ℂ := fun w => logGammaBranch w - riemannVonMangoldtGammaStirlingMain w
  have hznormpos : 0 < ‖z‖ := Complex.norm_pos_of_re_ge_quarter hz
  have hscale : Tendsto (fun t : ℝ => t * ‖z‖) atTop atTop :=
    tendsto_id.atTop_mul_const hznormpos
  have hreal :
      Tendsto (fun t : ℝ => R (((t * ‖z‖ : ℝ) : ℂ))) atTop (𝓝 0) := by
    simpa [R, Function.comp_def] using logGammaBranch_stirling_real_tendsto_zero.comp hscale
  have hdiff :
      Tendsto
        (fun t : ℝ => R ((t : ℂ) * z) - R (((t * ‖z‖ : ℝ) : ℂ)))
        atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t : ℝ => (16 * ‖z‖ / 3) / t) ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have ht0 : 0 ≤ t := le_trans zero_le_one ht
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
      let realPt : ℂ := ((t * ‖z‖ : ℝ) : ℂ)
      let v : ℂ := (t : ℂ) * z - realPt
      have hseg_re_lower :
          ∀ s ∈ Set.Icc (0 : ℝ) 1, t / 4 ≤ (realPt + (s : ℂ) * v).re := by
        intro s hs
        have hs0 : 0 ≤ s := hs.1
        have hs1 : s ≤ 1 := hs.2
        have hz_re_le_norm : z.re ≤ ‖z‖ := re_le_norm z
        have hreal_ge : t / 4 ≤ t * ‖z‖ := by
          have hquarter_norm : (1 / 4 : ℝ) ≤ ‖z‖ := le_trans hz hz_re_le_norm
          nlinarith [mul_le_mul_of_nonneg_left hquarter_norm ht0]
        have hray_ge : t / 4 ≤ t * z.re := by
          nlinarith [mul_le_mul_of_nonneg_left hz ht0]
        have hpart1 :
            (1 - s) * (t / 4) ≤ (1 - s) * (t * ‖z‖) :=
          mul_le_mul_of_nonneg_left hreal_ge (sub_nonneg.mpr hs1)
        have hpart2 : s * (t / 4) ≤ s * (t * z.re) :=
          mul_le_mul_of_nonneg_left hray_ge hs0
        have hre_eq :
            (realPt + (s : ℂ) * v).re =
              (1 - s) * (t * ‖z‖) + s * (t * z.re) := by
          dsimp [realPt, v]
          simp [Complex.mul_re, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
          ring
        rw [hre_eq]
        nlinarith
      have hline := norm_logGammaBranch_stirlingRemainder_line_sub_le
        (a := realPt) (v := v) (ρ := t / 4) (by positivity)
        (by
          intro s hs
          have hlower := hseg_re_lower s hs
          nlinarith)
        (by
          intro s hs
          exact le_trans (hseg_re_lower s hs) (re_le_norm (realPt + (s : ℂ) * v)))
      have hseglen : ‖v‖ ≤ 2 * t * ‖z‖ := by
        have hnorm_ray : ‖(t : ℂ) * z‖ = t * ‖z‖ :=
          Complex.norm_ofReal_mul_complex ht0 z
        have hnorm_real : ‖realPt‖ = t * ‖z‖ := by
          dsimp [realPt]
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg ht0 (norm_nonneg z))]
        calc
          ‖v‖ = ‖(t : ℂ) * z - realPt‖ := rfl
          _ ≤ ‖(t : ℂ) * z‖ + ‖realPt‖ := norm_sub_le ((t : ℂ) * z) realPt
          _ = 2 * t * ‖z‖ := by
            rw [hnorm_ray, hnorm_real]
            ring
      have hcoef_nonneg : 0 ≤ 1 / (6 * (t / 4) ^ 2) := by positivity
      have hline' :
          ‖R ((t : ℂ) * z) - R realPt‖ ≤
            (1 / (6 * (t / 4) ^ 2)) * ‖v‖ := by
        simpa [R, realPt, v] using hline
      calc
        ‖R ((t : ℂ) * z) - R (((t * ‖z‖ : ℝ) : ℂ))‖
            = ‖R ((t : ℂ) * z) - R realPt‖ := by rfl
        _ ≤ (1 / (6 * (t / 4) ^ 2)) * ‖v‖ := hline'
        _ ≤ (1 / (6 * (t / 4) ^ 2)) * (2 * t * ‖z‖) :=
          mul_le_mul_of_nonneg_left hseglen hcoef_nonneg
        _ = (16 * ‖z‖ / 3) / t := by
          field_simp [htpos.ne']
          ring
    · have hconst :
          Tendsto (fun _ : ℝ => (16 * ‖z‖ / 3 : ℝ)) atTop
            (𝓝 (16 * ‖z‖ / 3 : ℝ)) := tendsto_const_nhds
      simpa using hconst.div_atTop tendsto_id
  simpa [R] using hdiff.add hreal

/-- Sharp radial-ray Stirling remainder bound from the second-Binet digamma estimate. -/
theorem norm_logGammaBranch_sub_stirling_le {z : ℂ}
    (hz : (1 / 4 : ℝ) ≤ z.re) :
    ‖logGammaBranch z - riemannVonMangoldtGammaStirlingMain z‖ ≤
      1 / (6 * ‖z‖) :=
  norm_logGammaBranch_sub_stirling_le_of_tendsto hz
    (logGammaBranch_stirling_ray_tendsto_zero hz)

/-- The explicit phase appearing at `z = 1 / 4 + iT / 2`. -/
def riemannVonMangoldtGammaPhase (T : ℝ) : ℝ :=
  (T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8
    + (T / 4) * Real.log (1 + 1 / (4 * T ^ 2))
    + (1 / 4) * Real.arctan (1 / (2 * T))

lemma riemannVonMangoldtGammaPoint_norm (T : ℝ) (hT : 0 < T) :
    ‖riemannVonMangoldtGammaPoint T‖ =
      (T / 2) * Real.sqrt (1 + 1 / (4 * T ^ 2)) := by
  have hinside_nonneg : 0 ≤ 1 + (T ^ 2)⁻¹ * 4⁻¹ := by positivity
  have hnormsq :
      ‖riemannVonMangoldtGammaPoint T‖ ^ 2 =
        ((T / 2) * Real.sqrt (1 + 1 / (4 * T ^ 2))) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    suffices (1 / 4 : ℝ) * (1 / 4) + (T / 2) * (T / 2) =
        (T / 2 * Real.sqrt (1 + (T ^ 2)⁻¹ * 4⁻¹)) ^ 2 by
      simpa [riemannVonMangoldtGammaPoint, Complex.normSq_apply] using this
    rw [mul_pow, Real.sq_sqrt hinside_nonneg]
    field_simp [ne_of_gt hT]
    ring
  have hleft : 0 ≤ ‖riemannVonMangoldtGammaPoint T‖ := norm_nonneg _
  have hright : 0 ≤ (T / 2) * Real.sqrt (1 + 1 / (4 * T ^ 2)) := by positivity
  exact sq_eq_sq₀ hleft hright |>.mp hnormsq

lemma riemannVonMangoldtGammaPoint_log_norm (T : ℝ) (hT : 0 < T) :
    Real.log ‖riemannVonMangoldtGammaPoint T‖ =
      Real.log (T / 2) + (1 / 2) * Real.log (1 + 1 / (4 * T ^ 2)) := by
  rw [riemannVonMangoldtGammaPoint_norm T hT, Real.log_mul]
  · rw [Real.log_sqrt]
    · ring
    · positivity
  · positivity
  · positivity

lemma riemannVonMangoldtGammaPoint_arg (T : ℝ) (hT : 0 < T) :
    (riemannVonMangoldtGammaPoint T).arg =
      Real.pi / 2 - Real.arctan (1 / (2 * T)) := by
  have harg_atan :
      (riemannVonMangoldtGammaPoint T).arg = Real.arctan (2 * T) := by
    symm
    apply Real.arctan_eq_of_tan_eq
    · rw [Complex.tan_arg]
      simp [riemannVonMangoldtGammaPoint]
      field_simp
      ring
    · constructor
      · rw [Complex.neg_pi_div_two_lt_arg_iff]
        left
        simp [riemannVonMangoldtGammaPoint]
      · rw [Complex.arg_lt_pi_div_two_iff]
        left
        simp [riemannVonMangoldtGammaPoint]
  have hinv := Real.arctan_inv_of_pos (x := 2 * T) (by positivity)
  have hinv_eq : (2 * T)⁻¹ = 1 / (2 * T) := by ring
  rw [hinv_eq] at hinv
  rw [harg_atan]
  linarith

/-- The elementary phase identity for the Stirling main term at `1 / 4 + iT / 2`. -/
theorem riemannVonMangoldtGammaStirlingMain_im (T : ℝ) (hT : 0 < T) :
    (riemannVonMangoldtGammaStirlingMain (riemannVonMangoldtGammaPoint T)).im =
      riemannVonMangoldtGammaPhase T := by
  have him :
      (riemannVonMangoldtGammaStirlingMain (riemannVonMangoldtGammaPoint T)).im =
        (T / 2) * Real.log ‖riemannVonMangoldtGammaPoint T‖ - T / 2
          - (1 / 4) * (riemannVonMangoldtGammaPoint T).arg := by
    simp [riemannVonMangoldtGammaStirlingMain, riemannVonMangoldtGammaPoint,
      Complex.log_re, Complex.log_im]
    ring
  rw [him, riemannVonMangoldtGammaPoint_log_norm T hT,
    riemannVonMangoldtGammaPoint_arg T hT]
  simp [riemannVonMangoldtGammaPhase]
  ring

/-- Reduces the desired `Im log Γ(1/4+iT/2)` estimate to the missing `logGammaSeq`
branch Stirling remainder estimate. -/
theorem im_logGamma_quarter_stirling_of_logGammaSeq_stirling_remainder (T : ℝ) (hT : 1 ≤ T)
    (hstirling :
      |(riemannVonMangoldtLogGammaBranch (riemannVonMangoldtGammaPoint T) -
          riemannVonMangoldtGammaStirlingMain (riemannVonMangoldtGammaPoint T)).im|
        ≤ 1 / (3 * T)) :
    |(riemannVonMangoldtLogGammaBranch ((1 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im -
        ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8
          + (T / 4) * Real.log (1 + 1 / (4 * T ^ 2))
          + (1 / 4) * Real.arctan (1 / (2 * T)))| ≤ 1 / (3 * T) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hmain := riemannVonMangoldtGammaStirlingMain_im T hTpos
  have hstirling' :
      |(riemannVonMangoldtLogGammaBranch (riemannVonMangoldtGammaPoint T)).im -
          (riemannVonMangoldtGammaStirlingMain (riemannVonMangoldtGammaPoint T)).im|
        ≤ 1 / (3 * T) := by
    simpa [sub_im, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hstirling
  rw [hmain] at hstirling'
  simpa [riemannVonMangoldtGammaPoint, riemannVonMangoldtGammaPhase, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using hstirling'

/-- Riemann's entire xi function is meromorphic on every set. -/
theorem riemannXi_meromorphicOn (R : Set ℂ) : MeromorphicOn riemannXi R := by
  intro s _hs
  exact (differentiable_riemannXi.analyticAt s).meromorphicAt

/-- The logarithmic derivative of Riemann's xi function is meromorphic on every set. -/
theorem riemannXi_logDeriv_meromorphicOn (R : Set ℂ) :
    MeromorphicOn (logDeriv riemannXi) R := by
  intro s _hs
  exact
    ((differentiable_riemannXi.analyticAt s).meromorphicAt.deriv).div
      ((differentiable_riemannXi.analyticAt s).meromorphicAt)

/-- Riemann's xi function has finite meromorphic order at every point. -/
theorem riemannXi_meromorphicOrderAt_ne_top (s : ℂ) :
    meromorphicOrderAt riemannXi s ≠ ⊤ := by
  have hxi_mero_univ : MeromorphicOn riemannXi (Set.univ : Set ℂ) :=
    riemannXi_meromorphicOn Set.univ
  have hfinite_zero : meromorphicOrderAt riemannXi 0 ≠ ⊤ := by
    rw [(differentiable_riemannXi.analyticAt 0).meromorphicOrderAt_eq]
    rw [(differentiable_riemannXi.analyticAt 0).analyticOrderAt_eq_zero.2]
    · simp
    · simp [riemannXi_zero]
  have hall :=
    (hxi_mero_univ.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).1
      ⟨⟨(0 : ℂ), by simp⟩, by simpa using hfinite_zero⟩
  simpa using hall ⟨s, by simp⟩

/-- If xi is nonzero on the rectangle border, its divisor support is disjoint from that border. -/
theorem riemannXi_no_boundary_divisor_support {z w : ℂ}
    (hboundary : ∀ p ∈ RectangleBorder z w, riemannXi p ≠ 0) :
    Disjoint (RectangleBorder z w)
      (MeromorphicOn.divisor riemannXi (Rectangle z w)).support := by
  rw [Set.disjoint_left]
  intro p hp_border hp_support
  have hp_rect : p ∈ Rectangle z w := rectangleBorder_subset_rectangle z w hp_border
  have hp_divisor_ne :
      (MeromorphicOn.divisor riemannXi (Rectangle z w)) p ≠ 0 := by
    simpa [Function.mem_support] using hp_support
  have hp_order_zero : meromorphicOrderAt riemannXi p = (0 : WithTop ℤ) := by
    rw [(differentiable_riemannXi.analyticAt p).meromorphicOrderAt_eq]
    rw [(differentiable_riemannXi.analyticAt p).analyticOrderAt_eq_zero.2
      (hboundary p hp_border)]
    simp
  rw [MeromorphicOn.divisor_apply (riemannXi_meromorphicOn (Rectangle z w)) hp_rect]
    at hp_divisor_ne
  exact hp_divisor_ne (by simp [hp_order_zero])

/-- The xi-specialized rectangle count: the normalized integral of `ξ'/ξ` is the weighted
divisor sum inside the rectangle. -/
theorem riemannXi_rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt {z w : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (hboundary : ∀ p ∈ RectangleBorder z w, riemannXi p ≠ 0) :
    RectangleIntegral' (logDeriv riemannXi) z w =
      ∑ p ∈ (divisor_support_rectangle_finite riemannXi z w).toFinset,
        ((MeromorphicOn.divisor riemannXi (Rectangle z w)) p : ℂ) := by
  exact
    rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt zRe_le_wRe zIm_le_wIm
      (riemannXi_meromorphicOn (Rectangle z w))
      (riemannXi_logDeriv_meromorphicOn (Rectangle z w))
      (fun p _hp => riemannXi_meromorphicOrderAt_ne_top p)
      (riemannXi_no_boundary_divisor_support hboundary)

theorem riemannZeta_N_eq_riemannVonMangoldtXiCountingRectangleIntegral_re (T : ℝ)
    (hT : 0 < T)
    (hboundary :
      ∀ p ∈ RectangleBorder riemannVonMangoldtCountingRectangleLower
        (riemannVonMangoldtCountingRectangleUpper T),
        riemannXi p ≠ 0) :
    riemannZeta.N T =
      (riemannVonMangoldtXiCountingRectangleIntegral T).re := by
  classical
  let z := riemannVonMangoldtCountingRectangleLower
  let w := riemannVonMangoldtCountingRectangleUpper T
  let D := MeromorphicOn.divisor riemannXi (Rectangle z w)
  let hXi := divisor_support_rectangle_finite riemannXi z w
  have hxi_integral :
      RectangleIntegral' (logDeriv riemannXi) z w =
        ∑ p ∈ hXi.toFinset, ((D p : ℤ) : ℂ) := by
    simpa [z, w, D, hXi] using
      (riemannXi_rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt
        (z := z) (w := w)
        (by simp [z, w, riemannVonMangoldtCountingRectangleLower,
          riemannVonMangoldtCountingRectangleUpper])
        (by simpa [z, w, riemannVonMangoldtCountingRectangleLower,
          riemannVonMangoldtCountingRectangleUpper] using hT.le)
        (by simpa [z, w] using hboundary))
  have hsum_real :
      (∑ p ∈ hXi.toFinset, ((D p : ℤ) : ℝ)) =
        riemannZeta.N T := by
    simpa [z, w, D, hXi] using
      riemannXi_rectangle_divisor_sum_eq_riemannZeta_N T hT hboundary
  have hsum_complex :
      (∑ p ∈ hXi.toFinset, ((D p : ℤ) : ℂ)) =
        (riemannZeta.N T : ℂ) := by
    exact_mod_cast hsum_real
  rw [riemannVonMangoldtXiCountingRectangleIntegral, show
      riemannVonMangoldtCountingRectangleLower = z by rfl, show
      riemannVonMangoldtCountingRectangleUpper T = w by rfl]
  rw [hxi_integral, hsum_complex]
  simp

/-- Argument-change form of the xi-specialized rectangle count. -/
theorem riemannXi_rectangle_argumentChange_eq_two_pi_sum_meromorphicOrderAt {z w : ℂ}
    {argumentChange : ℝ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (hboundary : ∀ p ∈ RectangleBorder z w, riemannXi p ≠ 0)
    (hargumentChange :
      (argumentChange : ℂ) =
        (2 * Real.pi : ℂ) * RectangleIntegral' (logDeriv riemannXi) z w) :
    argumentChange =
      2 * Real.pi *
        ∑ p ∈ (divisor_support_rectangle_finite riemannXi z w).toFinset,
          (((MeromorphicOn.divisor riemannXi (Rectangle z w)) p : ℤ) : ℝ) := by
  exact
    rectangle_argumentChange_eq_two_pi_sum_meromorphicOrderAt zRe_le_wRe zIm_le_wIm
      (riemannXi_meromorphicOn (Rectangle z w))
      (riemannXi_logDeriv_meromorphicOn (Rectangle z w))
      (fun p _hp => riemannXi_meromorphicOrderAt_ne_top p)
      (riemannXi_no_boundary_divisor_support hboundary)
      hargumentChange

end
