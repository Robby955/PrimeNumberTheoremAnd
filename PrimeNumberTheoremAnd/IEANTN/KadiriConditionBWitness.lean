import PrimeNumberTheoremAnd.IEANTN.KadiriHorizontalConditionB

/-!
# A concrete witness for Kadiri's condition (B): non-vacuity of the q1 capstone

The q1 horizontal PV vanishing theorems
`kadiri_thm_3_1_q1_{top,bot}_horizontal_pv_vanishes_of_conditionB_finalBound`
are axiom-clean but conditional on `KadiriPhiConditionB φ a`.  This strictly
additive sidecar exhibits a concrete pair `(φ, a)` satisfying condition (B),
so the conditional capstone is genuinely non-vacuous.

The witness is the Gaussian-damped test function
`φ(x) = exp(-x/2 - x²)` with `a = 1/2`, `b = 1`.  Then
`φ(x) · e^{x/2} = e^{-x²}` and `φ'(x) · e^{x/2} = (-1/2 - 2x) · e^{-x²}`, both
of which decay faster than `e^{-(3/2)|x|}` because a Gaussian (times a
polynomial) outpaces any pure exponential: along `cocompact ℝ`, the exponent
`-x² + c·|x|` tends to `-∞`.
-/

namespace Kadiri

open MeasureTheory Complex Filter Asymptotics
open scoped Topology

noncomputable section

/-! ## A reusable Gaussian-beats-exponential little-o lemma -/

/-- If two real exponents `P` and `Q` satisfy `P - Q → -∞` along a filter `l`,
then `exp ∘ P = o(exp ∘ Q)` along `l`.  This is the analytic core that lets a
Gaussian exponent dominate a linear one. -/
theorem isLittleO_rexp_of_sub_tendsto_atBot {α : Type*} {l : Filter α}
    {P Q : α → ℝ} (h : Tendsto (fun x => P x - Q x) l atBot) :
    (fun x => Real.exp (P x)) =o[l] fun x => Real.exp (Q x) := by
  rw [Asymptotics.isLittleO_iff_tendsto
    (fun x hx => absurd hx (Real.exp_pos _).ne')]
  have hsub : Tendsto (fun x => Real.exp (P x - Q x)) l (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h
  refine hsub.congr (fun x => ?_)
  rw [Real.exp_sub]

/-- A downward parabola `-t² + c·t` tends to `-∞` as `t → atTop`. -/
private theorem tendsto_neg_sq_add_mul_atTop_atBot (c : ℝ) :
    Tendsto (fun t : ℝ => -t ^ 2 + c * t) atTop atBot := by
  have hprod : Tendsto (fun t : ℝ => t * (t - c)) atTop atTop :=
    Tendsto.atTop_mul_atTop₀ tendsto_id
      (tendsto_atTop_add_const_right atTop (-c) tendsto_id)
  have := tendsto_neg_atTop_atBot.comp hprod
  refine this.congr (fun t => ?_)
  simp only [Function.comp_apply]
  ring

/-- The exponent `-x² + c·|x|` tends to `-∞` along `cocompact ℝ`, for any `c`.
Split into the two tails: on `atTop`, `|x| = x`; on `atBot`, `|x| = -x`; the
downward parabola dominates either way. -/
theorem tendsto_neg_sq_add_mul_abs_atBot (c : ℝ) :
    Tendsto (fun x : ℝ => -x ^ 2 + c * |x|) (cocompact ℝ) atBot := by
  rw [cocompact_eq_atBot_atTop, tendsto_sup]
  constructor
  · -- atBot tail: eventually `|x| = -x`, function `= -x² - c·x`.
    have hkey : Tendsto (fun t : ℝ => -t ^ 2 + c * (-t)) atBot atBot := by
      have hcomp := (tendsto_neg_sq_add_mul_atTop_atBot c).comp tendsto_neg_atBot_atTop
      refine hcomp.congr (fun t => ?_)
      simp only [Function.comp_apply]
      ring
    refine hkey.congr' ?_
    filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
    rw [abs_of_nonpos hx]
  · -- atTop tail: eventually `|x| = x`, function `= -x² + c·x`.
    refine (tendsto_neg_sq_add_mul_atTop_atBot c).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [abs_of_nonneg hx]

/-! ## The concrete witness function and its bounds -/

/-- The witness test function `φ(x) = exp(-x/2 - x²)`. -/
def kadiriWitnessPhi : ℝ → ℂ := fun x => Complex.exp (-(x : ℂ) / 2 - (x : ℂ) ^ 2)

/-- The witness inner polynomial `x ↦ -x/2 - x²` (as a map `ℝ → ℂ`). -/
private def kadiriWitnessInner : ℝ → ℂ := fun x => -(x : ℂ) / 2 - (x : ℂ) ^ 2

private theorem hasDerivAt_kadiriWitnessInner (x : ℝ) :
    HasDerivAt kadiriWitnessInner (-(1 / 2 : ℂ) - 2 * (x : ℂ)) x := by
  have hx : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  have hlin : HasDerivAt (fun t : ℝ => -(t : ℂ) / 2) (-(1 / 2 : ℂ)) x := by
    have := (hx.neg).div_const 2
    simpa [neg_div] using this
  have hsq : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2) (2 * (x : ℂ)) x := by
    have h := hx.pow 2
    norm_num at h
    exact h
  exact hlin.sub hsq

theorem kadiriWitnessPhi_contDiff : ContDiff ℝ 1 kadiriWitnessPhi := by
  have hinner : ContDiff ℝ 1 kadiriWitnessInner := by
    have hofReal : ContDiff ℝ 1 (fun x : ℝ => (x : ℂ)) :=
      Complex.ofRealCLM.contDiff
    have : ContDiff ℝ 1 (fun x : ℝ => -(x : ℂ) / 2 - (x : ℂ) ^ 2) := by
      have h1 : ContDiff ℝ 1 (fun x : ℝ => -(x : ℂ) / 2) :=
        (hofReal.neg).div_const 2
      have h2 : ContDiff ℝ 1 (fun x : ℝ => (x : ℂ) ^ 2) := hofReal.pow 2
      exact h1.sub h2
    exact this
  exact Complex.contDiff_exp.comp hinner

/-- Pointwise derivative of the witness: `φ'(x) = (-1/2 - 2x)·φ(x)`. -/
theorem kadiriWitnessPhi_deriv (x : ℝ) :
    deriv kadiriWitnessPhi x =
      (-(1 / 2 : ℂ) - 2 * (x : ℂ)) * kadiriWitnessPhi x := by
  have hcomp : HasDerivAt kadiriWitnessPhi
      ((-(1 / 2 : ℂ) - 2 * (x : ℂ)) * kadiriWitnessPhi x) x := by
    have hinner := hasDerivAt_kadiriWitnessInner x
    have h := hinner.cexp
    rw [mul_comm] at h
    exact h
  exact hcomp.deriv

/-- `φ(x)·e^{x/2} = e^{-x²}` pointwise. -/
theorem kadiriWitnessPhi_mul_exp (x : ℝ) :
    kadiriWitnessPhi x * Complex.exp ((x : ℂ) / 2) = Complex.exp (-(x : ℂ) ^ 2) := by
  rw [kadiriWitnessPhi, ← Complex.exp_add]
  congr 1
  ring

/-- Norm of the damped witness: `‖φ(x)·e^{x/2}‖ = e^{-x²}`. -/
theorem norm_kadiriWitnessPhi_mul_exp (x : ℝ) :
    ‖kadiriWitnessPhi x * Complex.exp ((x : ℂ) / 2)‖ = Real.exp (-x ^ 2) := by
  rw [kadiriWitnessPhi_mul_exp, Complex.norm_exp]
  congr 1
  rw [show -(x : ℂ) ^ 2 = ((-x ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]

/-- The damped witness `φ(x)·e^{x/2} = e^{-x²}` is `O(e^{-(3/2)|x|})`. -/
theorem kadiriWitnessPhi_mul_exp_isBigO :
    (fun x : ℝ => kadiriWitnessPhi x * Complex.exp ((x : ℂ) / 2))
      =O[cocompact ℝ] fun x : ℝ => Real.exp (-(1 / 2 + 1) * |x|) := by
  -- Reduce to a real little-o via the norm identity.
  have hlit :
      (fun x : ℝ => Real.exp (-x ^ 2))
        =o[cocompact ℝ] fun x : ℝ => Real.exp (-(1 / 2 + 1) * |x|) := by
    apply isLittleO_rexp_of_sub_tendsto_atBot
    have := tendsto_neg_sq_add_mul_abs_atBot (3 / 2)
    refine this.congr (fun x => ?_)
    ring
  have hbigO := hlit.isBigO
  -- Transfer through the norm.
  rw [← isBigO_norm_left]
  refine hbigO.congr_left (fun x => ?_)
  exact (norm_kadiriWitnessPhi_mul_exp x).symm

/-- The damped witness derivative `φ'(x)·e^{x/2} = (-1/2-2x)·e^{-x²}` is
`O(e^{-(3/2)|x|})`. -/
theorem kadiriWitnessPhi_deriv_mul_exp_isBigO :
    (fun x : ℝ => deriv kadiriWitnessPhi x * Complex.exp ((x : ℂ) / 2))
      =O[cocompact ℝ] fun x : ℝ => Real.exp (-(1 / 2 + 1) * |x|) := by
  -- Pointwise norm: ‖φ'(x)·e^{x/2}‖ = |(-1/2-2x)|·e^{-x²}, bounded by e^{|x|}·e^{-x²}.
  have hnorm : ∀ x : ℝ,
      ‖deriv kadiriWitnessPhi x * Complex.exp ((x : ℂ) / 2)‖
        = ‖(-(1 / 2 : ℂ) - 2 * (x : ℂ))‖ * Real.exp (-x ^ 2) := by
    intro x
    rw [kadiriWitnessPhi_deriv, mul_assoc, norm_mul]
    rw [norm_kadiriWitnessPhi_mul_exp x]
  -- Dominate the polynomial factor by exp(|x|) and combine the exponents.
  have hlit :
      (fun x : ℝ => Real.exp (2 * |x| - x ^ 2))
        =o[cocompact ℝ] fun x : ℝ => Real.exp (-(1 / 2 + 1) * |x|) := by
    apply isLittleO_rexp_of_sub_tendsto_atBot
    have := tendsto_neg_sq_add_mul_abs_atBot (7 / 2)
    refine this.congr (fun x => ?_)
    ring
  have hbigO := hlit.isBigO
  -- The norm function is ≤ the dominating exponential pointwise.
  have hle : ∀ x : ℝ,
      ‖deriv kadiriWitnessPhi x * Complex.exp ((x : ℂ) / 2)‖
        ≤ Real.exp (2 * |x| - x ^ 2) := by
    intro x
    rw [hnorm x, Real.exp_sub]
    have hpoly : ‖(-(1 / 2 : ℂ) - 2 * (x : ℂ))‖ ≤ Real.exp (2 * |x|) := by
      have h1 : ‖(-(1 / 2 : ℂ) - 2 * (x : ℂ))‖ ≤ 1 + 2 * |x| := by
        calc ‖(-(1 / 2 : ℂ) - 2 * (x : ℂ))‖
            ≤ ‖(-(1 / 2 : ℂ))‖ + ‖(2 * (x : ℂ))‖ := norm_sub_le _ _
          _ ≤ 1 + 2 * |x| := by
              rw [norm_neg, norm_mul]
              simp [Complex.norm_real, Real.norm_eq_abs]
              norm_num
      have h2 : 1 + 2 * |x| ≤ Real.exp (2 * |x|) := by
        have := Real.add_one_le_exp (2 * |x|)
        linarith
      exact le_trans h1 h2
    calc ‖(-(1 / 2 : ℂ) - 2 * (x : ℂ))‖ * Real.exp (-x ^ 2)
        ≤ Real.exp (2 * |x|) * Real.exp (-x ^ 2) :=
          mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _)
      _ = Real.exp (2 * |x|) / Real.exp (x ^ 2) := by
          rw [Real.exp_neg]; ring
  -- Chain ‖·‖ ≤ exp(2|x|-x²) =o(...) to get =O.
  have hdom : (fun x : ℝ => deriv kadiriWitnessPhi x * Complex.exp ((x : ℂ) / 2))
      =O[cocompact ℝ] fun x : ℝ => Real.exp (2 * |x| - x ^ 2) :=
    Asymptotics.IsBigO.of_norm_le hle
  exact hdom.trans hbigO

/-! ## The witness, packaged as `KadiriPhiConditionB` -/

/-- The Gaussian-damped function `φ(x) = exp(-x/2 - x²)` satisfies Kadiri's
condition (B) with strip half-width `a = 1/2` and margin `b = 1`. -/
theorem kadiriWitnessPhi_conditionB :
    KadiriPhiConditionB kadiriWitnessPhi (1 / 2) where
  contDiff := kadiriWitnessPhi_contDiff
  bpos := by
    refine ⟨1, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · exact kadiriWitnessPhi_mul_exp_isBigO
    · exact kadiriWitnessPhi_deriv_mul_exp_isBigO

/-- **Non-vacuity of condition (B).**  There is a concrete `φ` and a positive
strip half-width `a` satisfying Kadiri's condition (B). -/
theorem kadiriPhiConditionB_witness :
    ∃ (φ : ℝ → ℂ) (a : ℝ), 0 < a ∧ KadiriPhiConditionB φ a :=
  ⟨kadiriWitnessPhi, 1 / 2, by norm_num, kadiriWitnessPhi_conditionB⟩

/-- The q1 top-horizontal PV vanishing capstone is non-vacuous: the concrete
witness satisfies condition (B) and drives the canonical PV to `0`. -/
theorem kadiri_thm_3_1_q1_top_horizontal_pv_vanishes_witness :
    ∃ (φ : ℝ → ℂ) (a : ℝ), 0 < a ∧ KadiriPhiConditionB φ a ∧
      Filter.Tendsto (kadiriTopHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  ⟨kadiriWitnessPhi, 1 / 2, by norm_num, kadiriWitnessPhi_conditionB,
    kadiri_thm_3_1_q1_top_horizontal_pv_vanishes_of_conditionB_finalBound
      (by norm_num) kadiriWitnessPhi_conditionB⟩

/-- The q1 bottom-horizontal PV vanishing capstone is non-vacuous. -/
theorem kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes_witness :
    ∃ (φ : ℝ → ℂ) (a : ℝ), 0 < a ∧ KadiriPhiConditionB φ a ∧
      Filter.Tendsto (kadiriBotHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  ⟨kadiriWitnessPhi, 1 / 2, by norm_num, kadiriWitnessPhi_conditionB,
    kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes_of_conditionB_finalBound
      (by norm_num) kadiriWitnessPhi_conditionB⟩

end

end Kadiri
