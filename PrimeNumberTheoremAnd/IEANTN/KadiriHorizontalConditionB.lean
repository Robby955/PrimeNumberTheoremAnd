import PrimeNumberTheoremAnd.IEANTN.KadiriPhiDecay
import PrimeNumberTheoremAnd.IEANTN.KadiriEq12Foundations
import PrimeNumberTheoremAnd.IEANTN.KadiriFinalBoundAssembly

/-!
# Kadiri Thm 3.1 horizontals: the condition-(B) capstone

This strictly-additive sidecar threads Kadiri's condition (B) on the test
function `φ` through the already-proved canonical horizontal PV route to the
q1 horizontal PV vanishing.  It sits on top of the condition-B integrability
and Fourier-IBP atoms in `KadiriPhiDecay`, and on the unconditional
partial-fraction-remainder side
`kadiriHorizontalPFRemainderLinearInput_of_finalBound`.

## Structure of the close

The canonical PV route reduces the q1 horizontal vanishing to two
`φ`-dependent contracts:

* `KadiriHorizontalPhiPrimeDecayBound φ a` — the `C¹` decay of the bilateral
  Laplace transform `Φ(s) = ∫ φ(y) e^{-s y} dy` and its derivative on the two
  horizontal strips, `‖Φ‖, ‖Φ′‖ ≤ A / |T|`;
* `KadiriHorizontalPVIntegrationBound φ a` — the resulting
  `O(log^k |T| / |T|)` estimate on the two horizontal integrals at non-zero
  ordinates.

Both are produced from `KadiriPhiConditionB`, the structured form of Kadiri's
hypothesis (φ ∈ C¹, with `φ(x) e^{x/2}` and `φ'(x) e^{x/2}` of exponential decay
`O(e^{-(1/2+b)|x|})` for some margin `b > a`).  The remaining genuine analytic
content is the two integrations by parts giving the `1/|T|` decay; it is named
explicitly as the obligation `KadiriHorizontalPhiC1Decay_of_conditionB`, with the
PV-integration assembly named as `KadiriHorizontalPVIntegration_of_conditionB`.
Every theorem below is axiom-clean and uses only the proved route.
-/

namespace Kadiri

open MeasureTheory Complex Filter Asymptotics
open scoped Topology

noncomputable section

/-! ## Condition (B) as a structured hypothesis -/

/-- Kadiri's condition (B) on the test function `φ`, in the exact form already
consumed by the horizontal vanishing wrappers in `KadiriHorizontalObstruction`
and the condition-B integrability lemmas in `KadiriPhiDecay`: `φ` is `C¹`, and
both `φ(x) e^{x/2}` and `φ'(x) e^{x/2}` decay like `e^{-(1/2+b)|x|}` for some
margin `b > 0` strictly exceeding the strip half-width `a` (and `a < 1`). -/
structure KadiriPhiConditionB (φ : ℝ → ℂ) (a : ℝ) : Prop where
  contDiff : ContDiff ℝ 1 φ
  bpos : ∃ b : ℝ, 0 < b ∧ a < b ∧ a < 1 ∧
    ((fun x : ℝ ↦ φ x * Complex.exp ((x : ℂ) / 2))
      =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|)) ∧
    ((fun x : ℝ ↦ deriv φ x * Complex.exp ((x : ℂ) / 2))
      =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|))

/-- The original q1 condition-(B) hypotheses package into the structured
`KadiriPhiConditionB` contract used by the horizontal PV route. -/
theorem kadiriPhiConditionB_of_q1_hypotheses
    {φ : ℝ → ℂ} {a b : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hb : 0 < b) (hab : a < b) (ha1 : a < 1)
    (hφ_decay : (fun x : ℝ ↦ φ x * Complex.exp ((x : ℂ) / 2))
      =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * Complex.exp ((x : ℂ) / 2))
      =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|)) :
    KadiriPhiConditionB φ a where
  contDiff := hφ
  bpos := ⟨b, hb, hab, ha1, hφ_decay, hφ'_decay⟩

/-- Condition (B) supplies, on every vertical line `σ ∈ [-a, 1+a]` of the strip,
the weighted `L¹` integrability of `φ(y) e^{σ y}` that underlies the Laplace
representation `Φ(-(σ + iT)) = ∫ φ(y) e^{(σ+iT) y} dy`. -/
private theorem KadiriPhiConditionB.weightedStripIntegrable
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    Integrable (fun y : ℝ => φ y * Complex.exp ((σ : ℂ) * (y : ℂ))) := by
  obtain ⟨b, _hb, hab, _ha1, hφ_decay, _hφ'_decay⟩ := hB.bpos
  exact kadiriConditionB_weightedStripIntegrable hB.contDiff hφ_decay hab hσ

/-- Condition (B) supplies the same weighted `L¹` integrability for `deriv φ`,
the input to the second integration by parts giving the `Φ′` decay. -/
private theorem KadiriPhiConditionB.weightedDerivStripIntegrable
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    Integrable (fun y : ℝ => deriv φ y * Complex.exp ((σ : ℂ) * (y : ℂ))) := by
  obtain ⟨b, _hb, hab, _ha1, _hφ_decay, hφ'_decay⟩ := hB.bpos
  exact kadiriConditionB_weightedDerivStripIntegrable hB.contDiff hφ'_decay hab hσ

/-- Condition (B) gives the weighted-line Fourier/IBP `1 / |T|` estimate on
the whole horizontal strip. -/
private theorem KadiriPhiConditionB.weightedLine_fourier_norm_le_deriv_integral_div_abs
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    {σ T : ℝ} (hT : T ≠ 0) (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    ‖∫ y : ℝ,
        (φ y * Complex.exp ((σ : ℂ) * (y : ℂ))) *
          Complex.exp (((T * y : ℝ) : ℂ) * Complex.I)‖
      ≤ (∫ y : ℝ,
          ‖deriv (fun x : ℝ => φ x * Complex.exp ((σ : ℂ) * (x : ℂ))) y *
            Complex.exp (((T * y : ℝ) : ℂ) * Complex.I)‖) / |T| := by
  obtain ⟨b, _hb, hab, _ha1, hφ_decay, hφ'_decay⟩ := hB.bpos
  exact kadiriConditionB_weightedLine_fourier_norm_le_deriv_integral_div_abs
    hB.contDiff hT hφ_decay hφ'_decay hab hσ

/-- Condition (B) gives the pointwise top-segment `Φ` estimate after the
weighted-line rewrite. -/
private theorem KadiriPhiConditionB.topHorizontalPhi_norm_le_weightedLine_deriv_integral_div_abs
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    {σ T : ℝ} (hT : T ≠ 0) (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    ‖kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))‖
      ≤ (∫ y : ℝ,
          ‖deriv (fun x : ℝ => φ x * Complex.exp ((σ : ℂ) * (x : ℂ))) y *
            Complex.exp (((T * y : ℝ) : ℂ) * Complex.I)‖) / |T| := by
  obtain ⟨b, _hb, hab, _ha1, hφ_decay, hφ'_decay⟩ := hB.bpos
  exact kadiriHorizontalPhi_top_norm_le_weightedLine_deriv_integral_div_abs
    hB.contDiff hT hφ_decay hφ'_decay hab hσ

/-- Condition (B) gives the pointwise bottom-segment `Φ` estimate after the
weighted-line rewrite. -/
private theorem KadiriPhiConditionB.botHorizontalPhi_norm_le_weightedLine_deriv_integral_div_abs
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    {σ T : ℝ} (hT : T ≠ 0) (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    ‖kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))‖
      ≤ (∫ y : ℝ,
          ‖deriv (fun x : ℝ => φ x * Complex.exp ((σ : ℂ) * (x : ℂ))) y *
            Complex.exp ((((-T) * y : ℝ) : ℂ) * Complex.I)‖) / |T| := by
  obtain ⟨b, _hb, hab, _ha1, hφ_decay, hφ'_decay⟩ := hB.bpos
  exact kadiriHorizontalPhi_bot_norm_le_weightedLine_deriv_integral_div_abs
    hB.contDiff hT hφ_decay hφ'_decay hab hσ

/-- Condition (B) identifies the complex derivative of the horizontal transform
through the full-strip Laplace differentiability lemma.  This is the derivative
bridge needed before the `Φ'` Fourier/IBP estimate can be applied on the two
horizontal segments. -/
private theorem KadiriPhiConditionB.kadiriHorizontalPhi_hasDerivAt
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    {z0 : ℂ} (hz : (-z0).re ∈ Set.Icc (-a) (1 + a)) :
    HasDerivAt (fun z : ℂ => kadiriHorizontalPhi φ z)
      (-(∫ y : ℝ,
          φ y * ((y : ℂ) * Complex.exp ((-z0) * (y : ℂ))) ∂volume)) z0 := by
  obtain ⟨b, _hb, hab, _ha1, hφ_decay, _hφ'_decay⟩ := hB.bpos
  have hslo : -b < (-z0).re := by
    linarith [hz.1, hab]
  have hshi : (-z0).re < 1 + b := by
    linarith [hz.2, hab]
  let F : ℂ → ℂ := fun s : ℂ =>
    ∫ y : ℝ, φ y * Complex.exp (s * (y : ℂ)) ∂volume
  have hF :
      HasDerivAt F
        (∫ y : ℝ,
          φ y * ((y : ℂ) * Complex.exp ((-z0) * (y : ℂ))) ∂volume)
        (-z0) := by
    simpa [F] using
      (kadiri_laplace_exp_hasDerivAt_of_full_strip
        (φ := φ) (b := b) (s0 := -z0)
        hB.contDiff hslo hshi hφ_decay)
  have hneg : HasDerivAt (fun z : ℂ => -z) (-1) z0 := by
    simpa using (hasDerivAt_id z0).neg
  have hcomp := hF.comp z0 hneg
  convert hcomp using 1
  ring

/-- Pointwise derivative formula for `kadiriHorizontalPhi`, extracted from the
condition-(B) full-strip differentiability bridge. -/
private theorem KadiriPhiConditionB.kadiriHorizontalPhi_deriv_eq
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    {z0 : ℂ} (hz : (-z0).re ∈ Set.Icc (-a) (1 + a)) :
    deriv (fun z : ℂ => kadiriHorizontalPhi φ z) z0 =
      -(∫ y : ℝ,
          φ y * ((y : ℂ) * Complex.exp ((-z0) * (y : ℂ))) ∂volume) :=
  (hB.kadiriHorizontalPhi_hasDerivAt hz).deriv

/-- Top-segment specialization of the condition-(B) derivative formula. -/
private theorem KadiriPhiConditionB.topHorizontalPhi_deriv_eq
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    {σ T : ℝ} (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
        (-(kadiriTopHorizontalPoint T σ)) =
      -(∫ y : ℝ,
          φ y * ((y : ℂ) *
            Complex.exp ((kadiriTopHorizontalPoint T σ) * (y : ℂ))) ∂volume) := by
  simpa using
    (hB.kadiriHorizontalPhi_deriv_eq
      (z0 := -(kadiriTopHorizontalPoint T σ)) (by
        simpa [kadiriTopHorizontalPoint] using hσ))

/-- Bottom-segment specialization of the condition-(B) derivative formula. -/
private theorem KadiriPhiConditionB.botHorizontalPhi_deriv_eq
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    {σ T : ℝ} (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
        (-(kadiriBotHorizontalPoint T σ)) =
      -(∫ y : ℝ,
          φ y * ((y : ℂ) *
            Complex.exp ((kadiriBotHorizontalPoint T σ) * (y : ℂ))) ∂volume) := by
  simpa using
    (hB.kadiriHorizontalPhi_deriv_eq
      (z0 := -(kadiriBotHorizontalPoint T σ)) (by
        simpa [kadiriBotHorizontalPoint] using hσ))

/-- Top-segment derivative formula rewritten as a weighted Fourier integral. -/
private theorem KadiriPhiConditionB.topHorizontalPhi_deriv_eq_weightedLineFourier
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    {σ T : ℝ} (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
        (-(kadiriTopHorizontalPoint T σ)) =
      -(∫ y : ℝ,
          ((φ y * (y : ℂ)) * Complex.exp ((σ : ℂ) * (y : ℂ))) *
            Complex.exp (((T * y : ℝ) : ℂ) * Complex.I)) := by
  rw [hB.topHorizontalPhi_deriv_eq hσ]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  calc
    φ y * ((y : ℂ) *
        Complex.exp ((kadiriTopHorizontalPoint T σ) * (y : ℂ)))
        = φ y * ((y : ℂ) *
            Complex.exp ((σ : ℂ) * (y : ℂ) + ((T * y : ℝ) : ℂ) * Complex.I)) := by
          congr 2
          congr 1
          simp [kadiriTopHorizontalPoint]
          ring
    _ = φ y * ((y : ℂ) *
          (Complex.exp ((σ : ℂ) * (y : ℂ)) *
            Complex.exp (((T * y : ℝ) : ℂ) * Complex.I))) := by
          rw [Complex.exp_add]
    _ = ((φ y * (y : ℂ)) * Complex.exp ((σ : ℂ) * (y : ℂ))) *
          Complex.exp (((T * y : ℝ) : ℂ) * Complex.I) := by
          ring

/-- Bottom-segment derivative formula rewritten as a weighted Fourier integral. -/
private theorem KadiriPhiConditionB.botHorizontalPhi_deriv_eq_weightedLineFourier
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    {σ T : ℝ} (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
        (-(kadiriBotHorizontalPoint T σ)) =
      -(∫ y : ℝ,
          ((φ y * (y : ℂ)) * Complex.exp ((σ : ℂ) * (y : ℂ))) *
            Complex.exp ((((-T) * y : ℝ) : ℂ) * Complex.I)) := by
  rw [hB.botHorizontalPhi_deriv_eq hσ]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  calc
    φ y * ((y : ℂ) *
        Complex.exp ((kadiriBotHorizontalPoint T σ) * (y : ℂ)))
        = φ y * ((y : ℂ) *
            Complex.exp ((σ : ℂ) * (y : ℂ) + (((-T) * y : ℝ) : ℂ) * Complex.I)) := by
          congr 2
          congr 1
          simp [kadiriBotHorizontalPoint]
          ring
    _ = φ y * ((y : ℂ) *
          (Complex.exp ((σ : ℂ) * (y : ℂ)) *
            Complex.exp ((((-T) * y : ℝ) : ℂ) * Complex.I))) := by
          rw [Complex.exp_add]
    _ = ((φ y * (y : ℂ)) * Complex.exp ((σ : ℂ) * (y : ℂ))) *
          Complex.exp ((((-T) * y : ℝ) : ℂ) * Complex.I) := by
          ring

/-! ## Uniform endpoint envelopes on the condition-(B) strip -/

/-- On a nonempty horizontal strip, condition (B) gives an endpoint envelope for
the weighted `L¹` norm of `φ`. -/
private theorem KadiriPhiConditionB.weightedEndpointEnvelopeIntegrable
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (hne : -a ≤ 1 + a) :
    Integrable (fun y : ℝ =>
      ‖φ y‖ * (Real.exp ((-a) * y) + Real.exp ((1 + a) * y))) := by
  obtain ⟨b, hb, hab, _ha1, hφ_decay, _hφ'_decay⟩ := hB.bpos
  have hleft_lo : -b < -a := by linarith
  have hright_hi : 1 + a < 1 + b := by linarith
  have hleft_hi : -a < 1 + b := by linarith
  have hright_lo : -b < 1 + a := by linarith
  have hleft :
      Integrable (fun y : ℝ =>
        Complex.exp (((-a : ℝ) : ℂ) * (y : ℂ)) * φ y) :=
    kadiri_laplace_full_strip_weight_integrable_of_continuous
      hB.contDiff.continuous hleft_lo hleft_hi hφ_decay
  have hright :
      Integrable (fun y : ℝ =>
        Complex.exp (((1 + a : ℝ) : ℂ) * (y : ℂ)) * φ y) :=
    kadiri_laplace_full_strip_weight_integrable_of_continuous
      hB.contDiff.continuous hright_lo hright_hi hφ_decay
  convert hleft.norm.add hright.norm using 1
  ext y
  simp [Complex.norm_exp, mul_add, mul_comm]

/-- On a nonempty horizontal strip, condition (B) gives an endpoint envelope for
the weighted `L¹` norm of `φ'`. -/
private theorem KadiriPhiConditionB.weightedDerivEndpointEnvelopeIntegrable
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (hne : -a ≤ 1 + a) :
    Integrable (fun y : ℝ =>
      ‖deriv φ y‖ * (Real.exp ((-a) * y) + Real.exp ((1 + a) * y))) := by
  obtain ⟨b, hb, hab, _ha1, _hφ_decay, hφ'_decay⟩ := hB.bpos
  have hleft_lo : -b < -a := by linarith
  have hright_hi : 1 + a < 1 + b := by linarith
  have hleft_hi : -a < 1 + b := by linarith
  have hright_lo : -b < 1 + a := by linarith
  have hderiv_cont : Continuous (fun y : ℝ => deriv φ y) :=
    hB.contDiff.continuous_deriv (by norm_num)
  have hleft :
      Integrable (fun y : ℝ =>
        Complex.exp (((-a : ℝ) : ℂ) * (y : ℂ)) * deriv φ y) :=
    kadiri_laplace_full_strip_weight_integrable_of_continuous
      hderiv_cont hleft_lo hleft_hi hφ'_decay
  have hright :
      Integrable (fun y : ℝ =>
        Complex.exp (((1 + a : ℝ) : ℂ) * (y : ℂ)) * deriv φ y) :=
    kadiri_laplace_full_strip_weight_integrable_of_continuous
      hderiv_cont hright_lo hright_hi hφ'_decay
  convert hleft.norm.add hright.norm using 1
  ext y
  simp [Complex.norm_exp, mul_add, mul_comm]

/-- On a nonempty horizontal strip, condition (B) gives a first-moment endpoint
envelope for `φ`. -/
private theorem KadiriPhiConditionB.weightedEndpointMomentEnvelopeIntegrable
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (hne : -a ≤ 1 + a) :
    Integrable (fun y : ℝ =>
      ‖(y : ℂ)‖ * ‖φ y‖ *
        (Real.exp ((-a) * y) + Real.exp ((1 + a) * y))) := by
  obtain ⟨b, _hb, hab, _ha1, hφ_decay, _hφ'_decay⟩ := hB.bpos
  have hleft_lo : -b < -a := by linarith
  have hright_hi : 1 + a < 1 + b := by linarith
  exact kadiri_laplace_full_strip_exp_interval_moment_integrable_of_continuous
    hB.contDiff.continuous hleft_lo hright_hi hne hφ_decay

/-- On a nonempty horizontal strip, condition (B) gives a first-moment endpoint
envelope for `φ'`. -/
private theorem KadiriPhiConditionB.weightedDerivEndpointMomentEnvelopeIntegrable
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (hne : -a ≤ 1 + a) :
    Integrable (fun y : ℝ =>
      ‖(y : ℂ)‖ * ‖deriv φ y‖ *
        (Real.exp ((-a) * y) + Real.exp ((1 + a) * y))) := by
  obtain ⟨b, _hb, hab, _ha1, _hφ_decay, hφ'_decay⟩ := hB.bpos
  have hleft_lo : -b < -a := by linarith
  have hright_hi : 1 + a < 1 + b := by linarith
  have hderiv_cont : Continuous (fun y : ℝ => deriv φ y) :=
    hB.contDiff.continuous_deriv (by norm_num)
  exact kadiri_laplace_full_strip_exp_interval_moment_integrable_of_continuous
    hderiv_cont hleft_lo hright_hi hne hφ'_decay

/-- The derivative of the weighted line source is pointwise dominated by the
endpoint envelope on the nonempty horizontal strip. -/
private theorem KadiriPhiConditionB.weightedLine_deriv_norm_le_endpointEnvelope
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    {σ T y : ℝ} (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    ‖deriv (fun x : ℝ => φ x * Complex.exp ((σ : ℂ) * (x : ℂ))) y *
        Complex.exp (((T * y : ℝ) : ℂ) * Complex.I)‖
      ≤ (‖deriv φ y‖ + max |(-a)| |(1 + a)| * ‖φ y‖) *
          (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)) := by
  let M : ℝ := max |(-a)| |(1 + a)|
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (-a)) (le_max_left _ _)
  have hσ_abs : |σ| ≤ M := by
    have hleft_abs : |(-a)| ≤ M := le_max_left _ _
    have hright_abs : |(1 + a)| ≤ M := le_max_right _ _
    have hleft : -M ≤ σ := by
      exact le_trans (abs_le.mp hleft_abs).1 hσ.1
    have hright : σ ≤ M := by
      exact le_trans hσ.2 (abs_le.mp hright_abs).2
    exact abs_le.mpr ⟨hleft, hright⟩
  have hexp_re : (((σ : ℂ) * (y : ℂ))).re = σ * y := by
    norm_num [Complex.mul_re]
  have hosc_re : ((((T * y : ℝ) : ℂ) * Complex.I)).re = 0 := by
    norm_num [Complex.mul_re]
  have hexp_le :
      Real.exp (σ * y) ≤ Real.exp ((-a) * y) + Real.exp ((1 + a) * y) := by
    by_cases hy : 0 ≤ y
    · have hmul : σ * y ≤ (1 + a) * y :=
        mul_le_mul_of_nonneg_right hσ.2 hy
      exact le_trans (Real.exp_le_exp.mpr hmul)
        (le_add_of_nonneg_left (Real.exp_nonneg _))
    · have hy' : y ≤ 0 := le_of_not_ge hy
      have hmul : σ * y ≤ (-a) * y :=
        mul_le_mul_of_nonpos_right hσ.1 hy'
      exact le_trans (Real.exp_le_exp.mpr hmul)
        (le_add_of_nonneg_right (Real.exp_nonneg _))
  rw [kadiriConditionB_weightedLine_deriv_eq hB.contDiff σ y]
  calc
    ‖(deriv φ y * Complex.exp ((σ : ℂ) * (y : ℂ)) +
          (σ : ℂ) * (φ y * Complex.exp ((σ : ℂ) * (y : ℂ)))) *
        Complex.exp (((T * y : ℝ) : ℂ) * Complex.I)‖
        = ‖deriv φ y * Complex.exp ((σ : ℂ) * (y : ℂ)) +
            (σ : ℂ) * (φ y * Complex.exp ((σ : ℂ) * (y : ℂ)))‖ := by
          rw [norm_mul, Complex.norm_exp, hosc_re, Real.exp_zero, mul_one]
    _ ≤ ‖deriv φ y * Complex.exp ((σ : ℂ) * (y : ℂ))‖ +
          ‖(σ : ℂ) * (φ y * Complex.exp ((σ : ℂ) * (y : ℂ)))‖ :=
        norm_add_le _ _
    _ = (‖deriv φ y‖ + |σ| * ‖φ y‖) * Real.exp (σ * y) := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, hexp_re,
            Complex.norm_real, Real.norm_eq_abs]
          ring
    _ ≤ (‖deriv φ y‖ + M * ‖φ y‖) * Real.exp (σ * y) := by
          gcongr
    _ ≤ (‖deriv φ y‖ + M * ‖φ y‖) *
          (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)) := by
          exact mul_le_mul_of_nonneg_left hexp_le
            (add_nonneg (norm_nonneg _) (mul_nonneg hM_nonneg (norm_nonneg _)))

/-- The endpoint envelope that dominates the weighted-line derivative is
integrable on the nonempty horizontal strip. -/
private theorem KadiriPhiConditionB.weightedLine_deriv_endpointEnvelopeIntegrable
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (hne : -a ≤ 1 + a) :
    Integrable (fun y : ℝ =>
      (‖deriv φ y‖ + max |(-a)| |(1 + a)| * ‖φ y‖) *
        (Real.exp ((-a) * y) + Real.exp ((1 + a) * y))) := by
  let M : ℝ := max |(-a)| |(1 + a)|
  have hderiv := hB.weightedDerivEndpointEnvelopeIntegrable hne
  have hphi := hB.weightedEndpointEnvelopeIntegrable hne
  have hscaled :
      Integrable (fun y : ℝ =>
        M * (‖φ y‖ * (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)))) :=
    hphi.const_mul M
  have hadd :
      Integrable (fun y : ℝ =>
        ‖deriv φ y‖ * (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)) +
          M * (‖φ y‖ * (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)))) :=
    hderiv.add hscaled
  convert hadd using 1
  ext y
  dsimp [M]
  ring

/-- The weighted-line derivative integral is bounded by the endpoint-envelope
integral, uniformly in the strip parameter `σ`. -/
private theorem KadiriPhiConditionB.weightedLine_deriv_integral_le_endpointEnvelope_integral
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (hne : -a ≤ 1 + a) {σ T : ℝ} (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    (∫ y : ℝ,
      ‖deriv (fun x : ℝ => φ x * Complex.exp ((σ : ℂ) * (x : ℂ))) y *
        Complex.exp (((T * y : ℝ) : ℂ) * Complex.I)‖)
      ≤ ∫ y : ℝ,
          (‖deriv φ y‖ + max |(-a)| |(1 + a)| * ‖φ y‖) *
            (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)) := by
  exact integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun y => norm_nonneg _)
    (hB.weightedLine_deriv_endpointEnvelopeIntegrable hne)
    (Filter.Eventually.of_forall fun y =>
      hB.weightedLine_deriv_norm_le_endpointEnvelope (T := T) hσ)

/-- Exact-name wrapper for the weighted-line derivative endpoint-envelope
bound used in the condition-B horizontal `Φ` IBP. -/
private theorem KadiriPhiConditionB.weightedLine_deriv_integral_le_endpointEnvelope
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (hne : -a ≤ 1 + a) {σ T : ℝ} (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    (∫ y : ℝ,
      ‖deriv (fun x : ℝ => φ x * Complex.exp ((σ : ℂ) * (x : ℂ))) y *
        Complex.exp (((T * y : ℝ) : ℂ) * Complex.I)‖)
      ≤ ∫ y : ℝ,
          (‖deriv φ y‖ + max |(-a)| |(1 + a)| * ‖φ y‖) *
            (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)) := by
  exact hB.weightedLine_deriv_integral_le_endpointEnvelope_integral (T := T) hne hσ

/-- Top-segment `Φ` estimate with the strip-uniform endpoint-envelope constant. -/
private theorem KadiriPhiConditionB.topHorizontalPhi_norm_le_endpointEnvelope_integral_div_abs
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (hne : -a ≤ 1 + a) {σ T : ℝ} (hT : T ≠ 0)
    (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    ‖kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))‖
      ≤ (∫ y : ℝ,
          (‖deriv φ y‖ + max |(-a)| |(1 + a)| * ‖φ y‖) *
            (Real.exp ((-a) * y) + Real.exp ((1 + a) * y))) / |T| := by
  exact (hB.topHorizontalPhi_norm_le_weightedLine_deriv_integral_div_abs hT hσ).trans
    (div_le_div_of_nonneg_right
      (hB.weightedLine_deriv_integral_le_endpointEnvelope_integral
        (T := T) hne hσ)
      (abs_nonneg T))

/-- Bottom-segment `Φ` estimate with the strip-uniform endpoint-envelope
constant. -/
private theorem KadiriPhiConditionB.botHorizontalPhi_norm_le_endpointEnvelope_integral_div_abs
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (hne : -a ≤ 1 + a) {σ T : ℝ} (hT : T ≠ 0)
    (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    ‖kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))‖
      ≤ (∫ y : ℝ,
          (‖deriv φ y‖ + max |(-a)| |(1 + a)| * ‖φ y‖) *
            (Real.exp ((-a) * y) + Real.exp ((1 + a) * y))) / |T| := by
  exact (hB.botHorizontalPhi_norm_le_weightedLine_deriv_integral_div_abs hT hσ).trans
    (div_le_div_of_nonneg_right
      (hB.weightedLine_deriv_integral_le_endpointEnvelope_integral
        (T := -T) hne hσ)
      (abs_nonneg T))

/-! ## First-moment Fourier input for `Φ'` -/

/-- Differentiability of the first-moment weighted-line source used for the
`Φ'` Fourier/IBP estimate. -/
private theorem KadiriPhiConditionB.weightedMomentLineDifferentiable
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a) (σ : ℝ) :
    Differentiable ℝ
      (fun y : ℝ => φ y * ((y : ℂ) * Complex.exp ((σ : ℂ) * (y : ℂ)))) := by
  intro y
  have hlinear : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) y := by
    simpa using (hasDerivAt_id y).ofReal_comp
  have hφy : HasDerivAt φ (deriv φ y) y :=
    ((hB.contDiff.differentiable (by norm_num)) y).hasDerivAt
  have hexp : HasDerivAt (fun x : ℝ => Complex.exp ((σ : ℂ) * (x : ℂ)))
      ((σ : ℂ) * Complex.exp ((σ : ℂ) * (y : ℂ))) y := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (((hasDerivAt_id y).ofReal_comp.const_mul (σ : ℂ)).cexp)
  have hmoment : HasDerivAt
      (fun x : ℝ => (x : ℂ) * Complex.exp ((σ : ℂ) * (x : ℂ)))
      (Complex.exp ((σ : ℂ) * (y : ℂ)) +
        (y : ℂ) * ((σ : ℂ) * Complex.exp ((σ : ℂ) * (y : ℂ)))) y := by
    simpa using hlinear.mul hexp
  exact (hφy.mul hmoment).differentiableAt

/-- Pointwise derivative of the first-moment weighted-line source. -/
private theorem KadiriPhiConditionB.weightedMomentLine_deriv_eq
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (σ y : ℝ) :
    deriv (fun x : ℝ =>
        φ x * ((x : ℂ) * Complex.exp ((σ : ℂ) * (x : ℂ)))) y =
      (deriv φ y * (y : ℂ) + φ y + (σ : ℂ) * (φ y * (y : ℂ))) *
        Complex.exp ((σ : ℂ) * (y : ℂ)) := by
  have hlinear : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) y := by
    simpa using (hasDerivAt_id y).ofReal_comp
  have hφy : HasDerivAt φ (deriv φ y) y :=
    ((hB.contDiff.differentiable (by norm_num)) y).hasDerivAt
  have hexp : HasDerivAt (fun x : ℝ => Complex.exp ((σ : ℂ) * (x : ℂ)))
      ((σ : ℂ) * Complex.exp ((σ : ℂ) * (y : ℂ))) y := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (((hasDerivAt_id y).ofReal_comp.const_mul (σ : ℂ)).cexp)
  have hmoment : HasDerivAt
      (fun x : ℝ => (x : ℂ) * Complex.exp ((σ : ℂ) * (x : ℂ)))
      (Complex.exp ((σ : ℂ) * (y : ℂ)) +
        (y : ℂ) * ((σ : ℂ) * Complex.exp ((σ : ℂ) * (y : ℂ)))) y := by
    simpa using hlinear.mul hexp
  have hmul := hφy.mul hmoment
  calc
    deriv (fun x : ℝ =>
        φ x * ((x : ℂ) * Complex.exp ((σ : ℂ) * (x : ℂ)))) y
        = deriv φ y * ((y : ℂ) * Complex.exp ((σ : ℂ) * (y : ℂ))) +
          φ y * (Complex.exp ((σ : ℂ) * (y : ℂ)) +
            (y : ℂ) * ((σ : ℂ) * Complex.exp ((σ : ℂ) * (y : ℂ)))) := by
          simpa [mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using hmul.deriv
    _ = (deriv φ y * (y : ℂ) + φ y + (σ : ℂ) * (φ y * (y : ℂ))) *
        Complex.exp ((σ : ℂ) * (y : ℂ)) := by
          ring

/-- The first-moment weighted source is dominated by the endpoint moment
envelope on the horizontal strip. -/
private theorem KadiriPhiConditionB.weightedMomentLine_norm_le_endpointMomentEnvelope
    {φ : ℝ → ℂ} {a : ℝ} {σ y : ℝ}
    (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    ‖φ y * ((y : ℂ) * Complex.exp ((σ : ℂ) * (y : ℂ)))‖
      ≤ ‖(y : ℂ)‖ * ‖φ y‖ *
          (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)) := by
  have hexp_re : (((σ : ℂ) * (y : ℂ))).re = σ * y := by
    norm_num [Complex.mul_re]
  have hexp_le :
      Real.exp (σ * y) ≤ Real.exp ((-a) * y) + Real.exp ((1 + a) * y) := by
    by_cases hy : 0 ≤ y
    · have hmul : σ * y ≤ (1 + a) * y :=
        mul_le_mul_of_nonneg_right hσ.2 hy
      exact le_trans (Real.exp_le_exp.mpr hmul)
        (le_add_of_nonneg_left (Real.exp_nonneg _))
    · have hy' : y ≤ 0 := le_of_not_ge hy
      have hmul : σ * y ≤ (-a) * y :=
        mul_le_mul_of_nonpos_right hσ.1 hy'
      exact le_trans (Real.exp_le_exp.mpr hmul)
        (le_add_of_nonneg_right (Real.exp_nonneg _))
  calc
    ‖φ y * ((y : ℂ) * Complex.exp ((σ : ℂ) * (y : ℂ)))‖
        = ‖(y : ℂ)‖ * ‖φ y‖ * Real.exp (σ * y) := by
          rw [norm_mul, norm_mul, Complex.norm_exp, hexp_re]
          ring
    _ ≤ ‖(y : ℂ)‖ * ‖φ y‖ *
          (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)) := by
          exact mul_le_mul_of_nonneg_left hexp_le
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Integrability of the first-moment weighted-line source. -/
private theorem KadiriPhiConditionB.weightedMomentLineIntegrable
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (hne : -a ≤ 1 + a) {σ : ℝ} (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    Integrable (fun y : ℝ =>
      φ y * ((y : ℂ) * Complex.exp ((σ : ℂ) * (y : ℂ)))) := by
  have hcont : Continuous (fun y : ℝ =>
      φ y * ((y : ℂ) * Complex.exp ((σ : ℂ) * (y : ℂ)))) := by
    have hφcont : Continuous φ := hB.contDiff.continuous
    fun_prop
  exact (hB.weightedEndpointMomentEnvelopeIntegrable hne).mono'
    hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y =>
      KadiriPhiConditionB.weightedMomentLine_norm_le_endpointMomentEnvelope hσ)

/-- The derivative of the first-moment weighted source is dominated by the
endpoint moment envelope. -/
private theorem KadiriPhiConditionB.weightedMomentLine_deriv_norm_le_endpointMomentEnvelope
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    {σ T y : ℝ} (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    ‖deriv (fun x : ℝ =>
        φ x * ((x : ℂ) * Complex.exp ((σ : ℂ) * (x : ℂ)))) y *
        Complex.exp (((T * y : ℝ) : ℂ) * Complex.I)‖
      ≤ (‖(y : ℂ)‖ * ‖deriv φ y‖ + ‖φ y‖ +
            max |(-a)| |(1 + a)| * (‖(y : ℂ)‖ * ‖φ y‖)) *
          (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)) := by
  let M : ℝ := max |(-a)| |(1 + a)|
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (-a)) (le_max_left _ _)
  have hσ_abs : |σ| ≤ M := by
    have hleft_abs : |(-a)| ≤ M := le_max_left _ _
    have hright_abs : |(1 + a)| ≤ M := le_max_right _ _
    have hleft : -M ≤ σ := by
      exact le_trans (abs_le.mp hleft_abs).1 hσ.1
    have hright : σ ≤ M := by
      exact le_trans hσ.2 (abs_le.mp hright_abs).2
    exact abs_le.mpr ⟨hleft, hright⟩
  have hexp_re : (((σ : ℂ) * (y : ℂ))).re = σ * y := by
    norm_num [Complex.mul_re]
  have hosc_re : ((((T * y : ℝ) : ℂ) * Complex.I)).re = 0 := by
    norm_num [Complex.mul_re]
  have hexp_le :
      Real.exp (σ * y) ≤ Real.exp ((-a) * y) + Real.exp ((1 + a) * y) := by
    by_cases hy : 0 ≤ y
    · have hmul : σ * y ≤ (1 + a) * y :=
        mul_le_mul_of_nonneg_right hσ.2 hy
      exact le_trans (Real.exp_le_exp.mpr hmul)
        (le_add_of_nonneg_left (Real.exp_nonneg _))
    · have hy' : y ≤ 0 := le_of_not_ge hy
      have hmul : σ * y ≤ (-a) * y :=
        mul_le_mul_of_nonpos_right hσ.1 hy'
      exact le_trans (Real.exp_le_exp.mpr hmul)
        (le_add_of_nonneg_right (Real.exp_nonneg _))
  have hnorm_sum :
      ‖deriv φ y * (y : ℂ) + φ y + (σ : ℂ) * (φ y * (y : ℂ))‖
        ≤ ‖deriv φ y * (y : ℂ)‖ + ‖φ y‖ +
          ‖(σ : ℂ) * (φ y * (y : ℂ))‖ := by
    calc
      ‖deriv φ y * (y : ℂ) + φ y + (σ : ℂ) * (φ y * (y : ℂ))‖
          ≤ ‖deriv φ y * (y : ℂ) + φ y‖ +
              ‖(σ : ℂ) * (φ y * (y : ℂ))‖ := norm_add_le _ _
      _ ≤ (‖deriv φ y * (y : ℂ)‖ + ‖φ y‖) +
              ‖(σ : ℂ) * (φ y * (y : ℂ))‖ :=
            add_le_add (norm_add_le _ _) le_rfl
      _ = ‖deriv φ y * (y : ℂ)‖ + ‖φ y‖ +
              ‖(σ : ℂ) * (φ y * (y : ℂ))‖ := by ring
  have hthird :
      |σ| * (‖(y : ℂ)‖ * ‖φ y‖) ≤ M * (‖(y : ℂ)‖ * ‖φ y‖) :=
    mul_le_mul_of_nonneg_right hσ_abs
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsum_coeff :
      ‖(y : ℂ)‖ * ‖deriv φ y‖ + ‖φ y‖ +
          |σ| * (‖(y : ℂ)‖ * ‖φ y‖)
        ≤ ‖(y : ℂ)‖ * ‖deriv φ y‖ + ‖φ y‖ +
          M * (‖(y : ℂ)‖ * ‖φ y‖) := by
    nlinarith [hthird]
  rw [hB.weightedMomentLine_deriv_eq σ y]
  calc
    ‖((deriv φ y * (y : ℂ) + φ y + (σ : ℂ) * (φ y * (y : ℂ))) *
          Complex.exp ((σ : ℂ) * (y : ℂ))) *
        Complex.exp (((T * y : ℝ) : ℂ) * Complex.I)‖
        = ‖(deriv φ y * (y : ℂ) + φ y + (σ : ℂ) * (φ y * (y : ℂ))) *
            Complex.exp ((σ : ℂ) * (y : ℂ))‖ := by
          rw [norm_mul, Complex.norm_exp, hosc_re, Real.exp_zero, mul_one]
    _ = ‖deriv φ y * (y : ℂ) + φ y + (σ : ℂ) * (φ y * (y : ℂ))‖ *
          Real.exp (σ * y) := by
          rw [norm_mul, Complex.norm_exp, hexp_re]
    _ ≤ (‖deriv φ y * (y : ℂ)‖ + ‖φ y‖ +
            ‖(σ : ℂ) * (φ y * (y : ℂ))‖) *
          Real.exp (σ * y) := by
          exact mul_le_mul_of_nonneg_right hnorm_sum (Real.exp_nonneg _)
    _ ≤ (‖(y : ℂ)‖ * ‖deriv φ y‖ + ‖φ y‖ +
            M * (‖(y : ℂ)‖ * ‖φ y‖)) * Real.exp (σ * y) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
          calc
            ‖deriv φ y * (y : ℂ)‖ + ‖φ y‖ +
                ‖(σ : ℂ) * (φ y * (y : ℂ))‖
                = ‖(y : ℂ)‖ * ‖deriv φ y‖ + ‖φ y‖ +
                    |σ| * (‖(y : ℂ)‖ * ‖φ y‖) := by
                  rw [norm_mul, norm_mul, norm_mul]
                  simp [Complex.norm_real, Real.norm_eq_abs, mul_comm]
            _ ≤ ‖(y : ℂ)‖ * ‖deriv φ y‖ + ‖φ y‖ +
                    M * (‖(y : ℂ)‖ * ‖φ y‖) := hsum_coeff
    _ ≤ (‖(y : ℂ)‖ * ‖deriv φ y‖ + ‖φ y‖ +
            M * (‖(y : ℂ)‖ * ‖φ y‖)) *
          (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)) := by
          exact mul_le_mul_of_nonneg_left hexp_le
            (add_nonneg
              (add_nonneg
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))
                (norm_nonneg _))
              (mul_nonneg hM_nonneg
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))))

/-- Integrability of the derivative of the first-moment weighted-line source. -/
private theorem KadiriPhiConditionB.weightedMomentLineDerivIntegrable
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (hne : -a ≤ 1 + a) {σ : ℝ} (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    Integrable (deriv (fun y : ℝ =>
      φ y * ((y : ℂ) * Complex.exp ((σ : ℂ) * (y : ℂ))))) := by
  let M : ℝ := max |(-a)| |(1 + a)|
  have hmoment_deriv := hB.weightedDerivEndpointMomentEnvelopeIntegrable hne
  have hphi := hB.weightedEndpointEnvelopeIntegrable hne
  have hmoment_phi := hB.weightedEndpointMomentEnvelopeIntegrable hne
  have hscaled :
      Integrable (fun y : ℝ =>
        M * (‖(y : ℂ)‖ * ‖φ y‖ *
          (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)))) :=
    hmoment_phi.const_mul M
  have hsum :
      Integrable (fun y : ℝ =>
        ‖(y : ℂ)‖ * ‖deriv φ y‖ *
            (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)) +
          ‖φ y‖ * (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)) +
          M * (‖(y : ℂ)‖ * ‖φ y‖ *
            (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)))) :=
    (hmoment_deriv.add hphi).add hscaled
  have henv :
      Integrable (fun y : ℝ =>
        (‖(y : ℂ)‖ * ‖deriv φ y‖ + ‖φ y‖ +
            M * (‖(y : ℂ)‖ * ‖φ y‖)) *
          (Real.exp ((-a) * y) + Real.exp ((1 + a) * y))) := by
    convert hsum using 1
    ext y
    ring
  have hcont : Continuous (fun y : ℝ =>
      φ y * ((y : ℂ) * Complex.exp ((σ : ℂ) * (y : ℂ)))) := by
    have hφcont : Continuous φ := hB.contDiff.continuous
    fun_prop
  have hderiv_eq : (fun y : ℝ => deriv (fun y : ℝ =>
      φ y * ((y : ℂ) * Complex.exp ((σ : ℂ) * (y : ℂ)))) y) =
      fun y : ℝ =>
        (deriv φ y * (y : ℂ) + φ y + (σ : ℂ) * (φ y * (y : ℂ))) *
          Complex.exp ((σ : ℂ) * (y : ℂ)) := by
    funext y
    exact hB.weightedMomentLine_deriv_eq σ y
  have hderiv_expr_cont : Continuous (fun y : ℝ =>
      (deriv φ y * (y : ℂ) + φ y + (σ : ℂ) * (φ y * (y : ℂ))) *
        Complex.exp ((σ : ℂ) * (y : ℂ))) := by
    have hφcont : Continuous φ := hB.contDiff.continuous
    have hderiv_cont : Continuous (fun y : ℝ => deriv φ y) :=
      hB.contDiff.continuous_deriv (by norm_num)
    fun_prop
  have hmeas :
      AEStronglyMeasurable (fun y : ℝ => deriv (fun y : ℝ =>
        φ y * ((y : ℂ) * Complex.exp ((σ : ℂ) * (y : ℂ)))) y) volume := by
    rw [hderiv_eq]
    exact hderiv_expr_cont.aestronglyMeasurable
  exact henv.mono'
    hmeas
    (Filter.Eventually.of_forall fun y => by
      simpa [M, abs_neg, neg_mul, mul_zero, zero_mul, Complex.exp_zero, mul_one] using
        hB.weightedMomentLine_deriv_norm_le_endpointMomentEnvelope
          (T := 0) (y := y) hσ)

/-- First-moment weighted-line Fourier/IBP norm estimate. -/
private theorem KadiriPhiConditionB.weightedMomentLine_fourier_norm_le_deriv_integral_div_abs
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (hne : -a ≤ 1 + a) {σ T : ℝ} (hT : T ≠ 0)
    (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    ‖∫ y : ℝ,
        ((φ y * (y : ℂ)) * Complex.exp ((σ : ℂ) * (y : ℂ))) *
          Complex.exp (((T * y : ℝ) : ℂ) * Complex.I)‖
      ≤ (∫ y : ℝ,
          ‖deriv (fun x : ℝ =>
              φ x * ((x : ℂ) * Complex.exp ((σ : ℂ) * (x : ℂ)))) y *
            Complex.exp (((T * y : ℝ) : ℂ) * Complex.I)‖) / |T| := by
  have hibp := kadiri_fourier_exp_i_mul_ibp
    (g := fun y : ℝ =>
      φ y * ((y : ℂ) * Complex.exp ((σ : ℂ) * (y : ℂ))))
    hT
    (hB.weightedMomentLineIntegrable hne hσ)
    (hB.weightedMomentLineDifferentiable σ)
    (hB.weightedMomentLineDerivIntegrable hne hσ)
  have hibp' :
      (∫ y : ℝ,
        ((φ y * (y : ℂ)) * Complex.exp ((σ : ℂ) * (y : ℂ))) *
          Complex.exp (((T * y : ℝ) : ℂ) * Complex.I))
      = (Complex.I / (T : ℂ)) *
        ∫ y : ℝ,
          deriv (fun x : ℝ =>
              φ x * ((x : ℂ) * Complex.exp ((σ : ℂ) * (x : ℂ)))) y *
            Complex.exp (((T * y : ℝ) : ℂ) * Complex.I) := by
    convert hibp using 1
    apply integral_congr_ae
    filter_upwards with y
    ring
  exact norm_fourier_le_integral_norm_div_abs hT hibp'

/-- The first-moment derivative integral is bounded by the endpoint moment
envelope integral, uniformly in `σ`. -/
private theorem KadiriPhiConditionB.weightedMomentLine_deriv_integral_le_endpointMomentEnvelope_integral
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (hne : -a ≤ 1 + a) {σ T : ℝ} (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    (∫ y : ℝ,
      ‖deriv (fun x : ℝ =>
          φ x * ((x : ℂ) * Complex.exp ((σ : ℂ) * (x : ℂ)))) y *
        Complex.exp (((T * y : ℝ) : ℂ) * Complex.I)‖)
      ≤ ∫ y : ℝ,
          (‖(y : ℂ)‖ * ‖deriv φ y‖ + ‖φ y‖ +
              max |(-a)| |(1 + a)| * (‖(y : ℂ)‖ * ‖φ y‖)) *
            (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)) := by
  exact integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun y => norm_nonneg _)
    (by
      let M : ℝ := max |(-a)| |(1 + a)|
      have hmoment_deriv := hB.weightedDerivEndpointMomentEnvelopeIntegrable hne
      have hphi := hB.weightedEndpointEnvelopeIntegrable hne
      have hmoment_phi := hB.weightedEndpointMomentEnvelopeIntegrable hne
      have hscaled :
          Integrable (fun y : ℝ =>
            M * (‖(y : ℂ)‖ * ‖φ y‖ *
              (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)))) :=
        hmoment_phi.const_mul M
      have hsum :
          Integrable (fun y : ℝ =>
            ‖(y : ℂ)‖ * ‖deriv φ y‖ *
                (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)) +
              ‖φ y‖ * (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)) +
              M * (‖(y : ℂ)‖ * ‖φ y‖ *
                (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)))) :=
        (hmoment_deriv.add hphi).add hscaled
      convert hsum using 1
      ext y
      dsimp [M]
      ring)
    (Filter.Eventually.of_forall fun y =>
      hB.weightedMomentLine_deriv_norm_le_endpointMomentEnvelope (T := T) hσ)

/-- Exact-name wrapper for the first-moment derivative endpoint-envelope
bound used in the condition-B horizontal `Φ'` IBP. -/
private theorem KadiriPhiConditionB.weightedMomentLine_deriv_integral_le_endpointMomentEnvelope
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (hne : -a ≤ 1 + a) {σ T : ℝ} (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    (∫ y : ℝ,
      ‖deriv (fun x : ℝ =>
          φ x * ((x : ℂ) * Complex.exp ((σ : ℂ) * (x : ℂ)))) y *
        Complex.exp (((T * y : ℝ) : ℂ) * Complex.I)‖)
      ≤ ∫ y : ℝ,
          (‖(y : ℂ)‖ * ‖deriv φ y‖ + ‖φ y‖ +
              max |(-a)| |(1 + a)| * (‖(y : ℂ)‖ * ‖φ y‖)) *
            (Real.exp ((-a) * y) + Real.exp ((1 + a) * y)) := by
  exact hB.weightedMomentLine_deriv_integral_le_endpointMomentEnvelope_integral (T := T) hne hσ

/-- Top-segment `Φ'` estimate with the strip-uniform endpoint moment constant. -/
private theorem KadiriPhiConditionB.topHorizontalPhi_deriv_norm_le_endpointMomentEnvelope_integral_div_abs
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (hne : -a ≤ 1 + a) {σ T : ℝ} (hT : T ≠ 0)
    (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    ‖deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
        (-(kadiriTopHorizontalPoint T σ))‖
      ≤ (∫ y : ℝ,
          (‖(y : ℂ)‖ * ‖deriv φ y‖ + ‖φ y‖ +
              max |(-a)| |(1 + a)| * (‖(y : ℂ)‖ * ‖φ y‖)) *
            (Real.exp ((-a) * y) + Real.exp ((1 + a) * y))) / |T| := by
  rw [hB.topHorizontalPhi_deriv_eq_weightedLineFourier hσ, norm_neg]
  exact (hB.weightedMomentLine_fourier_norm_le_deriv_integral_div_abs hne hT hσ).trans
    (div_le_div_of_nonneg_right
      (hB.weightedMomentLine_deriv_integral_le_endpointMomentEnvelope_integral
        (T := T) hne hσ)
      (abs_nonneg T))

/-- Bottom-segment `Φ'` estimate with the strip-uniform endpoint moment constant. -/
private theorem KadiriPhiConditionB.botHorizontalPhi_deriv_norm_le_endpointMomentEnvelope_integral_div_abs
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a)
    (hne : -a ≤ 1 + a) {σ T : ℝ} (hT : T ≠ 0)
    (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    ‖deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
        (-(kadiriBotHorizontalPoint T σ))‖
      ≤ (∫ y : ℝ,
          (‖(y : ℂ)‖ * ‖deriv φ y‖ + ‖φ y‖ +
              max |(-a)| |(1 + a)| * (‖(y : ℂ)‖ * ‖φ y‖)) *
            (Real.exp ((-a) * y) + Real.exp ((1 + a) * y))) / |T| := by
  rw [hB.botHorizontalPhi_deriv_eq_weightedLineFourier hσ, norm_neg]
  exact (hB.weightedMomentLine_fourier_norm_le_deriv_integral_div_abs hne
      (neg_ne_zero.mpr hT) hσ).trans
    (by
      simpa [abs_neg] using
        div_le_div_of_nonneg_right
          (hB.weightedMomentLine_deriv_integral_le_endpointMomentEnvelope_integral
            (T := -T) hne hσ)
          (abs_nonneg (-T)))

/-! ## The two named condition-(B) analytic inputs

These are the only remaining analytic obligations.  The first is the two
integrations by parts of `Φ` against the oscillatory kernel `e^{i T y}`; the
second is the assembly of that decay with the proved partial-fraction remainder
and single-pole kernel into the horizontal-integral estimate.  Each is named
with its precise goal and is never discharged with `sorry`. -/

/-- **Named analytic input (Φ/Φ′ decay).**  Under condition (B) the bilateral
Laplace transform `Φ` and its derivative decay like `1/|T|` uniformly on the two
horizontal strips, i.e. `KadiriHorizontalPhiPrimeDecayBound φ a` holds.  This is
the integration-by-parts estimate built from the weighted-`L¹` integrability of
`KadiriPhiDecay` plus the Fourier-IBP norm atom there; its precise goal is
exactly `KadiriHorizontalPhiPrimeDecayBound φ a`. -/
def KadiriHorizontalPhiC1Decay_of_conditionB (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  KadiriPhiConditionB φ a → KadiriHorizontalPhiPrimeDecayBound φ a

/-- Condition (B) gives the route's `Φ`/`Φ'` decay bound on every nonnegative
horizontal-width parameter `a`.  The constants are the two endpoint-envelope
integrals produced above, enlarged by `max 0 _` only to match the nonnegative
constant surface. -/
private theorem kadiriHorizontalPhiPrimeDecayBound_of_conditionB_nonneg
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (hB : KadiriPhiConditionB φ a) :
    KadiriHorizontalPhiPrimeDecayBound φ a := by
  have hne : -a ≤ 1 + a := by linarith
  let A0raw : ℝ := ∫ y : ℝ,
    (‖deriv φ y‖ + max |(-a)| |(1 + a)| * ‖φ y‖) *
      (Real.exp ((-a) * y) + Real.exp ((1 + a) * y))
  let A1raw : ℝ := ∫ y : ℝ,
    (‖(y : ℂ)‖ * ‖deriv φ y‖ + ‖φ y‖ +
        max |(-a)| |(1 + a)| * (‖(y : ℂ)‖ * ‖φ y‖)) *
      (Real.exp ((-a) * y) + Real.exp ((1 + a) * y))
  refine ⟨max 0 A0raw, max 0 A1raw, le_max_left 0 A0raw,
    le_max_left 0 A1raw, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with T hT
  have hT_nonneg : 0 ≤ T := by linarith
  have hT_abs : 2 ≤ |T| := by simpa [abs_of_nonneg hT_nonneg] using hT
  have hT_ne : T ≠ 0 := by linarith
  have hden_nonneg : 0 ≤ |T| := abs_nonneg T
  have hA0raw_le : A0raw ≤ max 0 A0raw := le_max_right 0 A0raw
  have hA1raw_le : A1raw ≤ max 0 A1raw := le_max_right 0 A1raw
  refine ⟨hT_abs, ?_, ?_⟩
  · intro σ hσ
    constructor
    · have htop :=
        hB.topHorizontalPhi_norm_le_endpointEnvelope_integral_div_abs
          (T := T) hne hT_ne hσ
      have htop' :
          ‖kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))‖
            ≤ A0raw / |T| := by
        simpa [A0raw] using htop
      exact htop'.trans
        (div_le_div_of_nonneg_right hA0raw_le hden_nonneg)
    · have htop :=
        hB.topHorizontalPhi_deriv_norm_le_endpointMomentEnvelope_integral_div_abs
          (T := T) hne hT_ne hσ
      have htop' :
          ‖deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
              (-(kadiriTopHorizontalPoint T σ))‖ ≤ A1raw / |T| := by
        simpa [A1raw] using htop
      exact htop'.trans
        (div_le_div_of_nonneg_right hA1raw_le hden_nonneg)
  · intro σ hσ
    constructor
    · have hbot :=
        hB.botHorizontalPhi_norm_le_endpointEnvelope_integral_div_abs
          (T := T) hne hT_ne hσ
      have hbot' :
          ‖kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))‖
            ≤ A0raw / |T| := by
        simpa [A0raw] using hbot
      exact hbot'.trans
        (div_le_div_of_nonneg_right hA0raw_le hden_nonneg)
    · have hbot :=
        hB.botHorizontalPhi_deriv_norm_le_endpointMomentEnvelope_integral_div_abs
          (T := T) hne hT_ne hσ
      have hbot' :
          ‖deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
              (-(kadiriBotHorizontalPoint T σ))‖ ≤ A1raw / |T| := by
        simpa [A1raw] using hbot
      exact hbot'.trans
        (div_le_div_of_nonneg_right hA1raw_le hden_nonneg)

/-- Condition (B), with `0 ≤ a`, supplies the named `Φ`/`Φ'` decay input. -/
theorem KadiriHorizontalPhiC1Decay_of_conditionB_of_nonneg
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) :
    KadiriHorizontalPhiC1Decay_of_conditionB φ a := by
  intro hB
  exact kadiriHorizontalPhiPrimeDecayBound_of_conditionB_nonneg ha hB

/-- **Named analytic input (PV integration estimate).**  Under condition (B) the
two horizontal integrals at non-zero ordinates are `O(log^k |T| / |T|)`, i.e.
`KadiriHorizontalPVIntegrationBound φ a` holds.  This is the assembly of the
Φ-decay with the proved partial-fraction remainder and single-pole kernel; its
precise goal is exactly `KadiriHorizontalPVIntegrationBound φ a`. -/
def KadiriHorizontalPVIntegration_of_conditionB (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  KadiriPhiConditionB φ a → KadiriHorizontalPVIntegrationBound φ a

private theorem KadiriPhiConditionB.topHorizontalLogIntegrand_continuousOn
    {φ : ℝ → ℂ} {a T : ℝ} (hB : KadiriPhiConditionB φ a)
    (hT : T ≠ 0) (hNo : KadiriNoZeroOrdinate T) :
    ContinuousOn (fun σ : ℝ =>
      (-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
          riemannZeta (kadiriTopHorizontalPoint T σ)) *
        kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)))
      (Set.Icc (-a) (1 + a)) := by
  intro σ hσ
  let s : ℂ := kadiriTopHorizontalPoint T σ
  have hs_ne_one : s ≠ 1 := by
    intro hs
    have him_eq : (kadiriTopHorizontalPoint T σ).im = (1 : ℂ).im := by
      simpa [s] using congrArg Complex.im hs
    have hT_zero : T = 0 := by
      calc
        T = (kadiriTopHorizontalPoint T σ).im := by simp [kadiriTopHorizontalPoint]
        _ = (1 : ℂ).im := him_eq
        _ = 0 := by simp
    exact hT hT_zero
  have hs_zeta : riemannZeta s ≠ 0 := by
    simpa [s] using
      kadiriTopHorizontalPoint_zeta_ne_zero_of_noZero (T := T) (σ := σ) hNo
  have hpoint : ContinuousAt (fun x : ℝ => kadiriTopHorizontalPoint T x) σ := by
    dsimp [kadiriTopHorizontalPoint]
    fun_prop
  have hlog : ContinuousAt (fun z : ℂ => -deriv riemannZeta z / riemannZeta z) s := by
    exact ((differentiableAt_deriv_riemannZeta hs_ne_one).continuousAt.neg).div
      (analyticAt_riemannZeta hs_ne_one).continuousAt hs_zeta
  have hlog_comp : ContinuousAt (fun x : ℝ =>
      -deriv riemannZeta (kadiriTopHorizontalPoint T x) /
        riemannZeta (kadiriTopHorizontalPoint T x)) σ := by
    simpa [Function.comp_def, s] using
      (ContinuousAt.comp (x := σ)
        (f := fun x : ℝ => kadiriTopHorizontalPoint T x)
        (g := fun z : ℂ => -deriv riemannZeta z / riemannZeta z)
        hlog hpoint)
  have hnegpoint : ContinuousAt (fun x : ℝ => -(kadiriTopHorizontalPoint T x)) σ :=
    hpoint.neg
  have hPhi_at : ContinuousAt (fun z : ℂ => kadiriHorizontalPhi φ z) (-s) := by
    have hderiv := hB.kadiriHorizontalPhi_hasDerivAt
      (z0 := -s) (by simpa [s, kadiriTopHorizontalPoint] using hσ)
    exact hderiv.continuousAt
  have hPhi_comp : ContinuousAt (fun x : ℝ =>
      kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T x))) σ := by
    simpa [Function.comp_def, s] using
      (ContinuousAt.comp (x := σ)
        (f := fun x : ℝ => -(kadiriTopHorizontalPoint T x))
        (g := fun z : ℂ => kadiriHorizontalPhi φ z)
        hPhi_at hnegpoint)
  exact (hlog_comp.mul hPhi_comp).continuousWithinAt

private theorem KadiriPhiConditionB.botHorizontalLogIntegrand_continuousOn
    {φ : ℝ → ℂ} {a T : ℝ} (hB : KadiriPhiConditionB φ a)
    (hT : T ≠ 0) (hNo : KadiriNoZeroOrdinate (-T)) :
    ContinuousOn (fun σ : ℝ =>
      (-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
          riemannZeta (kadiriBotHorizontalPoint T σ)) *
        kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)))
      (Set.Icc (-a) (1 + a)) := by
  intro σ hσ
  let s : ℂ := kadiriBotHorizontalPoint T σ
  have hs_ne_one : s ≠ 1 := by
    intro hs
    have him_eq : (kadiriBotHorizontalPoint T σ).im = (1 : ℂ).im := by
      simpa [s] using congrArg Complex.im hs
    have hnegT_zero : -T = 0 := by
      calc
        -T = (kadiriBotHorizontalPoint T σ).im := by simp [kadiriBotHorizontalPoint]
        _ = (1 : ℂ).im := him_eq
        _ = 0 := by simp
    exact hT (neg_eq_zero.mp hnegT_zero)
  have hs_zeta : riemannZeta s ≠ 0 := by
    simpa [s] using
      kadiriBotHorizontalPoint_zeta_ne_zero_of_noZero (T := T) (σ := σ) hNo
  have hpoint : ContinuousAt (fun x : ℝ => kadiriBotHorizontalPoint T x) σ := by
    dsimp [kadiriBotHorizontalPoint]
    fun_prop
  have hlog : ContinuousAt (fun z : ℂ => -deriv riemannZeta z / riemannZeta z) s := by
    exact ((differentiableAt_deriv_riemannZeta hs_ne_one).continuousAt.neg).div
      (analyticAt_riemannZeta hs_ne_one).continuousAt hs_zeta
  have hlog_comp : ContinuousAt (fun x : ℝ =>
      -deriv riemannZeta (kadiriBotHorizontalPoint T x) /
        riemannZeta (kadiriBotHorizontalPoint T x)) σ := by
    simpa [Function.comp_def, s] using
      (ContinuousAt.comp (x := σ)
        (f := fun x : ℝ => kadiriBotHorizontalPoint T x)
        (g := fun z : ℂ => -deriv riemannZeta z / riemannZeta z)
        hlog hpoint)
  have hnegpoint : ContinuousAt (fun x : ℝ => -(kadiriBotHorizontalPoint T x)) σ :=
    hpoint.neg
  have hPhi_at : ContinuousAt (fun z : ℂ => kadiriHorizontalPhi φ z) (-s) := by
    have hderiv := hB.kadiriHorizontalPhi_hasDerivAt
      (z0 := -s) (by simpa [s, kadiriBotHorizontalPoint] using hσ)
    exact hderiv.continuousAt
  have hPhi_comp : ContinuousAt (fun x : ℝ =>
      kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T x))) σ := by
    simpa [Function.comp_def, s] using
      (ContinuousAt.comp (x := σ)
        (f := fun x : ℝ => -(kadiriBotHorizontalPoint T x))
        (g := fun z : ℂ => kadiriHorizontalPhi φ z)
        hPhi_at hnegpoint)
  exact (hlog_comp.mul hPhi_comp).continuousWithinAt

private theorem KadiriPhiConditionB.topHorizontalZeroWindowIntegrand_continuousOn
    {φ : ℝ → ℂ} {a T : ℝ} (hB : KadiriPhiConditionB φ a)
    (hNo : KadiriNoZeroOrdinate T) :
    ContinuousOn (fun σ : ℝ =>
      (riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
        (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))) *
        kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)))
      (Set.Icc (-a) (1 + a)) := by
  let Z := (zeroes_rect_Ioo_Icc_window_finite T).toFinset
  have hsum_eq : (fun σ : ℝ =>
      riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
        (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))) =
      (fun σ : ℝ =>
        ∑ ρ ∈ Z,
          ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
            ((riemannZeta.order ρ : ℤ) : ℂ)) := by
    funext σ
    rw [zeroes_sum_eq_toFinset_sum
      (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))
      (zeroes_rect_Ioo_Icc_window_finite T)]
  have hsum_cont : ContinuousOn (fun σ : ℝ =>
        ∑ ρ ∈ Z,
          ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
            ((riemannZeta.order ρ : ℤ) : ℂ))
      (Set.Icc (-a) (1 + a)) := by
    refine continuousOn_finsetSum Z ?_
    intro ρ hρZ
    refine ContinuousOn.mul ?_ continuousOn_const
    intro σ _hσ
    have hpoint : ContinuousAt (fun x : ℝ => kadiriTopHorizontalPoint T x - ρ) σ := by
      dsimp [kadiriTopHorizontalPoint]
      fun_prop
    have hden : kadiriTopHorizontalPoint T σ - ρ ≠ 0 := by
      intro hzero
      have hp : kadiriTopHorizontalPoint T σ = ρ := sub_eq_zero.mp hzero
      have hρzero : riemannZeta ρ = 0 := by
        have hmem := (zeroes_rect_Ioo_Icc_window_finite T).mem_toFinset.mp hρZ
        simpa [riemannZeta.zeroes] using hmem.2.2
      have him : ρ.im = T := by
        rw [← hp]
        simp [kadiriTopHorizontalPoint]
      exact (hNo ρ hρzero) him
    exact (continuousAt_const.div hpoint hden).continuousWithinAt
  have hPhi_cont : ContinuousOn (fun σ : ℝ =>
      kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)))
      (Set.Icc (-a) (1 + a)) := by
    intro σ hσ
    have hpoint : ContinuousAt (fun x : ℝ => -(kadiriTopHorizontalPoint T x)) σ := by
      dsimp [kadiriTopHorizontalPoint]
      fun_prop
    have hPhi_at : ContinuousAt (fun z : ℂ => kadiriHorizontalPhi φ z)
        (-(kadiriTopHorizontalPoint T σ)) := by
      have hderiv := hB.kadiriHorizontalPhi_hasDerivAt
        (z0 := -(kadiriTopHorizontalPoint T σ)) (by
          simpa [kadiriTopHorizontalPoint] using hσ)
      exact hderiv.continuousAt
    exact (ContinuousAt.comp (x := σ)
        (f := fun x : ℝ => -(kadiriTopHorizontalPoint T x))
        (g := fun z : ℂ => kadiriHorizontalPhi φ z)
        hPhi_at hpoint).continuousWithinAt
  have hprod := hsum_cont.mul hPhi_cont
  convert hprod using 1
  ext σ
  have hσeq := congrFun hsum_eq σ
  rw [hσeq]
  rfl

private theorem KadiriPhiConditionB.botHorizontalZeroWindowIntegrand_continuousOn
    {φ : ℝ → ℂ} {a T : ℝ} (hB : KadiriPhiConditionB φ a)
    (hNo : KadiriNoZeroOrdinate (-T)) :
    ContinuousOn (fun σ : ℝ =>
      (riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc ((-T) - 1) ((-T) + 1))
        (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))) *
        kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)))
      (Set.Icc (-a) (1 + a)) := by
  let Z := (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset
  have hsum_eq : (fun σ : ℝ =>
      riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc ((-T) - 1) ((-T) + 1))
        (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))) =
      (fun σ : ℝ =>
        ∑ ρ ∈ Z,
          ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
            ((riemannZeta.order ρ : ℤ) : ℂ)) := by
    funext σ
    rw [zeroes_sum_eq_toFinset_sum
      (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))
      (zeroes_rect_Ioo_Icc_window_finite (-T))]
  have hsum_cont : ContinuousOn (fun σ : ℝ =>
        ∑ ρ ∈ Z,
          ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
            ((riemannZeta.order ρ : ℤ) : ℂ))
      (Set.Icc (-a) (1 + a)) := by
    refine continuousOn_finsetSum Z ?_
    intro ρ hρZ
    refine ContinuousOn.mul ?_ continuousOn_const
    intro σ _hσ
    have hpoint : ContinuousAt (fun x : ℝ => kadiriBotHorizontalPoint T x - ρ) σ := by
      dsimp [kadiriBotHorizontalPoint]
      fun_prop
    have hden : kadiriBotHorizontalPoint T σ - ρ ≠ 0 := by
      intro hzero
      have hp : kadiriBotHorizontalPoint T σ = ρ := sub_eq_zero.mp hzero
      have hρzero : riemannZeta ρ = 0 := by
        have hmem := (zeroes_rect_Ioo_Icc_window_finite (-T)).mem_toFinset.mp hρZ
        simpa [riemannZeta.zeroes] using hmem.2.2
      have him : ρ.im = -T := by
        rw [← hp]
        simp [kadiriBotHorizontalPoint]
      exact (hNo ρ hρzero) him
    exact (continuousAt_const.div hpoint hden).continuousWithinAt
  have hPhi_cont : ContinuousOn (fun σ : ℝ =>
      kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)))
      (Set.Icc (-a) (1 + a)) := by
    intro σ hσ
    have hpoint : ContinuousAt (fun x : ℝ => -(kadiriBotHorizontalPoint T x)) σ := by
      dsimp [kadiriBotHorizontalPoint]
      fun_prop
    have hPhi_at : ContinuousAt (fun z : ℂ => kadiriHorizontalPhi φ z)
        (-(kadiriBotHorizontalPoint T σ)) := by
      have hderiv := hB.kadiriHorizontalPhi_hasDerivAt
        (z0 := -(kadiriBotHorizontalPoint T σ)) (by
          simpa [kadiriBotHorizontalPoint] using hσ)
      exact hderiv.continuousAt
    exact (ContinuousAt.comp (x := σ)
        (f := fun x : ℝ => -(kadiriBotHorizontalPoint T x))
        (g := fun z : ℂ => kadiriHorizontalPhi φ z)
        hPhi_at hpoint).continuousWithinAt
  have hprod := hsum_cont.mul hPhi_cont
  convert hprod using 1
  ext σ
  have hσeq := congrFun hsum_eq σ
  rw [hσeq]
  rfl

/-- Condition (B) supplies the integrability needed to split the ordinary
horizontal integral from the finite zero-window contribution at non-zero
ordinates. -/
private theorem kadiriHorizontalZeroWindowPVIntegrability_of_conditionB
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a) :
    KadiriHorizontalZeroWindowPVIntegrability φ a := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT
  have hT_ne : T ≠ 0 := by linarith
  refine ⟨?_, ?_⟩
  · intro hNo
    exact
      ⟨(hB.topHorizontalLogIntegrand_continuousOn hT_ne hNo).integrableOn_Icc.mono_set
          Set.Ioo_subset_Icc_self,
        (hB.topHorizontalZeroWindowIntegrand_continuousOn hNo).integrableOn_Icc.mono_set
          Set.Ioo_subset_Icc_self⟩
  · intro hNo
    exact
      ⟨(hB.botHorizontalLogIntegrand_continuousOn hT_ne hNo).integrableOn_Icc.mono_set
          Set.Ioo_subset_Icc_self,
        (hB.botHorizontalZeroWindowIntegrand_continuousOn hNo).integrableOn_Icc.mono_set
          Set.Ioo_subset_Icc_self⟩

/-- Condition (B) supplies integrability of the projected-constant and variation
pieces in the top single-zero split. -/
private theorem KadiriPhiConditionB.topHorizontalSingleZeroWindowPVProjectedSplitIntegrable
    {φ : ℝ → ℂ} {a T : ℝ} (hB : KadiriPhiConditionB φ a)
    (hNo : KadiriNoZeroOrdinate T) {ρ : ℂ}
    (hρ : ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset) :
    Integrable (fun σ : ℝ =>
      ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
        kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re)))
      (volume.restrict (Set.Ioo (-a) (1 + a))) ∧
    Integrable (fun σ : ℝ =>
      ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
        (kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)) -
          kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re))))
      (volume.restrict (Set.Ioo (-a) (1 + a))) := by
  have hker_cont : ContinuousOn (fun σ : ℝ =>
      (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))
      (Set.Icc (-a) (1 + a)) := by
    intro σ _hσ
    have hpoint : ContinuousAt (fun x : ℝ => kadiriTopHorizontalPoint T x - ρ) σ := by
      dsimp [kadiriTopHorizontalPoint]
      fun_prop
    have hden : kadiriTopHorizontalPoint T σ - ρ ≠ 0 := by
      intro hzero
      have hp : kadiriTopHorizontalPoint T σ = ρ := sub_eq_zero.mp hzero
      have hρzero : riemannZeta ρ = 0 :=
        zeroes_rect_Ioo_Icc_window_toFinset_zeta_zero hρ
      have him : ρ.im = T := by
        rw [← hp]
        simp [kadiriTopHorizontalPoint]
      exact (hNo ρ hρzero) him
    exact (continuousAt_const.div hpoint hden).continuousWithinAt
  have hPhi_cont : ContinuousOn (fun σ : ℝ =>
      kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)))
      (Set.Icc (-a) (1 + a)) := by
    intro σ hσ
    have hpoint : ContinuousAt (fun x : ℝ => -(kadiriTopHorizontalPoint T x)) σ := by
      dsimp [kadiriTopHorizontalPoint]
      fun_prop
    have hPhi_at : ContinuousAt (fun z : ℂ => kadiriHorizontalPhi φ z)
        (-(kadiriTopHorizontalPoint T σ)) := by
      have hderiv := hB.kadiriHorizontalPhi_hasDerivAt
        (z0 := -(kadiriTopHorizontalPoint T σ)) (by
          simpa [kadiriTopHorizontalPoint] using hσ)
      exact hderiv.continuousAt
    exact (ContinuousAt.comp (x := σ)
        (f := fun x : ℝ => -(kadiriTopHorizontalPoint T x))
        (g := fun z : ℂ => kadiriHorizontalPhi φ z)
        hPhi_at hpoint).continuousWithinAt
  have hconst_cont : ContinuousOn (fun σ : ℝ =>
      ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
        kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re)))
      (Set.Icc (-a) (1 + a)) :=
    hker_cont.mul continuousOn_const
  have hvariation_cont : ContinuousOn (fun σ : ℝ =>
      ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
        (kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)) -
          kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re))))
      (Set.Icc (-a) (1 + a)) :=
    hker_cont.mul (hPhi_cont.sub continuousOn_const)
  constructor
  · have hint_icc : IntegrableOn (fun σ : ℝ =>
        ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
          kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re)))
        (Set.Icc (-a) (1 + a)) :=
      hconst_cont.integrableOn_Icc
    have hint := hint_icc.mono_set Set.Ioo_subset_Icc_self
    simpa [MeasureTheory.IntegrableOn] using hint
  · have hint_icc : IntegrableOn (fun σ : ℝ =>
        ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
          (kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)) -
            kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re))))
        (Set.Icc (-a) (1 + a)) :=
      hvariation_cont.integrableOn_Icc
    have hint := hint_icc.mono_set Set.Ioo_subset_Icc_self
    simpa [MeasureTheory.IntegrableOn] using hint

/-- Condition (B) supplies integrability of the projected-constant and variation
pieces in the bottom single-zero split. -/
private theorem KadiriPhiConditionB.botHorizontalSingleZeroWindowPVProjectedSplitIntegrable
    {φ : ℝ → ℂ} {a T : ℝ} (hB : KadiriPhiConditionB φ a)
    (hNo : KadiriNoZeroOrdinate (-T)) {ρ : ℂ}
    (hρ : ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset) :
    Integrable (fun σ : ℝ =>
      ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
        kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re)))
      (volume.restrict (Set.Ioo (-a) (1 + a))) ∧
    Integrable (fun σ : ℝ =>
      ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
        (kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)) -
          kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re))))
      (volume.restrict (Set.Ioo (-a) (1 + a))) := by
  have hker_cont : ContinuousOn (fun σ : ℝ =>
      (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))
      (Set.Icc (-a) (1 + a)) := by
    intro σ _hσ
    have hpoint : ContinuousAt (fun x : ℝ => kadiriBotHorizontalPoint T x - ρ) σ := by
      dsimp [kadiriBotHorizontalPoint]
      fun_prop
    have hden : kadiriBotHorizontalPoint T σ - ρ ≠ 0 := by
      intro hzero
      have hp : kadiriBotHorizontalPoint T σ = ρ := sub_eq_zero.mp hzero
      have hρzero : riemannZeta ρ = 0 :=
        zeroes_rect_Ioo_Icc_window_toFinset_zeta_zero hρ
      have him : ρ.im = -T := by
        rw [← hp]
        simp [kadiriBotHorizontalPoint]
      exact (hNo ρ hρzero) him
    exact (continuousAt_const.div hpoint hden).continuousWithinAt
  have hPhi_cont : ContinuousOn (fun σ : ℝ =>
      kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)))
      (Set.Icc (-a) (1 + a)) := by
    intro σ hσ
    have hpoint : ContinuousAt (fun x : ℝ => -(kadiriBotHorizontalPoint T x)) σ := by
      dsimp [kadiriBotHorizontalPoint]
      fun_prop
    have hPhi_at : ContinuousAt (fun z : ℂ => kadiriHorizontalPhi φ z)
        (-(kadiriBotHorizontalPoint T σ)) := by
      have hderiv := hB.kadiriHorizontalPhi_hasDerivAt
        (z0 := -(kadiriBotHorizontalPoint T σ)) (by
          simpa [kadiriBotHorizontalPoint] using hσ)
      exact hderiv.continuousAt
    exact (ContinuousAt.comp (x := σ)
        (f := fun x : ℝ => -(kadiriBotHorizontalPoint T x))
        (g := fun z : ℂ => kadiriHorizontalPhi φ z)
        hPhi_at hpoint).continuousWithinAt
  have hconst_cont : ContinuousOn (fun σ : ℝ =>
      ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
        kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re)))
      (Set.Icc (-a) (1 + a)) :=
    hker_cont.mul continuousOn_const
  have hvariation_cont : ContinuousOn (fun σ : ℝ =>
      ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
        (kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)) -
          kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re))))
      (Set.Icc (-a) (1 + a)) :=
    hker_cont.mul (hPhi_cont.sub continuousOn_const)
  constructor
  · have hint_icc : IntegrableOn (fun σ : ℝ =>
        ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
          kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re)))
        (Set.Icc (-a) (1 + a)) :=
      hconst_cont.integrableOn_Icc
    have hint := hint_icc.mono_set Set.Ioo_subset_Icc_self
    simpa [MeasureTheory.IntegrableOn] using hint
  · have hint_icc : IntegrableOn (fun σ : ℝ =>
        ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
          (kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)) -
            kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re))))
        (Set.Icc (-a) (1 + a)) :=
      hvariation_cont.integrableOn_Icc
    have hint := hint_icc.mono_set Set.Ioo_subset_Icc_self
    simpa [MeasureTheory.IntegrableOn] using hint

/-- Condition (B) gives the direct top single-zero projected-constant plus
variation split. -/
private theorem KadiriPhiConditionB.topHorizontalSingleZeroWindowPVIntegral_eq_projectedConst_add_variation
    {φ : ℝ → ℂ} {a T : ℝ} (hB : KadiriPhiConditionB φ a)
    (hNo : KadiriNoZeroOrdinate T) {ρ : ℂ}
    (hρ : ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset) :
    kadiriTopHorizontalSingleZeroWindowPVIntegral φ a T ρ =
      kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ +
        kadiriTopHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ := by
  rcases hB.topHorizontalSingleZeroWindowPVProjectedSplitIntegrable hNo hρ with
    ⟨hconst, hvariation⟩
  exact kadiriTopHorizontalSingleZeroWindowPVIntegral_eq_projectedConst_add_variation
    hconst hvariation

/-- Condition (B) gives the direct bottom single-zero projected-constant plus
variation split. -/
private theorem KadiriPhiConditionB.botHorizontalSingleZeroWindowPVIntegral_eq_projectedConst_add_variation
    {φ : ℝ → ℂ} {a T : ℝ} (hB : KadiriPhiConditionB φ a)
    (hNo : KadiriNoZeroOrdinate (-T)) {ρ : ℂ}
    (hρ : ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset) :
    kadiriBotHorizontalSingleZeroWindowPVIntegral φ a T ρ =
      kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ +
        kadiriBotHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ := by
  rcases hB.botHorizontalSingleZeroWindowPVProjectedSplitIntegrable hNo hρ with
    ⟨hconst, hvariation⟩
  exact kadiriBotHorizontalSingleZeroWindowPVIntegral_eq_projectedConst_add_variation
    hconst hvariation

/-- Condition (B) supplies the projected split for every zero-window
single-pole integral. -/
private theorem kadiriHorizontalZeroWindowProjectedSplit_of_conditionB
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a) :
    KadiriHorizontalZeroWindowProjectedSplit φ a := by
  filter_upwards with T
  constructor
  · intro hNo ρ hρ
    exact hB.topHorizontalSingleZeroWindowPVIntegral_eq_projectedConst_add_variation
      hNo hρ
  · intro hNo ρ hρ
    exact hB.botHorizontalSingleZeroWindowPVIntegral_eq_projectedConst_add_variation
      hNo hρ

private theorem KadiriPhiConditionB.topHorizontalPhi_variation_norm_le
    {φ : ℝ → ℂ} {a T σ τ A1 : ℝ} (hB : KadiriPhiConditionB φ a)
    (hderiv :
      ∀ x ∈ Set.Icc (-a) (1 + a),
        ‖deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
            (-(kadiriTopHorizontalPoint T x))‖ ≤ A1 / |T|)
    (hσ : σ ∈ Set.Icc (-a) (1 + a))
    (hτ : τ ∈ Set.Icc (-a) (1 + a)) :
    ‖kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)) -
        kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T τ))‖
      ≤ (A1 / |T|) * |σ - τ| := by
  let f : ℝ → ℂ := fun x =>
    kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T x))
  have hf : ∀ x ∈ Set.Icc (-a) (1 + a),
      HasDerivWithinAt f
        ((-1 : ℂ) •
          deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
            (-(kadiriTopHorizontalPoint T x)))
        (Set.Icc (-a) (1 + a)) x := by
    intro x hx
    have hpoint :
        HasDerivAt (fun x : ℝ => -(kadiriTopHorizontalPoint T x))
          (-1 : ℂ) x := by
      have hpoint_pos :
          HasDerivAt (fun x : ℝ => kadiriTopHorizontalPoint T x)
            (1 : ℂ) x := by
        dsimp [kadiriTopHorizontalPoint]
        simpa using
          (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((T : ℂ) * I)
      simpa using hpoint_pos.neg
    have hcomplex0 := hB.kadiriHorizontalPhi_hasDerivAt
      (z0 := -(kadiriTopHorizontalPoint T x)) (by
        simpa [kadiriTopHorizontalPoint] using hx)
    have hcomplex :
        HasDerivAt (fun z : ℂ => kadiriHorizontalPhi φ z)
          (deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
            (-(kadiriTopHorizontalPoint T x)))
          (-(kadiriTopHorizontalPoint T x)) := by
      simpa [hcomplex0.deriv] using hcomplex0
    have hcomp := hcomplex.scomp x hpoint
    simpa [f] using hcomp.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Icc (-a) (1 + a),
      ‖(-1 : ℂ) •
          deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
            (-(kadiriTopHorizontalPoint T x))‖ ≤ A1 / |T| := by
    intro x hx
    simpa using hderiv x hx
  have hmv :=
    (convex_Icc (-a) (1 + a)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f)
      (f' := fun x =>
        (-1 : ℂ) •
          deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
            (-(kadiriTopHorizontalPoint T x)))
      hf hbound hτ hσ
  simpa [f, Real.norm_eq_abs, abs_sub_comm] using hmv

private theorem KadiriPhiConditionB.botHorizontalPhi_variation_norm_le
    {φ : ℝ → ℂ} {a T σ τ A1 : ℝ} (hB : KadiriPhiConditionB φ a)
    (hderiv :
      ∀ x ∈ Set.Icc (-a) (1 + a),
        ‖deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
            (-(kadiriBotHorizontalPoint T x))‖ ≤ A1 / |T|)
    (hσ : σ ∈ Set.Icc (-a) (1 + a))
    (hτ : τ ∈ Set.Icc (-a) (1 + a)) :
    ‖kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)) -
        kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T τ))‖
      ≤ (A1 / |T|) * |σ - τ| := by
  let f : ℝ → ℂ := fun x =>
    kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T x))
  have hf : ∀ x ∈ Set.Icc (-a) (1 + a),
      HasDerivWithinAt f
        ((-1 : ℂ) •
          deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
            (-(kadiriBotHorizontalPoint T x)))
        (Set.Icc (-a) (1 + a)) x := by
    intro x hx
    have hpoint :
        HasDerivAt (fun x : ℝ => -(kadiriBotHorizontalPoint T x))
          (-1 : ℂ) x := by
      have hpoint_pos :
          HasDerivAt (fun x : ℝ => kadiriBotHorizontalPoint T x)
            (1 : ℂ) x := by
        dsimp [kadiriBotHorizontalPoint]
        simpa using
          (Complex.ofRealCLM.hasDerivAt (x := x)).add_const (((-T : ℝ) : ℂ) * I)
      simpa using hpoint_pos.neg
    have hcomplex0 := hB.kadiriHorizontalPhi_hasDerivAt
      (z0 := -(kadiriBotHorizontalPoint T x)) (by
        simpa [kadiriBotHorizontalPoint] using hx)
    have hcomplex :
        HasDerivAt (fun z : ℂ => kadiriHorizontalPhi φ z)
          (deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
            (-(kadiriBotHorizontalPoint T x)))
          (-(kadiriBotHorizontalPoint T x)) := by
      simpa [hcomplex0.deriv] using hcomplex0
    have hcomp := hcomplex.scomp x hpoint
    simpa [f] using hcomp.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Icc (-a) (1 + a),
      ‖(-1 : ℂ) •
          deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
            (-(kadiriBotHorizontalPoint T x))‖ ≤ A1 / |T| := by
    intro x hx
    simpa using hderiv x hx
  have hmv :=
    (convex_Icc (-a) (1 + a)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f)
      (f' := fun x =>
        (-1 : ℂ) •
          deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
            (-(kadiriBotHorizontalPoint T x)))
      hf hbound hτ hσ
  simpa [f, Real.norm_eq_abs, abs_sub_comm] using hmv

private theorem kadiriTopHorizontalCauchyRatio_mul_abs_re_le_one
    {T σ : ℝ} {ρ : ℂ}
    (hden : kadiriTopHorizontalPoint T σ - ρ ≠ 0) :
    ‖(1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)‖ *
        |σ - ρ.re| ≤ 1 := by
  have hzpos : 0 < ‖kadiriTopHorizontalPoint T σ - ρ‖ :=
    norm_pos_iff.mpr hden
  have hre :
      |σ - ρ.re| ≤ ‖kadiriTopHorizontalPoint T σ - ρ‖ := by
    have hre_eq :
        (kadiriTopHorizontalPoint T σ - ρ).re = σ - ρ.re := by
      simp [kadiriTopHorizontalPoint]
    calc
      |σ - ρ.re| = |(kadiriTopHorizontalPoint T σ - ρ).re| := by
        rw [hre_eq]
      _ ≤ ‖kadiriTopHorizontalPoint T σ - ρ‖ :=
        Complex.abs_re_le_norm _
  calc
    ‖(1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)‖ * |σ - ρ.re|
        = (1 / ‖kadiriTopHorizontalPoint T σ - ρ‖) * |σ - ρ.re| := by
          rw [Complex.norm_div, norm_one]
    _ ≤ (1 / ‖kadiriTopHorizontalPoint T σ - ρ‖) *
          ‖kadiriTopHorizontalPoint T σ - ρ‖ :=
          mul_le_mul_of_nonneg_left hre
            (one_div_nonneg.mpr (norm_nonneg _))
    _ = 1 := by
          field_simp [hzpos.ne']

private theorem kadiriBotHorizontalCauchyRatio_mul_abs_re_le_one
    {T σ : ℝ} {ρ : ℂ}
    (hden : kadiriBotHorizontalPoint T σ - ρ ≠ 0) :
    ‖(1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)‖ *
        |σ - ρ.re| ≤ 1 := by
  have hzpos : 0 < ‖kadiriBotHorizontalPoint T σ - ρ‖ :=
    norm_pos_iff.mpr hden
  have hre :
      |σ - ρ.re| ≤ ‖kadiriBotHorizontalPoint T σ - ρ‖ := by
    have hre_eq :
        (kadiriBotHorizontalPoint T σ - ρ).re = σ - ρ.re := by
      simp [kadiriBotHorizontalPoint]
    calc
      |σ - ρ.re| = |(kadiriBotHorizontalPoint T σ - ρ).re| := by
        rw [hre_eq]
      _ ≤ ‖kadiriBotHorizontalPoint T σ - ρ‖ :=
        Complex.abs_re_le_norm _
  calc
    ‖(1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)‖ * |σ - ρ.re|
        = (1 / ‖kadiriBotHorizontalPoint T σ - ρ‖) * |σ - ρ.re| := by
          rw [Complex.norm_div, norm_one]
    _ ≤ (1 / ‖kadiriBotHorizontalPoint T σ - ρ‖) *
          ‖kadiriBotHorizontalPoint T σ - ρ‖ :=
          mul_le_mul_of_nonneg_left hre
            (one_div_nonneg.mpr (norm_nonneg _))
    _ = 1 := by
          field_simp [hzpos.ne']

private theorem KadiriPhiConditionB.topHorizontalSingleZeroWindowPVVariation_norm_le
    {φ : ℝ → ℂ} {a T A1 : ℝ} {ρ : ℂ}
    (ha : 0 ≤ a) (hB : KadiriPhiConditionB φ a) (hA1 : 0 ≤ A1)
    (hderiv :
      ∀ x ∈ Set.Icc (-a) (1 + a),
        ‖deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
            (-(kadiriTopHorizontalPoint T x))‖ ≤ A1 / |T|)
    (hNo : KadiriNoZeroOrdinate T)
    (hρ : ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset) :
    ‖kadiriTopHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ‖
      ≤ (‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ *
            volume.real (Set.Ioo (-a) (1 + a)) * A1) / |T| := by
  let prefactor : ℂ := 1 / (2 * (Real.pi : ℂ) * I)
  let S : Set ℝ := Set.Ioo (-a) (1 + a)
  have hmeasure : volume S < ⊤ := by
    simp [S, Real.volume_Ioo]
  have hC_nonneg : 0 ≤ A1 / |T| := div_nonneg hA1 (abs_nonneg T)
  have hρre_Ioo := zeroes_rect_Ioo_Icc_window_toFinset_re_mem hρ
  have hρre_Icc : ρ.re ∈ Set.Icc (-a) (1 + a) := by
    constructor
    · linarith [ha, hρre_Ioo.1]
    · linarith [ha, hρre_Ioo.2]
  have hset :
      ‖∫ σ in S,
        ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
          (kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)) -
            kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re)))‖
        ≤ (A1 / |T|) * volume.real S := by
    refine MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := S)
      (f := fun σ : ℝ =>
        ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
          (kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)) -
            kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re))))
      hmeasure ?_
    intro σ hσ
    have hσ_Icc : σ ∈ Set.Icc (-a) (1 + a) :=
      Set.Ioo_subset_Icc_self hσ
    have hρzero := zeroes_rect_Ioo_Icc_window_toFinset_zeta_zero hρ
    have hden : kadiriTopHorizontalPoint T σ - ρ ≠ 0 := by
      intro hzero
      have hp : kadiriTopHorizontalPoint T σ = ρ := sub_eq_zero.mp hzero
      have him : ρ.im = T := by
        rw [← hp]
        simp [kadiriTopHorizontalPoint]
      exact (hNo ρ hρzero) him
    have hphi :=
      hB.topHorizontalPhi_variation_norm_le hderiv hσ_Icc hρre_Icc
    have hslope := kadiriTopHorizontalCauchyRatio_mul_abs_re_le_one hden
    calc
      ‖((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
          (kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)) -
            kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re)))‖
          = ‖(1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)‖ *
              ‖kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)) -
                kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re))‖ := by
            rw [norm_mul]
      _ ≤ ‖(1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)‖ *
            ((A1 / |T|) * |σ - ρ.re|) :=
            mul_le_mul_of_nonneg_left hphi (norm_nonneg _)
      _ = (A1 / |T|) *
            (‖(1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)‖ *
              |σ - ρ.re|) := by
            ring
      _ ≤ (A1 / |T|) * 1 :=
            mul_le_mul_of_nonneg_left hslope hC_nonneg
      _ = A1 / |T| := by
            ring
  calc
    ‖kadiriTopHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ‖
        = ‖prefactor *
            ∫ σ in S,
              ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
                (kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)) -
                  kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re)))‖ := by
          simp [kadiriTopHorizontalSingleZeroWindowPVVariationIntegral, prefactor, S]
    _ = ‖prefactor‖ *
          ‖∫ σ in S,
              ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
                (kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)) -
                  kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re)))‖ := by
          rw [norm_mul]
    _ ≤ ‖prefactor‖ * ((A1 / |T|) * volume.real S) :=
          mul_le_mul_of_nonneg_left hset (norm_nonneg _)
    _ = (‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ *
            volume.real (Set.Ioo (-a) (1 + a)) * A1) / |T| := by
          dsimp [prefactor, S]
          ring

private theorem KadiriPhiConditionB.botHorizontalSingleZeroWindowPVVariation_norm_le
    {φ : ℝ → ℂ} {a T A1 : ℝ} {ρ : ℂ}
    (ha : 0 ≤ a) (hB : KadiriPhiConditionB φ a) (hA1 : 0 ≤ A1)
    (hderiv :
      ∀ x ∈ Set.Icc (-a) (1 + a),
        ‖deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
            (-(kadiriBotHorizontalPoint T x))‖ ≤ A1 / |T|)
    (hNo : KadiriNoZeroOrdinate (-T))
    (hρ : ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset) :
    ‖kadiriBotHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ‖
      ≤ (‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ *
            volume.real (Set.Ioo (-a) (1 + a)) * A1) / |T| := by
  let prefactor : ℂ := 1 / (2 * (Real.pi : ℂ) * I)
  let S : Set ℝ := Set.Ioo (-a) (1 + a)
  have hmeasure : volume S < ⊤ := by
    simp [S, Real.volume_Ioo]
  have hC_nonneg : 0 ≤ A1 / |T| := div_nonneg hA1 (abs_nonneg T)
  have hρre_Ioo := zeroes_rect_Ioo_Icc_window_toFinset_re_mem hρ
  have hρre_Icc : ρ.re ∈ Set.Icc (-a) (1 + a) := by
    constructor
    · linarith [ha, hρre_Ioo.1]
    · linarith [ha, hρre_Ioo.2]
  have hset :
      ‖∫ σ in S,
        ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
          (kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)) -
            kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re)))‖
        ≤ (A1 / |T|) * volume.real S := by
    refine MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := S)
      (f := fun σ : ℝ =>
        ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
          (kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)) -
            kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re))))
      hmeasure ?_
    intro σ hσ
    have hσ_Icc : σ ∈ Set.Icc (-a) (1 + a) :=
      Set.Ioo_subset_Icc_self hσ
    have hρzero := zeroes_rect_Ioo_Icc_window_toFinset_zeta_zero hρ
    have hden : kadiriBotHorizontalPoint T σ - ρ ≠ 0 := by
      intro hzero
      have hp : kadiriBotHorizontalPoint T σ = ρ := sub_eq_zero.mp hzero
      have him : ρ.im = -T := by
        rw [← hp]
        simp [kadiriBotHorizontalPoint]
      exact (hNo ρ hρzero) him
    have hphi :=
      hB.botHorizontalPhi_variation_norm_le hderiv hσ_Icc hρre_Icc
    have hslope := kadiriBotHorizontalCauchyRatio_mul_abs_re_le_one hden
    calc
      ‖((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
          (kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)) -
            kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re)))‖
          = ‖(1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)‖ *
              ‖kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)) -
                kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re))‖ := by
            rw [norm_mul]
      _ ≤ ‖(1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)‖ *
            ((A1 / |T|) * |σ - ρ.re|) :=
            mul_le_mul_of_nonneg_left hphi (norm_nonneg _)
      _ = (A1 / |T|) *
            (‖(1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)‖ *
              |σ - ρ.re|) := by
            ring
      _ ≤ (A1 / |T|) * 1 :=
            mul_le_mul_of_nonneg_left hslope hC_nonneg
      _ = A1 / |T| := by
            ring
  calc
    ‖kadiriBotHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ‖
        = ‖prefactor *
            ∫ σ in S,
              ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
                (kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)) -
                  kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re)))‖ := by
          simp [kadiriBotHorizontalSingleZeroWindowPVVariationIntegral, prefactor, S]
    _ = ‖prefactor‖ *
          ‖∫ σ in S,
              ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
                (kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)) -
                  kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re)))‖ := by
          rw [norm_mul]
    _ ≤ ‖prefactor‖ * ((A1 / |T|) * volume.real S) :=
          mul_le_mul_of_nonneg_left hset (norm_nonneg _)
    _ = (‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ *
            volume.real (Set.Ioo (-a) (1 + a)) * A1) / |T| := by
          dsimp [prefactor, S]
          ring

private theorem kadiriConditionB_riemannZeta_order_cast_real_nonneg_of_window
    {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset) :
    0 ≤ ((riemannZeta.order ρ : ℤ) : ℝ) := by
  have hρmem :
      ρ ∈ riemannZeta.zeroes_rect (Set.Ioo (0 : ℝ) 1)
        (Set.Icc (T - 1) (T + 1)) :=
    (zeroes_rect_Ioo_Icc_window_finite T).mem_toFinset.mp hρ
  exact_mod_cast riemannZeta_order_nonneg (zeroes_rect_Ioo_ne_one hρmem)

private theorem kadiriConditionB_riemannZeta_order_complex_norm_eq_real_of_window
    {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset) :
    ‖((riemannZeta.order ρ : ℤ) : ℂ)‖ =
      ((riemannZeta.order ρ : ℤ) : ℝ) := by
  have horder_nonneg :=
    kadiriConditionB_riemannZeta_order_cast_real_nonneg_of_window hρ
  change ‖(((riemannZeta.order ρ : ℤ) : ℝ) : ℂ)‖ =
    ((riemannZeta.order ρ : ℤ) : ℝ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg horder_nonneg]

/-- Condition (B) proves the remaining zero-window `Φ`-variation estimate. -/
private theorem kadiriHorizontalZeroWindowVariationEstimate_of_conditionB
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hB : KadiriPhiConditionB φ a) :
    KadiriHorizontalZeroWindowVariationEstimate φ a := by
  rcases kadiriHorizontalPhiPrimeDecayBound_of_conditionB_nonneg ha hB with
    ⟨_A0, A1, _hA0, hA1, hΦ⟩
  let prefactor : ℂ := 1 / (2 * (Real.pi : ℂ) * I)
  let S : Set ℝ := Set.Ioo (-a) (1 + a)
  let A : ℝ := ‖prefactor‖ * volume.real S * A1
  refine ⟨A, ?_, ?_⟩
  · dsimp [A]
    positivity
  · filter_upwards [hΦ, Filter.eventually_ge_atTop (Real.exp 1)] with T hΦT hT_ge
    have hT_nonneg : 0 ≤ T := le_trans (Real.exp_pos 1).le hT_ge
    have hT_exp : Real.exp 1 ≤ |T| := by
      simpa [abs_of_nonneg hT_nonneg] using hT_ge
    rcases hΦT with ⟨_hT_two, hΦtop, hΦbot⟩
    refine ⟨hT_exp, ?_, ?_⟩
    · intro hNo ρ hρ
      have hvar :=
        hB.topHorizontalSingleZeroWindowPVVariation_norm_le
          ha hA1 (fun x hx => (hΦtop x hx).2) hNo hρ
      have horder_nonneg :=
        kadiriConditionB_riemannZeta_order_cast_real_nonneg_of_window hρ
      have horder_norm :=
        kadiriConditionB_riemannZeta_order_complex_norm_eq_real_of_window hρ
      calc
        ‖((riemannZeta.order ρ : ℤ) : ℂ) *
            kadiriTopHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ‖
            = ‖((riemannZeta.order ρ : ℤ) : ℂ)‖ *
                ‖kadiriTopHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ‖ := by
              rw [norm_mul]
        _ = ((riemannZeta.order ρ : ℤ) : ℝ) *
                ‖kadiriTopHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ‖ := by
              rw [horder_norm]
        _ ≤ ((riemannZeta.order ρ : ℤ) : ℝ) *
              ((‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ *
                    volume.real (Set.Ioo (-a) (1 + a)) * A1) / |T|) :=
              mul_le_mul_of_nonneg_left hvar horder_nonneg
        _ = (A / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ) := by
              dsimp [A, prefactor, S]
              ring
    · intro hNo ρ hρ
      have hvar :=
        hB.botHorizontalSingleZeroWindowPVVariation_norm_le
          ha hA1 (fun x hx => (hΦbot x hx).2) hNo hρ
      have horder_nonneg :=
        kadiriConditionB_riemannZeta_order_cast_real_nonneg_of_window hρ
      have horder_norm :=
        kadiriConditionB_riemannZeta_order_complex_norm_eq_real_of_window hρ
      calc
        ‖((riemannZeta.order ρ : ℤ) : ℂ) *
            kadiriBotHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ‖
            = ‖((riemannZeta.order ρ : ℤ) : ℂ)‖ *
                ‖kadiriBotHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ‖ := by
              rw [norm_mul]
        _ = ((riemannZeta.order ρ : ℤ) : ℝ) *
                ‖kadiriBotHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ‖ := by
              rw [horder_norm]
        _ ≤ ((riemannZeta.order ρ : ℤ) : ℝ) *
              ((‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ *
                    volume.real (Set.Ioo (-a) (1 + a)) * A1) / |T|) :=
              mul_le_mul_of_nonneg_left hvar horder_nonneg
        _ = (A / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ) := by
              dsimp [A, prefactor, S]
              ring

/-- Condition (B) supplies enough continuity to expand the finite zero-window
PV contribution into the finite sum of single-zero PV integrals. -/
private theorem kadiriHorizontalZeroWindowFinitePoleExpansion_of_conditionB
    {φ : ℝ → ℂ} {a : ℝ} (hB : KadiriPhiConditionB φ a) :
    KadiriHorizontalZeroWindowFinitePoleExpansion φ a := by
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T _hT
  constructor
  · intro hNo
    let S : Set ℝ := Set.Ioo (-a) (1 + a)
    let Z := (zeroes_rect_Ioo_Icc_window_finite T).toFinset
    let prefactor : ℂ := 1 / (2 * (Real.pi : ℂ) * I)
    have hterm_int :
        ∀ ρ ∈ Z, Integrable (fun σ : ℝ =>
          ((riemannZeta.order ρ : ℤ) : ℂ) *
            (((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
              kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))))
          (volume.restrict S) := by
      intro ρ hρ
      have hker_cont : ContinuousOn (fun σ : ℝ =>
          (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))
          (Set.Icc (-a) (1 + a)) := by
        intro σ _hσ
        have hpoint : ContinuousAt (fun x : ℝ => kadiriTopHorizontalPoint T x - ρ) σ := by
          dsimp [kadiriTopHorizontalPoint]
          fun_prop
        have hden : kadiriTopHorizontalPoint T σ - ρ ≠ 0 := by
          intro hzero
          have hp : kadiriTopHorizontalPoint T σ = ρ := sub_eq_zero.mp hzero
          have hρzero : riemannZeta ρ = 0 := by
            have hmem := (zeroes_rect_Ioo_Icc_window_finite T).mem_toFinset.mp
              (by simpa [Z] using hρ)
            simpa [riemannZeta.zeroes] using hmem.2.2
          have him : ρ.im = T := by
            rw [← hp]
            simp [kadiriTopHorizontalPoint]
          exact (hNo ρ hρzero) him
        exact (continuousAt_const.div hpoint hden).continuousWithinAt
      have hPhi_cont : ContinuousOn (fun σ : ℝ =>
          kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)))
          (Set.Icc (-a) (1 + a)) := by
        intro σ hσ
        have hpoint : ContinuousAt (fun x : ℝ => -(kadiriTopHorizontalPoint T x)) σ := by
          dsimp [kadiriTopHorizontalPoint]
          fun_prop
        have hPhi_at : ContinuousAt (fun z : ℂ => kadiriHorizontalPhi φ z)
            (-(kadiriTopHorizontalPoint T σ)) := by
          have hderiv := hB.kadiriHorizontalPhi_hasDerivAt
            (z0 := -(kadiriTopHorizontalPoint T σ)) (by
              simpa [kadiriTopHorizontalPoint] using hσ)
          exact hderiv.continuousAt
        exact (ContinuousAt.comp (x := σ)
            (f := fun x : ℝ => -(kadiriTopHorizontalPoint T x))
            (g := fun z : ℂ => kadiriHorizontalPhi φ z)
            hPhi_at hpoint).continuousWithinAt
      have hcont :
          ContinuousOn (fun σ : ℝ =>
            ((riemannZeta.order ρ : ℤ) : ℂ) *
              (((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
                kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))))
            (Set.Icc (-a) (1 + a)) :=
        continuousOn_const.mul (hker_cont.mul hPhi_cont)
      have hint_icc :
          IntegrableOn (fun σ : ℝ =>
            ((riemannZeta.order ρ : ℤ) : ℂ) *
              (((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
                kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))))
            (Set.Icc (-a) (1 + a)) :=
        hcont.integrableOn_Icc
      have hint_ioo := hint_icc.mono_set Set.Ioo_subset_Icc_self
      simpa [S, MeasureTheory.IntegrableOn] using hint_ioo
    have hsum_integrand : ∀ σ : ℝ,
        (riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
          (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))) *
          kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)) =
        ∑ ρ ∈ Z,
          ((riemannZeta.order ρ : ℤ) : ℂ) *
            (((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
              kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))) := by
      intro σ
      rw [zeroes_sum_eq_toFinset_sum
        (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))
        (zeroes_rect_Ioo_Icc_window_finite T), Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro ρ hρ
      ring
    calc
      kadiriTopHorizontalZeroWindowPVIntegral φ a T
          = prefactor *
              ∫ σ in S,
                (riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
                  (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))) *
                  kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)) := by
              simp [kadiriTopHorizontalZeroWindowPVIntegral, prefactor, S]
      _ = prefactor *
              ∫ σ in S,
                ∑ ρ ∈ Z,
                  ((riemannZeta.order ρ : ℤ) : ℂ) *
                    (((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
                      kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))) := by
              congr 1
              exact MeasureTheory.integral_congr_ae
                (Filter.Eventually.of_forall hsum_integrand)
      _ = prefactor *
              ∑ ρ ∈ Z,
                ∫ σ in S,
                  ((riemannZeta.order ρ : ℤ) : ℂ) *
                    (((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
                      kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))) := by
              rw [MeasureTheory.integral_finsetSum Z hterm_int]
      _ = ∑ ρ ∈ Z,
            ((riemannZeta.order ρ : ℤ) : ℂ) *
              kadiriTopHorizontalSingleZeroWindowPVIntegral φ a T ρ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro ρ hρ
              rw [MeasureTheory.integral_const_mul]
              simp [kadiriTopHorizontalSingleZeroWindowPVIntegral, prefactor, S]
              ring
  · intro hNo
    let S : Set ℝ := Set.Ioo (-a) (1 + a)
    let Z := (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset
    let prefactor : ℂ := 1 / (2 * (Real.pi : ℂ) * I)
    have hterm_int :
        ∀ ρ ∈ Z, Integrable (fun σ : ℝ =>
          ((riemannZeta.order ρ : ℤ) : ℂ) *
            (((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
              kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))))
          (volume.restrict S) := by
      intro ρ hρ
      have hker_cont : ContinuousOn (fun σ : ℝ =>
          (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))
          (Set.Icc (-a) (1 + a)) := by
        intro σ _hσ
        have hpoint : ContinuousAt (fun x : ℝ => kadiriBotHorizontalPoint T x - ρ) σ := by
          dsimp [kadiriBotHorizontalPoint]
          fun_prop
        have hden : kadiriBotHorizontalPoint T σ - ρ ≠ 0 := by
          intro hzero
          have hp : kadiriBotHorizontalPoint T σ = ρ := sub_eq_zero.mp hzero
          have hρzero : riemannZeta ρ = 0 := by
            have hmem := (zeroes_rect_Ioo_Icc_window_finite (-T)).mem_toFinset.mp
              (by simpa [Z] using hρ)
            simpa [riemannZeta.zeroes] using hmem.2.2
          have him : ρ.im = -T := by
            rw [← hp]
            simp [kadiriBotHorizontalPoint]
          exact (hNo ρ hρzero) him
        exact (continuousAt_const.div hpoint hden).continuousWithinAt
      have hPhi_cont : ContinuousOn (fun σ : ℝ =>
          kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)))
          (Set.Icc (-a) (1 + a)) := by
        intro σ hσ
        have hpoint : ContinuousAt (fun x : ℝ => -(kadiriBotHorizontalPoint T x)) σ := by
          dsimp [kadiriBotHorizontalPoint]
          fun_prop
        have hPhi_at : ContinuousAt (fun z : ℂ => kadiriHorizontalPhi φ z)
            (-(kadiriBotHorizontalPoint T σ)) := by
          have hderiv := hB.kadiriHorizontalPhi_hasDerivAt
            (z0 := -(kadiriBotHorizontalPoint T σ)) (by
              simpa [kadiriBotHorizontalPoint] using hσ)
          exact hderiv.continuousAt
        exact (ContinuousAt.comp (x := σ)
            (f := fun x : ℝ => -(kadiriBotHorizontalPoint T x))
            (g := fun z : ℂ => kadiriHorizontalPhi φ z)
            hPhi_at hpoint).continuousWithinAt
      have hcont :
          ContinuousOn (fun σ : ℝ =>
            ((riemannZeta.order ρ : ℤ) : ℂ) *
              (((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
                kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))))
            (Set.Icc (-a) (1 + a)) :=
        continuousOn_const.mul (hker_cont.mul hPhi_cont)
      have hint_icc :
          IntegrableOn (fun σ : ℝ =>
            ((riemannZeta.order ρ : ℤ) : ℂ) *
              (((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
                kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))))
            (Set.Icc (-a) (1 + a)) :=
        hcont.integrableOn_Icc
      have hint_ioo := hint_icc.mono_set Set.Ioo_subset_Icc_self
      simpa [S, MeasureTheory.IntegrableOn] using hint_ioo
    have hsum_integrand : ∀ σ : ℝ,
        (riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc ((-T) - 1) ((-T) + 1))
          (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))) *
          kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)) =
        ∑ ρ ∈ Z,
          ((riemannZeta.order ρ : ℤ) : ℂ) *
            (((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
              kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))) := by
      intro σ
      rw [zeroes_sum_eq_toFinset_sum
        (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))
        (zeroes_rect_Ioo_Icc_window_finite (-T)), Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro ρ hρ
      ring
    calc
      kadiriBotHorizontalZeroWindowPVIntegral φ a T
          = prefactor *
              ∫ σ in S,
                (riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc ((-T) - 1) ((-T) + 1))
                  (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))) *
                  kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)) := by
              simp [kadiriBotHorizontalZeroWindowPVIntegral, prefactor, S]
      _ = prefactor *
              ∫ σ in S,
                ∑ ρ ∈ Z,
                  ((riemannZeta.order ρ : ℤ) : ℂ) *
                    (((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
                      kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))) := by
              congr 1
              exact MeasureTheory.integral_congr_ae
                (Filter.Eventually.of_forall hsum_integrand)
      _ = prefactor *
              ∑ ρ ∈ Z,
                ∫ σ in S,
                  ((riemannZeta.order ρ : ℤ) : ℂ) *
                    (((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
                      kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))) := by
              rw [MeasureTheory.integral_finsetSum Z hterm_int]
      _ = ∑ ρ ∈ Z,
            ((riemannZeta.order ρ : ℤ) : ℂ) *
              kadiriBotHorizontalSingleZeroWindowPVIntegral φ a T ρ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro ρ hρ
              rw [MeasureTheory.integral_const_mul]
              simp [kadiriBotHorizontalSingleZeroWindowPVIntegral, prefactor, S]
              ring

/-- Condition (B), the finite zero-window kernel-order estimate, and
zero-window order counting give the finite zero-window PV kernel estimate. -/
private theorem kadiriHorizontalFiniteZeroWindowPVKernelEstimate_of_conditionB_kernelOrder_count
    {φ : ℝ → ℂ} {a : ℝ}
    (hdecay : KadiriHorizontalPhiC1Decay_of_conditionB φ a)
    (hB : KadiriPhiConditionB φ a)
    (hkernel : KadiriHorizontalZeroWindowPVKernelOrderEstimate_of_phiPrime φ a)
    (horders : KadiriHorizontalZeroWindowOrderSumBound) :
    KadiriHorizontalFiniteZeroWindowPVKernelEstimate φ a :=
  kadiriHorizontalFiniteZeroWindowPVKernelEstimate_of_phiPrime_kernelOrder_count
    (hdecay hB) hkernel horders

/-- Condition (B), the finite zero-window kernel-order estimate, and
zero-window order counting supply the two analytic inputs consumed by the
zero-window PV correction theorem. -/
private theorem kadiriHorizontalZeroWindowPVInputs_of_conditionB_kernelOrder_count
    {φ : ℝ → ℂ} {a : ℝ}
    (hdecay : KadiriHorizontalPhiC1Decay_of_conditionB φ a)
    (hB : KadiriPhiConditionB φ a)
    (hkernel : KadiriHorizontalZeroWindowPVKernelOrderEstimate_of_phiPrime φ a)
    (horders : KadiriHorizontalZeroWindowOrderSumBound) :
    KadiriHorizontalFiniteZeroWindowPVKernelEstimate φ a ∧
      KadiriHorizontalZeroWindowPVIntegrability φ a :=
  ⟨kadiriHorizontalFiniteZeroWindowPVKernelEstimate_of_conditionB_kernelOrder_count
      hdecay hB hkernel horders,
    kadiriHorizontalZeroWindowPVIntegrability_of_conditionB hB⟩

private theorem kadiriHorizontalZeroWindowPVInputs_of_conditionB_finitePoleExpansion_count
    {φ : ℝ → ℂ} {a : ℝ}
    (hB : KadiriPhiConditionB φ a)
    (hexpand : KadiriHorizontalZeroWindowFinitePoleExpansion φ a)
    (hsingle : KadiriHorizontalZeroWindowSinglePoleWeightedEstimate φ a)
    (horders : KadiriHorizontalZeroWindowOrderSumBound) :
    KadiriHorizontalFiniteZeroWindowPVKernelEstimate φ a ∧
      KadiriHorizontalZeroWindowPVIntegrability φ a :=
  ⟨kadiriHorizontalFiniteZeroWindowPVKernelEstimate_of_finitePoleExpansion_count
      hexpand hsingle horders,
    kadiriHorizontalZeroWindowPVIntegrability_of_conditionB hB⟩

/-- Condition (B) supplies the finite-pole expansion and zero-window
integrability; the per-zero weighted kernel estimate and zero-window order
counting supply the finite zero-window kernel estimate. -/
private theorem kadiriHorizontalZeroWindowPVInputs_of_conditionB_singlePole_count
    {φ : ℝ → ℂ} {a : ℝ}
    (hB : KadiriPhiConditionB φ a)
    (hsingle : KadiriHorizontalZeroWindowSinglePoleWeightedEstimate φ a)
    (horders : KadiriHorizontalZeroWindowOrderSumBound) :
    KadiriHorizontalFiniteZeroWindowPVKernelEstimate φ a ∧
      KadiriHorizontalZeroWindowPVIntegrability φ a :=
  kadiriHorizontalZeroWindowPVInputs_of_conditionB_finitePoleExpansion_count
    hB (kadiriHorizontalZeroWindowFinitePoleExpansion_of_conditionB hB)
    hsingle horders

private theorem kadiriHorizontalZeroWindowPVCorrectionBound_of_conditionB_and_zeroWindowKernelEstimate
    {φ : ℝ → ℂ} {a : ℝ}
    (hB : KadiriPhiConditionB φ a)
    (hkernel : KadiriHorizontalFiniteZeroWindowPVKernelEstimate φ a) :
    KadiriHorizontalZeroWindowPVCorrectionBound φ a :=
  kadiriHorizontalZeroWindowPVCorrectionBound_of_kernelEstimate
    (kadiriHorizontalZeroWindowPVIntegrability_of_conditionB hB) hkernel

private theorem kadiriHorizontalZeroWindowPVCorrectionBound_of_conditionB_finitePoleExpansion_count
    {φ : ℝ → ℂ} {a : ℝ}
    (hB : KadiriPhiConditionB φ a)
    (hexpand : KadiriHorizontalZeroWindowFinitePoleExpansion φ a)
    (hsingle : KadiriHorizontalZeroWindowSinglePoleWeightedEstimate φ a)
    (horders : KadiriHorizontalZeroWindowOrderSumBound) :
    KadiriHorizontalZeroWindowPVCorrectionBound φ a :=
  kadiriHorizontalZeroWindowPVCorrectionBound_of_finitePoleExpansion_count
    (kadiriHorizontalZeroWindowPVIntegrability_of_conditionB hB)
    hexpand hsingle horders

/-- Condition (B) supplies zero-window integrability and the finite-pole
expansion; the per-zero weighted kernel estimate and zero-window order counting
give the finite zero-window correction bound. -/
private theorem kadiriHorizontalZeroWindowPVCorrectionBound_of_conditionB_singlePole_count
    {φ : ℝ → ℂ} {a : ℝ}
    (hB : KadiriPhiConditionB φ a)
    (hsingle : KadiriHorizontalZeroWindowSinglePoleWeightedEstimate φ a)
    (horders : KadiriHorizontalZeroWindowOrderSumBound) :
    KadiriHorizontalZeroWindowPVCorrectionBound φ a :=
  kadiriHorizontalZeroWindowPVCorrectionBound_of_conditionB_finitePoleExpansion_count
    hB (kadiriHorizontalZeroWindowFinitePoleExpansion_of_conditionB hB)
    hsingle horders

private theorem kadiriHorizontalZeroWindowPVCorrectionBound_of_conditionB_singlePole_finalBound
    {φ : ℝ → ℂ} {a : ℝ}
    (hB : KadiriPhiConditionB φ a)
    (hsingle : KadiriHorizontalZeroWindowSinglePoleWeightedEstimate φ a) :
    KadiriHorizontalZeroWindowPVCorrectionBound φ a :=
  kadiriHorizontalZeroWindowPVCorrectionBound_of_conditionB_singlePole_count
    hB hsingle kadiriHorizontalZeroWindowOrderSumBound_of_finalBound

/-- Named alias spelling out that the remaining single-pole input is the
per-zero weighted estimate. -/
private theorem kadiriHorizontalZeroWindowPVCorrectionBound_of_conditionB_singlePoleWeighted_finalBound
    {φ : ℝ → ℂ} {a : ℝ}
    (hB : KadiriPhiConditionB φ a)
    (hsingle : KadiriHorizontalZeroWindowSinglePoleWeightedEstimate φ a) :
    KadiriHorizontalZeroWindowPVCorrectionBound φ a :=
  kadiriHorizontalZeroWindowPVCorrectionBound_of_conditionB_singlePole_finalBound
    hB hsingle

/-- Condition (B), the finite zero-window kernel-order estimate, and zero-window
order counting give the finite zero-window correction bound. -/
private theorem kadiriHorizontalZeroWindowPVCorrectionBound_of_conditionB_kernelOrder_count
    {φ : ℝ → ℂ} {a : ℝ}
    (hdecay : KadiriHorizontalPhiC1Decay_of_conditionB φ a)
    (hB : KadiriPhiConditionB φ a)
    (hkernel : KadiriHorizontalZeroWindowPVKernelOrderEstimate_of_phiPrime φ a)
    (horders : KadiriHorizontalZeroWindowOrderSumBound) :
    KadiriHorizontalZeroWindowPVCorrectionBound φ a :=
  kadiriHorizontalZeroWindowPVCorrectionBound_of_conditionB_and_zeroWindowKernelEstimate hB
    (kadiriHorizontalFiniteZeroWindowPVKernelEstimate_of_conditionB_kernelOrder_count
      hdecay hB hkernel horders)

private theorem kadiriHorizontalZeroWindowPVCorrectionBound_of_conditionB_kernelOrder_finalBound
    {φ : ℝ → ℂ} {a : ℝ}
    (hdecay : KadiriHorizontalPhiC1Decay_of_conditionB φ a)
    (hB : KadiriPhiConditionB φ a)
    (hkernel : KadiriHorizontalZeroWindowPVKernelOrderEstimate_of_phiPrime φ a) :
    KadiriHorizontalZeroWindowPVCorrectionBound φ a :=
  kadiriHorizontalZeroWindowPVCorrectionBound_of_conditionB_kernelOrder_count
    hdecay hB hkernel kadiriHorizontalZeroWindowOrderSumBound_of_finalBound

/-- For `a ≥ 0`, condition (B) supplies `Φ`/`Φ'` decay, while FinalBound supplies
the finite zero-window order budget. -/
private theorem kadiriHorizontalZeroWindowPVCorrectionBound_of_conditionB_kernelOrder_finalBound_of_nonneg
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hB : KadiriPhiConditionB φ a)
    (hkernel : KadiriHorizontalZeroWindowPVKernelOrderEstimate_of_phiPrime φ a) :
    KadiriHorizontalZeroWindowPVCorrectionBound φ a :=
  kadiriHorizontalZeroWindowPVCorrectionBound_of_conditionB_kernelOrder_finalBound
    (KadiriHorizontalPhiC1Decay_of_conditionB_of_nonneg ha) hB hkernel

/-! ## The q1 close from condition (B)

Everything below is axiom-clean and uses only the proved route: the PF remainder
side is unconditional via `kadiriHorizontalPFRemainderLinearInput_of_finalBound`,
and the two `φ`-dependent contracts are supplied by the named condition-(B)
analytic inputs above. -/

/-- The named condition-(B) C¹ decay input supplies the
`KadiriHorizontalPhiPrimeDecayBound` contract for a condition-(B) `φ`. -/
private theorem kadiriHorizontalPhiPrimeDecayBound_of_conditionB
    {φ : ℝ → ℂ} {a : ℝ}
    (hdecay : KadiriHorizontalPhiC1Decay_of_conditionB φ a)
    (hB : KadiriPhiConditionB φ a) :
    KadiriHorizontalPhiPrimeDecayBound φ a :=
  hdecay hB

/-- The named condition-(B) PV-integration input supplies the
`KadiriHorizontalPVIntegrationBound` contract for a condition-(B) `φ`. -/
private theorem kadiriHorizontalPVIntegrationBound_of_conditionB
    {φ : ℝ → ℂ} {a : ℝ}
    (hpv : KadiriHorizontalPVIntegration_of_conditionB φ a)
    (hB : KadiriPhiConditionB φ a) :
    KadiriHorizontalPVIntegrationBound φ a :=
  hpv hB

/-- The condition-(B) C¹ decay and PV-integration inputs assemble the
`KadiriHorizontalPhiC1DecayBound` route input for a condition-(B) `φ`. -/
private theorem kadiriHorizontalPhiC1DecayBound_of_conditionB'
    {φ : ℝ → ℂ} {a : ℝ}
    (hdecay : KadiriHorizontalPhiC1Decay_of_conditionB φ a)
    (hpv : KadiriHorizontalPVIntegration_of_conditionB φ a)
    (hB : KadiriPhiConditionB φ a) :
    KadiriHorizontalPhiC1DecayBound φ a :=
  kadiriHorizontalPhiC1DecayBound_of_conditionB
    (kadiriHorizontalPhiPrimeDecayBound_of_conditionB hdecay hB)
    (kadiriHorizontalPVIntegrationBound_of_conditionB hpv hB)

/-- FinalBound, condition-(B) C¹ decay, and the finite zero-window correction
prove the named condition-(B) PV-integration target.  This isolates the only
remaining pole-window input from the pure `φ` decay step. -/
private theorem kadiriHorizontalPVIntegration_of_conditionB_and_zeroWindowCorrection
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hdecay : KadiriHorizontalPhiC1Decay_of_conditionB φ a)
    (hcorr : KadiriHorizontalZeroWindowPVCorrectionBound φ a) :
    KadiriHorizontalPVIntegration_of_conditionB φ a := by
  intro hB
  exact kadiriHorizontalPVIntegrationBound_of_pf_phiPrime_and_zeroWindowCorrection
    (kadiriHorizontalPartialFractionRemainderBound_of_finalBound ha)
    (hdecay hB)
    hcorr

/-- FinalBound, the proved condition-(B) `Φ`/`Φ'` decay, and the finite
zero-window correction prove the named condition-(B) PV-integration target. -/
private theorem kadiriHorizontalPVIntegration_of_conditionB_and_zeroWindowCorrection_from_conditionB
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hcorr : KadiriHorizontalZeroWindowPVCorrectionBound φ a) :
    KadiriHorizontalPVIntegration_of_conditionB φ a :=
  kadiriHorizontalPVIntegration_of_conditionB_and_zeroWindowCorrection ha
    (KadiriHorizontalPhiC1Decay_of_conditionB_of_nonneg ha) hcorr

/-- FinalBound, condition (B), and the finite zero-window kernel-order estimate
prove the named condition-(B) PV-integration target. -/
private theorem kadiriHorizontalPVIntegration_of_conditionB_and_zeroWindowKernelOrder_finalBound
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hkernel : KadiriHorizontalZeroWindowPVKernelOrderEstimate_of_phiPrime φ a) :
    KadiriHorizontalPVIntegration_of_conditionB φ a := by
  intro hB
  exact kadiriHorizontalPVIntegration_of_conditionB_and_zeroWindowCorrection_from_conditionB
    ha
    (kadiriHorizontalZeroWindowPVCorrectionBound_of_conditionB_kernelOrder_finalBound_of_nonneg
      ha hB hkernel)
    hB

/-- FinalBound, condition (B), the proved finite-pole expansion, and the
per-zero weighted single-pole estimate prove the named condition-(B)
PV-integration target. -/
private theorem kadiriHorizontalPVIntegration_of_conditionB_and_singlePoleWeighted_finalBound
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hsingle : KadiriHorizontalZeroWindowSinglePoleWeightedEstimate φ a) :
    KadiriHorizontalPVIntegration_of_conditionB φ a := by
  intro hB
  exact kadiriHorizontalPVIntegration_of_conditionB_and_zeroWindowCorrection_from_conditionB
    ha
    (kadiriHorizontalZeroWindowPVCorrectionBound_of_conditionB_singlePoleWeighted_finalBound
      hB hsingle)
    hB

/-- Condition (B), the projected-constant estimate, and the variation estimate
assemble the per-zero weighted single-pole estimate. -/
private theorem kadiriHorizontalZeroWindowSinglePoleWeightedEstimate_of_conditionB_projectedConstant_variation
    {φ : ℝ → ℂ} {a : ℝ}
    (hB : KadiriPhiConditionB φ a)
    (hconst : KadiriHorizontalZeroWindowProjectedConstantEstimate φ a)
    (hvariation : KadiriHorizontalZeroWindowVariationEstimate φ a) :
    KadiriHorizontalZeroWindowSinglePoleWeightedEstimate φ a :=
  kadiriHorizontalZeroWindowSinglePoleWeightedEstimate_of_projectedConstant_variation
    (kadiriHorizontalZeroWindowProjectedSplit_of_conditionB hB) hconst hvariation

/-- FinalBound, condition (B), the projected-constant estimate, and the
variation estimate prove the named condition-(B) PV-integration target. -/
private theorem kadiriHorizontalPVIntegration_of_conditionB_and_projectedConstant_variation_finalBound
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hconst : KadiriHorizontalZeroWindowProjectedConstantEstimate φ a)
    (hvariation : KadiriHorizontalZeroWindowVariationEstimate φ a) :
    KadiriHorizontalPVIntegration_of_conditionB φ a := by
  intro hB
  exact
    (kadiriHorizontalPVIntegration_of_conditionB_and_singlePoleWeighted_finalBound
      ha
      (kadiriHorizontalZeroWindowSinglePoleWeightedEstimate_of_conditionB_projectedConstant_variation
        hB hconst hvariation)) hB

/-- Condition (B), scalar Cauchy control, and the variation estimate assemble
the per-zero weighted single-pole estimate. The projected-constant half is
supplied by the proved `Φ` decay. -/
private theorem kadiriHorizontalZeroWindowSinglePoleWeightedEstimate_of_conditionB_scalarVariation
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hB : KadiriPhiConditionB φ a)
    (hscalar : KadiriHorizontalZeroWindowPVScalarIntegralBound a)
    (hvariation : KadiriHorizontalZeroWindowVariationEstimate φ a) :
    KadiriHorizontalZeroWindowSinglePoleWeightedEstimate φ a :=
  kadiriHorizontalZeroWindowSinglePoleWeightedEstimate_of_conditionB_projectedConstant_variation
    hB
    (kadiriHorizontalZeroWindowProjectedConstantEstimate_of_phiPrime_scalarIntegral
      ha (kadiriHorizontalPhiPrimeDecayBound_of_conditionB_nonneg ha hB) hscalar)
    hvariation

private theorem kadiriHorizontalPVIntegration_of_conditionB_and_scalarVariation_finalBound
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hscalar : KadiriHorizontalZeroWindowPVScalarIntegralBound a)
    (hvariation : KadiriHorizontalZeroWindowVariationEstimate φ a) :
    KadiriHorizontalPVIntegration_of_conditionB φ a := by
  intro hB
  exact
    (kadiriHorizontalPVIntegration_of_conditionB_and_singlePoleWeighted_finalBound
      ha
      (kadiriHorizontalZeroWindowSinglePoleWeightedEstimate_of_conditionB_scalarVariation
        ha hB hscalar hvariation)) hB

/-- For `0 < a`, the proved scalar Cauchy bound leaves only the variation
estimate as the zero-window input for the condition-(B) PV-integration target. -/
private theorem kadiriHorizontalPVIntegration_of_conditionB_and_variation_finalBound
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hvariation : KadiriHorizontalZeroWindowVariationEstimate φ a) :
    KadiriHorizontalPVIntegration_of_conditionB φ a :=
  kadiriHorizontalPVIntegration_of_conditionB_and_scalarVariation_finalBound
    (le_of_lt ha)
    (kadiriHorizontalZeroWindowPVScalarIntegralBound_of_singlePoleKernelBound
      ha (kadiriSinglePolePVKernelBound_holds a))
    hvariation

/-- FinalBound and condition (B) prove the named condition-(B) PV-integration
target with no auxiliary zero-window input. -/
theorem kadiriHorizontalPVIntegration_of_conditionB_finalBound
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 < a) :
    KadiriHorizontalPVIntegration_of_conditionB φ a := by
  intro hB
  exact
    (kadiriHorizontalPVIntegration_of_conditionB_and_variation_finalBound
      ha
      (kadiriHorizontalZeroWindowVariationEstimate_of_conditionB
        (le_of_lt ha) hB)) hB

/-- FinalBound, condition-(B) C¹ decay, zero-window integrability, and the
finite zero-window kernel estimate prove the named condition-(B) PV-integration
target. -/
private theorem kadiriHorizontalPVIntegration_of_conditionB_and_zeroWindowKernelEstimate
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hdecay : KadiriHorizontalPhiC1Decay_of_conditionB φ a)
    (hint : KadiriHorizontalZeroWindowPVIntegrability φ a)
    (hkernel : KadiriHorizontalFiniteZeroWindowPVKernelEstimate φ a) :
    KadiriHorizontalPVIntegration_of_conditionB φ a :=
  kadiriHorizontalPVIntegration_of_conditionB_and_zeroWindowCorrection ha hdecay
    (kadiriHorizontalZeroWindowPVCorrectionBound_of_kernelEstimate hint hkernel)

theorem kadiriHorizontalPVCanonical_bound_of_conditionB
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hdecay : KadiriHorizontalPhiC1Decay_of_conditionB φ a)
    (hpv : KadiriHorizontalPVIntegration_of_conditionB φ a)
    (hB : KadiriPhiConditionB φ a) :
    KadiriHorizontalPVBound
      (kadiriTopHorizontalPVCanonical φ a)
      (kadiriBotHorizontalPVCanonical φ a) :=
  kadiriHorizontalPVCanonical_bound_of_finalBound_and_phiC1Decay ha
    (kadiriHorizontalPhiC1DecayBound_of_conditionB' hdecay hpv hB)

/-- **Horizontal PV package for any condition-(B) `φ`.** -/
def kadiriHorizontalPVPackage_of_conditionB
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hdecay : KadiriHorizontalPhiC1Decay_of_conditionB φ a)
    (hpv : KadiriHorizontalPVIntegration_of_conditionB φ a)
    (hB : KadiriPhiConditionB φ a) :
    KadiriHorizontalPVPackage φ a :=
  kadiriHorizontalPVPackage_of_canonical_bound
    (kadiriHorizontalPVCanonical_bound_of_conditionB ha hdecay hpv hB)

/-- Horizontal PV package from condition (B), FinalBound, and the finite
zero-window correction. -/
private def kadiriHorizontalPVPackage_of_conditionB_and_zeroWindowCorrection
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hdecay : KadiriHorizontalPhiC1Decay_of_conditionB φ a)
    (hcorr : KadiriHorizontalZeroWindowPVCorrectionBound φ a)
    (hB : KadiriPhiConditionB φ a) :
    KadiriHorizontalPVPackage φ a :=
  kadiriHorizontalPVPackage_of_conditionB ha hdecay
    (kadiriHorizontalPVIntegration_of_conditionB_and_zeroWindowCorrection ha hdecay hcorr)
    hB

/-- Horizontal PV package from condition (B), FinalBound, zero-window
integrability, and the finite zero-window kernel estimate. -/
private def kadiriHorizontalPVPackage_of_conditionB_and_zeroWindowKernelEstimate
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hdecay : KadiriHorizontalPhiC1Decay_of_conditionB φ a)
    (hint : KadiriHorizontalZeroWindowPVIntegrability φ a)
    (hkernel : KadiriHorizontalFiniteZeroWindowPVKernelEstimate φ a)
    (hB : KadiriPhiConditionB φ a) :
    KadiriHorizontalPVPackage φ a :=
  kadiriHorizontalPVPackage_of_conditionB ha hdecay
    (kadiriHorizontalPVIntegration_of_conditionB_and_zeroWindowKernelEstimate
      ha hdecay hint hkernel)
    hB

/-- **Top q1 horizontal PV vanishing for any condition-(B) `φ`.**  Given the two
named condition-(B) analytic inputs, the top canonical horizontal PV value tends
to `0` for every `φ` satisfying Kadiri's condition (B). -/
theorem kadiri_thm_3_1_q1_top_horizontal_pv_vanishes_of_conditionB
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hdecay : KadiriHorizontalPhiC1Decay_of_conditionB φ a)
    (hpv : KadiriHorizontalPVIntegration_of_conditionB φ a)
    (hB : KadiriPhiConditionB φ a) :
    Filter.Tendsto (kadiriTopHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_top_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_conditionB ha hdecay hpv hB)

/-- **Bottom q1 horizontal PV vanishing for any condition-(B) `φ`.** -/
theorem kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes_of_conditionB
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hdecay : KadiriHorizontalPhiC1Decay_of_conditionB φ a)
    (hpv : KadiriHorizontalPVIntegration_of_conditionB φ a)
    (hB : KadiriPhiConditionB φ a) :
    Filter.Tendsto (kadiriBotHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_conditionB ha hdecay hpv hB)

private theorem kadiri_thm_3_1_q1_top_horizontal_pv_vanishes_of_conditionB_and_variation_finalBound
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hvariation : KadiriHorizontalZeroWindowVariationEstimate φ a)
    (hB : KadiriPhiConditionB φ a) :
    Filter.Tendsto (kadiriTopHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_top_horizontal_pv_vanishes_of_conditionB
    (le_of_lt ha)
    (KadiriHorizontalPhiC1Decay_of_conditionB_of_nonneg (le_of_lt ha))
    (kadiriHorizontalPVIntegration_of_conditionB_and_variation_finalBound
      ha hvariation)
    hB

/-- Bottom q1 horizontal PV vanishing from condition (B), FinalBound, the proved
scalar Cauchy bound, and the variation estimate. -/
private theorem kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes_of_conditionB_and_variation_finalBound
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hvariation : KadiriHorizontalZeroWindowVariationEstimate φ a)
    (hB : KadiriPhiConditionB φ a) :
    Filter.Tendsto (kadiriBotHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes_of_conditionB
    (le_of_lt ha)
    (KadiriHorizontalPhiC1Decay_of_conditionB_of_nonneg (le_of_lt ha))
    (kadiriHorizontalPVIntegration_of_conditionB_and_variation_finalBound
      ha hvariation)
    hB

/-- Top q1 horizontal PV vanishing from condition (B) and FinalBound, with no
auxiliary zero-window input. -/
theorem kadiri_thm_3_1_q1_top_horizontal_pv_vanishes_of_conditionB_finalBound
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hB : KadiriPhiConditionB φ a) :
    Filter.Tendsto (kadiriTopHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_top_horizontal_pv_vanishes_of_conditionB_and_variation_finalBound
    ha
    (kadiriHorizontalZeroWindowVariationEstimate_of_conditionB
      (le_of_lt ha) hB)
    hB

/-- Bottom q1 horizontal PV vanishing from condition (B) and FinalBound, with no
auxiliary zero-window input. -/
theorem kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes_of_conditionB_finalBound
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hB : KadiriPhiConditionB φ a) :
    Filter.Tendsto (kadiriBotHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes_of_conditionB_and_variation_finalBound
    ha
    (kadiriHorizontalZeroWindowVariationEstimate_of_conditionB
      (le_of_lt ha) hB)
    hB

/-- Top q1 horizontal PV vanishing directly from the original condition-(B)
hypotheses on the test function. -/
theorem kadiri_thm_3_1_q1_top_horizontal_pv_vanishes_of_q1_hypotheses_finalBound
    {φ : ℝ → ℂ} {a b : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hb : 0 < b) (ha : 0 < a) (hab : a < b)
    (ha1 : a < 1)
    (hφ_decay : (fun x : ℝ ↦ φ x * Complex.exp ((x : ℂ) / 2))
      =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * Complex.exp ((x : ℂ) / 2))
      =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|)) :
    Filter.Tendsto (kadiriTopHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_top_horizontal_pv_vanishes_of_conditionB_finalBound
    ha
    (kadiriPhiConditionB_of_q1_hypotheses
      hφ hb hab ha1 hφ_decay hφ'_decay)

/-- Bottom q1 horizontal PV vanishing directly from the original condition-(B)
hypotheses on the test function. -/
theorem kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes_of_q1_hypotheses_finalBound
    {φ : ℝ → ℂ} {a b : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hb : 0 < b) (ha : 0 < a) (hab : a < b)
    (ha1 : a < 1)
    (hφ_decay : (fun x : ℝ ↦ φ x * Complex.exp ((x : ℂ) / 2))
      =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * Complex.exp ((x : ℂ) / 2))
      =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|)) :
    Filter.Tendsto (kadiriBotHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes_of_conditionB_finalBound
    ha
    (kadiriPhiConditionB_of_q1_hypotheses
      hφ hb hab ha1 hφ_decay hφ'_decay)

end

end Kadiri
