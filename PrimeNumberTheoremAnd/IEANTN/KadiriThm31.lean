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
