import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Hadamard Log-Derivative Bridges for Kadiri

This file contains zeta-specific algebraic bridges from the completed zeta
factor to the logarithmic derivative `-ζ'/ζ` used in Kadiri's zero-free-region
argument.
-/

namespace Kadiri

open Complex Filter Topology

/-- The genus-one elementary factor used in Hadamard products. -/
noncomputable def hadamardGenusOneFactor (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp z

/-- Pairing the genus-one factors at opposite zeros cancels the exponential corrections. -/
theorem hadamardGenusOneFactor_pair_cancellation (α w : ℂ) (hα : α ≠ 0) :
    hadamardGenusOneFactor (w / α) * hadamardGenusOneFactor (w / (-α)) = 1 - w ^ 2 / α ^ 2 := by
  unfold hadamardGenusOneFactor
  have hsum : w / α + w / (-α) = 0 := by
    field_simp [hα]
    ring
  have hexp : Complex.exp (w / α) * Complex.exp (w / (-α)) = 1 := by
    rw [← Complex.exp_add, hsum, Complex.exp_zero]
  calc
    (1 - w / α) * Complex.exp (w / α) *
        ((1 - w / (-α)) * Complex.exp (w / (-α)))
        = ((1 - w / α) * (1 - w / (-α))) *
            (Complex.exp (w / α) * Complex.exp (w / (-α))) := by
          ring
    _ = 1 - w ^ 2 / α ^ 2 := by
      rw [hexp]
      field_simp [hα]
      ring

/-- The quadratic zero-orbit block normalized at a basepoint `w₀`. -/
noncomputable def centeredHadamardOrbitBlock (w₀ α w : ℂ) : ℂ :=
  (α ^ 2 - w ^ 2) / (α ^ 2 - w₀ ^ 2)

theorem centeredHadamardOrbitBlock_base {w₀ α : ℂ} (hden : α ^ 2 - w₀ ^ 2 ≠ 0) :
    centeredHadamardOrbitBlock w₀ α w₀ = 1 := by
  unfold centeredHadamardOrbitBlock
  field_simp [hden]

theorem centeredHadamardOrbitBlock_zero_pos {w₀ α : ℂ} :
    centeredHadamardOrbitBlock w₀ α α = 0 := by
  unfold centeredHadamardOrbitBlock
  simp

theorem centeredHadamardOrbitBlock_zero_neg {w₀ α : ℂ} :
    centeredHadamardOrbitBlock w₀ α (-α) = 0 := by
  unfold centeredHadamardOrbitBlock
  simp

theorem centeredHadamardOrbitBlock_ne_zero {w₀ α w : ℂ}
    (hden : α ^ 2 - w₀ ^ 2 ≠ 0) (hw : w ^ 2 ≠ α ^ 2) :
    centeredHadamardOrbitBlock w₀ α w ≠ 0 := by
  unfold centeredHadamardOrbitBlock
  have hnum : α ^ 2 - w ^ 2 ≠ 0 := by
    intro h
    exact hw (sub_eq_zero.mp h).symm
  exact div_ne_zero hnum hden

/-- The normalized paired genus-one factors are exactly the centered quadratic orbit block. -/
theorem normalized_hadamardGenusOneFactor_pair_cancellation (α w₀ w : ℂ)
    (hα : α ≠ 0) (hden : α ^ 2 - w₀ ^ 2 ≠ 0) :
    (hadamardGenusOneFactor (w / α) * hadamardGenusOneFactor (w / (-α))) /
        (hadamardGenusOneFactor (w₀ / α) * hadamardGenusOneFactor (w₀ / (-α))) =
      centeredHadamardOrbitBlock w₀ α w := by
  rw [hadamardGenusOneFactor_pair_cancellation α w hα, hadamardGenusOneFactor_pair_cancellation α w₀ hα]
  unfold centeredHadamardOrbitBlock
  field_simp [hα, hden]

theorem logDeriv_centeredHadamardOrbitBlock (w₀ α w : ℂ)
    (hden : α ^ 2 - w₀ ^ 2 ≠ 0) (hw : w ^ 2 ≠ α ^ 2) :
    logDeriv (fun z : ℂ => centeredHadamardOrbitBlock w₀ α z) w =
      2 * w / (w ^ 2 - α ^ 2) := by
  unfold centeredHadamardOrbitBlock
  rw [logDeriv_apply]
  have hderiv :
      deriv (fun z : ℂ => (α ^ 2 - z ^ 2) / (α ^ 2 - w₀ ^ 2)) w =
        (-2 * w) / (α ^ 2 - w₀ ^ 2) := by
    simp
  rw [hderiv]
  have hden' : w ^ 2 - α ^ 2 ≠ 0 := sub_ne_zero.mpr hw
  have hden'' : α ^ 2 - w ^ 2 ≠ 0 := sub_ne_zero.mpr hw.symm
  field_simp [hden, hden', hden'']
  ring

/-- Finite product of centered zero-orbit blocks. -/
noncomputable def finiteCenteredHadamardOrbitProduct (w₀ : ℂ) (A : Finset ℂ) (w : ℂ) : ℂ :=
  ∏ α ∈ A, centeredHadamardOrbitBlock w₀ α w

/-- Finite logarithmic-derivative contribution of centered zero-orbit blocks. -/
noncomputable def finiteCenteredHadamardOrbitLogDerivSum (A : Finset ℂ) (w : ℂ) : ℂ :=
  ∑ α ∈ A, 2 * w / (w ^ 2 - α ^ 2)

/-- The standard genus-one zero contribution in the Hadamard logarithmic derivative. -/
noncomputable def genusOneZeroLogTerm (ρ s : ℂ) : ℂ :=
  1 / ρ + 1 / (s - ρ)

/-- A standard Hadamard zero sum, indexed by a supplied zero enumeration. -/
noncomputable def genusOneZeroLogSum {ι : Type*} (zero : ι → ℂ) (s : ℂ) : ℂ :=
  ∑' i : ι, genusOneZeroLogTerm (zero i) s

/-- The centered zero-orbit contribution after writing `w = s - 1/2`. -/
noncomputable def centeredHadamardOrbitLogTerm (α s : ℂ) : ℂ :=
  let w := s - (1 / 2 : ℂ)
  2 * w / (w ^ 2 - α ^ 2)

/-- A centered zero-orbit Hadamard sum, indexed by a supplied orbit representative map. -/
noncomputable def centeredHadamardOrbitLogSum {ι : Type*} (orbit : ι → ℂ) (s : ℂ) : ℂ :=
  ∑' i : ι, centeredHadamardOrbitLogTerm (orbit i) s

/-- Finite Hadamard-orbit calculation before any infinite product limit is needed. -/
theorem logDeriv_finiteCenteredHadamardOrbitProduct (w₀ w : ℂ) (A : Finset ℂ)
    (hden : ∀ α ∈ A, α ^ 2 - w₀ ^ 2 ≠ 0)
    (hw : ∀ α ∈ A, w ^ 2 ≠ α ^ 2) :
    logDeriv (fun z : ℂ => finiteCenteredHadamardOrbitProduct w₀ A z) w =
      finiteCenteredHadamardOrbitLogDerivSum A w := by
  classical
  unfold finiteCenteredHadamardOrbitProduct finiteCenteredHadamardOrbitLogDerivSum
  rw [logDeriv_prod]
  · exact Finset.sum_congr rfl fun α hα =>
      logDeriv_centeredHadamardOrbitBlock w₀ α w (hden α hα) (hw α hα)
  · exact fun α hα => centeredHadamardOrbitBlock_ne_zero (hden α hα) (hw α hα)
  · intro α hα
    unfold centeredHadamardOrbitBlock
    fun_prop

/-- The pole factor in the completed zeta function. -/
noncomputable def zetaPoleFactor (s : ℂ) : ℂ :=
  s - 1

/-- The archimedean exponential factor `π^{-s/2}`, written as an exponential
to expose its logarithmic derivative directly. -/
noncomputable def zetaPiFactor (s : ℂ) : ℂ :=
  Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))

/-- The gamma factor in the Kadiri normalization of the completed zeta function. -/
noncomputable def zetaGammaFactor (s : ℂ) : ℂ :=
  Gamma (s / 2 + 1)

/-- The Kadiri normalization of the completed zeta factor:
`(s - 1) π^{-s/2} Γ(s/2+1) ζ(s)`. -/
noncomputable def completedZetaFactor (s : ℂ) : ℂ :=
  zetaPoleFactor s * zetaPiFactor s * zetaGammaFactor s * riemannZeta s

theorem logDeriv_zetaPoleFactor (s : ℂ) :
    logDeriv zetaPoleFactor s = 1 / (s - 1) := by
  unfold zetaPoleFactor
  rw [logDeriv_apply]
  simp

theorem logDeriv_zetaPiFactor (s : ℂ) :
    logDeriv zetaPiFactor s = -(1 / 2 : ℂ) * Real.log Real.pi := by
  unfold zetaPiFactor
  rw [show (fun s : ℂ => Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))) =
      Complex.exp ∘ (fun s : ℂ => -(s / 2) * (Real.log Real.pi : ℂ)) by rfl]
  rw [logDeriv_comp]
  · simp
  · fun_prop
  · fun_prop

theorem logDeriv_zetaGammaFactor (s : ℂ)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    logDeriv zetaGammaFactor s = (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
  unfold zetaGammaFactor
  rw [show (fun s : ℂ => Gamma (s / 2 + 1)) =
      Gamma ∘ (fun s : ℂ => s / 2 + 1) by rfl]
  rw [logDeriv_comp]
  · simp [digamma_def]
    ring
  · exact differentiableAt_Gamma _ hΓdiff
  · fun_prop

theorem logDeriv_completedZetaFactor (s : ℂ)
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hζ : riemannZeta s ≠ 0) :
    logDeriv completedZetaFactor s =
      1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1)
      + deriv riemannZeta s / riemannZeta s := by
  have hpole : zetaPoleFactor s ≠ 0 := by
    simp [zetaPoleFactor, sub_ne_zero, hs1]
  have hpi : zetaPiFactor s ≠ 0 := by
    simp [zetaPiFactor]
  have hpole_diff : DifferentiableAt ℂ zetaPoleFactor s := by
    unfold zetaPoleFactor
    fun_prop
  have hpi_diff : DifferentiableAt ℂ zetaPiFactor s := by
    unfold zetaPiFactor
    fun_prop
  have hgamma_diff : DifferentiableAt ℂ zetaGammaFactor s := by
    unfold zetaGammaFactor
    exact (differentiableAt_Gamma _ hΓdiff).comp s (by fun_prop)
  have hzeta_diff : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs1
  unfold completedZetaFactor
  rw [logDeriv_mul]
  · rw [logDeriv_mul]
    · rw [logDeriv_mul]
      · rw [logDeriv_zetaPoleFactor, logDeriv_zetaPiFactor,
          logDeriv_zetaGammaFactor s hΓdiff, logDeriv_apply]
        ring
      · exact hpole
      · exact hpi
      · exact hpole_diff
      · exact hpi_diff
    · exact mul_ne_zero hpole hpi
    · exact hΓ
    · exact hpole_diff.mul hpi_diff
    · exact hgamma_diff
  · exact mul_ne_zero (mul_ne_zero hpole hpi) hΓ
  · exact hζ
  · exact (hpole_diff.mul hpi_diff).mul hgamma_diff
  · exact hzeta_diff

/-- Kadiri-facing algebraic bridge from the completed zeta factor to `-ζ'/ζ`. -/
theorem neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv
    (s : ℂ)
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hζ : riemannZeta s ≠ 0) :
    -deriv riemannZeta s / riemannZeta s =
      -logDeriv completedZetaFactor s
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
  rw [logDeriv_completedZetaFactor s hs1 hΓdiff hΓ hζ]
  ring

private lemma zetaPiFactor_eq_cpow (s : ℂ) :
    zetaPiFactor s = (Real.pi : ℂ) ^ (-(s / 2)) := by
  unfold zetaPiFactor
  rw [Complex.cpow_def_of_ne_zero, Complex.ofReal_log Real.pi_pos.le]
  · ring_nf
  · exact_mod_cast Real.pi_ne_zero

private lemma completedZetaFactor_eq_mul_completedRiemannZeta {s : ℂ}
    (hs0 : s ≠ 0) (hΓhalf : Gamma (s / 2) ≠ 0) :
    completedZetaFactor s = (s * (s - 1) / 2) * completedRiemannZeta s := by
  have hGamma :
      Gamma (s / 2 + 1) = (s / 2) * Gamma (s / 2) := by
    exact Gamma_add_one (s / 2) (div_ne_zero hs0 two_ne_zero)
  rw [completedZetaFactor, zetaPoleFactor, zetaGammaFactor, zetaPiFactor_eq_cpow,
    hGamma, riemannZeta_def_of_ne_zero hs0, Gammaℝ_def]
  field_simp [hs0, hΓhalf]

private lemma gamma_half_avoid_neg_nat_of_shift {s : ℂ} (hs0 : s ≠ 0)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    ∀ m : ℕ, s / 2 ≠ -m := by
  intro m hm
  cases m with
  | zero =>
      apply hs0
      rw [show s = 2 * (s / 2) by ring, hm]
      ring
  | succ m =>
      have hbad : s / 2 + 1 = -(m : ℂ) := by
        rw [hm]
        norm_num
      exact hΓdiff m hbad

private lemma gamma_half_ne_zero_of_shift {s : ℂ} (hs0 : s ≠ 0)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    Gamma (s / 2) ≠ 0 :=
  Gamma_ne_zero (gamma_half_avoid_neg_nat_of_shift hs0 hΓdiff)

private theorem completedZetaFactor_one_sub {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΓhalf : Gamma (s / 2) ≠ 0) (hΓhalf_ref : Gamma ((1 - s) / 2) ≠ 0) :
    completedZetaFactor (1 - s) = completedZetaFactor s := by
  have h1s0 : 1 - s ≠ 0 := by
    intro h
    apply hs1
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 := by rw [h]; ring
  rw [completedZetaFactor_eq_mul_completedRiemannZeta h1s0 hΓhalf_ref,
    completedZetaFactor_eq_mul_completedRiemannZeta hs0 hΓhalf, completedRiemannZeta_one_sub]
  ring

private lemma differentiableAt_completedZetaFactor {s : ℂ}
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    DifferentiableAt ℂ completedZetaFactor s := by
  unfold completedZetaFactor zetaPoleFactor zetaPiFactor zetaGammaFactor
  exact (((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s - 1) s).mul
      (by
        rw [show (fun s : ℂ => Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))) =
          Complex.exp ∘ (fun s : ℂ => -(s / 2) * (Real.log Real.pi : ℂ)) by rfl]
        exact Complex.differentiableAt_exp.comp s (by fun_prop))).mul
      ((differentiableAt_Gamma _ hΓdiff).comp s (by fun_prop))).mul
    (differentiableAt_riemannZeta hs1)

private theorem logDeriv_completedZetaFactor_one_sub {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΓdiff_s : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓdiff_ref : ∀ m : ℕ, (1 - s) / 2 + 1 ≠ -m) :
    logDeriv completedZetaFactor (1 - s) = -logDeriv completedZetaFactor s := by
  let R : ℂ → ℂ := fun z => 1 - z
  have hΓhalf_s : Gamma (s / 2) ≠ 0 :=
    gamma_half_ne_zero_of_shift hs0 hΓdiff_s
  have hΓhalf_ref_s : Gamma ((1 - s) / 2) ≠ 0 :=
    gamma_half_ne_zero_of_shift (by
      intro h
      apply hs1
      calc
        s = 1 - (1 - s) := by ring
        _ = 1 := by rw [h]; ring) hΓdiff_ref
  have hΓhalf_near : ∀ᶠ z in 𝓝 s, Gamma (z / 2) ≠ 0 := by
    have hdiff : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2)) s :=
      (differentiableAt_Gamma _ (gamma_half_avoid_neg_nat_of_shift hs0 hΓdiff_s)).comp
        s (by fun_prop)
    have hcont : ContinuousAt (fun z : ℂ => Gamma (z / 2)) s := hdiff.continuousAt
    exact (hcont.ne_iff_eventually_ne continuousAt_const).mp hΓhalf_s
  have hΓhalf_ref_near : ∀ᶠ z in 𝓝 s, Gamma ((1 - z) / 2) ≠ 0 := by
    have hdiff : DifferentiableAt ℂ (fun z : ℂ => Gamma ((1 - z) / 2)) s :=
      (differentiableAt_Gamma _ (gamma_half_avoid_neg_nat_of_shift (by
        intro h
        apply hs1
        calc
          s = 1 - (1 - s) := by ring
          _ = 1 := by rw [h]; ring) hΓdiff_ref)).comp s (by fun_prop)
    have hcont : ContinuousAt (fun z : ℂ => Gamma ((1 - z) / 2)) s := hdiff.continuousAt
    exact (hcont.ne_iff_eventually_ne continuousAt_const).mp hΓhalf_ref_s
  have hsym_near :
      (completedZetaFactor ∘ R) =ᶠ[𝓝 s] completedZetaFactor := by
    filter_upwards [isOpen_ne.mem_nhds hs0, isOpen_ne.mem_nhds hs1, hΓhalf_near,
      hΓhalf_ref_near] with z hz0 hz1 hΓz hΓrefz
    exact completedZetaFactor_one_sub hz0 hz1 hΓz hΓrefz
  have hcomp :
      logDeriv (completedZetaFactor ∘ R) s =
        logDeriv completedZetaFactor (R s) * deriv R s := by
    rw [logDeriv_comp]
    · exact differentiableAt_completedZetaFactor
        (by simpa [R] using sub_ne_zero.mpr hs0.symm) hΓdiff_ref
    · dsimp [R]
      fun_prop
  have hderivR : deriv R s = -1 := by
    dsimp [R]
    simp
  have hlog_eq :
      logDeriv (completedZetaFactor ∘ R) s = logDeriv completedZetaFactor s := by
    rw [logDeriv_apply, logDeriv_apply]
    rw [Filter.EventuallyEq.deriv_eq hsym_near]
    exact congrArg (fun z => deriv completedZetaFactor s / z) hsym_near.eq_of_nhds
  rw [hcomp, hderivR] at hlog_eq
  calc
    logDeriv completedZetaFactor (1 - s)
        = -(logDeriv completedZetaFactor (R s) * -1) := by simp [R]
    _ = -logDeriv completedZetaFactor s := by rw [hlog_eq]

private theorem neg_logDeriv_zeta_left_eq_reflected {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hζz : riemannZeta z ≠ 0)
    (hζref : riemannZeta (1 - z) ≠ 0)
    (hΓz_diff : ∀ m : ℕ, z / 2 + 1 ≠ -m)
    (hΓref_diff : ∀ m : ℕ, (1 - z) / 2 + 1 ≠ -m)
    (hΓz : zetaGammaFactor z ≠ 0)
    (hΓref : zetaGammaFactor (1 - z) ≠ 0) :
    -deriv riemannZeta z / riemannZeta z =
      deriv riemannZeta (1 - z) / riemannZeta (1 - z)
        + 1 / (z - 1) + 1 / ((1 - z) - 1)
        - (Real.log Real.pi : ℂ)
        + (1 / 2 : ℂ) * digamma (z / 2 + 1)
        + (1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1) := by
  have href1 : 1 - z ≠ 1 := by
    intro h
    apply hz0
    calc
      z = 1 - (1 - z) := by ring
      _ = 0 := by rw [h]; ring
  have hleft := neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv z hz1 hΓz_diff hΓz hζz
  have hright := neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv (1 - z) href1
    hΓref_diff hΓref hζref
  have htransport := logDeriv_completedZetaFactor_one_sub hz0 hz1 hΓz_diff hΓref_diff
  have hnegLD :
      -logDeriv completedZetaFactor z =
        deriv riemannZeta (1 - z) / riemannZeta (1 - z)
          + 1 / ((1 - z) - 1)
          - (1 / 2 : ℂ) * Real.log Real.pi
          + (1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1) := by
    rw [htransport] at hright
    have hright' := congrArg Neg.neg hright
    ring_nf at hright' ⊢
    rw [hright']
    ring
  rw [hleft, hnegLD]
  ring

private lemma zetaGammaFactor_shift_avoid_of_not_zero {s : ℂ}
    (hsZ : s ∉ riemannZeta.zeroes) :
    ∀ m : ℕ, s / 2 + 1 ≠ -m := by
  intro m hm
  apply hsZ
  have hs_eq : s = -2 * ((m : ℂ) + 1) := by
    calc
      s = 2 * (s / 2 + 1) - 2 := by ring
      _ = 2 * (-(m : ℂ)) - 2 := by rw [hm]
      _ = -2 * ((m : ℂ) + 1) := by ring
  rw [riemannZeta.zeroes]
  simpa [hs_eq, Nat.cast_add, Nat.cast_one] using
    riemannZeta_neg_two_mul_nat_add_one m

private theorem functional_eq_correct_sign {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hζs : riemannZeta s ≠ 0)
    (hζref : riemannZeta (1 - s) ≠ 0)
    (hΓs_diff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓref_diff : ∀ m : ℕ, (1 - s) / 2 + 1 ≠ -m) :
    -deriv riemannZeta s / riemannZeta s =
      ((-Real.log Real.pi : ℝ) : ℂ)
      + deriv riemannZeta (1 - s) / riemannZeta (1 - s)
      + (1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2)) := by
  have h1s0 : (1 : ℂ) - s ≠ 0 := by
    intro h
    apply hs1
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 := by rw [h]; ring
  have hΓs : zetaGammaFactor s ≠ 0 := by
    unfold zetaGammaFactor
    exact Gamma_ne_zero hΓs_diff
  have hΓref : zetaGammaFactor (1 - s) ≠ 0 := by
    unfold zetaGammaFactor
    exact Gamma_ne_zero hΓref_diff
  have hFE := neg_logDeriv_zeta_left_eq_reflected hs0 hs1 hζs hζref
    hΓs_diff hΓref_diff hΓs hΓref
  have hψs : digamma (s / 2 + 1) = digamma (s / 2) + (s / 2)⁻¹ :=
    digamma_apply_add_one _ (gamma_half_avoid_neg_nat_of_shift hs0 hΓs_diff)
  have hψref : digamma ((1 - s) / 2 + 1) = digamma ((1 - s) / 2) + ((1 - s) / 2)⁻¹ :=
    digamma_apply_add_one _ (gamma_half_avoid_neg_nat_of_shift h1s0 hΓref_diff)
  have hcancel :
      1 / (s - 1) + 1 / (1 - s - 1)
        + (1 / 2 : ℂ) * (s / 2)⁻¹ + (1 / 2 : ℂ) * ((1 - s) / 2)⁻¹ = 0 := by
    have hs_sub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [show (1 : ℂ) - s - 1 = -s by ring]
    field_simp [hs0, hs_sub]
    ring_nf
  rw [hFE, hψs, hψref, Complex.ofReal_neg]
  linear_combination hcancel

theorem zeta_logDeriv_functional_eq {s : ℂ}
    (hs1 : s ≠ 1) (hs0 : s ≠ 0)
    (hζs : riemannZeta s ≠ 0)
    (hζ1s : riemannZeta (1 - s) ≠ 0) :
    -deriv riemannZeta s / riemannZeta s =
      ((-Real.log Real.pi : ℝ) : ℂ)
      + deriv riemannZeta (1 - s) / riemannZeta (1 - s)
      + (1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2)) := by
  exact functional_eq_correct_sign hs0 hs1 hζs hζ1s
    (zetaGammaFactor_shift_avoid_of_not_zero
      (by simpa [riemannZeta.zeroes] using hζs))
    (zetaGammaFactor_shift_avoid_of_not_zero
      (by simpa [riemannZeta.zeroes] using hζ1s))

/-- Kadiri-facing bridge after a Hadamard log-derivative formula has been supplied. -/
theorem neg_zeta_logDeriv_eq_of_completed_hadamard_logDeriv
    (s B Z : ℂ)
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hζ : riemannZeta s ≠ 0)
    (hHad : logDeriv completedZetaFactor s = B + Z) :
    -deriv riemannZeta s / riemannZeta s =
      -B - Z
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
  rw [neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv s hs1 hΓdiff hΓ hζ, hHad]
  ring

/--
Assuming a Hadamard logarithmic-derivative formula for the completed zeta factor,
recover the classical explicit expression for `-ζ'/ζ` in terms of the Hadamard
zero sum.
-/
theorem neg_zeta_logDeriv_eq_of_genusOne_hadamard
    {ι : Type*} (zero : ι → ℂ) (s B : ℂ)
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hζ : riemannZeta s ≠ 0)
    (hHad : logDeriv completedZetaFactor s = B + genusOneZeroLogSum zero s) :
    -deriv riemannZeta s / riemannZeta s =
      -B - genusOneZeroLogSum zero s
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1) :=
  neg_zeta_logDeriv_eq_of_completed_hadamard_logDeriv s B (genusOneZeroLogSum zero s)
    hs1 hΓdiff hΓ hζ hHad

/--
Assuming a centered zero-orbit Hadamard logarithmic-derivative formula for the
completed zeta factor, recover the corresponding explicit expression for
`-ζ'/ζ`.
-/
theorem neg_zeta_logDeriv_eq_of_centered_orbit_hadamard
    {ι : Type*} (orbit : ι → ℂ) (s B : ℂ)
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hζ : riemannZeta s ≠ 0)
    (hHad : logDeriv completedZetaFactor s = B + centeredHadamardOrbitLogSum orbit s) :
    -deriv riemannZeta s / riemannZeta s =
      -B - centeredHadamardOrbitLogSum orbit s
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1) :=
  neg_zeta_logDeriv_eq_of_completed_hadamard_logDeriv s B (centeredHadamardOrbitLogSum orbit s)
    hs1 hΓdiff hΓ hζ hHad

end Kadiri
