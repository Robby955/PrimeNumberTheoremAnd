import PrimeNumberTheoremAnd.RectangleArgumentPrinciple
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.CompletedXi
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.PhaseBounds
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
