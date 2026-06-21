import PrimeNumberTheoremAnd.RectangleArgumentPrinciple
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.CompletedXi
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
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
