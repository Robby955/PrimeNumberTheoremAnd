import PrimeNumberTheoremAnd.RectangleArgumentPrinciple
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.CompletedXi

/-!
# Riemann xi rectangle count

This file specializes the rectangle logarithmic-derivative identity to Riemann's
entire xi function.  The later Riemann-von-Mangoldt main-term extraction needs
phase-level Stirling estimates for `Complex.Gamma`; this file records the
divisor-counting layer that sits below that extraction.

The next analytic brick is a principal-log Stirling estimate at
`z = 1 / 4 + (T / 2) * I`.  The local Gamma API currently has norm growth
bounds and the `logGammaSeq`/digamma construction, but not a reusable theorem
of the following shape:

`| (Complex.log (Complex.Gamma z)).im -
    ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8
      + (T / 4) * Real.log (1 + 1 / (4 * T ^ 2))
      + (1 / 4) * Real.arctan (1 / (2 * T))) | ≤ 1 / (3 * T)`.
-/

open Complex Set BigOperators

noncomputable section

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
