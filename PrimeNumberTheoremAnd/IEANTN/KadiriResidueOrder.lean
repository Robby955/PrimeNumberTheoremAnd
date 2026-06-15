import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Meromorphic.Order

/-!
# Single-pole residue order lemmas for Kadiri eq. 12

This file isolates the single-pole order-m residue step needed for the eq. 12
rectangle decomposition.  It does not modify the eq. 12 theorem.
-/

open Complex Topology Filter Asymptotics
open Set

open scoped Interval

noncomputable section

namespace Kadiri

private theorem logDeriv_zpow_sub (p s : ℂ) (m : ℤ) :
    logDeriv (fun z : ℂ ↦ (z - p) ^ m) s = (m : ℂ) / (s - p) := by
  rw [logDeriv_fun_zpow (by fun_prop)]
  simp [logDeriv_apply, div_eq_mul_inv]

private theorem logDeriv_principal_part_of_factorization
    {g Phi u : ℂ → ℂ} {p : ℂ} {m : ℤ}
    (hu : AnalyticAt ℂ u p) (hu_ne : u p ≠ 0)
    (hfactor : g =ᶠ[𝓝[≠] p] fun s ↦ (s - p) ^ m * u s)
    (hPhi : AnalyticAt ℂ Phi p) :
    ((fun s ↦ logDeriv g s * Phi s) -
        (fun s ↦ ((m : ℂ) * Phi p) / (s - p))) =O[𝓝[≠] p]
      (1 : ℂ → ℂ) := by
  have hu_ne_eventually : ∀ᶠ s in 𝓝[≠] p, u s ≠ 0 :=
    (hu.continuousAt.eventually_ne hu_ne).filter_mono nhdsWithin_le_nhds
  have hu_analytic_eventually : ∀ᶠ s in 𝓝[≠] p, AnalyticAt ℂ u s :=
    hu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hlog_to_prod :
      logDeriv g =ᶠ[𝓝[≠] p]
        logDeriv (fun s ↦ (s - p) ^ m * u s) := by
    rw [show logDeriv g = fun s ↦ deriv g s / g s by rfl]
    rw [show logDeriv (fun s ↦ (s - p) ^ m * u s) =
      fun s ↦ deriv (fun s ↦ (s - p) ^ m * u s) s / ((s - p) ^ m * u s) by rfl]
    exact hfactor.nhdsNE_deriv.div hfactor
  have hsplit :
      logDeriv (fun s ↦ (s - p) ^ m * u s) =ᶠ[𝓝[≠] p]
        fun s ↦ (m : ℂ) / (s - p) + logDeriv u s := by
    filter_upwards [self_mem_nhdsWithin, hu_ne_eventually, hu_analytic_eventually]
      with s hs hune hs_an
    have hs_ne : s ≠ p := hs
    have hpow_ne : (s - p) ^ m ≠ 0 := zpow_ne_zero _ (sub_ne_zero.mpr hs_ne)
    have hpow_diff : DifferentiableAt ℂ (fun z : ℂ ↦ (z - p) ^ m) s :=
      ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ ↦ z - p) s).zpow
        (Or.inl (sub_ne_zero.mpr hs_ne)))
    rw [logDeriv_mul s hpow_ne hune hpow_diff hs_an.differentiableAt]
    rw [logDeriv_zpow_sub]
  have hlog :
      logDeriv g =ᶠ[𝓝[≠] p] fun s ↦ (m : ℂ) / (s - p) + logDeriv u s :=
    hlog_to_prod.trans hsplit
  have htarget :
      ((fun s ↦ logDeriv g s * Phi s) -
          (fun s ↦ ((m : ℂ) * Phi p) / (s - p))) =ᶠ[𝓝[≠] p]
        fun s ↦ (m : ℂ) * ((Phi s - Phi p) / (s - p)) + logDeriv u s * Phi s := by
    filter_upwards [self_mem_nhdsWithin, hlog] with s hs hlogs
    have hs_ne : s ≠ p := hs
    calc
      logDeriv g s * Phi s - ((m : ℂ) * Phi p) / (s - p)
          = (((m : ℂ) / (s - p) + logDeriv u s) * Phi s -
              ((m : ℂ) * Phi p) / (s - p)) := by rw [hlogs]
      _ = (m : ℂ) * ((Phi s - Phi p) / (s - p)) + logDeriv u s * Phi s := by
          field_simp [sub_ne_zero.mpr hs_ne]
          ring
  have hPhiSlope :
      (fun s ↦ (Phi s - Phi p) / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    have ht : Tendsto (slope Phi p) (𝓝[≠] p) (𝓝 (deriv Phi p)) :=
      hPhi.differentiableAt.hasDerivAt.tendsto_slope
    have hbig : (slope Phi p) =O[𝓝[≠] p] (1 : ℂ → ℂ) := ht.isBigO_one ℂ
    simpa [slope, div_eq_inv_mul, sub_eq_add_neg] using hbig
  have hloguPhi : (fun s ↦ logDeriv u s * Phi s) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    have hlogu_cont : ContinuousAt (logDeriv u) p := by
      rw [show logDeriv u = fun z ↦ deriv u z / u z by rfl]
      exact (hu.deriv.continuousAt.div hu.continuousAt hu_ne)
    have ht : Tendsto (fun s ↦ logDeriv u s * Phi s) (𝓝[≠] p)
        (𝓝 (logDeriv u p * Phi p)) := by
      exact (hlogu_cont.tendsto.mul hPhi.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    exact ht.isBigO_one ℂ
  exact htarget.trans_isBigO ((hPhiSlope.const_mul_left (m : ℂ)).add hloguPhi)

/--
Rectangle residue evaluation from an explicit order-`m` logarithmic-derivative
principal part.

The hypothesis `hprincipal` is the local analytic input: after subtracting
`m * Phi p / (s - p)`, the integrand is bounded near the puncture.  The
existing rectangle machinery then evaluates the rectangle integral.
-/
theorem kadiri_logDeriv_residue_order_principal_part_rectangleIntegral
    {g Phi : ℂ → ℂ} {z w p : ℂ} {m : ℤ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p)
    (horder : meromorphicOrderAt g p = ((m : ℤ) : WithTop ℤ))
    (hHolo : HolomorphicOn (fun s ↦ logDeriv g s * Phi s) (Rectangle z w \ {p}))
    (hprincipal :
      ((fun s ↦ logDeriv g s * Phi s) -
          (fun s ↦ ((m : ℂ) * Phi p) / (s - p))) =O[𝓝[≠] p]
        (1 : ℂ → ℂ)) :
    RectangleIntegral' (fun s ↦ logDeriv g s * Phi s) z w =
      (m : ℂ) * Phi p := by
  have _ := horder
  exact ResidueTheoremOnRectangleWithSimplePole'
    zRe_le_wRe zIm_le_wIm pInRectInterior hHolo hprincipal

/--
Rectangle residue evaluation from a finite-order meromorphic factorization.

The `meromorphicOrderAt` hypothesis supplies the local factorization
`g(s) = (s - p)^m u(s)` with analytic nonvanishing `u`.  The proof turns that
factorization into the bounded principal-part condition consumed by
`ResidueTheoremOnRectangleWithSimplePole'`.
-/
theorem kadiri_logDeriv_residue_order_rectangleIntegral
    {g Phi : ℂ → ℂ} {z w p : ℂ} {m : ℤ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p)
    (hMer : MeromorphicAt g p)
    (horder : meromorphicOrderAt g p = ((m : ℤ) : WithTop ℤ))
    (hPhi : AnalyticAt ℂ Phi p)
    (hHolo : HolomorphicOn (fun s ↦ logDeriv g s * Phi s) (Rectangle z w \ {p})) :
    RectangleIntegral' (fun s ↦ logDeriv g s * Phi s) z w =
      (m : ℂ) * Phi p := by
  obtain ⟨u, hu, hu_ne, hfactor_smul⟩ := (meromorphicOrderAt_eq_int_iff hMer).1 horder
  have hfactor : g =ᶠ[𝓝[≠] p] fun s ↦ (s - p) ^ m * u s := by
    simpa using hfactor_smul
  exact kadiri_logDeriv_residue_order_principal_part_rectangleIntegral
    zRe_le_wRe zIm_le_wIm pInRectInterior horder hHolo
    (logDeriv_principal_part_of_factorization hu hu_ne hfactor hPhi)

/--
Sign-correct residue evaluation for the Kadiri integrand with `-logDeriv`.

At a zero of order `m`, `logDeriv g` has residue `m`, hence `-logDeriv g` has
residue `-m`.
-/
theorem kadiri_negLogDeriv_residue_order_principal_part_rectangleIntegral
    {g Phi : ℂ → ℂ} {z w p : ℂ} {m : ℤ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p)
    (horder : meromorphicOrderAt g p = ((m : ℤ) : WithTop ℤ))
    (hHolo : HolomorphicOn (fun s ↦ (-logDeriv g s) * Phi s) (Rectangle z w \ {p}))
    (hprincipal :
      ((fun s ↦ (-logDeriv g s) * Phi s) -
          (fun s ↦ (-((m : ℂ) * Phi p)) / (s - p))) =O[𝓝[≠] p]
        (1 : ℂ → ℂ)) :
    RectangleIntegral' (fun s ↦ (-logDeriv g s) * Phi s) z w =
      -((m : ℂ) * Phi p) := by
  have _ := horder
  exact ResidueTheoremOnRectangleWithSimplePole'
    zRe_le_wRe zIm_le_wIm pInRectInterior hHolo hprincipal

/--
Sign-correct rectangle residue evaluation for `-logDeriv` from finite
meromorphic order.
-/
theorem kadiri_negLogDeriv_residue_order_rectangleIntegral
    {g Phi : ℂ → ℂ} {z w p : ℂ} {m : ℤ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p)
    (hMer : MeromorphicAt g p)
    (horder : meromorphicOrderAt g p = ((m : ℤ) : WithTop ℤ))
    (hPhi : AnalyticAt ℂ Phi p)
    (hHolo : HolomorphicOn (fun s ↦ (-logDeriv g s) * Phi s) (Rectangle z w \ {p})) :
    RectangleIntegral' (fun s ↦ (-logDeriv g s) * Phi s) z w =
      -((m : ℂ) * Phi p) := by
  obtain ⟨u, hu, hu_ne, hfactor_smul⟩ := (meromorphicOrderAt_eq_int_iff hMer).1 horder
  have hfactor : g =ᶠ[𝓝[≠] p] fun s ↦ (s - p) ^ m * u s := by
    simpa using hfactor_smul
  have hprincipal_pos :
      ((fun s ↦ logDeriv g s * Phi s) -
          (fun s ↦ ((m : ℂ) * Phi p) / (s - p))) =O[𝓝[≠] p]
        (1 : ℂ → ℂ) :=
    logDeriv_principal_part_of_factorization hu hu_ne hfactor hPhi
  have hprincipal_neg :
      ((fun s ↦ (-logDeriv g s) * Phi s) -
          (fun s ↦ (-((m : ℂ) * Phi p)) / (s - p))) =O[𝓝[≠] p]
        (1 : ℂ → ℂ) := by
    have htarget :
        ((fun s ↦ (-logDeriv g s) * Phi s) -
            (fun s ↦ (-((m : ℂ) * Phi p)) / (s - p))) =ᶠ[𝓝[≠] p]
          fun s ↦ (-1 : ℂ) *
            (((fun s ↦ logDeriv g s * Phi s) -
                (fun s ↦ ((m : ℂ) * Phi p) / (s - p))) s) := by
      filter_upwards with s
      change -logDeriv g s * Phi s - (-(↑m * Phi p) / (s - p)) =
        (-1 : ℂ) * (logDeriv g s * Phi s - (↑m * Phi p) / (s - p))
      ring
    exact htarget.trans_isBigO (hprincipal_pos.const_mul_left (-1 : ℂ))
  exact kadiri_negLogDeriv_residue_order_principal_part_rectangleIntegral
    zRe_le_wRe zIm_le_wIm pInRectInterior horder hHolo hprincipal_neg

private lemma riemannZeta_meromorphicOrderAt_eq_order_of_nontrivialZero
    (rho : NontrivialZeros) :
    meromorphicOrderAt riemannZeta (rho : ℂ) =
      ((riemannZeta.order (rho : ℂ) : ℤ) : WithTop ℤ) := by
  have hfinite := riemannZeta_meromorphicOrderAt_ne_top_nontrivialZero rho
  unfold riemannZeta.order
  cases h : meromorphicOrderAt riemannZeta (rho : ℂ) with
  | top =>
      exact (hfinite h).elim
  | coe n =>
      simp

/--
Kadiri-facing zeta corollary at a nontrivial zero.

This is the sign-correct local contribution for the Kadiri integrand
`(-ζ'/ζ)(s) * Phi(-s)` at a nontrivial zero.
-/
theorem kadiri_riemannZeta_negLogDeriv_residue_order_rectangleIntegral
    {Phi : ℂ → ℂ} {z w : ℂ} (rho : NontrivialZeros)
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 (rho : ℂ))
    (hPhi : AnalyticAt ℂ Phi (-(rho : ℂ)))
    (hHolo :
      HolomorphicOn
        (fun s ↦ (-logDeriv riemannZeta s) * Phi (-s))
        (Rectangle z w \ {(rho : ℂ)})) :
    RectangleIntegral' (fun s ↦ (-logDeriv riemannZeta s) * Phi (-s)) z w =
      -((riemannZeta.order (rho : ℂ) : ℂ) * Phi (-(rho : ℂ))) := by
  have hPhi_comp : AnalyticAt ℂ (fun s : ℂ ↦ Phi (-s)) (rho : ℂ) := by
    have hneg : AnalyticAt ℂ (fun s : ℂ ↦ -s) (rho : ℂ) := by
      simpa [Pi.neg_def] using
        ((analyticAt_id (𝕜 := ℂ) (z := (rho : ℂ))) :
          AnalyticAt ℂ (fun s : ℂ ↦ s) (rho : ℂ)).neg
    simpa [Function.comp_def] using hPhi.comp hneg
  exact kadiri_negLogDeriv_residue_order_rectangleIntegral
    (g := riemannZeta)
    (Phi := fun s ↦ Phi (-s))
    (z := z) (w := w) (p := (rho : ℂ))
    (m := riemannZeta.order (rho : ℂ))
    zRe_le_wRe zIm_le_wIm pInRectInterior
    (riemannZeta_analyticAt_nontrivialZero rho).meromorphicAt
    (riemannZeta_meromorphicOrderAt_eq_order_of_nontrivialZero rho)
    hPhi_comp hHolo

end Kadiri
