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
The logarithmic derivative of a meromorphic function with finite local order is
meromorphic at that point.
-/
theorem kadiri_logDeriv_meromorphicAt_of_order
    {g : ℂ → ℂ} {p : ℂ} {m : ℤ}
    (hMer : MeromorphicAt g p)
    (horder : meromorphicOrderAt g p = ((m : ℤ) : WithTop ℤ)) :
    MeromorphicAt (logDeriv g) p := by
  obtain ⟨u, hu, hu_ne, hfactor_smul⟩ := (meromorphicOrderAt_eq_int_iff hMer).1 horder
  have hfactor : g =ᶠ[𝓝[≠] p] fun s ↦ (s - p) ^ m * u s := by
    simpa using hfactor_smul
  let model : ℂ → ℂ := fun s ↦ (m : ℂ) / (s - p) + logDeriv u s
  have hmodel : MeromorphicAt model p := by
    have hprincipal : MeromorphicAt (fun s : ℂ ↦ (m : ℂ) / (s - p)) p := by
      exact (analyticAt_const.meromorphicAt).div
        ((analyticAt_id.sub analyticAt_const).meromorphicAt)
    have hlogu : MeromorphicAt (logDeriv u) p := by
      rw [show logDeriv u = fun z ↦ deriv u z / u z by rfl]
      exact hu.deriv.meromorphicAt.div hu.meromorphicAt
    exact hprincipal.add hlogu
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
  exact hmodel.congr ((hlog_to_prod.trans hsplit).symm)

/--
The logarithmic derivative of a finite-order meromorphic germ has at worst a
simple pole.
-/
theorem kadiri_logDeriv_order_ge_neg_one_of_order
    {g : ℂ → ℂ} {p : ℂ} {m : ℤ}
    (hMer : MeromorphicAt g p)
    (horder : meromorphicOrderAt g p = ((m : ℤ) : WithTop ℤ)) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (logDeriv g) p := by
  obtain ⟨u, hu, hu_ne, hfactor_smul⟩ := (meromorphicOrderAt_eq_int_iff hMer).1 horder
  have hfactor : g =ᶠ[𝓝[≠] p] fun s ↦ (s - p) ^ m * u s := by
    simpa using hfactor_smul
  let principal : ℂ → ℂ := fun s ↦ (m : ℂ) / (s - p)
  let regular : ℂ → ℂ := logDeriv u
  let model : ℂ → ℂ := fun s ↦ principal s + regular s
  have hprincipal_mero : MeromorphicAt principal p := by
    exact (analyticAt_const.meromorphicAt).div
      ((analyticAt_id.sub analyticAt_const).meromorphicAt)
  have hprincipal_ge :
      ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt principal p := by
    by_cases hm : (m : ℂ) = 0
    · have hzero : principal = fun _ : ℂ ↦ 0 := by
        ext s
        simp [principal, hm]
      rw [hzero, meromorphicOrderAt_const]
      simp
    · rw [show principal = (fun _ : ℂ ↦ (m : ℂ)) / (fun s : ℂ ↦ s - p) by
        rfl]
      rw [meromorphicOrderAt_div
        (f := fun _ : ℂ ↦ (m : ℂ)) (g := fun s : ℂ ↦ s - p)
        (x := p) (analyticAt_const.meromorphicAt)
        ((analyticAt_id.sub analyticAt_const).meromorphicAt)]
      rw [meromorphicOrderAt_const, if_neg hm, meromorphicOrderAt_id_sub_const]
      norm_num
  have hregular_an : AnalyticAt ℂ regular p := by
    rw [show regular = fun z ↦ deriv u z / u z by rfl]
    exact hu.deriv.div hu hu_ne
  have hregular_ge : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt regular p := by
    exact le_trans
      (WithTop.coe_le_coe.mpr (by norm_num : (-1 : ℤ) ≤ 0))
      hregular_an.meromorphicOrderAt_nonneg
  have hmodel_ge : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt model p := by
    have hmin_ge :
        ((-1 : ℤ) : WithTop ℤ) ≤
          min (meromorphicOrderAt principal p) (meromorphicOrderAt regular p) :=
      le_min hprincipal_ge hregular_ge
    exact le_trans hmin_ge
      (meromorphicOrderAt_add hprincipal_mero hregular_an.meromorphicAt)
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
        fun s ↦ principal s + regular s := by
    filter_upwards [self_mem_nhdsWithin, hu_ne_eventually, hu_analytic_eventually]
      with s hs hune hs_an
    have hs_ne : s ≠ p := hs
    have hpow_ne : (s - p) ^ m ≠ 0 := zpow_ne_zero _ (sub_ne_zero.mpr hs_ne)
    have hpow_diff : DifferentiableAt ℂ (fun z : ℂ ↦ (z - p) ^ m) s :=
      ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ ↦ z - p) s).zpow
        (Or.inl (sub_ne_zero.mpr hs_ne)))
    rw [logDeriv_mul s hpow_ne hune hpow_diff hs_an.differentiableAt]
    rw [logDeriv_zpow_sub]
  rwa [meromorphicOrderAt_congr (hlog_to_prod.trans hsplit)]

/--
If `Phi` is analytic at the same point, then the Kadiri-style integrand
`(-logDeriv g) * Phi` is meromorphic there.
-/
theorem kadiri_negLogDeriv_mul_meromorphicAt_of_order
    {g Phi : ℂ → ℂ} {p : ℂ} {m : ℤ}
    (hMer : MeromorphicAt g p)
    (horder : meromorphicOrderAt g p = ((m : ℤ) : WithTop ℤ))
    (hPhi : AnalyticAt ℂ Phi p) :
    MeromorphicAt (fun s ↦ (-logDeriv g s) * Phi s) p := by
  have hlog : MeromorphicAt (logDeriv g) p :=
    kadiri_logDeriv_meromorphicAt_of_order hMer horder
  have hneg : MeromorphicAt (fun s ↦ -logDeriv g s) p := by
    have hconst : MeromorphicAt (fun _ : ℂ ↦ (-1 : ℂ)) p :=
      analyticAt_const.meromorphicAt
    have hprod : MeromorphicAt ((fun _ : ℂ ↦ (-1 : ℂ)) * logDeriv g) p :=
      hconst.mul hlog
    refine hprod.congr ?_
    filter_upwards with s
    simp [Pi.mul_apply]
  exact hneg.mul hPhi.meromorphicAt

/--
Multiplying by an analytic factor preserves the at-worst-simple-pole bound for
`-logDeriv`.
-/
theorem kadiri_negLogDeriv_mul_order_ge_neg_one_of_order
    {g Phi : ℂ → ℂ} {p : ℂ} {m : ℤ}
    (hMer : MeromorphicAt g p)
    (horder : meromorphicOrderAt g p = ((m : ℤ) : WithTop ℤ))
    (hPhi : AnalyticAt ℂ Phi p) :
    ((-1 : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun s ↦ (-logDeriv g s) * Phi s) p := by
  have hlog_ge : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (logDeriv g) p :=
    kadiri_logDeriv_order_ge_neg_one_of_order hMer horder
  have hneg_mero : MeromorphicAt (fun s ↦ -logDeriv g s) p := by
    have hlog : MeromorphicAt (logDeriv g) p :=
      kadiri_logDeriv_meromorphicAt_of_order hMer horder
    have hconst : MeromorphicAt (fun _ : ℂ ↦ (-1 : ℂ)) p :=
      analyticAt_const.meromorphicAt
    have hprod : MeromorphicAt ((fun _ : ℂ ↦ (-1 : ℂ)) * logDeriv g) p :=
      hconst.mul hlog
    refine hprod.congr ?_
    filter_upwards with s
    simp [Pi.mul_apply]
  have hneg_order :
      meromorphicOrderAt (fun s ↦ -logDeriv g s) p =
        meromorphicOrderAt (logDeriv g) p := by
    have hfun_neg :
        meromorphicOrderAt (fun s ↦ -logDeriv g s) p =
          meromorphicOrderAt (-(logDeriv g)) p := by
      apply meromorphicOrderAt_congr
      filter_upwards with s
      simp [Pi.neg_apply]
    rw [hfun_neg, ← meromorphicOrderAt_neg (f := logDeriv g) (x := p)]
  have hprod_order :
      meromorphicOrderAt (fun s ↦ (-logDeriv g s) * Phi s) p =
        meromorphicOrderAt (fun s ↦ -logDeriv g s) p +
          meromorphicOrderAt Phi p := by
    rw [show (fun s ↦ (-logDeriv g s) * Phi s) =
        (fun s ↦ -logDeriv g s) * Phi by rfl]
    exact meromorphicOrderAt_mul hneg_mero hPhi.meromorphicAt
  rw [hprod_order, hneg_order]
  have hsum := add_le_add hlog_ge hPhi.meromorphicOrderAt_nonneg
  simpa using hsum

/--
Away from `1` and the zeros of `ζ`, the Kadiri integrand is meromorphic
whenever `Phi` is analytic at the reflected point.
-/
theorem kadiri_riemannZeta_negLogDeriv_mul_meromorphicAt_of_ne_one_ne_zero
    {Phi : ℂ → ℂ} {z : ℂ}
    (hz_one : z ≠ 1)
    (hzeta : riemannZeta z ≠ 0)
    (hPhi : AnalyticAt ℂ Phi (-z)) :
    MeromorphicAt (fun s ↦ (-logDeriv riemannZeta s) * Phi (-s)) z := by
  have hzeta_an : AnalyticAt ℂ riemannZeta z := by
    exact riemannZeta_analyticOn_compl_one z
      (by simpa [Set.mem_compl_iff] using hz_one)
  have hlog : AnalyticAt ℂ (logDeriv riemannZeta) z := by
    rw [show logDeriv riemannZeta =
      fun s ↦ deriv riemannZeta s / riemannZeta s by rfl]
    exact hzeta_an.deriv.div hzeta_an hzeta
  have hPhi_comp : AnalyticAt ℂ (fun s : ℂ ↦ Phi (-s)) z := by
    have hneg : AnalyticAt ℂ (fun s : ℂ ↦ -s) z := by
      simpa [Pi.neg_def] using
        ((analyticAt_id (𝕜 := ℂ) (z := z)) :
          AnalyticAt ℂ (fun s : ℂ ↦ s) z).neg
    simpa [Function.comp_def] using hPhi.comp hneg
  have hneglog : MeromorphicAt (fun s ↦ -logDeriv riemannZeta s) z := by
    have hconst : MeromorphicAt (fun _ : ℂ ↦ (-1 : ℂ)) z :=
      analyticAt_const.meromorphicAt
    have hprod : MeromorphicAt ((fun _ : ℂ ↦ (-1 : ℂ)) * logDeriv riemannZeta) z :=
      hconst.mul hlog.meromorphicAt
    refine hprod.congr ?_
    filter_upwards with s
    simp [Pi.mul_apply]
  exact hneglog.mul hPhi_comp.meromorphicAt

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
Sign-correct principal part for `-logDeriv` from finite meromorphic order.
-/
theorem kadiri_negLogDeriv_residue_order_principal_part
    {g Phi : ℂ → ℂ} {p : ℂ} {m : ℤ}
    (hMer : MeromorphicAt g p)
    (horder : meromorphicOrderAt g p = ((m : ℤ) : WithTop ℤ))
    (hPhi : AnalyticAt ℂ Phi p) :
    ((fun s ↦ (-logDeriv g s) * Phi s) -
        (fun s ↦ (-((m : ℂ) * Phi p)) / (s - p))) =O[𝓝[≠] p]
      (1 : ℂ → ℂ) := by
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
          (fun s ↦ (-((m : ℂ) * Phi p)) / (s - p))) =ᶠ[𝓝[≠] p]
        fun s ↦ (-1 : ℂ) *
          (((fun s ↦ logDeriv g s * Phi s) -
              (fun s ↦ ((m : ℂ) * Phi p) / (s - p))) s) := by
    filter_upwards with s
    change -logDeriv g s * Phi s - (-(↑m * Phi p) / (s - p)) =
      (-1 : ℂ) * (logDeriv g s * Phi s - (↑m * Phi p) / (s - p))
    ring
  exact hprincipal_neg.trans_isBigO (hprincipal_pos.const_mul_left (-1 : ℂ))

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

/--
Principal part of the Kadiri integrand at a nontrivial zero.
-/
theorem kadiri_riemannZeta_negLogDeriv_residue_order_principal_part
    {Phi : ℂ → ℂ} (rho : NontrivialZeros)
    (hPhi : AnalyticAt ℂ Phi (-(rho : ℂ))) :
    ((fun s ↦ (-logDeriv riemannZeta s) * Phi (-s)) -
        (fun s ↦
          (-((riemannZeta.order (rho : ℂ) : ℂ) * Phi (-(rho : ℂ)))) / (s - (rho : ℂ)))) =O[
        𝓝[≠] (rho : ℂ)] (1 : ℂ → ℂ) := by
  have hPhi_comp : AnalyticAt ℂ (fun s : ℂ ↦ Phi (-s)) (rho : ℂ) := by
    have hneg : AnalyticAt ℂ (fun s : ℂ ↦ -s) (rho : ℂ) := by
      simpa [Pi.neg_def] using
        ((analyticAt_id (𝕜 := ℂ) (z := (rho : ℂ))) :
          AnalyticAt ℂ (fun s : ℂ ↦ s) (rho : ℂ)).neg
    simpa [Function.comp_def] using hPhi.comp hneg
  exact kadiri_negLogDeriv_residue_order_principal_part
    (g := riemannZeta)
    (Phi := fun s ↦ Phi (-s))
    (p := (rho : ℂ))
    (m := riemannZeta.order (rho : ℂ))
    (riemannZeta_analyticAt_nontrivialZero rho).meromorphicAt
    (riemannZeta_meromorphicOrderAt_eq_order_of_nontrivialZero rho)
    hPhi_comp

/--
The Kadiri integrand is meromorphic at each non-trivial zeta zero once `Phi`
is analytic at the reflected zero.
-/
theorem kadiri_riemannZeta_negLogDeriv_mul_meromorphicAt_nontrivialZero
    {Phi : ℂ → ℂ} (rho : NontrivialZeros)
    (hPhi : AnalyticAt ℂ Phi (-(rho : ℂ))) :
    MeromorphicAt (fun s ↦ (-logDeriv riemannZeta s) * Phi (-s)) (rho : ℂ) := by
  have hPhi_comp : AnalyticAt ℂ (fun s : ℂ ↦ Phi (-s)) (rho : ℂ) := by
    have hneg : AnalyticAt ℂ (fun s : ℂ ↦ -s) (rho : ℂ) := by
      simpa [Pi.neg_def] using
        ((analyticAt_id (𝕜 := ℂ) (z := (rho : ℂ))) :
          AnalyticAt ℂ (fun s : ℂ ↦ s) (rho : ℂ)).neg
    simpa [Function.comp_def] using hPhi.comp hneg
  exact kadiri_negLogDeriv_mul_meromorphicAt_of_order
    (g := riemannZeta)
    (Phi := fun s ↦ Phi (-s))
    (p := (rho : ℂ))
    (m := riemannZeta.order (rho : ℂ))
    (riemannZeta_analyticAt_nontrivialZero rho).meromorphicAt
    (riemannZeta_meromorphicOrderAt_eq_order_of_nontrivialZero rho)
    hPhi_comp

/--
At a non-trivial zeta zero, the Kadiri integrand has at most a simple pole once
`Phi` is analytic at the reflected zero.
-/
theorem kadiri_riemannZeta_negLogDeriv_mul_order_ge_neg_one_nontrivialZero
    {Phi : ℂ → ℂ} (rho : NontrivialZeros)
    (hPhi : AnalyticAt ℂ Phi (-(rho : ℂ))) :
    ((-1 : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun s ↦ (-logDeriv riemannZeta s) * Phi (-s)) (rho : ℂ) := by
  have hPhi_comp : AnalyticAt ℂ (fun s : ℂ ↦ Phi (-s)) (rho : ℂ) := by
    have hneg : AnalyticAt ℂ (fun s : ℂ ↦ -s) (rho : ℂ) := by
      simpa [Pi.neg_def] using
        ((analyticAt_id (𝕜 := ℂ) (z := (rho : ℂ))) :
          AnalyticAt ℂ (fun s : ℂ ↦ s) (rho : ℂ)).neg
    simpa [Function.comp_def] using hPhi.comp hneg
  exact kadiri_negLogDeriv_mul_order_ge_neg_one_of_order
    (g := riemannZeta)
    (Phi := fun s ↦ Phi (-s))
    (p := (rho : ℂ))
    (m := riemannZeta.order (rho : ℂ))
    (riemannZeta_analyticAt_nontrivialZero rho).meromorphicAt
    (riemannZeta_meromorphicOrderAt_eq_order_of_nontrivialZero rho)
    hPhi_comp

/--
The residue contribution from the simple pole of `ζ` at `1` for the Kadiri
integrand `(-ζ'/ζ)(s) * Phi(-s)`.
-/
theorem kadiri_riemannZeta_one_negLogDeriv_residue_rectangleIntegral
    {Phi : ℂ → ℂ} {z w : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 (1 : ℂ))
    (hPhi : AnalyticAt ℂ Phi (-1))
    (hHolo :
      HolomorphicOn
        (fun s ↦ (-logDeriv riemannZeta s) * Phi (-s))
        (Rectangle z w \ {(1 : ℂ)})) :
    RectangleIntegral' (fun s ↦ (-logDeriv riemannZeta s) * Phi (-s)) z w =
      Phi (-1) := by
  refine ResidueTheoremOnRectangleWithSimplePole'
    zRe_le_wRe zIm_le_wIm pInRectInterior hHolo ?_
  let f : ℂ → ℂ := fun s ↦ -logDeriv riemannZeta s
  let g : ℂ → ℂ := fun s ↦ Phi (-s)
  have hPhi_comp : AnalyticAt ℂ g (1 : ℂ) := by
    have hneg : AnalyticAt ℂ (fun s : ℂ ↦ -s) (1 : ℂ) := by
      simpa [Pi.neg_def] using
        ((analyticAt_id (𝕜 := ℂ) (z := (1 : ℂ))) :
          AnalyticAt ℂ (fun s : ℂ ↦ s) (1 : ℂ)).neg
    simpa [g, Function.comp_def] using hPhi.comp hneg
  let U : Set ℂ := {s | AnalyticAt ℂ g s}
  have hU : U ∈ 𝓝 (1 : ℂ) :=
    hPhi_comp.eventually_analyticAt
  have g_holc : HolomorphicOn g U := by
    intro s hs
    exact hs.differentiableAt.differentiableWithinAt
  have f_near_p :
      (f - fun z : ℂ ↦ 1 * (z - 1)⁻¹) =O[𝓝[≠] (1 : ℂ)]
        (1 : ℂ → ℂ) := by
    simp only [one_mul, f]
    simpa [logDeriv_apply, Pi.neg_apply, Pi.div_apply, neg_div] using
      riemannZetaLogDerivResidueBigO
  have hnear :
      (f * g - fun z : ℂ ↦ 1 * g (1 : ℂ) * (z - 1)⁻¹) =O[𝓝[≠] (1 : ℂ)]
        (1 : ℂ → ℂ) :=
    ResidueMult g_holc hU f_near_p
  convert hnear using 1
  ext s
  simp [f, g, div_eq_mul_inv]

end Kadiri
