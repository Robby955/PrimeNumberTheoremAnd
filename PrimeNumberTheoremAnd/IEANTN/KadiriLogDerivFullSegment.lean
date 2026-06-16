import PrimeNumberTheoremAnd.IEANTN.Kadiri
import PrimeNumberTheoremAnd.IEANTN.KadiriTransversalKernel
import PrimeNumberTheoremAnd.ZetaBounds

/-!
# Kadiri full-segment logarithmic-derivative scaffolding

This file starts the L2 lane for the horizontal-vanishing nodes.  The target is a
quantitative bound for `zeta'/zeta` on the whole real segment `(-a, 1 + a)` at height `T`,
including the part with nonpositive real part.

Named L2 pieces:

* `kadiri_logDeriv_zeta_nonpositive_horizontal_reflection`: proved here.  It transports
  `-zeta'/zeta` from `Re s <= 0` to the reflected point `1 - s`, discharging the zeta
  nonvanishing hypotheses from `Im s != 0`.
* `kadiri_digamma_pair_log_bound_on_nonpositive_segment`: reuse the digamma-series branch
  for this.  It bounds the two digamma
  terms in the reflected identity by `C * Real.log (3 + |T|)` for `sigma in [-a, 0]`.
* `kadiri_reflected_logDeriv_bound_from_right_halfplane`: proved here.  It uses the
  reflected point `1 - (sigma + T*I)`, whose real part is at least `1`, to get the zeta
  part under control from `LogDerivZetaBndUnif`.
* `kadiri_logDeriv_zeta_hadamard_pv_remainder_bound`: isolate the moving-pole remainder
  on the critical-strip part of the segment.
* `kadiri_logDeriv_zeta_full_segment_offpole_bound`: assemble the nonpositive, right-strip,
  and principal-value pieces into the segment-wide off-pole growth bound.
-/

noncomputable section

namespace Kadiri

open Complex Filter MeasureTheory
open scoped Topology Interval

/--
Functional-equation transport for the nonpositive real part of the horizontal segment.

This is the initial L2 brick: when `s = sigma + T * I`, `sigma <= 0`, and `T != 0`, the
denominators in Kadiri's functional-equation identity are nonzero without an assumed
zero-free hypothesis.  The point `s` is zero-free by the left-half-plane zeta lemma, and
the reflected point `1 - s` has real part at least `1`.
-/
theorem kadiri_logDeriv_zeta_nonpositive_horizontal_reflection
    {sigma T : ℝ} (hsigma : sigma ≤ 0) (hT : T ≠ 0) :
    -deriv riemannZeta (((sigma : ℂ) + (T : ℂ) * I)) /
        riemannZeta (((sigma : ℂ) + (T : ℂ) * I)) =
      ((-Real.log Real.pi : ℝ) : ℂ)
      + deriv riemannZeta (1 - (((sigma : ℂ) + (T : ℂ) * I))) /
          riemannZeta (1 - (((sigma : ℂ) + (T : ℂ) * I)))
      + (1 / 2 : ℂ) *
          (digamma ((((sigma : ℂ) + (T : ℂ) * I) / 2)) +
            digamma (((1 - (((sigma : ℂ) + (T : ℂ) * I))) / 2))) := by
  let s : ℂ := (sigma : ℂ) + (T : ℂ) * I
  have hs_re : s.re = sigma := by
    simp [s]
  have hs_im : s.im = T := by
    simp [s]
  have hs0 : s ≠ 0 := by
    intro hs
    apply hT
    have him0 : s.im = 0 := by
      rw [hs]
      simp
    simpa [hs_im] using him0
  have hs1 : s ≠ 1 := by
    intro hs
    apply hT
    have him0 : s.im = 0 := by
      rw [hs]
      simp
    simpa [hs_im] using him0
  have hzeta_s : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_re_nonpos_im_ne_zero
      (by simpa [hs_re] using hsigma)
      (by simpa [hs_im] using hT)
  have href_re : 1 ≤ (1 - s).re := by
    simp [s]
    linarith
  have hzeta_ref : riemannZeta (1 - s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re href_re
  simpa [s] using
    (kadiri_thm_3_1_q1_functional_eq (s := s) hs1 hs0 hzeta_s hzeta_ref)

/--
Right-half-plane bound for the reflected zeta term in the nonpositive part of the
horizontal segment.

For `sigma <= 0`, the reflected point `1 - (sigma + T * I)` has real part at least `1`.
The existing `LogDerivZetaBndUnif` therefore applies directly, after rewriting the reflected
point as `(1 - sigma) + (-T) * I`.
-/
theorem kadiri_reflected_logDeriv_bound_from_right_halfplane :
    ∃ C : ℝ, 0 < C ∧
      ∀ {sigma T : ℝ}, sigma ≤ 0 → 3 < |T| →
        ‖deriv riemannZeta (1 - (((sigma : ℂ) + (T : ℂ) * I))) /
            riemannZeta (1 - (((sigma : ℂ) + (T : ℂ) * I)))‖
          ≤ C * Real.log |T| ^ 9 := by
  obtain ⟨A, hA, C, hC, hbound⟩ := LogDerivZetaBndUnif
  refine ⟨C, hC, ?_⟩
  intro sigma T hsigma hT
  have hlog_pos : 0 < Real.log |T| ^ 9 := by
    have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hT.le
    positivity
  have hAdiv_nonneg : 0 ≤ A / Real.log |T| ^ 9 :=
    div_nonneg hA.1.le hlog_pos.le
  have hmem : (1 - sigma) ∈ Set.Ici (1 - A / Real.log |(-T)| ^ 9) := by
    simp only [Set.mem_Ici, abs_neg]
    linarith
  have hTneg : 3 < |(-T : ℝ)| := by
    simpa [abs_neg] using hT
  have h := hbound (1 - sigma) (-T) hTneg hmem
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, abs_neg] using h

/-- The reflected zeta logarithmic-derivative term is integrable on `[-a, 0]`. -/
theorem kadiri_reflected_logDeriv_nonpositive_horizontal_intervalIntegrable
    (a T : ℝ) (ha : 0 ≤ a) (hT : T ≠ 0) :
    IntervalIntegrable
      (fun σ : ℝ =>
        deriv riemannZeta (1 - (((σ : ℂ) + (T : ℂ) * I))) /
          riemannZeta (1 - (((σ : ℂ) + (T : ℂ) * I))))
      volume (-a) 0 := by
  have hle : -a ≤ 0 := by linarith
  refine ContinuousOn.intervalIntegrable_of_Icc hle ?_
  refine continuousOn_of_forall_continuousAt ?_
  intro σ hσ
  let z : ℂ := 1 - (((σ : ℂ) + (T : ℂ) * I))
  have hz_ne_one : z ≠ 1 := by
    intro hz
    apply hT
    have him : z.im = (1 : ℂ).im := congrArg Complex.im hz
    simpa [z] using him
  have hzeta_ne : riemannZeta z ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    have hσ_nonpos : σ ≤ 0 := hσ.2
    simp [z]
    linarith
  have hz_cont :
      ContinuousAt (fun σ : ℝ => 1 - (((σ : ℂ) + (T : ℂ) * I))) σ := by
    exact (continuous_const.sub (Complex.continuous_ofReal.add continuous_const)).continuousAt
  have hderiv_cont :
      ContinuousAt (fun σ : ℝ =>
        deriv riemannZeta (1 - (((σ : ℂ) + (T : ℂ) * I)))) σ := by
    exact ContinuousAt.comp
      (f := fun σ : ℝ => 1 - (((σ : ℂ) + (T : ℂ) * I)))
      (g := fun z : ℂ => deriv riemannZeta z)
      (x := σ)
      (differentiableAt_deriv_riemannZeta (by simpa [z] using hz_ne_one)).continuousAt
      hz_cont
  have hzeta_cont :
      ContinuousAt (fun σ : ℝ =>
        riemannZeta (1 - (((σ : ℂ) + (T : ℂ) * I)))) σ := by
    exact ContinuousAt.comp
      (f := fun σ : ℝ => 1 - (((σ : ℂ) + (T : ℂ) * I)))
      (g := fun z : ℂ => riemannZeta z)
      (x := σ)
      (differentiableAt_riemannZeta (by simpa [z] using hz_ne_one)).continuousAt
      hz_cont
  exact hderiv_cont.div hzeta_cont hzeta_ne

/--
Integral wrapper for the reflected zeta term on the nonpositive part of the horizontal
segment.
-/
theorem kadiri_reflected_logDeriv_nonpositive_horizontal_integral_bound
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {T : ℝ}, 3 < |T| →
        ‖∫ σ in (-a)..0,
            deriv riemannZeta (1 - (((σ : ℂ) + (T : ℂ) * I))) /
              riemannZeta (1 - (((σ : ℂ) + (T : ℂ) * I)))‖
          ≤ (C * Real.log |T| ^ 9) * a := by
  obtain ⟨C, hC, hpointwise⟩ := kadiri_reflected_logDeriv_bound_from_right_halfplane
  refine ⟨C, hC.le, ?_⟩
  intro T hT
  have hle : -a ≤ 0 := by linarith
  have hpoint :
      ∀ σ ∈ Ι (-a) 0,
        ‖deriv riemannZeta (1 - (((σ : ℂ) + (T : ℂ) * I))) /
            riemannZeta (1 - (((σ : ℂ) + (T : ℂ) * I)))‖
          ≤ C * Real.log |T| ^ 9 := by
    intro σ hσ
    have hσ_nonpos : σ ≤ 0 := by
      rw [Set.uIoc_of_le hle] at hσ
      exact hσ.2
    exact hpointwise (sigma := σ) (T := T) hσ_nonpos hT
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -a) (b := 0) (C := C * Real.log |T| ^ 9)
      (f := fun σ : ℝ =>
        deriv riemannZeta (1 - (((σ : ℂ) + (T : ℂ) * I))) /
          riemannZeta (1 - (((σ : ℂ) + (T : ℂ) * I)))) hpoint
  simpa [sub_eq_add_neg, abs_of_nonneg ha] using hnorm

/--
Functional-equation assembly on the nonpositive part of the horizontal segment.

The reflected zeta term is controlled by the right-half-plane bound; this leaves the
digamma-pair integral as the remaining analytic budget.
-/
theorem kadiri_nonpositive_logDeriv_integral_bound_of_digamma_budget
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {T D : ℝ}, 3 < |T| →
        IntervalIntegrable
          (fun σ : ℝ =>
            (1 / 2 : ℂ) *
              (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
                digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2))))
          volume (-a) 0 →
        ‖∫ σ in (-a)..0,
            (1 / 2 : ℂ) *
              (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
                digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖ ≤ D →
        ‖∫ σ in (-a)..0,
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a + D := by
  obtain ⟨C, hC, href_bound⟩ :=
    kadiri_reflected_logDeriv_nonpositive_horizontal_integral_bound a ha
  refine ⟨C, hC, ?_⟩
  intro T D hT hdigamma_int hdigamma_bound
  have hT_ne : T ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hT
    norm_num at hT
  let lhs : ℝ → ℂ := fun σ =>
    -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
      riemannZeta (((σ : ℂ) + (T : ℂ) * I))
  let constTerm : ℝ → ℂ := fun _ => ((-Real.log Real.pi : ℝ) : ℂ)
  let reflectedTerm : ℝ → ℂ := fun σ =>
    deriv riemannZeta (1 - (((σ : ℂ) + (T : ℂ) * I))) /
      riemannZeta (1 - (((σ : ℂ) + (T : ℂ) * I)))
  let digammaTerm : ℝ → ℂ := fun σ =>
    (1 / 2 : ℂ) *
      (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
        digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))
  have hle : -a ≤ 0 := by linarith
  have hcongr :
      Set.EqOn lhs (fun σ => constTerm σ + reflectedTerm σ + digammaTerm σ) [[-a, 0]] := by
    intro σ hσ
    have hσ_nonpos : σ ≤ 0 := by
      rw [Set.uIcc_of_le hle] at hσ
      exact hσ.2
    simpa [lhs, constTerm, reflectedTerm, digammaTerm, add_assoc] using
      (kadiri_logDeriv_zeta_nonpositive_horizontal_reflection
        (sigma := σ) (T := T) hσ_nonpos hT_ne)
  have hconst_int :
      IntervalIntegrable constTerm volume (-a) 0 :=
    continuous_const.intervalIntegrable _ _
  have href_int :
      IntervalIntegrable reflectedTerm volume (-a) 0 := by
    simpa [reflectedTerm] using
      kadiri_reflected_logDeriv_nonpositive_horizontal_intervalIntegrable a T ha hT_ne
  have hconst_reflected_int :
      IntervalIntegrable (fun σ => constTerm σ + reflectedTerm σ) volume (-a) 0 :=
    hconst_int.add href_int
  have hsplit_main :
      (∫ σ in (-a)..0, constTerm σ + reflectedTerm σ + digammaTerm σ) =
        (∫ σ in (-a)..0, constTerm σ + reflectedTerm σ) +
          ∫ σ in (-a)..0, digammaTerm σ := by
    exact intervalIntegral.integral_add hconst_reflected_int hdigamma_int
  have hsplit_reflected :
      (∫ σ in (-a)..0, constTerm σ + reflectedTerm σ) =
        (∫ σ in (-a)..0, constTerm σ) +
          ∫ σ in (-a)..0, reflectedTerm σ := by
    exact intervalIntegral.integral_add hconst_int href_int
  have hconst_bound :
      ‖∫ σ in (-a)..0, constTerm σ‖ ≤ |Real.log Real.pi| * a := by
    have hpoint :
        ∀ σ ∈ Ι (-a) 0, ‖constTerm σ‖ ≤ |Real.log Real.pi| := by
      intro σ hσ
      simp [constTerm]
    have hnorm :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := -a) (b := 0) (C := |Real.log Real.pi|)
        (f := constTerm) hpoint
    simpa [sub_eq_add_neg, abs_of_nonneg ha] using hnorm
  have hreflected_bound :
      ‖∫ σ in (-a)..0, reflectedTerm σ‖ ≤ (C * Real.log |T| ^ 9) * a := by
    simpa [reflectedTerm] using href_bound hT
  have hsum_bound :
      ‖(∫ σ in (-a)..0, constTerm σ) +
          ∫ σ in (-a)..0, reflectedTerm σ‖
        ≤ |Real.log Real.pi| * a + (C * Real.log |T| ^ 9) * a :=
    (norm_add_le _ _).trans (add_le_add hconst_bound hreflected_bound)
  calc
    ‖∫ σ in (-a)..0,
        -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        = ‖∫ σ in (-a)..0, lhs σ‖ := by
          simp [lhs]
    _ = ‖∫ σ in (-a)..0, constTerm σ + reflectedTerm σ + digammaTerm σ‖ := by
          rw [intervalIntegral.integral_congr hcongr]
    _ = ‖((∫ σ in (-a)..0, constTerm σ) +
            ∫ σ in (-a)..0, reflectedTerm σ) +
          ∫ σ in (-a)..0, digammaTerm σ‖ := by
          rw [hsplit_main, hsplit_reflected]
    _ ≤ ‖(∫ σ in (-a)..0, constTerm σ) +
            ∫ σ in (-a)..0, reflectedTerm σ‖ +
          ‖∫ σ in (-a)..0, digammaTerm σ‖ :=
          norm_add_le _ _
    _ ≤ (|Real.log Real.pi| * a + (C * Real.log |T| ^ 9) * a) + D :=
          add_le_add hsum_bound (by simpa [digammaTerm] using hdigamma_bound)
    _ = (C * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a + D := by
          ring

/--
Local principal-part control for the logarithmic derivative at an analytic zero.

If `f` has order `n > 0` at `p`, then `f'/f - n/(s-p)` is bounded in a punctured
neighborhood of `p`. This is the local Hadamard/PV brick used below for zeta zeros.
-/
theorem kadiri_logDeriv_analytic_zero_principal_part_remainder_bound
    {f : ℂ → ℂ} {p : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f p) (horder : analyticOrderAt f p = n) :
    (logDeriv f - fun s : ℂ ↦ (n : ℂ) / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  obtain ⟨g, hg_analytic, hg_ne, hfg⟩ := (hf.analyticOrderAt_eq_natCast).1 horder
  let F : ℂ → ℂ := fun s ↦ (s - p) ^ n * g s
  have hfg_ne : f =ᶠ[𝓝[≠] p] F := by
    exact hfg.filter_mono nhdsWithin_le_nhds
  have hderiv_ne : deriv f =ᶠ[𝓝[≠] p] deriv F := hfg_ne.nhdsNE_deriv
  have hg_nonzero_ne : ∀ᶠ s in 𝓝[≠] p, g s ≠ 0 := by
    exact (hg_analytic.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hg_ne
      |>.filter_mono nhdsWithin_le_nhds
  have hg_analytic_ne : ∀ᶠ s in 𝓝[≠] p, AnalyticAt ℂ g s := by
    exact hg_analytic.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hlog_eq :
      (logDeriv f - fun s : ℂ ↦ (n : ℂ) / (s - p)) =ᶠ[𝓝[≠] p] logDeriv g := by
    filter_upwards [hfg_ne, hderiv_ne, self_mem_nhdsWithin, hg_nonzero_ne, hg_analytic_ne]
      with s hfs hderiv hs_ne hgs_ne hgs_analytic
    have hpow_ne : (s - p) ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hs_ne)
    have hdiff_pow : DifferentiableAt ℂ (fun z : ℂ ↦ (z - p) ^ n) s := by fun_prop
    have hlogF :
        logDeriv F s =
          logDeriv (fun z : ℂ ↦ (z - p) ^ n) s + logDeriv g s := by
      exact logDeriv_mul (f := fun z : ℂ ↦ (z - p) ^ n) (g := g) s
        hpow_ne hgs_ne hdiff_pow hgs_analytic.differentiableAt
    have hlogpow : logDeriv (fun z : ℂ ↦ (z - p) ^ n) s = (n : ℂ) / (s - p) := by
      rw [logDeriv_fun_pow (f := fun z : ℂ ↦ z - p) (x := s) (by fun_prop) n]
      simp [logDeriv_apply, div_eq_mul_inv]
    simp only [Pi.sub_apply]
    calc
      logDeriv f s - (n : ℂ) / (s - p)
          = logDeriv F s - (n : ℂ) / (s - p) := by
            simp [logDeriv_apply, hfs, hderiv]
      _ = logDeriv g s := by
            rw [hlogF, hlogpow]
            ring
  have hderiv_bounded : deriv g =O[𝓝 p] (1 : ℂ → ℂ) :=
    hg_analytic.deriv.continuousAt.norm.isBoundedUnder_le.isBigO_one ℂ
  have hinv_bounded : g⁻¹ =O[𝓝 p] (1 : ℂ → ℂ) :=
    (hg_analytic.continuousAt.inv₀ hg_ne).norm.isBoundedUnder_le.isBigO_one ℂ
  have hlog_bounded : logDeriv g =O[𝓝 p] (1 : ℂ → ℂ) := by
    have hmul_bounded :
        (deriv g * g⁻¹) =O[𝓝 p] ((1 : ℂ → ℂ) * (1 : ℂ → ℂ)) :=
      Asymptotics.IsBigO.mul hderiv_bounded hinv_bounded
    simpa [logDeriv_apply, Pi.div_apply, Pi.mul_apply, div_eq_mul_inv] using hmul_bounded
  exact hlog_eq.trans_isBigO (hlog_bounded.mono nhdsWithin_le_nhds)

/--
Hadamard/PV local remainder at a non-trivial zeta zero.

After subtracting the multiplicity-weighted principal part at `rho`, the zeta logarithmic
derivative is bounded in a punctured neighborhood of `rho`.
-/
theorem kadiri_logDeriv_zeta_hadamard_pv_remainder_bound (rho : NontrivialZeros) :
    ((deriv riemannZeta / riemannZeta) -
        fun s : ℂ ↦ ((riemannZeta.order (rho : ℂ) : ℂ) / (s - (rho : ℂ))))
      =O[𝓝[≠] (rho : ℂ)] (1 : ℂ → ℂ) := by
  have han := riemannZeta_analyticAt_nontrivialZero rho
  have horder_ne_top := riemannZeta_meromorphicOrderAt_ne_top_nontrivialZero rho
  cases hO : analyticOrderAt riemannZeta (rho : ℂ) with
  | top =>
      exfalso
      exact horder_ne_top (by simp [han.meromorphicOrderAt_eq, hO])
  | coe n =>
      have horder_nat : riemannZeta.order (rho : ℂ) = n := by
        unfold riemannZeta.order
        rw [han.meromorphicOrderAt_eq, hO, ENat.map_coe, WithTop.untopD_coe]
      have hmain :=
        kadiri_logDeriv_analytic_zero_principal_part_remainder_bound
          (f := riemannZeta) (p := (rho : ℂ)) (n := n) han hO
      convert hmain using 2
      · ext s
        simp [horder_nat]

/--
Uniform horizontal-integral bound for one moving simple pole away from the endpoints.

This rewrites the Kadiri line `sigma + T * I - rho` into the transversal kernel with
`beta = rho.re` and `delta = T - rho.im`. The hypothesis `rho.im != T` is the
off-segment condition.
-/
theorem kadiri_moving_pole_principal_part_horizontal_integral_bound
    (a e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : ℂ) (T : ℝ) (rho : ℂ),
        rho.re ∈ Set.Icc (-a + e) (1 + a - e) →
        rho.im ≠ T →
          ‖∫ σ in (-a)..(1 + a),
              A / (((σ : ℂ) + (T : ℂ) * I) - rho)‖
            ≤ ‖A‖ * C := by
  obtain ⟨C, hC, hbound⟩ := transversal_pole_crossing_norm_le a e he
  refine ⟨C, hC, ?_⟩
  intro A T rho hrho hT
  let β : ℝ := rho.re
  let δ : ℝ := T - rho.im
  have hδ : δ ≠ 0 := by
    intro hδ0
    exact hT (sub_eq_zero.mp hδ0).symm
  have hline (σ : ℝ) :
      (((σ : ℂ) + (T : ℂ) * I) - rho) =
        (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I) := by
    rw [Complex.ext_iff]
    constructor <;> simp [β, δ]
  have hfun :
      (fun σ : ℝ => A / (((σ : ℂ) + (T : ℂ) * I) - rho)) =
        fun σ : ℝ => A * ((((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹) := by
    funext σ
    rw [hline σ]
    simp [div_eq_mul_inv]
  rw [hfun, intervalIntegral.integral_const_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (hbound δ hδ β (by simpa [β] using hrho))
    (norm_nonneg A)

/--
Kadiri-facing specialization of the moving-pole integral bound to a zeta zero principal
part, with the coefficient equal to the zeta multiplicity at `rho`.
-/
theorem kadiri_moving_pole_zeta_principal_part_horizontal_integral_bound
    (a e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : ℝ) (rho : NontrivialZeros),
        (rho : ℂ).re ∈ Set.Icc (-a + e) (1 + a - e) →
        (rho : ℂ).im ≠ T →
          ‖∫ σ in (-a)..(1 + a),
              ((riemannZeta.order (rho : ℂ) : ℂ) /
                (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖
            ≤ ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ * C := by
  obtain ⟨C, hC, hbound⟩ :=
    kadiri_moving_pole_principal_part_horizontal_integral_bound a e he
  refine ⟨C, hC, ?_⟩
  intro T rho hrho hT
  exact hbound ((riemannZeta.order (rho : ℂ) : ℂ)) T (rho : ℂ) hrho hT

/-- The off-segment moving-pole integrand is interval-integrable on the horizontal segment. -/
theorem kadiri_moving_pole_principal_part_intervalIntegrable
    (a : ℝ) (A : ℂ) (T : ℝ) (rho : ℂ) (hT : rho.im ≠ T) :
    IntervalIntegrable
      (fun σ : ℝ => A / (((σ : ℂ) + (T : ℂ) * I) - rho))
      volume (-a) (1 + a) := by
  have hden_ne (σ : ℝ) : (((σ : ℂ) + (T : ℂ) * I) - rho) ≠ 0 := by
    intro hzero
    apply hT
    have hzero_im : (((σ : ℂ) + (T : ℂ) * I) - rho).im = 0 := by
      rw [hzero]
      simp
    have hdiff : T - rho.im = 0 := by
      simpa using hzero_im
    exact (sub_eq_zero.mp hdiff).symm
  exact (continuous_const.div (by fun_prop) hden_ne).intervalIntegrable _ _

/--
Finite-family version of the moving-pole zeta principal-part integral bound.

The right side keeps the sum of multiplicity norms explicit; this is the budget that later
zero-counting estimates must discharge for a concrete truncated zero family.
-/
theorem kadiri_moving_pole_zeta_principal_part_finite_sum_horizontal_integral_bound
    (a e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Finset NontrivialZeros) (T : ℝ),
        (∀ rho ∈ S,
          (rho : ℂ).re ∈ Set.Icc (-a + e) (1 + a - e) ∧ (rho : ℂ).im ≠ T) →
          ‖∫ σ in (-a)..(1 + a), (
              ∑ rho ∈ S,
                ((riemannZeta.order (rho : ℂ) : ℂ) /
                  (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
            ≤ (∑ rho ∈ S, ‖(riemannZeta.order (rho : ℂ) : ℂ)‖) * C := by
  classical
  obtain ⟨C, hC, hsingle⟩ :=
    kadiri_moving_pole_zeta_principal_part_horizontal_integral_bound a e he
  refine ⟨C, hC, ?_⟩
  intro S T hS
  let f : NontrivialZeros → ℝ → ℂ := fun rho σ =>
    ((riemannZeta.order (rho : ℂ) : ℂ) /
      (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))
  have hint : ∀ rho ∈ S, IntervalIntegrable (f rho) volume (-a) (1 + a) := by
    intro rho hrho
    exact kadiri_moving_pole_principal_part_intervalIntegrable
      a ((riemannZeta.order (rho : ℂ) : ℂ)) T (rho : ℂ) (hS rho hrho).2
  have hintegral_sum :
      (∫ σ in (-a)..(1 + a), ∑ rho ∈ S, f rho σ) =
        ∑ rho ∈ S, ∫ σ in (-a)..(1 + a), f rho σ := by
    exact intervalIntegral.integral_finsetSum hint
  calc
    ‖∫ σ in (-a)..(1 + a), (
        ∑ rho ∈ S,
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
        = ‖∫ σ in (-a)..(1 + a), ∑ rho ∈ S, f rho σ‖ := by
          simp [f]
    _ = ‖∑ rho ∈ S, ∫ σ in (-a)..(1 + a), f rho σ‖ := by
          rw [hintegral_sum]
    _ ≤ ∑ rho ∈ S, ‖∫ σ in (-a)..(1 + a), f rho σ‖ :=
          norm_sum_le _ _
    _ ≤ ∑ rho ∈ S, ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ * C := by
          refine Finset.sum_le_sum fun rho hrho => ?_
          simpa [f] using hsingle T rho (hS rho hrho).1 (hS rho hrho).2
    _ = (∑ rho ∈ S, ‖(riemannZeta.order (rho : ℂ) : ℂ)‖) * C := by
          rw [Finset.sum_mul]

/--
Coarse cardinality-budget form of the finite-family moving-pole bound.

It is ready for a later zero-counting lemma that supplies a family size and a uniform
multiplicity cap.
-/
theorem kadiri_moving_pole_zeta_principal_part_finite_sum_horizontal_integral_card_bound
    (a e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Finset NontrivialZeros) (T M : ℝ),
        (∀ rho ∈ S,
          (rho : ℂ).re ∈ Set.Icc (-a + e) (1 + a - e) ∧ (rho : ℂ).im ≠ T) →
        (∀ rho ∈ S, ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ ≤ M) →
          ‖∫ σ in (-a)..(1 + a), (
              ∑ rho ∈ S,
                ((riemannZeta.order (rho : ℂ) : ℂ) /
                  (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
            ≤ ((S.card : ℝ) * M) * C := by
  classical
  obtain ⟨C, hC, hsum⟩ :=
    kadiri_moving_pole_zeta_principal_part_finite_sum_horizontal_integral_bound a e he
  refine ⟨C, hC, ?_⟩
  intro S T M hS hM
  calc
    ‖∫ σ in (-a)..(1 + a), (
        ∑ rho ∈ S,
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
        ≤ (∑ rho ∈ S, ‖(riemannZeta.order (rho : ℂ) : ℂ)‖) * C :=
          hsum S T hS
    _ ≤ (∑ rho ∈ S, M) * C := by
          exact mul_le_mul_of_nonneg_right
            (Finset.sum_le_sum fun rho hrho => hM rho hrho)
            hC
    _ = ((S.card : ℝ) * M) * C := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- The concrete finite family of non-trivial zeros with bounded absolute height. -/
def kadiriTruncatedNontrivialZeros (R : ℝ) : Finset NontrivialZeros :=
  (nontrivialZeros_abs_im_lt_finite R).toFinset

/-- Membership in the finite absolute-height truncation. -/
@[simp] theorem mem_kadiriTruncatedNontrivialZeros {R : ℝ} {rho : NontrivialZeros} :
    rho ∈ kadiriTruncatedNontrivialZeros R ↔ |(rho : ℂ).im| < R := by
  unfold kadiriTruncatedNontrivialZeros
  exact (nontrivialZeros_abs_im_lt_finite R).mem_toFinset

/-- For a non-trivial zero, the complex norm of the zeta order is its real order. -/
theorem kadiri_nontrivial_zero_zeta_order_norm_eq (rho : NontrivialZeros) :
    ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ =
      ((riemannZeta.order (rho : ℂ) : ℤ) : ℝ) := by
  have hordZ : (0 : ℤ) ≤ riemannZeta.order (rho : ℂ) :=
    riemannZeta_order_nonneg (nontrivialZero_ne_one rho)
  rw [Complex.norm_intCast]
  exact_mod_cast abs_of_nonneg hordZ

/-- The truncated family's norm budget is its order-weighted multiplicity sum. -/
theorem kadiriTruncatedNontrivialZeros_orderNorm_sum_eq (R : ℝ) :
    (∑ rho ∈ kadiriTruncatedNontrivialZeros R,
        ‖(riemannZeta.order (rho : ℂ) : ℂ)‖) =
      ∑ rho ∈ kadiriTruncatedNontrivialZeros R,
        ((riemannZeta.order (rho : ℂ) : ℤ) : ℝ) := by
  refine Finset.sum_congr rfl fun rho _hrho ↦ ?_
  exact kadiri_nontrivial_zero_zeta_order_norm_eq rho

/--
Concrete truncated-zero version of the moving-pole bound with the actual order sum on the
right-hand side.
-/
theorem kadiri_moving_pole_zeta_principal_part_truncated_horizontal_integral_order_sum_bound
    (a e R : ℝ) (he : 0 < e) (hea : e ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : ℝ),
        (∀ rho : NontrivialZeros,
          |(rho : ℂ).im| < R → (rho : ℂ).im ≠ T) →
          ‖∫ σ in (-a)..(1 + a), (
              ∑ rho ∈ kadiriTruncatedNontrivialZeros R,
                ((riemannZeta.order (rho : ℂ) : ℂ) /
                  (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
            ≤ (∑ rho ∈ kadiriTruncatedNontrivialZeros R,
                ((riemannZeta.order (rho : ℂ) : ℤ) : ℝ)) * C := by
  classical
  obtain ⟨C, hC, hsum⟩ :=
    kadiri_moving_pole_zeta_principal_part_finite_sum_horizontal_integral_bound a e he
  refine ⟨C, hC, ?_⟩
  intro T hoff
  have hS :
      ∀ rho ∈ kadiriTruncatedNontrivialZeros R,
        (rho : ℂ).re ∈ Set.Icc (-a + e) (1 + a - e) ∧ (rho : ℂ).im ≠ T := by
    intro rho hrho
    have him : |(rho : ℂ).im| < R := by
      simpa using (mem_kadiriTruncatedNontrivialZeros (R := R) (rho := rho)).mp hrho
    constructor
    · constructor
      · linarith [rho.property.1.1, hea]
      · linarith [rho.property.1.2, hea]
    · exact hoff rho him
  calc
    ‖∫ σ in (-a)..(1 + a), (
        ∑ rho ∈ kadiriTruncatedNontrivialZeros R,
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
        ≤ (∑ rho ∈ kadiriTruncatedNontrivialZeros R,
            ‖(riemannZeta.order (rho : ℂ) : ℂ)‖) * C :=
          hsum (kadiriTruncatedNontrivialZeros R) T hS
    _ = (∑ rho ∈ kadiriTruncatedNontrivialZeros R,
          ((riemannZeta.order (rho : ℂ) : ℤ) : ℝ)) * C := by
          rw [kadiriTruncatedNontrivialZeros_orderNorm_sum_eq R]

/-- The dyadic truncated order sum is bounded by the weighted zero-counting profile. -/
theorem kadiriTruncatedNontrivialZeros_dyadic_order_sum_le_weighted_count (k : ℕ) :
    (∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
        ((riemannZeta.order (rho : ℂ) : ℤ) : ℝ)) ≤
      2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| + weightedZeroHeightBucket := by
  classical
  let R : ℝ := (2 : ℝ) ^ (k + 1)
  let e :
      {rho : NontrivialZeros // rho ∈ kadiriTruncatedNontrivialZeros R} ≃
        {rho : NontrivialZeros // |(rho : ℂ).im| < R} :=
    Equiv.subtypeEquivRight fun rho ↦
      mem_kadiriTruncatedNontrivialZeros (R := R) (rho := rho)
  haveI : Fintype {rho : NontrivialZeros // |(rho : ℂ).im| < R} :=
    (nontrivialZeros_abs_im_lt_finite R).fintype
  have hsum_eq :
      (∑ rho ∈ kadiriTruncatedNontrivialZeros R,
          ((riemannZeta.order (rho : ℂ) : ℤ) : ℝ)) =
        ∑ rho : {rho : NontrivialZeros // |(rho : ℂ).im| < R},
          ((riemannZeta.order ((rho : NontrivialZeros) : ℂ) : ℤ) : ℝ) := by
    rw [← Finset.sum_attach]
    exact Fintype.sum_equiv e _ _ fun rho ↦ rfl
  have hweighted :
      (∑' rho : {rho : NontrivialZeros // |(rho : ℂ).im| < R},
          ((riemannZeta.order ((rho : NontrivialZeros) : ℂ) : ℤ) : ℝ)) ≤
        2 * |riemannZeta.N R| + weightedZeroHeightBucket := by
    simpa [R] using weighted_cumulative_count_le k
  simpa [R, hsum_eq, tsum_fintype] using hweighted

/--
Dyadic truncated-zero version of the moving-pole bound after discharging the order sum by
the weighted zero-counting profile.
-/
theorem kadiri_moving_pole_zeta_principal_part_dyadic_horizontal_integral_weighted_count_bound
    (a e : ℝ) (he : 0 < e) (hea : e ≤ a) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : ℝ),
        (∀ rho : NontrivialZeros,
          |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1) → (rho : ℂ).im ≠ T) →
          ‖∫ σ in (-a)..(1 + a), (
              ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
                ((riemannZeta.order (rho : ℂ) : ℂ) /
                  (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
            ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
                weightedZeroHeightBucket) * C := by
  classical
  obtain ⟨C, hC, htrunc⟩ :=
    kadiri_moving_pole_zeta_principal_part_truncated_horizontal_integral_order_sum_bound
      a e ((2 : ℝ) ^ (k + 1)) he hea
  refine ⟨C, hC, ?_⟩
  intro T hoff
  calc
    ‖∫ σ in (-a)..(1 + a), (
        ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
        ≤ (∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
            ((riemannZeta.order (rho : ℂ) : ℤ) : ℝ)) * C :=
          htrunc T hoff
    _ ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
          weightedZeroHeightBucket) * C := by
          exact mul_le_mul_of_nonneg_right
            (kadiriTruncatedNontrivialZeros_dyadic_order_sum_le_weighted_count k)
            hC

/--
The finite set of truncated zero heights can be avoided for cofinally many horizontal
segment heights.
-/
theorem kadiri_truncated_zero_family_eventually_off_height (R : ℝ) :
    ∀ᶠ T : ℝ in Filter.cofinite,
      ∀ rho : NontrivialZeros, |(rho : ℂ).im| < R → (rho : ℂ).im ≠ T := by
  classical
  rw [Filter.eventually_cofinite]
  let S : Finset NontrivialZeros := kadiriTruncatedNontrivialZeros R
  let bad : Set ℝ := (fun rho : NontrivialZeros => (rho : ℂ).im) '' (S : Set NontrivialZeros)
  have hbad_finite : bad.Finite := by
    simpa [bad] using
      (S.finite_toSet.image (fun rho : NontrivialZeros => (rho : ℂ).im))
  refine Set.Finite.subset hbad_finite ?_
  intro T hT
  rw [Set.mem_setOf_eq] at hT
  by_contra hT_not_bad
  apply hT
  intro rho hrho hEq
  apply hT_not_bad
  exact ⟨rho, by simpa [S] using
    (mem_kadiriTruncatedNontrivialZeros (R := R) (rho := rho)).mpr hrho, hEq⟩

/--
Cofinite-height form of the dyadic moving-pole bound.  This discharges the explicit
off-pole hypothesis in the weighted-count estimate by deleting the finitely many bad
zero heights.
-/
theorem
    kadiri_moving_pole_zeta_principal_part_dyadic_horizontal_integral_weighted_count_eventually
    (a e : ℝ) (he : 0 < e) (hea : e ≤ a) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in Filter.cofinite,
        ‖∫ σ in (-a)..(1 + a), (
            ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
              ((riemannZeta.order (rho : ℂ) : ℂ) /
                (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
          ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
              weightedZeroHeightBucket) * C := by
  classical
  obtain ⟨C, hC, hbound⟩ :=
    kadiri_moving_pole_zeta_principal_part_dyadic_horizontal_integral_weighted_count_bound
      a e he hea k
  refine ⟨C, hC, ?_⟩
  filter_upwards
    [kadiri_truncated_zero_family_eventually_off_height ((2 : ℝ) ^ (k + 1))]
    with T hoff
  exact hbound T hoff

/--
Assembly step for the dyadic principal part and a verified Hadamard/PV remainder budget.

The pole selector is discharged by the cofinite-height lemma; the remaining inputs are the
remainder's interval-integrability and its integral bound.
-/
theorem
    kadiri_moving_pole_zeta_principal_part_dyadic_with_remainder_eventually_bound
    (a e : ℝ) (he : 0 < e) (hea : e ≤ a) (k : ℕ)
    (rem : ℝ → ℝ → ℂ) (B : ℝ)
    (hrem_int : ∀ᶠ T : ℝ in Filter.cofinite,
      IntervalIntegrable (fun σ : ℝ => rem T σ) volume (-a) (1 + a))
    (hrem_bound : ∀ᶠ T : ℝ in Filter.cofinite,
      ‖∫ σ in (-a)..(1 + a), rem T σ‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in Filter.cofinite,
        ‖∫ σ in (-a)..(1 + a), (
            (∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
              ((riemannZeta.order (rho : ℂ) : ℂ) /
                (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))) + rem T σ)‖
          ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
              weightedZeroHeightBucket) * C + B := by
  classical
  obtain ⟨C, hC, hprincipal_bound⟩ :=
    kadiri_moving_pole_zeta_principal_part_dyadic_horizontal_integral_weighted_count_eventually
      a e he hea k
  refine ⟨C, hC, ?_⟩
  filter_upwards
    [hprincipal_bound, hrem_int, hrem_bound,
      kadiri_truncated_zero_family_eventually_off_height ((2 : ℝ) ^ (k + 1))]
    with T hprincipal hrem_integrable hrem_norm hoff
  let R : ℝ := (2 : ℝ) ^ (k + 1)
  let S : Finset NontrivialZeros := kadiriTruncatedNontrivialZeros R
  let p : NontrivialZeros → ℝ → ℂ := fun rho σ =>
    ((riemannZeta.order (rho : ℂ) : ℂ) /
      (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))
  let principal : ℝ → ℂ := ∑ rho ∈ S, p rho
  have hprincipal_integrable :
      IntervalIntegrable principal volume (-a) (1 + a) := by
    have hp : ∀ rho ∈ S, IntervalIntegrable (p rho) volume (-a) (1 + a) := by
      intro rho hrho
      have hheight : |(rho : ℂ).im| < R := by
        simpa [S] using (mem_kadiriTruncatedNontrivialZeros (R := R) (rho := rho)).mp hrho
      exact kadiri_moving_pole_principal_part_intervalIntegrable
        a ((riemannZeta.order (rho : ℂ) : ℂ)) T (rho : ℂ) (hoff rho hheight)
    have hsum : IntervalIntegrable (∑ rho ∈ S, p rho) volume (-a) (1 + a) :=
      IntervalIntegrable.sum S hp
    simpa [principal] using hsum
  have hsplit :
      (∫ σ in (-a)..(1 + a), principal σ + rem T σ) =
        (∫ σ in (-a)..(1 + a), principal σ) +
          ∫ σ in (-a)..(1 + a), rem T σ := by
    exact intervalIntegral.integral_add hprincipal_integrable hrem_integrable
  have hprincipal' :
      ‖∫ σ in (-a)..(1 + a), principal σ‖
        ≤ (2 * |riemannZeta.N R| + weightedZeroHeightBucket) * C := by
    simpa [principal, p, S, R, Finset.sum_apply] using hprincipal
  calc
    ‖∫ σ in (-a)..(1 + a), (
        (∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))) + rem T σ)‖
        = ‖∫ σ in (-a)..(1 + a), principal σ + rem T σ‖ := by
          simp [principal, p, S, R, Finset.sum_apply]
    _ = ‖(∫ σ in (-a)..(1 + a), principal σ) +
          ∫ σ in (-a)..(1 + a), rem T σ‖ := by
          rw [hsplit]
    _ ≤ ‖∫ σ in (-a)..(1 + a), principal σ‖ +
          ‖∫ σ in (-a)..(1 + a), rem T σ‖ :=
          norm_add_le _ _
    _ ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
          weightedZeroHeightBucket) * C + B := by
          simpa [R] using add_le_add hprincipal' hrem_norm

/--
Filter-parametric version of the dyadic principal-part plus remainder assembly.

This lets the later actual off-pole argument work on a filter that is finer than
`cofinite`, for example a cofinite filter restricted to heights avoiding all zeta zeros.
-/
theorem
    kadiri_moving_pole_zeta_principal_part_dyadic_with_remainder_eventually_bound_on_filter
    (a e : ℝ) (he : 0 < e) (hea : e ≤ a) (k : ℕ)
    (rem : ℝ → ℝ → ℂ) (B : ℝ) (L : Filter ℝ) (hL : L ≤ Filter.cofinite)
    (hrem_int : ∀ᶠ T : ℝ in L,
      IntervalIntegrable (fun σ : ℝ => rem T σ) volume (-a) (1 + a))
    (hrem_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in (-a)..(1 + a), rem T σ‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in L,
        ‖∫ σ in (-a)..(1 + a), (
            (∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
              ((riemannZeta.order (rho : ℂ) : ℂ) /
                (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))) + rem T σ)‖
          ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
              weightedZeroHeightBucket) * C + B := by
  classical
  obtain ⟨C, hC, hprincipal_bound⟩ :=
    kadiri_moving_pole_zeta_principal_part_dyadic_horizontal_integral_weighted_count_eventually
      a e he hea k
  refine ⟨C, hC, ?_⟩
  filter_upwards
    [hprincipal_bound.filter_mono hL, hrem_int, hrem_bound,
      (kadiri_truncated_zero_family_eventually_off_height ((2 : ℝ) ^ (k + 1))).filter_mono hL]
    with T hprincipal hrem_integrable hrem_norm hoff
  let R : ℝ := (2 : ℝ) ^ (k + 1)
  let S : Finset NontrivialZeros := kadiriTruncatedNontrivialZeros R
  let p : NontrivialZeros → ℝ → ℂ := fun rho σ =>
    ((riemannZeta.order (rho : ℂ) : ℂ) /
      (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))
  let principal : ℝ → ℂ := ∑ rho ∈ S, p rho
  have hprincipal_integrable :
      IntervalIntegrable principal volume (-a) (1 + a) := by
    have hp : ∀ rho ∈ S, IntervalIntegrable (p rho) volume (-a) (1 + a) := by
      intro rho hrho
      have hheight : |(rho : ℂ).im| < R := by
        simpa [S] using (mem_kadiriTruncatedNontrivialZeros (R := R) (rho := rho)).mp hrho
      exact kadiri_moving_pole_principal_part_intervalIntegrable
        a ((riemannZeta.order (rho : ℂ) : ℂ)) T (rho : ℂ) (hoff rho hheight)
    have hsum : IntervalIntegrable (∑ rho ∈ S, p rho) volume (-a) (1 + a) :=
      IntervalIntegrable.sum S hp
    simpa [principal] using hsum
  have hsplit :
      (∫ σ in (-a)..(1 + a), principal σ + rem T σ) =
        (∫ σ in (-a)..(1 + a), principal σ) +
          ∫ σ in (-a)..(1 + a), rem T σ := by
    exact intervalIntegral.integral_add hprincipal_integrable hrem_integrable
  have hprincipal' :
      ‖∫ σ in (-a)..(1 + a), principal σ‖
        ≤ (2 * |riemannZeta.N R| + weightedZeroHeightBucket) * C := by
    simpa [principal, p, S, R, Finset.sum_apply] using hprincipal
  calc
    ‖∫ σ in (-a)..(1 + a), (
        (∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))) + rem T σ)‖
        = ‖∫ σ in (-a)..(1 + a), principal σ + rem T σ‖ := by
          simp [principal, p, S, R, Finset.sum_apply]
    _ = ‖(∫ σ in (-a)..(1 + a), principal σ) +
          ∫ σ in (-a)..(1 + a), rem T σ‖ := by
          rw [hsplit]
    _ ≤ ‖∫ σ in (-a)..(1 + a), principal σ‖ +
          ‖∫ σ in (-a)..(1 + a), rem T σ‖ :=
          norm_add_le _ _
    _ ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
          weightedZeroHeightBucket) * C + B := by
          simpa [R] using add_le_add hprincipal' hrem_norm

/--
If a Hadamard/PV decomposition identifies the actual zeta logarithmic derivative with the
dyadic principal part plus a controlled remainder on the full horizontal segment, the
previous pole-sum and remainder estimate gives the actual off-pole segment bound.

The remaining hard input is the decomposition hypothesis `hpv_eq`, not the finite zero
sum or weighted-count budget.
-/
theorem
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_pv_decomposition
    (a e : ℝ) (he : 0 < e) (hea : e ≤ a) (k : ℕ)
    (rem : ℝ → ℝ → ℂ) (B : ℝ)
    (hrem_int : ∀ᶠ T : ℝ in Filter.cofinite,
      IntervalIntegrable (fun σ : ℝ => rem T σ) volume (-a) (1 + a))
    (hrem_bound : ∀ᶠ T : ℝ in Filter.cofinite,
      ‖∫ σ in (-a)..(1 + a), rem T σ‖ ≤ B)
    (hpv_eq : ∀ᶠ T : ℝ in Filter.cofinite,
      Set.EqOn
        (fun σ : ℝ =>
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I)))
        (fun σ : ℝ =>
          (∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
            ((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))) + rem T σ)
        [[-a, 1 + a]]) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in Filter.cofinite,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
              weightedZeroHeightBucket) * C + B := by
  classical
  obtain ⟨C, hC, hdecomp_bound⟩ :=
    kadiri_moving_pole_zeta_principal_part_dyadic_with_remainder_eventually_bound
      a e he hea k rem B hrem_int hrem_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [hdecomp_bound, hpv_eq] with T hbound hEq
  calc
    ‖∫ σ in (-a)..(1 + a),
        -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        = ‖∫ σ in (-a)..(1 + a), (
            (∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
              ((riemannZeta.order (rho : ℂ) : ℂ) /
                (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))) + rem T σ)‖ := by
          rw [intervalIntegral.integral_congr hEq]
    _ ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
          weightedZeroHeightBucket) * C + B :=
          hbound

/--
Concrete dyadic Hadamard/PV remainder after subtracting the truncated zero-principal
block from the actual zeta logarithmic derivative on the moving horizontal segment.
-/
noncomputable def kadiriDyadicHadamardPVRemainder (k : ℕ) (T σ : ℝ) : ℂ :=
  -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
      riemannZeta (((σ : ℂ) + (T : ℂ) * I)) -
    ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
      ((riemannZeta.order (rho : ℂ) : ℂ) /
        (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))

/-- Heights whose horizontal line avoids the pole at `1` and every non-trivial zeta zero. -/
def kadiriHorizontalZetaOffPoleHeight (T : ℝ) : Prop :=
  T ≠ 0 ∧ ∀ rho : NontrivialZeros, (rho : ℂ).im ≠ T

/--
The off-pole height filter for the horizontal segment: a cofinite height filter restricted
to heights avoiding all non-trivial zeta zero ordinates and the real axis.
-/
noncomputable def kadiriHorizontalZetaOffPoleFilter : Filter ℝ :=
  Filter.cofinite ⊓ 𝓟 {T : ℝ | kadiriHorizontalZetaOffPoleHeight T}

/-- The off-pole filter is finer than the cofinite filter. -/
theorem kadiriHorizontalZetaOffPoleFilter_le_cofinite :
    kadiriHorizontalZetaOffPoleFilter ≤ Filter.cofinite := by
  exact inf_le_left

/-- Along the off-pole filter, the height condition holds eventually by definition. -/
theorem eventually_kadiriHorizontalZetaOffPoleHeight :
    ∀ᶠ T : ℝ in kadiriHorizontalZetaOffPoleFilter,
      kadiriHorizontalZetaOffPoleHeight T := by
  have hprincipal :
      ∀ᶠ T : ℝ in 𝓟 {T : ℝ | kadiriHorizontalZetaOffPoleHeight T},
        kadiriHorizontalZetaOffPoleHeight T :=
    Filter.mem_principal_self _
  exact hprincipal.filter_mono inf_le_right

/-- Off-pole nonvanishing of `ζ` on the moving horizontal segment. -/
theorem riemannZeta_ne_zero_on_horizontal_of_offPole
    {T σ : ℝ} (hT : kadiriHorizontalZetaOffPoleHeight T) :
    riemannZeta (((σ : ℂ) + (T : ℂ) * I)) ≠ 0 := by
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  have hs_re : s.re = σ := by
    simp [s]
  have hs_im : s.im = T := by
    simp [s]
  by_cases hσ_nonpos : σ ≤ 0
  · exact riemannZeta_ne_zero_of_re_nonpos_im_ne_zero
      (by simpa [hs_re] using hσ_nonpos)
      (by simpa [hs_im] using hT.1)
  · by_cases hσ_one : 1 ≤ σ
    · exact riemannZeta_ne_zero_of_one_le_re (by simpa [hs_re] using hσ_one)
    · have hσ_pos : 0 < σ := lt_of_not_ge hσ_nonpos
      have hσ_lt_one : σ < 1 := lt_of_not_ge hσ_one
      intro hz
      let rho : NontrivialZeros :=
        ⟨s, ⟨by simpa [hs_re] using hσ_pos, by simpa [hs_re] using hσ_lt_one⟩,
          Set.mem_univ _, hz⟩
      exact hT.2 rho (by simp [rho, hs_im])

/-- The actual zeta logarithmic-derivative integrand is integrable on off-pole heights. -/
theorem kadiri_neg_zeta_logDeriv_horizontal_intervalIntegrable_of_offPole
    (a T : ℝ) (ha : 0 ≤ a) (hT : kadiriHorizontalZetaOffPoleHeight T) :
    IntervalIntegrable
      (fun σ : ℝ =>
        -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I)))
      volume (-a) (1 + a) := by
  have hle : -a ≤ 1 + a := by linarith
  refine ContinuousOn.intervalIntegrable_of_Icc hle ?_
  refine continuousOn_of_forall_continuousAt ?_
  intro σ _hσ
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  have hs_ne_one : s ≠ 1 := by
    intro hs
    apply hT.1
    have him : s.im = (1 : ℂ).im := congrArg Complex.im hs
    simpa [s] using him
  have hzeta_ne : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_on_horizontal_of_offPole (T := T) (σ := σ) hT
  have hs_cont : ContinuousAt (fun σ : ℝ => ((σ : ℂ) + (T : ℂ) * I)) σ := by
    exact (Complex.continuous_ofReal.add continuous_const).continuousAt
  have hderiv_cont :
      ContinuousAt (fun σ : ℝ => -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I))) σ := by
    exact (ContinuousAt.comp
      (f := fun σ : ℝ => ((σ : ℂ) + (T : ℂ) * I))
      (g := fun z : ℂ => deriv riemannZeta z)
      (x := σ)
      (differentiableAt_deriv_riemannZeta (by simpa [s] using hs_ne_one)).continuousAt
      hs_cont).neg
  have hzeta_cont :
      ContinuousAt (fun σ : ℝ => riemannZeta (((σ : ℂ) + (T : ℂ) * I))) σ := by
    exact ContinuousAt.comp
      (f := fun σ : ℝ => ((σ : ℂ) + (T : ℂ) * I))
      (g := fun z : ℂ => riemannZeta z)
      (x := σ)
      (differentiableAt_riemannZeta (by simpa [s] using hs_ne_one)).continuousAt
      hs_cont
  exact hderiv_cont.div hzeta_cont (by simpa [s] using hzeta_ne)

/-- The dyadic zero-principal finite sum is integrable on off-pole heights. -/
theorem kadiriDyadicPrincipalPart_intervalIntegrable_of_offPole
    (a T : ℝ) (k : ℕ) (hT : kadiriHorizontalZetaOffPoleHeight T) :
    IntervalIntegrable
      (fun σ : ℝ =>
        ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))
      volume (-a) (1 + a) := by
  classical
  let S : Finset NontrivialZeros := kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))
  let p : NontrivialZeros → ℝ → ℂ := fun rho σ =>
    ((riemannZeta.order (rho : ℂ) : ℂ) /
      (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))
  have hp : ∀ rho ∈ S, IntervalIntegrable (p rho) volume (-a) (1 + a) := by
    intro rho _hrho
    exact kadiri_moving_pole_principal_part_intervalIntegrable
      a ((riemannZeta.order (rho : ℂ) : ℂ)) T (rho : ℂ) (hT.2 rho)
  have hsum : IntervalIntegrable (∑ rho ∈ S, p rho) volume (-a) (1 + a) :=
    IntervalIntegrable.sum S hp
  have hfun :
      (fun σ : ℝ =>
        ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))) =
        (∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
          fun σ : ℝ =>
            ((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))) := by
    funext σ
    simp
  rw [hfun]
  simpa [S, p] using hsum

/-- The concrete dyadic Hadamard/PV remainder is integrable on off-pole heights. -/
theorem kadiriDyadicHadamardPVRemainder_intervalIntegrable_of_offPole
    (a T : ℝ) (ha : 0 ≤ a) (k : ℕ) (hT : kadiriHorizontalZetaOffPoleHeight T) :
    IntervalIntegrable (fun σ : ℝ => kadiriDyadicHadamardPVRemainder k T σ)
      volume (-a) (1 + a) := by
  have hactual :=
    kadiri_neg_zeta_logDeriv_horizontal_intervalIntegrable_of_offPole a T ha hT
  have hprincipal :=
    kadiriDyadicPrincipalPart_intervalIntegrable_of_offPole a T k hT
  simpa [kadiriDyadicHadamardPVRemainder] using hactual.sub hprincipal

/-- On the off-pole filter, the concrete dyadic Hadamard/PV remainder is integrable. -/
theorem eventually_kadiriDyadicHadamardPVRemainder_intervalIntegrable
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    ∀ᶠ T : ℝ in kadiriHorizontalZetaOffPoleFilter,
      IntervalIntegrable (fun σ : ℝ => kadiriDyadicHadamardPVRemainder k T σ)
        volume (-a) (1 + a) := by
  filter_upwards [eventually_kadiriHorizontalZetaOffPoleHeight] with T hT
  exact kadiriDyadicHadamardPVRemainder_intervalIntegrable_of_offPole a T ha k hT

/--
A pointwise bound for the concrete dyadic Hadamard/PV remainder controls its full
horizontal-segment integral.
-/
theorem kadiriDyadicHadamardPVRemainder_integral_bound_of_pointwise_bound
    (a T : ℝ) (ha : 0 ≤ a) (k : ℕ) (B : ℝ)
    (hpoint : ∀ σ ∈ Ι (-a) (1 + a),
      ‖kadiriDyadicHadamardPVRemainder k T σ‖ ≤ B) :
    ‖∫ σ in (-a)..(1 + a), kadiriDyadicHadamardPVRemainder k T σ‖ ≤
      B * (1 + 2 * a) := by
  have hlen_nonneg : 0 ≤ 1 + 2 * a := by linarith
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -a) (b := 1 + a) (C := B)
      (f := fun σ : ℝ => kadiriDyadicHadamardPVRemainder k T σ) hpoint
  have hlen_abs : |a + (a + 1)| = 1 + 2 * a := by
    rw [abs_of_nonneg]
    · ring
    · linarith
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, hlen_abs] using hnorm

/--
Eventual pointwise control of the concrete dyadic Hadamard/PV remainder supplies the
eventual integral norm budget needed by the full-segment assembly.
-/
theorem eventually_kadiriDyadicHadamardPVRemainder_integral_bound_of_pointwise_bound
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (B : ℝ)
    (hpoint : ∀ᶠ T : ℝ in kadiriHorizontalZetaOffPoleFilter,
      ∀ σ ∈ Ι (-a) (1 + a),
        ‖kadiriDyadicHadamardPVRemainder k T σ‖ ≤ B) :
    ∀ᶠ T : ℝ in kadiriHorizontalZetaOffPoleFilter,
      ‖∫ σ in (-a)..(1 + a), kadiriDyadicHadamardPVRemainder k T σ‖ ≤
        B * (1 + 2 * a) := by
  filter_upwards [hpoint] with T hT_point
  exact kadiriDyadicHadamardPVRemainder_integral_bound_of_pointwise_bound
    a T ha k B hT_point

/--
Actual full-segment dyadic off-pole bound from a concrete Hadamard/PV remainder budget.

Compared with
`kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_pv_decomposition`,
the decomposition equality is no longer an input: it is definitional for
`kadiriDyadicHadamardPVRemainder`.  The remaining analytic work is to prove the stated
integrability and integral bound for this concrete remainder.
-/
theorem
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_concrete_remainder_budget
    (a e : ℝ) (he : 0 < e) (hea : e ≤ a) (k : ℕ) (B : ℝ)
    (hrem_int : ∀ᶠ T : ℝ in Filter.cofinite,
      IntervalIntegrable (fun σ : ℝ => kadiriDyadicHadamardPVRemainder k T σ)
        volume (-a) (1 + a))
    (hrem_bound : ∀ᶠ T : ℝ in Filter.cofinite,
      ‖∫ σ in (-a)..(1 + a), kadiriDyadicHadamardPVRemainder k T σ‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in Filter.cofinite,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
              weightedZeroHeightBucket) * C + B := by
  refine
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_pv_decomposition
      a e he hea k (kadiriDyadicHadamardPVRemainder k) B hrem_int hrem_bound ?_
  exact Filter.Eventually.of_forall fun T => by
    intro σ _hσ
    simp [kadiriDyadicHadamardPVRemainder]

/--
Filter-parametric actual off-pole bound for the concrete dyadic Hadamard/PV remainder.

Use this form when the final contour argument works on a finer off-pole height filter
rather than on all but finitely many real heights.
-/
theorem
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_concrete_remainder_budget_on_filter
    (a e : ℝ) (he : 0 < e) (hea : e ≤ a) (k : ℕ) (B : ℝ)
    (L : Filter ℝ) (hL : L ≤ Filter.cofinite)
    (hrem_int : ∀ᶠ T : ℝ in L,
      IntervalIntegrable (fun σ : ℝ => kadiriDyadicHadamardPVRemainder k T σ)
        volume (-a) (1 + a))
    (hrem_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in (-a)..(1 + a), kadiriDyadicHadamardPVRemainder k T σ‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in L,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
              weightedZeroHeightBucket) * C + B := by
  obtain ⟨C, hC, hbound⟩ :=
    kadiri_moving_pole_zeta_principal_part_dyadic_with_remainder_eventually_bound_on_filter
      a e he hea k (kadiriDyadicHadamardPVRemainder k) B L hL hrem_int hrem_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with T hT_bound
  have hEq :
      Set.EqOn
        (fun σ : ℝ =>
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I)))
        (fun σ : ℝ =>
          (∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
            ((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))) +
            kadiriDyadicHadamardPVRemainder k T σ)
        [[-a, 1 + a]] := by
    intro σ _hσ
    simp [kadiriDyadicHadamardPVRemainder]
  calc
    ‖∫ σ in (-a)..(1 + a),
        -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        = ‖∫ σ in (-a)..(1 + a), (
            (∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
              ((riemannZeta.order (rho : ℂ) : ℂ) /
                (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))) +
              kadiriDyadicHadamardPVRemainder k T σ)‖ := by
          rw [intervalIntegral.integral_congr hEq]
    _ ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
          weightedZeroHeightBucket) * C + B :=
          hT_bound

/--
Actual full-segment dyadic off-pole bound on the canonical off-pole height filter, after
the concrete Hadamard/PV remainder norm bound has been supplied.
-/
theorem
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_concrete_remainder_bound
    (a e : ℝ) (ha : 0 ≤ a) (he : 0 < e) (hea : e ≤ a) (k : ℕ) (B : ℝ)
    (hrem_bound : ∀ᶠ T : ℝ in kadiriHorizontalZetaOffPoleFilter,
      ‖∫ σ in (-a)..(1 + a), kadiriDyadicHadamardPVRemainder k T σ‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
              weightedZeroHeightBucket) * C + B := by
  exact
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_concrete_remainder_budget_on_filter
      a e he hea k B kadiriHorizontalZetaOffPoleFilter
      kadiriHorizontalZetaOffPoleFilter_le_cofinite
      (eventually_kadiriDyadicHadamardPVRemainder_intervalIntegrable a ha k)
      hrem_bound

/--
Actual full-segment dyadic off-pole bound from a pointwise bound on the concrete
Hadamard/PV remainder.

This is the form left for the analytic Hadamard/PV estimate: prove pointwise control of
`kadiriDyadicHadamardPVRemainder` on the moving segment, and the pole-sum/counting
machinery supplies the integral bound.
-/
theorem
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_concrete_remainder_pointwise_bound
    (a e : ℝ) (ha : 0 ≤ a) (he : 0 < e) (hea : e ≤ a) (k : ℕ) (B : ℝ)
    (hpoint : ∀ᶠ T : ℝ in kadiriHorizontalZetaOffPoleFilter,
      ∀ σ ∈ Ι (-a) (1 + a),
        ‖kadiriDyadicHadamardPVRemainder k T σ‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
              weightedZeroHeightBucket) * C + B * (1 + 2 * a) := by
  exact
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_concrete_remainder_bound
      a e ha he hea k (B * (1 + 2 * a))
      (eventually_kadiriDyadicHadamardPVRemainder_integral_bound_of_pointwise_bound
        a ha k B hpoint)

/--
Concrete truncated-zero version of the finite-family moving-pole bound.

The hypotheses left open are exactly the later off-pole and multiplicity-budget obligations:
no member of the truncated family lies on the horizontal line at height `T`, and every member
has multiplicity norm at most `M`.
-/
theorem kadiri_moving_pole_zeta_principal_part_truncated_horizontal_integral_card_bound
    (a e R : ℝ) (he : 0 < e) (hea : e ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T M : ℝ),
        (∀ rho : NontrivialZeros,
          |(rho : ℂ).im| < R → (rho : ℂ).im ≠ T) →
        (∀ rho : NontrivialZeros,
          |(rho : ℂ).im| < R →
            ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ ≤ M) →
          ‖∫ σ in (-a)..(1 + a), (
              ∑ rho ∈ kadiriTruncatedNontrivialZeros R,
                ((riemannZeta.order (rho : ℂ) : ℂ) /
                  (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
            ≤ (((kadiriTruncatedNontrivialZeros R).card : ℝ) * M) * C := by
  classical
  obtain ⟨C, hC, hcard⟩ :=
    kadiri_moving_pole_zeta_principal_part_finite_sum_horizontal_integral_card_bound a e he
  refine ⟨C, hC, ?_⟩
  intro T M hoff hM
  refine hcard (kadiriTruncatedNontrivialZeros R) T M ?_ ?_
  · intro rho hrho
    have him : |(rho : ℂ).im| < R := by
      have hmem :
          rho ∈ ({rho : NontrivialZeros | |(rho : ℂ).im| < R} :
            Set NontrivialZeros) := by
        exact (nontrivialZeros_abs_im_lt_finite R).mem_toFinset.mp
          (by simpa [kadiriTruncatedNontrivialZeros] using hrho)
      simpa using hmem
    constructor
    · constructor
      · linarith [rho.property.1.1, hea]
      · linarith [rho.property.1.2, hea]
    · exact hoff rho him
  · intro rho hrho
    have him : |(rho : ℂ).im| < R := by
      have hmem :
          rho ∈ ({rho : NontrivialZeros | |(rho : ℂ).im| < R} :
            Set NontrivialZeros) := by
        exact (nontrivialZeros_abs_im_lt_finite R).mem_toFinset.mp
          (by simpa [kadiriTruncatedNontrivialZeros] using hrho)
      simpa using hmem
    exact hM rho him

end Kadiri
