import PrimeNumberTheoremAnd.IEANTN.Kadiri
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

open Complex Filter
open scoped Topology

/--
Functional-equation transport for the nonpositive real part of the horizontal segment.

This is the first L2 brick: when `s = sigma + T * I`, `sigma <= 0`, and `T != 0`, the
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

end Kadiri
