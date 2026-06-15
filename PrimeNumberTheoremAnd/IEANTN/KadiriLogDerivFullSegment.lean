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
