import PrimeNumberTheoremAnd.IEANTN.Kadiri
import PrimeNumberTheoremAnd.IEANTN.KadiriGoodHeightSelector
import PrimeNumberTheoremAnd.IEANTN.KadiriTransversalKernel
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
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
Terminal right-segment integral bound from the uniform right-half-plane zeta
logarithmic-derivative estimate.

Once the moving left endpoint `x` lies in the region
`1 - A / log |T| ^ 9 <= Re s`, the `LogDerivZetaBndUnif` pointwise bound controls
the integral of the actual `-ζ'/ζ` term over `[x, 1 + a]`.
-/
theorem kadiri_right_terminal_neg_logDeriv_integral_bound_from_right_halfplane :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ {a T x : ℝ}, x ≤ 1 + a → 3 < |T| →
        x ∈ Set.Ici (1 - A / Real.log |T| ^ 9) →
          ‖∫ σ in x..(1 + a),
              -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
            ≤ (C * Real.log |T| ^ 9) * |1 + a - x| := by
  obtain ⟨A, hA, C, hC, hbound⟩ := LogDerivZetaBndUnif
  refine ⟨A, C, hA.1.le, hC, ?_⟩
  intro a T x hx hT hxmem
  have hpoint :
      ∀ σ ∈ Ι x (1 + a),
        ‖-deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖ ≤
          C * Real.log |T| ^ 9 := by
    intro σ hσ
    have hσ_mem : σ ∈ Set.Ioc x (1 + a) := by
      rw [Set.uIoc_of_le hx] at hσ
      exact hσ
    have hσ_region : σ ∈ Set.Ici (1 - A / Real.log |T| ^ 9) := by
      exact le_trans hxmem hσ_mem.1.le
    have h := hbound σ T hT hσ_region
    simpa [neg_div, norm_neg] using h
  simpa using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := x) (b := 1 + a) (C := C * Real.log |T| ^ 9)
      (f := fun σ : ℝ =>
        -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I))) hpoint)

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

/-- The digamma function is analytic away from the real axis. -/
theorem kadiri_digamma_analyticAt_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    AnalyticAt ℂ digamma z := by
  let U : Set ℂ := {w : ℂ | w.im ≠ 0}
  have hUopen : IsOpen U := by
    simpa [U] using (continuous_im.isOpen_preimage _ isOpen_ne)
  have hdiff : DifferentiableOn ℂ Gamma U := by
    intro w hw
    exact (differentiableAt_Gamma w (fun m => by
      intro hwm
      have him : w.im = 0 := by
        rw [hwm]
        simp
      exact hw him)).differentiableWithinAt
  have hGamma_analyticOn : AnalyticOnNhd ℂ Gamma U :=
    hdiff.analyticOnNhd hUopen
  have hGamma_an : AnalyticAt ℂ Gamma z := hGamma_analyticOn z hz
  have hderiv_an : AnalyticAt ℂ (deriv Gamma) z := hGamma_an.deriv
  have hGamma_ne : Gamma z ≠ 0 := Gamma_ne_zero (s := z) (fun m => by
    intro hzm
    have him : z.im = 0 := by
      rw [hzm]
      simp
    exact hz him)
  have hquot : AnalyticAt ℂ (fun w => deriv Gamma w / Gamma w) z :=
    hderiv_an.fun_div hGamma_an hGamma_ne
  simpa [digamma_def, logDeriv_apply] using hquot

/--
The digamma pair in Kadiri's functional-equation transport is integrable on the
nonpositive segment whenever the horizontal height is nonzero.
-/
theorem kadiri_digamma_pair_nonpositive_horizontal_intervalIntegrable
    (a T : ℝ) (ha : 0 ≤ a) (hT : T ≠ 0) :
    IntervalIntegrable
      (fun σ : ℝ =>
        (1 / 2 : ℂ) *
          (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
            digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2))))
      volume (-a) 0 := by
  have hle : -a ≤ 0 := by linarith
  refine ContinuousOn.intervalIntegrable_of_Icc hle ?_
  refine continuousOn_of_forall_continuousAt ?_
  intro σ hσ
  have hz1_im_ne : ((((σ : ℂ) + (T : ℂ) * I) / 2).im) ≠ 0 := by
    simp [hT]
  have hz2_im_ne : (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2).im) ≠ 0 := by
    simp [hT]
  have harg1 :
      ContinuousAt (fun x : ℝ => (((x : ℂ) + (T : ℂ) * I) / 2)) σ := by
    fun_prop
  have harg2 :
      ContinuousAt (fun x : ℝ => ((1 - (((x : ℂ) + (T : ℂ) * I))) / 2)) σ := by
    fun_prop
  have hd1 :
      ContinuousAt
        (fun x : ℝ => digamma ((((x : ℂ) + (T : ℂ) * I) / 2))) σ := by
    simpa [Function.comp_def] using
      (ContinuousAt.comp
        (f := fun x : ℝ => (((x : ℂ) + (T : ℂ) * I) / 2))
        (g := digamma)
        (kadiri_digamma_analyticAt_of_im_ne_zero hz1_im_ne).continuousAt harg1)
  have hd2 :
      ContinuousAt
        (fun x : ℝ => digamma (((1 - (((x : ℂ) + (T : ℂ) * I))) / 2))) σ := by
    simpa [Function.comp_def] using
      (ContinuousAt.comp
        (f := fun x : ℝ => ((1 - (((x : ℂ) + (T : ℂ) * I))) / 2))
        (g := digamma)
        (kadiri_digamma_analyticAt_of_im_ne_zero hz2_im_ne).continuousAt harg2)
  exact continuousAt_const.mul (hd1.add hd2)

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
The nonpositive horizontal zeta logarithmic-derivative integrand is integrable once the
digamma pair from the functional equation is integrable.
-/
theorem kadiri_nonpositive_logDeriv_intervalIntegrable_of_digamma
    (a T : ℝ) (ha : 0 ≤ a) (hT : T ≠ 0)
    (hdigamma_int :
      IntervalIntegrable
        (fun σ : ℝ =>
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2))))
        volume (-a) 0) :
    IntervalIntegrable
      (fun σ : ℝ =>
        -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I)))
      volume (-a) 0 := by
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
      Set.EqOn lhs (fun σ => constTerm σ + reflectedTerm σ + digammaTerm σ)
        (Set.uIoc (-a) 0) := by
    intro σ hσ
    have hσ_nonpos : σ ≤ 0 := by
      rw [Set.uIoc_of_le hle] at hσ
      exact hσ.2
    simpa [lhs, constTerm, reflectedTerm, digammaTerm, add_assoc] using
      (kadiri_logDeriv_zeta_nonpositive_horizontal_reflection
        (sigma := σ) (T := T) hσ_nonpos hT)
  have hconst_int :
      IntervalIntegrable constTerm volume (-a) 0 :=
    continuous_const.intervalIntegrable _ _
  have href_int :
      IntervalIntegrable reflectedTerm volume (-a) 0 := by
    simpa [reflectedTerm] using
      kadiri_reflected_logDeriv_nonpositive_horizontal_intervalIntegrable a T ha hT
  have hsum_int :
      IntervalIntegrable
        (fun σ : ℝ => constTerm σ + reflectedTerm σ + digammaTerm σ)
        volume (-a) 0 := by
    exact (hconst_int.add href_int).add (by simpa [digammaTerm] using hdigamma_int)
  exact IntervalIntegrable.congr hcongr.symm hsum_int

/--
Full-segment assembly from the reflected nonpositive budget and a supplied right-segment
budget.

This is the split point between the reflected functional-equation lane on `[-a, 0]` and
the moving-pole PV lane on `[0, 1 + a]`.
-/
theorem kadiri_logDeriv_zeta_full_segment_bound_of_nonpositive_and_right_budget
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {T D R : ℝ}, 3 < |T| →
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
        IntervalIntegrable
          (fun σ : ℝ =>
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I)))
          volume 0 (1 + a) →
        ‖∫ σ in 0..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖ ≤ R →
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ ((C * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a + D) + R := by
  obtain ⟨C, hC, hleft_bound⟩ :=
    kadiri_nonpositive_logDeriv_integral_bound_of_digamma_budget a ha
  refine ⟨C, hC, ?_⟩
  intro T D R hT hdigamma_int hdigamma_bound hright_int hright_bound
  let f : ℝ → ℂ := fun σ =>
    -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
      riemannZeta (((σ : ℂ) + (T : ℂ) * I))
  have hT_ne : T ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hT
    norm_num at hT
  have hleft_int : IntervalIntegrable f volume (-a) 0 := by
    simpa [f] using
      kadiri_nonpositive_logDeriv_intervalIntegrable_of_digamma
        a T ha hT_ne hdigamma_int
  have hleft :
      ‖∫ σ in (-a)..0, f σ‖ ≤
        (C * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a + D := by
    simpa [f] using hleft_bound hT hdigamma_int hdigamma_bound
  have hsplit :
      (∫ σ in (-a)..0, f σ) + (∫ σ in 0..(1 + a), f σ) =
        ∫ σ in (-a)..(1 + a), f σ := by
    exact intervalIntegral.integral_add_adjacent_intervals hleft_int (by simpa [f] using hright_int)
  calc
    ‖∫ σ in (-a)..(1 + a),
        -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        = ‖∫ σ in (-a)..(1 + a), f σ‖ := by
          simp [f]
    _ = ‖(∫ σ in (-a)..0, f σ) + (∫ σ in 0..(1 + a), f σ)‖ := by
          rw [hsplit]
    _ ≤ ‖∫ σ in (-a)..0, f σ‖ + ‖∫ σ in 0..(1 + a), f σ‖ :=
          norm_add_le _ _
    _ ≤ ((C * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a + D) + R := by
          exact add_le_add hleft (by simpa [f] using hright_bound)

/--
Filter-parametric full-segment assembly from reflected nonpositive control and an eventual
right-segment budget.

The large-height hypothesis is explicit because `3 < |T|` is not a cofinite condition on
the real line.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_nonpositive_and_right_budget_on_filter
    (a D R : ℝ) (ha : 0 ≤ a) (L : Filter ℝ)
    (hlarge : ∀ᶠ T : ℝ in L, 3 < |T|)
    (hdigamma_int : ∀ᶠ T : ℝ in L,
      IntervalIntegrable
        (fun σ : ℝ =>
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2))))
        volume (-a) 0)
    (hdigamma_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in (-a)..0,
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖ ≤ D)
    (hright_int : ∀ᶠ T : ℝ in L,
      IntervalIntegrable
        (fun σ : ℝ =>
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I)))
        volume 0 (1 + a))
    (hright_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in 0..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖ ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in L,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ ((C * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a + D) + R := by
  obtain ⟨C, hC, hpoint⟩ :=
    kadiri_logDeriv_zeta_full_segment_bound_of_nonpositive_and_right_budget a ha
  refine ⟨C, hC, ?_⟩
  filter_upwards [hlarge, hdigamma_int, hdigamma_bound, hright_int, hright_bound]
    with T hT hdigamma_int_T hdigamma_bound_T hright_int_T hright_bound_T
  exact hpoint hT hdigamma_int_T hdigamma_bound_T hright_int_T hright_bound_T

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
Right-segment transversal kernel bound with an explicit lower endpoint margin.

This is the translated form needed on `[0, 1 + a]`: it reuses the symmetric
`[-a / 2, 1 + a / 2]` kernel after shifting the real axis by `a / 2`.
-/
theorem kadiri_right_segment_transversal_pole_crossing_norm_le
    (a e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ δ : ℝ, δ ≠ 0 → ∀ β : ℝ,
        β ∈ Set.Icc e (1 + a - e) →
          ‖∫ σ in 0..(1 + a), (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := transversal_pole_crossing_norm_le (a / 2) e he
  refine ⟨C, hC, ?_⟩
  intro δ hδ β hβ
  let β' : ℝ := β - a / 2
  have hβ' : β' ∈ Set.Icc (-(a / 2) + e) (1 + a / 2 - e) := by
    constructor
    · dsimp [β']
      linarith [hβ.1]
    · dsimp [β']
      linarith [hβ.2]
  let g : ℝ → ℂ := fun τ => (((τ : ℂ) - (β' : ℂ)) + (δ : ℂ) * I)⁻¹
  have hfun :
      (fun σ : ℝ => (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹) =
        fun σ : ℝ => g (σ - a / 2) := by
    funext σ
    simp [g, β']
  calc
    ‖∫ σ in 0..(1 + a), (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹‖
        = ‖∫ σ in 0..(1 + a), g (σ - a / 2)‖ := by
          rw [hfun]
    _ = ‖∫ σ in (0 - a / 2)..(1 + a - a / 2), g σ‖ := by
          rw [intervalIntegral.integral_comp_sub_right]
    _ = ‖∫ σ in -(a / 2)..(1 + a / 2), g σ‖ := by
          congr 3 <;> ring
    _ ≤ C := by
          simpa [g, β'] using hbound δ hδ β' hβ'

/--
Uniform right-segment integral bound for one moving simple pole away from the endpoints.

The real-part hypothesis is stronger than the full-segment strip condition: it includes the
lower margin `e <= rho.re` needed to keep the pole away from the right segment's left
endpoint.
-/
theorem kadiri_moving_pole_principal_part_right_integral_bound
    (a e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : ℂ) (T : ℝ) (rho : ℂ),
        rho.re ∈ Set.Icc e (1 + a - e) →
        rho.im ≠ T →
          ‖∫ σ in 0..(1 + a),
              A / (((σ : ℂ) + (T : ℂ) * I) - rho)‖
            ≤ ‖A‖ * C := by
  obtain ⟨C, hC, hbound⟩ :=
    kadiri_right_segment_transversal_pole_crossing_norm_le a e he
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

/--
Right-segment specialization of the moving-pole integral bound to a zeta zero principal
part, with the endpoint margin kept explicit.
-/
theorem kadiri_moving_pole_zeta_principal_part_right_integral_bound
    (a e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : ℝ) (rho : NontrivialZeros),
        (rho : ℂ).re ∈ Set.Icc e (1 + a - e) →
        (rho : ℂ).im ≠ T →
          ‖∫ σ in 0..(1 + a),
              ((riemannZeta.order (rho : ℂ) : ℂ) /
                (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖
            ≤ ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ * C := by
  obtain ⟨C, hC, hbound⟩ :=
    kadiri_moving_pole_principal_part_right_integral_bound a e he
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

/-- The off-segment moving-pole integrand is interval-integrable on the right segment. -/
theorem kadiri_moving_pole_principal_part_right_intervalIntegrable
    (a : ℝ) (A : ℂ) (T : ℝ) (rho : ℂ) (hT : rho.im ≠ T) :
    IntervalIntegrable
      (fun σ : ℝ => A / (((σ : ℂ) + (T : ℂ) * I) - rho))
      volume 0 (1 + a) := by
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
Right-segment finite-family version of the moving-pole zeta principal-part integral bound.

The endpoint-margin hypothesis is carried memberwise; a later selector must supply it for
the concrete truncated family used in the full-segment assembly.
-/
theorem kadiri_moving_pole_zeta_principal_part_finite_sum_right_integral_bound
    (a e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Finset NontrivialZeros) (T : ℝ),
        (∀ rho ∈ S,
          (rho : ℂ).re ∈ Set.Icc e (1 + a - e) ∧ (rho : ℂ).im ≠ T) →
          ‖∫ σ in 0..(1 + a), (
              ∑ rho ∈ S,
                ((riemannZeta.order (rho : ℂ) : ℂ) /
                  (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
            ≤ (∑ rho ∈ S, ‖(riemannZeta.order (rho : ℂ) : ℂ)‖) * C := by
  classical
  obtain ⟨C, hC, hsingle⟩ :=
    kadiri_moving_pole_zeta_principal_part_right_integral_bound a e he
  refine ⟨C, hC, ?_⟩
  intro S T hS
  let f : NontrivialZeros → ℝ → ℂ := fun rho σ =>
    ((riemannZeta.order (rho : ℂ) : ℂ) /
      (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))
  have hint : ∀ rho ∈ S, IntervalIntegrable (f rho) volume 0 (1 + a) := by
    intro rho hrho
    exact kadiri_moving_pole_principal_part_right_intervalIntegrable
      a ((riemannZeta.order (rho : ℂ) : ℂ)) T (rho : ℂ) (hS rho hrho).2
  have hintegral_sum :
      (∫ σ in 0..(1 + a), ∑ rho ∈ S, f rho σ) =
        ∑ rho ∈ S, ∫ σ in 0..(1 + a), f rho σ := by
    exact intervalIntegral.integral_finsetSum hint
  calc
    ‖∫ σ in 0..(1 + a), (
        ∑ rho ∈ S,
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
        = ‖∫ σ in 0..(1 + a), ∑ rho ∈ S, f rho σ‖ := by
          simp [f]
    _ = ‖∑ rho ∈ S, ∫ σ in 0..(1 + a), f rho σ‖ := by
          rw [hintegral_sum]
    _ ≤ ∑ rho ∈ S, ‖∫ σ in 0..(1 + a), f rho σ‖ :=
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

/--
Right-segment cardinality-budget form of the finite-family moving-pole bound.

The lower endpoint margin remains an explicit hypothesis instead of being hidden inside
the zero-counting budget.
-/
theorem kadiri_moving_pole_zeta_principal_part_finite_sum_right_integral_card_bound
    (a e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Finset NontrivialZeros) (T M : ℝ),
        (∀ rho ∈ S,
          (rho : ℂ).re ∈ Set.Icc e (1 + a - e) ∧ (rho : ℂ).im ≠ T) →
        (∀ rho ∈ S, ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ ≤ M) →
          ‖∫ σ in 0..(1 + a), (
              ∑ rho ∈ S,
                ((riemannZeta.order (rho : ℂ) : ℂ) /
                  (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
            ≤ ((S.card : ℝ) * M) * C := by
  classical
  obtain ⟨C, hC, hsum⟩ :=
    kadiri_moving_pole_zeta_principal_part_finite_sum_right_integral_bound a e he
  refine ⟨C, hC, ?_⟩
  intro S T M hS hM
  calc
    ‖∫ σ in 0..(1 + a), (
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

/--
Any finite family of non-trivial zeros has a positive real-part margin inside
`[0, 1 + a]`.
-/
theorem nontrivialZeros_finset_endpoint_margin_exists
    (a : ℝ) (ha : 0 ≤ a) (S : Finset NontrivialZeros) :
    ∃ e : ℝ, 0 < e ∧
      ∀ rho ∈ S, (rho : ℂ).re ∈ Set.Icc e (1 + a - e) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · refine ⟨1, by norm_num, ?_⟩
    intro rho hrho
    simp at hrho
  · intro rho0 S hrho0_notin ih
    obtain ⟨eS, heS, hS⟩ := ih
    let m : ℝ := min (rho0 : ℂ).re (1 + a - (rho0 : ℂ).re)
    have hm_pos : 0 < m := by
      have hre_pos : 0 < (rho0 : ℂ).re := rho0.property.1.1
      have hupper_pos : 0 < 1 + a - (rho0 : ℂ).re := by
        have hlt : (rho0 : ℂ).re < 1 := rho0.property.1.2
        linarith
      exact lt_min hre_pos hupper_pos
    refine ⟨min m eS, lt_min hm_pos heS, ?_⟩
    intro eta heta
    rcases Finset.mem_insert.mp heta with heta_eq | hetaS
    · subst eta
      constructor
      · exact le_trans (min_le_left m eS)
          (min_le_left (rho0 : ℂ).re (1 + a - (rho0 : ℂ).re))
      · have hle : min m eS ≤ 1 + a - (rho0 : ℂ).re :=
          le_trans (min_le_left m eS)
            (min_le_right (rho0 : ℂ).re (1 + a - (rho0 : ℂ).re))
        linarith
    · have heta_margin := hS eta hetaS
      constructor
      · exact le_trans (min_le_right m eS) heta_margin.1
      · linarith [min_le_right m eS, heta_margin.2]

/-- The absolute-height truncated zero family has a positive right-segment endpoint margin. -/
theorem kadiriTruncatedNontrivialZeros_endpoint_margin_exists
    (a R : ℝ) (ha : 0 ≤ a) :
    ∃ e : ℝ, 0 < e ∧
      ∀ rho : NontrivialZeros, |(rho : ℂ).im| < R →
        (rho : ℂ).re ∈ Set.Icc e (1 + a - e) := by
  obtain ⟨e, he, hS⟩ :=
    nontrivialZeros_finset_endpoint_margin_exists
      a ha (kadiriTruncatedNontrivialZeros R)
  refine ⟨e, he, ?_⟩
  intro rho hrho
  exact hS rho ((mem_kadiriTruncatedNontrivialZeros (R := R) (rho := rho)).mpr hrho)

/--
The Kadiri terminal shift `A / log |T|^9` is eventually smaller than any positive
fixed margin.
-/
theorem eventually_const_div_log_abs_pow_lt_atTop (A e : ℝ) (he : 0 < e) :
    ∀ᶠ T : ℝ in Filter.atTop, A / Real.log |T| ^ (9 : ℕ) < e := by
  have hlog_abs :
      Filter.Tendsto (fun T : ℝ => Real.log |T|) Filter.atTop Filter.atTop := by
    exact Real.tendsto_log_atTop.comp tendsto_norm_atTop_atTop
  have hden :
      Filter.Tendsto (fun T : ℝ => Real.log |T| ^ (9 : ℕ))
        Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop (by norm_num : (9 : ℕ) ≠ 0)).comp hlog_abs
  have hratio :
      Filter.Tendsto (fun T : ℝ => A / Real.log |T| ^ (9 : ℕ))
        Filter.atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  exact hratio.eventually (gt_mem_nhds he)

/--
For a fixed dyadic truncation, all retained non-trivial zeros eventually lie strictly
to the left of Kadiri's moving terminal line `1 - A / log |T|^9`.

This is the right-boundary selector needed before the terminal right-half-plane estimate
can be combined with the finite moving-pole principal block.
-/
theorem eventually_kadiri_truncated_zero_family_left_of_log_terminal_on_filter
    (A : ℝ) (k : ℕ) (L : Filter ℝ) (hL : L ≤ Filter.atTop) :
    ∀ᶠ T : ℝ in L,
      ∀ rho : NontrivialZeros,
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1) →
          (rho : ℂ).re < 1 - A / Real.log |T| ^ (9 : ℕ) := by
  let R : ℝ := (2 : ℝ) ^ (k + 1)
  obtain ⟨e, he, hmargin⟩ :=
    kadiriTruncatedNontrivialZeros_endpoint_margin_exists 0 R (by norm_num)
  filter_upwards [(eventually_const_div_log_abs_pow_lt_atTop A e he).filter_mono hL]
    with T hshift rho hrho
  have hright : (rho : ℂ).re ≤ 1 - e := by
    have h := hmargin rho (by simpa [R] using hrho)
    linarith [h.2]
  linarith

/--
Quantitative form of the dyadic right-boundary selector.  For a fixed dyadic truncation,
large heights eventually leave a positive real gap between every retained zero and the
moving terminal line `1 - A / log |T|^9`.
-/
theorem eventually_kadiri_truncated_zero_family_gap_left_of_log_terminal_on_filter
    (A : ℝ) (k : ℕ) (L : Filter ℝ) (hL : L ≤ Filter.atTop) :
    ∃ d : ℝ, 0 < d ∧
      ∀ᶠ T : ℝ in L,
        ∀ rho : NontrivialZeros,
          |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1) →
            (rho : ℂ).re + d ≤ 1 - A / Real.log |T| ^ (9 : ℕ) := by
  let R : ℝ := (2 : ℝ) ^ (k + 1)
  obtain ⟨e, he, hmargin⟩ :=
    kadiriTruncatedNontrivialZeros_endpoint_margin_exists 0 R (by norm_num)
  refine ⟨e / 2, half_pos he, ?_⟩
  filter_upwards [(eventually_const_div_log_abs_pow_lt_atTop A (e / 2) (half_pos he)).filter_mono hL]
    with T hshift rho hrho
  have hright : (rho : ℂ).re ≤ 1 - e := by
    have h := hmargin rho (by simpa [R] using hrho)
    linarith [h.2]
  linarith

/-- Any finite family of non-trivial zeros has a finite multiplicity-norm cap. -/
theorem nontrivialZeros_finset_order_norm_bound_exists
    (S : Finset NontrivialZeros) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ rho ∈ S, ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ ≤ M := by
  classical
  refine Finset.induction_on S ?_ ?_
  · refine ⟨0, by norm_num, ?_⟩
    intro rho hrho
    simp at hrho
  · intro rho0 S hrho0_notin ih
    obtain ⟨M, hM_nonneg, hS⟩ := ih
    refine ⟨max ‖(riemannZeta.order (rho0 : ℂ) : ℂ)‖ M, ?_, ?_⟩
    · exact le_trans (norm_nonneg _) (le_max_left _ _)
    · intro eta heta
      rcases Finset.mem_insert.mp heta with heta_eq | hetaS
      · subst eta
        exact le_max_left _ _
      · exact le_trans (hS eta hetaS) (le_max_right _ _)

/-- The absolute-height truncated zero family has a finite multiplicity-norm cap. -/
theorem kadiriTruncatedNontrivialZeros_order_norm_bound_exists
    (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ rho : NontrivialZeros, |(rho : ℂ).im| < R →
        ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ ≤ M := by
  obtain ⟨M, hM_nonneg, hS⟩ :=
    nontrivialZeros_finset_order_norm_bound_exists (kadiriTruncatedNontrivialZeros R)
  refine ⟨M, hM_nonneg, ?_⟩
  intro rho hrho
  exact hS rho ((mem_kadiriTruncatedNontrivialZeros (R := R) (rho := rho)).mpr hrho)

/-- For a non-trivial zero, the complex norm of the zeta order is its real order. -/
theorem kadiri_nontrivial_zero_zeta_order_norm_eq (rho : NontrivialZeros) :
    ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ =
      ((riemannZeta.order (rho : ℂ) : ℤ) : ℝ) := by
  have hordZ : (0 : ℤ) ≤ riemannZeta.order (rho : ℂ) :=
    riemannZeta_order_nonneg (nontrivialZero_ne_one rho)
  rw [Complex.norm_intCast]
  exact_mod_cast abs_of_nonneg hordZ

/-- The local zero window's order-norm budget is bounded by the Jensen local count atom. -/
theorem kadiriLocalZeroWindow_orderNorm_sum_le_nearbyZeroCount {T : ℝ} (hT : 3 ≤ |T|) :
    (∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
        ‖(riemannZeta.order (rho : ℂ) : ℂ)‖) ≤
      u6aNearbyZeroCount (-1) 2 T := by
  classical
  let L : Finset NontrivialZeros := (kadiriLocalZeroWindow_finite T).toFinset
  let N : Finset ℂ := (u6aFTNearbyWindow_finite T).toFinset
  have hcount := riemannZeta.zeroes_sum_eq_finset_of_finite
    (I := Set.uIcc (-1 : ℝ) 2) (J := Set.Icc (T - 1) (T + 1))
    (fun _ => (1 : ℝ)) (u6aFTNearbyWindow_finite T)
  have hcount_finset :
      u6aNearbyZeroCount (-1) 2 T =
        ∑ z ∈ N, ((riemannZeta.order z : ℤ) : ℝ) := by
    simpa [u6aNearbyZeroCount, N] using hcount
  have himage_subset : L.image (fun rho : NontrivialZeros => (rho : ℂ)) ⊆ N := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨rho, hrhoL, rfl⟩ := hz
    dsimp [L] at hrhoL
    have hrho : rho ∈ kadiriLocalZeroWindow T :=
      (kadiriLocalZeroWindow_finite T).mem_toFinset.mp hrhoL
    rw [kadiriLocalZeroWindow, Set.mem_setOf_eq] at hrho
    dsimp [N]
    rw [(u6aFTNearbyWindow_finite T).mem_toFinset]
    unfold u6aFTNearbyWindow riemannZeta.zeroes_rect
    have him_abs := abs_le.mp hrho
    refine ⟨?_, ?_, riemannZeta_nontrivialZero_zero rho⟩
    · rw [Set.mem_uIcc]
      exact Or.inl ⟨by linarith [rho.property.1.1], by linarith [rho.property.1.2]⟩
    · exact ⟨by linarith [him_abs.1], by linarith [him_abs.2]⟩
  have hsum_image :
      (∑ rho ∈ L, ((riemannZeta.order (rho : ℂ) : ℤ) : ℝ)) =
        ∑ z ∈ L.image (fun rho : NontrivialZeros => (rho : ℂ)),
          ((riemannZeta.order z : ℤ) : ℝ) := by
    rw [Finset.sum_image]
    intro rho _ eta _ hcast
    exact Subtype.ext hcast
  have hnonneg_N : ∀ z ∈ N, 0 ≤ ((riemannZeta.order z : ℤ) : ℝ) := by
    intro z hz
    dsimp [N] at hz
    have hzmem : z ∈ u6aFTNearbyWindow T :=
      (u6aFTNearbyWindow_finite T).mem_toFinset.mp hz
    unfold u6aFTNearbyWindow riemannZeta.zeroes_rect at hzmem
    obtain ⟨_hre, him, _hζ⟩ := hzmem
    have hzne1 : z ≠ 1 := by
      intro h1
      rw [h1] at him
      have him0 : (0 : ℝ) ∈ Set.Icc (T - 1) (T + 1) := by
        simpa using him
      have hTabs : |T| ≤ 1 := abs_le.mpr ⟨by linarith [him0.2], by linarith [him0.1]⟩
      linarith
    exact_mod_cast riemannZeta_order_nonneg hzne1
  have hsum_le :
      (∑ z ∈ L.image (fun rho : NontrivialZeros => (rho : ℂ)),
          ((riemannZeta.order z : ℤ) : ℝ)) ≤
        ∑ z ∈ N, ((riemannZeta.order z : ℤ) : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset
      (fun z hzN _hzNot => hnonneg_N z hzN)
  calc
    (∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
        ‖(riemannZeta.order (rho : ℂ) : ℂ)‖)
        = ∑ rho ∈ L, ((riemannZeta.order (rho : ℂ) : ℤ) : ℝ) := by
          dsimp [L]
          refine Finset.sum_congr rfl fun rho _hrho => ?_
          exact kadiri_nontrivial_zero_zeta_order_norm_eq rho
    _ = ∑ z ∈ L.image (fun rho : NontrivialZeros => (rho : ℂ)),
          ((riemannZeta.order z : ℤ) : ℝ) := hsum_image
    _ ≤ ∑ z ∈ N, ((riemannZeta.order z : ℤ) : ℝ) := hsum_le
    _ = u6aNearbyZeroCount (-1) 2 T := hcount_finset.symm

/--
Pointwise finite-principal-part control from a quantitative height gap.

At a selected good height, every zero in the local window is at ordinate distance at least
`η`, so the whole local principal block is bounded by `η⁻¹` times the order-weighted
local zero count.
-/
theorem kadiri_local_principal_part_pointwise_bound_of_gap_and_count {η T σ : ℝ}
    (hη : 0 < η) (hT : 3 ≤ |T|)
    (hgap : ∀ rho : NontrivialZeros, rho ∈ kadiriLocalZeroWindow T →
      η < |T - (rho : ℂ).im|) :
    ‖∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
        ((riemannZeta.order (rho : ℂ) : ℂ) /
          (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖ ≤
      η⁻¹ * u6aNearbyZeroCount (-1) 2 T := by
  classical
  let S : Finset NontrivialZeros := (kadiriLocalZeroWindow_finite T).toFinset
  have hterm : ∀ rho ∈ S,
      ‖((riemannZeta.order (rho : ℂ) : ℂ) /
          (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖ ≤
        η⁻¹ * ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ := by
    intro rho hrho
    have hrho_window : rho ∈ kadiriLocalZeroWindow T := by
      dsimp [S] at hrho
      exact (kadiriLocalZeroWindow_finite T).mem_toFinset.mp hrho
    let z : ℂ := ((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)
    have hz_im : z.im = T - (rho : ℂ).im := by
      simp [z]
    have hgap_rho : η < |z.im| := by
      rw [hz_im]
      simpa [abs_sub_comm] using hgap rho hrho_window
    have hz_norm_ge : η ≤ ‖z‖ := le_trans hgap_rho.le (Complex.abs_im_le_norm z)
    have hdiv :
        ‖((riemannZeta.order (rho : ℂ) : ℂ) / z)‖ =
          ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ / ‖z‖ := by
      rw [norm_div]
    rw [show (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)) = z by rfl, hdiv]
    rw [div_eq_mul_inv]
    calc
      ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ * ‖z‖⁻¹
          ≤ ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ * η⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ hη hz_norm_ge)
              (norm_nonneg ((riemannZeta.order (rho : ℂ) : ℂ)))
      _ = η⁻¹ * ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ := by ring
  calc
    ‖∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
        ((riemannZeta.order (rho : ℂ) : ℂ) /
          (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖
        ≤ ∑ rho ∈ S,
            ‖((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖ := by
          dsimp [S]
          exact norm_sum_le _ _
    _ ≤ ∑ rho ∈ S, η⁻¹ * ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ :=
          Finset.sum_le_sum hterm
    _ = η⁻¹ * (∑ rho ∈ S, ‖(riemannZeta.order (rho : ℂ) : ℂ)‖) := by
          rw [Finset.mul_sum]
    _ ≤ η⁻¹ * u6aNearbyZeroCount (-1) 2 T :=
          mul_le_mul_of_nonneg_left
            (by simpa [S] using
              kadiriLocalZeroWindow_orderNorm_sum_le_nearbyZeroCount (T := T) hT)
            (inv_nonneg.mpr hη.le)

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
For any filter finer than `cofinite`, the truncated zero family has a selected endpoint
margin and eventually avoids the moving horizontal height.
-/
theorem
    eventually_kadiri_truncated_zero_family_endpoint_margin_and_off_height_on_filter
    (a R : ℝ) (ha : 0 ≤ a) (L : Filter ℝ) (hL : L ≤ Filter.cofinite) :
    ∃ e : ℝ, 0 < e ∧
      ∀ᶠ T : ℝ in L,
        ∀ rho : NontrivialZeros, |(rho : ℂ).im| < R →
          (rho : ℂ).re ∈ Set.Icc e (1 + a - e) ∧ (rho : ℂ).im ≠ T := by
  obtain ⟨e, he, hmargin⟩ :=
    kadiriTruncatedNontrivialZeros_endpoint_margin_exists a R ha
  refine ⟨e, he, ?_⟩
  filter_upwards [(kadiri_truncated_zero_family_eventually_off_height R).filter_mono hL]
    with T hoff
  intro rho hrho
  exact ⟨hmargin rho hrho, hoff rho hrho⟩

/--
Dyadic selector for the right-segment principal budget: a real endpoint margin, eventual
off-height deletion, and a finite multiplicity-norm cap for the truncated zero family.
-/
theorem
    kadiri_dyadic_truncated_zero_family_margin_and_multiplicity_selector_on_filter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (L : Filter ℝ) (hL : L ≤ Filter.cofinite) :
    ∃ e M : ℝ, 0 < e ∧ 0 ≤ M ∧
      (∀ᶠ T : ℝ in L,
        ∀ rho : NontrivialZeros,
          |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1) →
            (rho : ℂ).re ∈ Set.Icc e (1 + a - e) ∧ (rho : ℂ).im ≠ T) ∧
      (∀ rho : NontrivialZeros,
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1) →
          ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ ≤ M) := by
  let R : ℝ := (2 : ℝ) ^ (k + 1)
  obtain ⟨e, he, hmargin_off⟩ :=
    eventually_kadiri_truncated_zero_family_endpoint_margin_and_off_height_on_filter
      a R ha L hL
  obtain ⟨M, hM_nonneg, hM⟩ :=
    kadiriTruncatedNontrivialZeros_order_norm_bound_exists R
  refine ⟨e, M, he, hM_nonneg, ?_, ?_⟩
  · simpa [R] using hmargin_off
  · simpa [R] using hM

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

/--
Sign-correct dyadic zeta logarithmic-derivative remainder after subtracting the truncated
zero principal part from `ζ'/ζ`.

The concrete Kadiri integrand is `-ζ'/ζ`; this auxiliary keeps the analytic zero-local
sign, so the local Hadamard/PV remainder estimates apply directly.
-/
noncomputable def kadiriDyadicZetaLogDerivPVRemainder (k : ℕ) (T σ : ℝ) : ℂ :=
  deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
      riemannZeta (((σ : ℂ) + (T : ℂ) * I)) -
    ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
      ((riemannZeta.order (rho : ℂ) : ℂ) /
        (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))

/-- Complex-plane version of the sign-correct dyadic zeta Hadamard/PV remainder. -/
noncomputable def kadiriDyadicZetaLogDerivPVRemainderComplex (k : ℕ) (s : ℂ) : ℂ :=
  deriv riemannZeta s / riemannZeta s -
    ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
      ((riemannZeta.order (rho : ℂ) : ℂ) / (s - (rho : ℂ)))

/-- The real horizontal sign-correct remainder is the complex remainder on the line. -/
theorem kadiriDyadicZetaLogDerivPVRemainder_eq_complex (k : ℕ) (T σ : ℝ) :
    kadiriDyadicZetaLogDerivPVRemainder k T σ =
      kadiriDyadicZetaLogDerivPVRemainderComplex k (((σ : ℂ) + (T : ℂ) * I)) := by
  rfl

/--
At every zero retained by the dyadic truncation, the sign-correct finite Hadamard/PV
remainder is locally bounded after the pole at that zero is subtracted.

The single-zero analytic input is
`kadiri_logDeriv_zeta_hadamard_pv_remainder_bound`; all other retained zero terms are
ordinary continuous functions near this zero.
-/
theorem kadiriDyadicZetaLogDerivPVRemainderComplex_isBigO_at_truncated_zero
    (k : ℕ) {rho : NontrivialZeros}
    (hrho : rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))) :
    kadiriDyadicZetaLogDerivPVRemainderComplex k =O[𝓝[≠] (rho : ℂ)]
      (1 : ℂ → ℂ) := by
  classical
  let S : Finset NontrivialZeros :=
    kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))
  let poleTerm : NontrivialZeros → ℂ → ℂ := fun eta s =>
    ((riemannZeta.order (eta : ℂ) : ℂ) / (s - (eta : ℂ)))
  have hlocal :
      ((deriv riemannZeta / riemannZeta) - fun s : ℂ => poleTerm rho s)
        =O[𝓝[≠] (rho : ℂ)] (1 : ℂ → ℂ) := by
    simpa [poleTerm] using kadiri_logDeriv_zeta_hadamard_pv_remainder_bound rho
  have htail :
      (fun s : ℂ => ∑ eta ∈ S.erase rho, poleTerm eta s)
        =O[𝓝[≠] (rho : ℂ)] (1 : ℂ → ℂ) := by
    refine Asymptotics.IsBigO.sum fun eta heta => ?_
    have heta_ne : eta ≠ rho := (Finset.mem_erase.mp heta).1
    have hval_ne : (rho : ℂ) ≠ (eta : ℂ) := by
      intro hval
      apply heta_ne
      ext
      exact hval.symm
    have hcont :
        ContinuousAt (fun s : ℂ => poleTerm eta s) (rho : ℂ) := by
      exact continuousAt_const.div
        (continuousAt_id.sub continuousAt_const)
        (by simpa [poleTerm, sub_ne_zero] using hval_ne)
    exact Asymptotics.IsBigO.mono
      (hcont.norm.isBoundedUnder_le.isBigO_one ℂ) nhdsWithin_le_nhds
  have hdecomp :
      kadiriDyadicZetaLogDerivPVRemainderComplex k =ᶠ[𝓝[≠] (rho : ℂ)]
        fun s : ℂ =>
          ((deriv riemannZeta / riemannZeta) s - poleTerm rho s) -
            ∑ eta ∈ S.erase rho, poleTerm eta s := by
    exact Filter.Eventually.of_forall fun s => by
      have hsum :
          poleTerm rho s + (∑ eta ∈ S.erase rho, poleTerm eta s) =
            ∑ eta ∈ S, poleTerm eta s := by
        exact Finset.add_sum_erase S (fun eta => poleTerm eta s) (by simpa [S] using hrho)
      change deriv riemannZeta s / riemannZeta s - (∑ eta ∈ S, poleTerm eta s) =
        (deriv riemannZeta / riemannZeta) s - poleTerm rho s -
          ∑ eta ∈ S.erase rho, poleTerm eta s
      calc
        deriv riemannZeta s / riemannZeta s - (∑ eta ∈ S, poleTerm eta s)
            = deriv riemannZeta s / riemannZeta s -
                (poleTerm rho s + ∑ eta ∈ S.erase rho, poleTerm eta s) := by
              exact congrArg (fun z => deriv riemannZeta s / riemannZeta s - z) hsum.symm
        _ = (deriv riemannZeta / riemannZeta) s - poleTerm rho s -
              ∑ eta ∈ S.erase rho, poleTerm eta s := by
              simp only [Pi.div_apply]
              abel_nf
  exact hdecomp.trans_isBigO (hlocal.sub htail)

/--
At a retained dyadic zero, the sign-correct finite Hadamard/PV remainder has an explicit
local punctured-neighborhood norm bound.
-/
theorem kadiriDyadicZetaLogDerivPVRemainderComplex_eventually_norm_le_at_truncated_zero
    (k : ℕ) {rho : NontrivialZeros}
    (hrho : rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ s in 𝓝[≠] (rho : ℂ),
        ‖kadiriDyadicZetaLogDerivPVRemainderComplex k s‖ ≤ C := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    (kadiriDyadicZetaLogDerivPVRemainderComplex_isBigO_at_truncated_zero
      k hrho).exists_nonneg
  refine ⟨C, hC_nonneg, ?_⟩
  filter_upwards [hC.bound] with s hs
  simpa using hs

/--
One finite norm constant controls the local punctured-neighborhood bounds at every zero
retained by a fixed dyadic truncation.

The neighborhoods may still depend on the zero; this is the finite-family local Hadamard/PV
input before any global critical-strip covering argument.
-/
theorem
    kadiriDyadicZetaLogDerivPVRemainderComplex_truncated_zero_uniform_eventually_norm_bound
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
        ∀ᶠ s in 𝓝[≠] (rho : ℂ),
          ‖kadiriDyadicZetaLogDerivPVRemainderComplex k s‖ ≤ C := by
  classical
  let S : Finset NontrivialZeros := kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))
  have hlocal : ∀ rho ∈ S, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ s in 𝓝[≠] (rho : ℂ),
        ‖kadiriDyadicZetaLogDerivPVRemainderComplex k s‖ ≤ C := by
    intro rho hrho
    exact kadiriDyadicZetaLogDerivPVRemainderComplex_eventually_norm_le_at_truncated_zero
      k (by simpa [S] using hrho)
  let C0 : NontrivialZeros → ℝ := fun rho =>
    if h : rho ∈ S then Classical.choose (hlocal rho h) else 0
  have hC0_nonneg : ∀ rho ∈ S, 0 ≤ C0 rho := by
    intro rho hrho
    have hspec := Classical.choose_spec (hlocal rho hrho)
    simpa [C0, hrho] using hspec.1
  have hC0_event : ∀ rho ∈ S,
      ∀ᶠ s in 𝓝[≠] (rho : ℂ),
        ‖kadiriDyadicZetaLogDerivPVRemainderComplex k s‖ ≤ C0 rho := by
    intro rho hrho
    have hspec := Classical.choose_spec (hlocal rho hrho)
    simpa [C0, hrho] using hspec.2
  let C : ℝ := ∑ rho ∈ S, C0 rho
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact Finset.sum_nonneg fun rho hrho => hC0_nonneg rho hrho
  · intro rho hrho
    have hle : C0 rho ≤ C := by
      dsimp [C]
      exact Finset.single_le_sum (fun eta heta => hC0_nonneg eta heta)
        (by simpa [S] using hrho)
    filter_upwards [hC0_event rho (by simpa [S] using hrho)] with s hs
    exact hs.trans hle

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

/--
Large positive heights, restricted to the horizontal lines that avoid `0` and the
non-trivial zero ordinates.
-/
noncomputable def kadiriLargeHorizontalZetaOffPoleFilter : Filter ℝ :=
  Filter.atTop ⊓ 𝓟 {T : ℝ | kadiriHorizontalZetaOffPoleHeight T}

/-- The large off-pole filter is finer than the cofinite filter. -/
theorem kadiriLargeHorizontalZetaOffPoleFilter_le_cofinite :
    kadiriLargeHorizontalZetaOffPoleFilter ≤ Filter.cofinite := by
  exact le_trans inf_le_left Filter.atTop_le_cofinite

/-- The large off-pole filter is finer than `atTop`. -/
theorem kadiriLargeHorizontalZetaOffPoleFilter_le_atTop :
    kadiriLargeHorizontalZetaOffPoleFilter ≤ Filter.atTop := by
  exact inf_le_left

/-- Along the large off-pole filter, `3 < |T|` eventually holds. -/
theorem eventually_kadiriLargeHorizontalZetaOffPoleFilter_large :
    ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter, 3 < |T| := by
  have htop : ∀ᶠ T : ℝ in Filter.atTop, 3 < |T| := by
    filter_upwards [Filter.eventually_gt_atTop (3 : ℝ)] with T hT
    exact lt_of_lt_of_le hT (le_abs_self T)
  exact htop.filter_mono inf_le_left

/-- Along the large off-pole filter, the off-pole height condition holds by definition. -/
theorem eventually_kadiriLargeHorizontalZetaOffPoleHeight :
    ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      kadiriHorizontalZetaOffPoleHeight T := by
  have hprincipal :
      ∀ᶠ T : ℝ in 𝓟 {T : ℝ | kadiriHorizontalZetaOffPoleHeight T},
        kadiriHorizontalZetaOffPoleHeight T :=
    Filter.mem_principal_self _
  exact hprincipal.filter_mono inf_le_right

/-- A quantitative dyadic zero-ordinate gap implies the selected horizontal height is
off-pole for the zeta logarithmic derivative. -/
theorem kadiriHorizontalZetaOffPoleHeight_of_dyadic_gap {X η T : ℝ}
    (hX : 0 < X) (hη : 0 ≤ η)
    (hT : T ∈ Set.Ioc X (2 * X))
    (hgap : ∀ rho : NontrivialZeros, rho ∈ kadiriDyadicZeroWindow X →
      η < |T - (rho : ℂ).im|) :
    kadiriHorizontalZetaOffPoleHeight T := by
  constructor
  · intro hT0
    have hTX : X < T := hT.1
    linarith
  · intro rho him
    have hrho_window : rho ∈ kadiriDyadicZeroWindow X := by
      rw [kadiriDyadicZeroWindow, Set.mem_setOf_eq]
      rw [him]
      exact ⟨by linarith [hT.1], by linarith [hT.2]⟩
    have hgap_rho := hgap rho hrho_window
    rw [him] at hgap_rho
    simp at hgap_rho
    linarith

/--
Endpoint-facing selectable-radius form of the dyadic good-height selector.  Once the
zero-count source is available, callers may choose any `η ≤ c / log(2^k)` and get a
large off-pole height with both dyadic and local zero-window gaps.
-/
theorem exists_kadiriDyadicGoodHeightSelector_of_le_logRadius_offPole
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      ∀ η : ℝ, 0 ≤ η →
        η ≤ c / Real.log ((2 : ℝ) ^ k) →
          ∃ T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)),
            kadiriHorizontalZetaOffPoleHeight T ∧
              (∀ rho : NontrivialZeros, rho ∈ kadiriDyadicZeroWindow ((2 : ℝ) ^ k) →
                η < |T - (rho : ℂ).im|) ∧
              (∀ rho : NontrivialZeros, rho ∈ kadiriLocalZeroWindow T →
                η < |T - (rho : ℂ).im|) := by
  obtain ⟨c, hc, hsel⟩ := exists_kadiriDyadicGoodHeightSelector_of_le_logRadius hsrc
  refine ⟨c, hc, ?_⟩
  filter_upwards [hsel] with k hsel_k η hη hη_le
  obtain ⟨T, hT, hgap⟩ := hsel_k η hη hη_le
  refine ⟨T, hT, ?_, hgap, ?_⟩
  · exact kadiriHorizontalZetaOffPoleHeight_of_dyadic_gap
      (X := (2 : ℝ) ^ k) (η := η) (T := T) (pow_pos (by norm_num) k) hη hT hgap
  · exact kadiriLocalZeroWindow_gap_of_dyadic_gap (X := (2 : ℝ) ^ k)
      (η := η) (T := T) hT hgap

/-- Endpoint-facing form of the dyadic good-height selector: the selected heights are
large dyadic heights, quantitatively separated from the relevant zero ordinates, and
already satisfy the off-pole predicate used by the full-segment layer. -/
theorem exists_kadiriDyadicGoodHeightSelector_logRadius_offPole
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      ∃ T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)),
        kadiriHorizontalZetaOffPoleHeight T ∧
          (∀ rho : NontrivialZeros, rho ∈ kadiriDyadicZeroWindow ((2 : ℝ) ^ k) →
            c / Real.log ((2 : ℝ) ^ k) < |T - (rho : ℂ).im|) ∧
          (∀ rho : NontrivialZeros, rho ∈ kadiriLocalZeroWindow T →
            c / Real.log ((2 : ℝ) ^ k) < |T - (rho : ℂ).im|) := by
  obtain ⟨c, hc, hsel⟩ := exists_kadiriDyadicGoodHeightSelector_logRadius hsrc
  refine ⟨c, hc, ?_⟩
  filter_upwards [hsel, Filter.eventually_ge_atTop (1 : ℕ)] with k hsel_k hk
  obtain ⟨T, hT, hgap⟩ := hsel_k
  refine ⟨T, hT, ?_, hgap, ?_⟩
  · have hXpos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
    have hk_ne : k ≠ 0 := by omega
    have hX_gt_one : 1 < (2 : ℝ) ^ k :=
      one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) hk_ne
    have hlog_pos : 0 < Real.log ((2 : ℝ) ^ k) := Real.log_pos hX_gt_one
    have hη : 0 ≤ c / Real.log ((2 : ℝ) ^ k) := div_nonneg hc.le hlog_pos.le
    exact kadiriHorizontalZetaOffPoleHeight_of_dyadic_gap
      (X := (2 : ℝ) ^ k) (η := c / Real.log ((2 : ℝ) ^ k)) (T := T)
      hXpos hη hT hgap
  · exact kadiriLocalZeroWindow_gap_of_dyadic_gap (X := (2 : ℝ) ^ k)
      (η := c / Real.log ((2 : ℝ) ^ k)) (T := T) hT hgap

/-- The radius constant selected by the concrete dyadic good-height construction. -/
noncomputable def kadiriDyadicGoodHeightRadius
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) : ℝ :=
  Classical.choose (exists_kadiriDyadicGoodHeightSelector_logRadius_offPole hsrc)

theorem kadiriDyadicGoodHeightRadius_pos
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    0 < kadiriDyadicGoodHeightRadius hsrc := by
  exact (Classical.choose_spec
    (exists_kadiriDyadicGoodHeightSelector_logRadius_offPole hsrc)).1

/-- The full dyadic good-height package at level `k` for a selected height `T`. -/
def kadiriDyadicGoodHeightSequenceSpec
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) (k : ℕ) (T : ℝ) : Prop :=
  T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)) ∧
    kadiriHorizontalZetaOffPoleHeight T ∧
      (∀ rho : NontrivialZeros, rho ∈ kadiriDyadicZeroWindow ((2 : ℝ) ^ k) →
        kadiriDyadicGoodHeightRadius hsrc / Real.log ((2 : ℝ) ^ k) <
          |T - (rho : ℂ).im|) ∧
      (∀ rho : NontrivialZeros, rho ∈ kadiriLocalZeroWindow T →
        kadiriDyadicGoodHeightRadius hsrc / Real.log ((2 : ℝ) ^ k) <
          |T - (rho : ℂ).im|)

theorem eventually_exists_kadiriDyadicGoodHeightSequenceSpec
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    ∀ᶠ k : ℕ in atTop,
      ∃ T : ℝ, kadiriDyadicGoodHeightSequenceSpec hsrc k T := by
  have hsel :=
    (Classical.choose_spec
      (exists_kadiriDyadicGoodHeightSelector_logRadius_offPole hsrc)).2
  filter_upwards [hsel] with k hk
  obtain ⟨T, hT, hoff, hgap_dyadic, hgap_local⟩ := hk
  exact ⟨T, hT, hoff, hgap_dyadic, hgap_local⟩

/--
A noncomputable selected good-height sequence, choosing one certified height from each
large dyadic level and falling back to the left endpoint before the selector starts.
-/
noncomputable def kadiriDyadicGoodHeightSequence
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) (k : ℕ) : ℝ :=
  by
    classical
    exact
      if h : ∃ T : ℝ, kadiriDyadicGoodHeightSequenceSpec hsrc k T then
        Classical.choose h
      else
        (2 : ℝ) ^ k

theorem eventually_kadiriDyadicGoodHeightSequence_spec
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    ∀ᶠ k : ℕ in atTop,
      kadiriDyadicGoodHeightSequenceSpec hsrc k
        (kadiriDyadicGoodHeightSequence hsrc k) := by
  filter_upwards [eventually_exists_kadiriDyadicGoodHeightSequenceSpec hsrc] with k hk
  have hchoose := Classical.choose_spec hk
  simpa [kadiriDyadicGoodHeightSequence, hk] using hchoose

theorem tendsto_kadiriDyadicGoodHeightSequence_atTop
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    Tendsto (kadiriDyadicGoodHeightSequence hsrc) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro B
  have hpow : ∀ᶠ k : ℕ in atTop, B ≤ (2 : ℝ) ^ k :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually
      (Filter.eventually_ge_atTop B)
  filter_upwards [eventually_kadiriDyadicGoodHeightSequence_spec hsrc, hpow]
    with k hspec hpowk
  exact hpowk.trans hspec.1.1.le

/-- The good-height filter obtained from the selected dyadic good-height sequence. -/
noncomputable def kadiriDyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) : Filter ℝ :=
  Filter.map (kadiriDyadicGoodHeightSequence hsrc) atTop

theorem kadiriDyadicGoodHeightFilter_le_atTop
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    kadiriDyadicGoodHeightFilter hsrc ≤ atTop := by
  simpa [kadiriDyadicGoodHeightFilter] using
    tendsto_kadiriDyadicGoodHeightSequence_atTop hsrc

theorem eventually_kadiriDyadicGoodHeightFilter_offPole
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
      kadiriHorizontalZetaOffPoleHeight T := by
  rw [kadiriDyadicGoodHeightFilter]
  change ∀ᶠ k : ℕ in atTop,
    kadiriHorizontalZetaOffPoleHeight (kadiriDyadicGoodHeightSequence hsrc k)
  exact
    (eventually_kadiriDyadicGoodHeightSequence_spec hsrc).mono
      (fun _ hspec => hspec.2.1)

theorem eventually_kadiriDyadicGoodHeightFilter_scale
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
      ∃ k : ℕ,
        T = kadiriDyadicGoodHeightSequence hsrc k ∧
          T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)) := by
  rw [kadiriDyadicGoodHeightFilter]
  change ∀ᶠ n : ℕ in atTop,
    ∃ k : ℕ,
      kadiriDyadicGoodHeightSequence hsrc n = kadiriDyadicGoodHeightSequence hsrc k ∧
        kadiriDyadicGoodHeightSequence hsrc n ∈
          Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k))
  filter_upwards [eventually_kadiriDyadicGoodHeightSequence_spec hsrc] with k hspec
  exact ⟨k, rfl, hspec.1⟩

theorem eventually_kadiriDyadicGoodHeightFilter_localGap
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
      ∃ k : ℕ,
        T = kadiriDyadicGoodHeightSequence hsrc k ∧
          ∀ rho : NontrivialZeros, rho ∈ kadiriLocalZeroWindow T →
            kadiriDyadicGoodHeightRadius hsrc / Real.log ((2 : ℝ) ^ k) <
              |T - (rho : ℂ).im| := by
  rw [kadiriDyadicGoodHeightFilter]
  change ∀ᶠ n : ℕ in atTop,
    ∃ k : ℕ,
      kadiriDyadicGoodHeightSequence hsrc n = kadiriDyadicGoodHeightSequence hsrc k ∧
        ∀ rho : NontrivialZeros,
          rho ∈ kadiriLocalZeroWindow (kadiriDyadicGoodHeightSequence hsrc n) →
            kadiriDyadicGoodHeightRadius hsrc / Real.log ((2 : ℝ) ^ k) <
              |kadiriDyadicGoodHeightSequence hsrc n - (rho : ℂ).im|
  filter_upwards [eventually_kadiriDyadicGoodHeightSequence_spec hsrc] with k hspec
  exact ⟨k, rfl, hspec.2.2.2⟩

/--
The selected dyadic sequence also serves any requested radius below the concrete
`c / log(2^k)` budget.
-/
theorem eventually_kadiriDyadicGoodHeightSequence_spec_of_le_logRadius
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) {η : ℕ → ℝ}
    (hη_le : ∀ᶠ k : ℕ in atTop,
      η k ≤ kadiriDyadicGoodHeightRadius hsrc / Real.log ((2 : ℝ) ^ k)) :
    ∀ᶠ k : ℕ in atTop,
      kadiriDyadicGoodHeightSequence hsrc k ∈
          Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)) ∧
        kadiriHorizontalZetaOffPoleHeight (kadiriDyadicGoodHeightSequence hsrc k) ∧
          (∀ rho : NontrivialZeros, rho ∈ kadiriDyadicZeroWindow ((2 : ℝ) ^ k) →
            η k < |kadiriDyadicGoodHeightSequence hsrc k - (rho : ℂ).im|) ∧
          (∀ rho : NontrivialZeros,
            rho ∈ kadiriLocalZeroWindow (kadiriDyadicGoodHeightSequence hsrc k) →
              η k < |kadiriDyadicGoodHeightSequence hsrc k - (rho : ℂ).im|) := by
  filter_upwards [eventually_kadiriDyadicGoodHeightSequence_spec hsrc, hη_le]
    with k hspec hη_le_k
  refine ⟨hspec.1, hspec.2.1, ?_, ?_⟩
  · intro rho hrho
    exact lt_of_le_of_lt hη_le_k (hspec.2.2.1 rho hrho)
  · intro rho hrho
    exact lt_of_le_of_lt hη_le_k (hspec.2.2.2 rho hrho)

theorem eventually_kadiriDyadicGoodHeightSequence_spec_of_radiusConstant_le
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) {a : ℝ}
    (ha : a ≤ kadiriDyadicGoodHeightRadius hsrc) :
    ∀ᶠ k : ℕ in atTop,
      kadiriDyadicGoodHeightSequence hsrc k ∈
          Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)) ∧
        kadiriHorizontalZetaOffPoleHeight (kadiriDyadicGoodHeightSequence hsrc k) ∧
          (∀ rho : NontrivialZeros, rho ∈ kadiriDyadicZeroWindow ((2 : ℝ) ^ k) →
            a / Real.log ((2 : ℝ) ^ k) <
              |kadiriDyadicGoodHeightSequence hsrc k - (rho : ℂ).im|) ∧
          (∀ rho : NontrivialZeros,
            rho ∈ kadiriLocalZeroWindow (kadiriDyadicGoodHeightSequence hsrc k) →
              a / Real.log ((2 : ℝ) ^ k) <
                |kadiriDyadicGoodHeightSequence hsrc k - (rho : ℂ).im|) := by
  refine eventually_kadiriDyadicGoodHeightSequence_spec_of_le_logRadius hsrc ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with k hk
  have hk_ne : k ≠ 0 := by omega
  have hX_gt_one : 1 < (2 : ℝ) ^ k :=
    one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) hk_ne
  have hlog_pos : 0 < Real.log ((2 : ℝ) ^ k) := Real.log_pos hX_gt_one
  have hmul :
      a * (Real.log ((2 : ℝ) ^ k))⁻¹ ≤
        kadiriDyadicGoodHeightRadius hsrc * (Real.log ((2 : ℝ) ^ k))⁻¹ :=
    mul_le_mul_of_nonneg_right ha (inv_nonneg.mpr hlog_pos.le)
  simpa [div_eq_mul_inv] using hmul

theorem eventually_kadiriDyadicGoodHeightFilter_localGap_of_le_logRadius
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) {η : ℕ → ℝ}
    (hη_le : ∀ᶠ k : ℕ in atTop,
      η k ≤ kadiriDyadicGoodHeightRadius hsrc / Real.log ((2 : ℝ) ^ k)) :
    ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
      ∃ k : ℕ,
        T = kadiriDyadicGoodHeightSequence hsrc k ∧
          ∀ rho : NontrivialZeros, rho ∈ kadiriLocalZeroWindow T →
            η k < |T - (rho : ℂ).im| := by
  rw [kadiriDyadicGoodHeightFilter]
  change ∀ᶠ n : ℕ in atTop,
    ∃ k : ℕ,
      kadiriDyadicGoodHeightSequence hsrc n = kadiriDyadicGoodHeightSequence hsrc k ∧
        ∀ rho : NontrivialZeros,
          rho ∈ kadiriLocalZeroWindow (kadiriDyadicGoodHeightSequence hsrc n) →
            η k < |kadiriDyadicGoodHeightSequence hsrc n - (rho : ℂ).im|
  filter_upwards [eventually_kadiriDyadicGoodHeightSequence_spec_of_le_logRadius hsrc hη_le]
    with k hspec
  exact ⟨k, rfl, hspec.2.2.2⟩

theorem eventually_kadiriDyadicGoodHeightFilter_localGap_of_radiusConstant_le
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) {a : ℝ}
    (ha : a ≤ kadiriDyadicGoodHeightRadius hsrc) :
    ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
      ∃ k : ℕ,
        T = kadiriDyadicGoodHeightSequence hsrc k ∧
          ∀ rho : NontrivialZeros, rho ∈ kadiriLocalZeroWindow T →
            a / Real.log ((2 : ℝ) ^ k) < |T - (rho : ℂ).im| := by
  exact eventually_kadiriDyadicGoodHeightFilter_localGap_of_le_logRadius hsrc
    (η := fun k : ℕ => a / Real.log ((2 : ℝ) ^ k))
    (by
      filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with k hk
      have hk_ne : k ≠ 0 := by omega
      have hX_gt_one : 1 < (2 : ℝ) ^ k :=
        one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) hk_ne
      have hlog_pos : 0 < Real.log ((2 : ℝ) ^ k) := Real.log_pos hX_gt_one
      have hmul :
          a * (Real.log ((2 : ℝ) ^ k))⁻¹ ≤
            kadiriDyadicGoodHeightRadius hsrc * (Real.log ((2 : ℝ) ^ k))⁻¹ :=
        mul_le_mul_of_nonneg_right ha (inv_nonneg.mpr hlog_pos.le)
      simpa [div_eq_mul_inv] using hmul)

/--
Selected dyadic good heights give a pointwise `log^2` bound for the local zero principal
block.

This is the finite principal-block half of the Backlund/Kadiri good-height estimate:
the selector supplies the `c / log X` ordinate gap, while the U6a local Jensen atom
supplies the order-weighted `O(log |T|)` zero count.
-/
theorem exists_kadiriDyadicGoodHeightSelector_localPrincipal_logSq
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop,
      ∃ T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)),
        kadiriHorizontalZetaOffPoleHeight T ∧
          ∀ σ : ℝ,
            ‖∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
                ((riemannZeta.order (rho : ℂ) : ℂ) /
                  (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖ ≤
              C * Real.log |T| ^ (2 : ℕ) := by
  obtain ⟨c, hc, hsel⟩ := exists_kadiriDyadicGoodHeightSelector_logRadius_offPole hsrc
  obtain ⟨D, Tₘᵢₙ, hcnt⟩ := exists_u6aLocalZeroCountLogHypothesis
  rcases hcnt with ⟨hD, hcnt⟩
  refine ⟨D / c, div_nonneg hD.le hc.le, ?_⟩
  let B : ℝ := max (max |Tₘᵢₙ| 3) 1
  have hpow_large : ∀ᶠ k : ℕ in atTop, B ≤ (2 : ℝ) ^ k := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually
      (Filter.eventually_ge_atTop B)
  filter_upwards [hsel, hpow_large, Filter.eventually_ge_atTop (1 : ℕ)]
    with k hsel_k hk_large hk_one
  obtain ⟨T, hT, hoff, _hgap_dyadic, hgap_local⟩ := hsel_k
  refine ⟨T, hT, hoff, ?_⟩
  intro σ
  let X : ℝ := (2 : ℝ) ^ k
  have hXpos : 0 < X := by
    dsimp [X]
    exact pow_pos (by norm_num) k
  have hk_ne : k ≠ 0 := by omega
  have hX_gt_one : 1 < X := by
    dsimp [X]
    exact one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) hk_ne
  have hlogX_pos : 0 < Real.log X := Real.log_pos hX_gt_one
  have hηpos : 0 < c / Real.log X := div_pos hc hlogX_pos
  have hTpos : 0 < T := by linarith [hXpos, hT.1]
  have hTabs : |T| = T := abs_of_pos hTpos
  have hB_abs : |Tₘᵢₙ| ≤ B := by
    dsimp [B]
    exact le_trans (le_max_left |Tₘᵢₙ| 3) (le_max_left (max |Tₘᵢₙ| 3) 1)
  have hB_three : (3 : ℝ) ≤ B := by
    dsimp [B]
    exact le_trans (le_max_right |Tₘᵢₙ| 3) (le_max_left (max |Tₘᵢₙ| 3) 1)
  have hTmin_abs : Tₘᵢₙ ≤ |T| := by
    rw [hTabs]
    calc
      Tₘᵢₙ ≤ |Tₘᵢₙ| := le_abs_self Tₘᵢₙ
      _ ≤ B := hB_abs
      _ ≤ X := by simpa [X] using hk_large
      _ ≤ T := hT.1.le
  have hT_three_abs : (3 : ℝ) ≤ |T| := by
    rw [hTabs]
    calc
      (3 : ℝ) ≤ B := hB_three
      _ ≤ X := by simpa [X] using hk_large
      _ ≤ T := hT.1.le
  have hlogT_nonneg : 0 ≤ Real.log |T| := Real.log_nonneg (by linarith)
  have hlogX_le_logT : Real.log X ≤ Real.log |T| := by
    rw [hTabs]
    exact Real.log_le_log hXpos hT.1.le
  have hcount_T : u6aNearbyZeroCount (-1) 2 T ≤ D * Real.log |T| :=
    hcnt T hTmin_abs hT_three_abs
  have hprincipal :=
    kadiri_local_principal_part_pointwise_bound_of_gap_and_count
      (η := c / Real.log X) (T := T) (σ := σ) hηpos hT_three_abs
      (by simpa [X] using hgap_local)
  calc
    ‖∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
        ((riemannZeta.order (rho : ℂ) : ℂ) /
          (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖
        ≤ (c / Real.log X)⁻¹ * u6aNearbyZeroCount (-1) 2 T := hprincipal
    _ ≤ (c / Real.log X)⁻¹ * (D * Real.log |T|) :=
          mul_le_mul_of_nonneg_left hcount_T (inv_nonneg.mpr hηpos.le)
    _ = (D / c) * (Real.log X * Real.log |T|) := by
          field_simp [ne_of_gt hc, ne_of_gt hlogX_pos]
    _ ≤ (D / c) * (Real.log |T| * Real.log |T|) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hlogX_le_logT hlogT_nonneg)
            (div_nonneg hD.le hc.le)
    _ = (D / c) * Real.log |T| ^ (2 : ℕ) := by ring

/--
The selected dyadic good-height sequence carries the local zero-principal `log^2` bound.
-/
theorem exists_kadiriDyadicGoodHeightSequence_localPrincipal_logSq
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ σ : ℝ,
        ‖∑ rho ∈
            (kadiriLocalZeroWindow_finite (kadiriDyadicGoodHeightSequence hsrc k)).toFinset,
            ((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + ((kadiriDyadicGoodHeightSequence hsrc k : ℝ) : ℂ) * I) -
                (rho : ℂ)))‖ ≤
          C * Real.log |kadiriDyadicGoodHeightSequence hsrc k| ^ (2 : ℕ) := by
  let c : ℝ := kadiriDyadicGoodHeightRadius hsrc
  have hc : 0 < c := by
    dsimp [c]
    exact kadiriDyadicGoodHeightRadius_pos hsrc
  obtain ⟨D, Tₘᵢₙ, hcnt⟩ := exists_u6aLocalZeroCountLogHypothesis
  rcases hcnt with ⟨hD, hcnt⟩
  refine ⟨D / c, div_nonneg hD.le hc.le, ?_⟩
  let B : ℝ := max (max |Tₘᵢₙ| 3) 1
  have hpow_large : ∀ᶠ k : ℕ in atTop, B ≤ (2 : ℝ) ^ k := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually
      (Filter.eventually_ge_atTop B)
  filter_upwards [eventually_kadiriDyadicGoodHeightSequence_spec hsrc, hpow_large,
    Filter.eventually_ge_atTop (1 : ℕ)] with k hspec hk_large hk_one
  intro σ
  let T : ℝ := kadiriDyadicGoodHeightSequence hsrc k
  let X : ℝ := (2 : ℝ) ^ k
  have hT : T ∈ Set.Ioc X (2 * X) := by
    simpa [T, X] using hspec.1
  have hgap_local :
      ∀ rho : NontrivialZeros, rho ∈ kadiriLocalZeroWindow T →
        c / Real.log X < |T - (rho : ℂ).im| := by
    simpa [T, X, c] using hspec.2.2.2
  have hXpos : 0 < X := by
    dsimp [X]
    exact pow_pos (by norm_num) k
  have hk_ne : k ≠ 0 := by omega
  have hX_gt_one : 1 < X := by
    dsimp [X]
    exact one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) hk_ne
  have hlogX_pos : 0 < Real.log X := Real.log_pos hX_gt_one
  have hηpos : 0 < c / Real.log X := div_pos hc hlogX_pos
  have hTpos : 0 < T := by linarith [hXpos, hT.1]
  have hTabs : |T| = T := abs_of_pos hTpos
  have hB_abs : |Tₘᵢₙ| ≤ B := by
    dsimp [B]
    exact le_trans (le_max_left |Tₘᵢₙ| 3) (le_max_left (max |Tₘᵢₙ| 3) 1)
  have hB_three : (3 : ℝ) ≤ B := by
    dsimp [B]
    exact le_trans (le_max_right |Tₘᵢₙ| 3) (le_max_left (max |Tₘᵢₙ| 3) 1)
  have hTmin_abs : Tₘᵢₙ ≤ |T| := by
    rw [hTabs]
    calc
      Tₘᵢₙ ≤ |Tₘᵢₙ| := le_abs_self Tₘᵢₙ
      _ ≤ B := hB_abs
      _ ≤ X := by simpa [X] using hk_large
      _ ≤ T := hT.1.le
  have hT_three_abs : (3 : ℝ) ≤ |T| := by
    rw [hTabs]
    calc
      (3 : ℝ) ≤ B := hB_three
      _ ≤ X := by simpa [X] using hk_large
      _ ≤ T := hT.1.le
  have hlogT_nonneg : 0 ≤ Real.log |T| := Real.log_nonneg (by linarith)
  have hlogX_le_logT : Real.log X ≤ Real.log |T| := by
    rw [hTabs]
    exact Real.log_le_log hXpos hT.1.le
  have hcount_T : u6aNearbyZeroCount (-1) 2 T ≤ D * Real.log |T| :=
    hcnt T hTmin_abs hT_three_abs
  have hprincipal :=
    kadiri_local_principal_part_pointwise_bound_of_gap_and_count
      (η := c / Real.log X) (T := T) (σ := σ) hηpos hT_three_abs
      hgap_local
  calc
    ‖∑ rho ∈ (kadiriLocalZeroWindow_finite (kadiriDyadicGoodHeightSequence hsrc k)).toFinset,
        ((riemannZeta.order (rho : ℂ) : ℂ) /
          (((σ : ℂ) + ((kadiriDyadicGoodHeightSequence hsrc k : ℝ) : ℂ) * I) -
            (rho : ℂ)))‖
        = ‖∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
            ((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖ := by simp [T]
    _ ≤ (c / Real.log X)⁻¹ * u6aNearbyZeroCount (-1) 2 T := hprincipal
    _ ≤ (c / Real.log X)⁻¹ * (D * Real.log |T|) :=
          mul_le_mul_of_nonneg_left hcount_T (inv_nonneg.mpr hηpos.le)
    _ = (D / c) * (Real.log X * Real.log |T|) := by
          field_simp [ne_of_gt hc, ne_of_gt hlogX_pos]
    _ ≤ (D / c) * (Real.log |T| * Real.log |T|) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hlogX_le_logT hlogT_nonneg)
            (div_nonneg hD.le hc.le)
    _ = (D / c) * Real.log |kadiriDyadicGoodHeightSequence hsrc k| ^ (2 : ℕ) := by
          simp [T, pow_two]

theorem eventually_kadiriDyadicGoodHeightFilter_localPrincipal_logSq
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ∀ σ : ℝ,
          ‖∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
              ((riemannZeta.order (rho : ℂ) : ℂ) /
                (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖ ≤
            C * Real.log |T| ^ (2 : ℕ) := by
  obtain ⟨C, hC, hseq⟩ := exists_kadiriDyadicGoodHeightSequence_localPrincipal_logSq hsrc
  refine ⟨C, hC, ?_⟩
  rw [kadiriDyadicGoodHeightFilter]
  change ∀ᶠ k : ℕ in atTop,
    ∀ σ : ℝ,
      ‖∑ rho ∈
          (kadiriLocalZeroWindow_finite (kadiriDyadicGoodHeightSequence hsrc k)).toFinset,
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + ((kadiriDyadicGoodHeightSequence hsrc k : ℝ) : ℂ) * I) -
              (rho : ℂ)))‖ ≤
        C * Real.log |kadiriDyadicGoodHeightSequence hsrc k| ^ (2 : ℕ)
  exact hseq

/--
Pointwise logarithmic-derivative control on a selected horizontal line.

This is the consumer shape supplied by a good-height/partial-fraction argument: the whole
strip between `σ₁` and `σ₂` is controlled at both heights with absolute ordinate `T`.
-/
def kadiriHorizontalSegmentLogDerivBound (σ₁ σ₂ T C : ℝ) : Prop :=
  ∀ σ ∈ Set.uIcc σ₁ σ₂, ∀ t : ℝ, |t| = T →
    ‖deriv riemannZeta (((σ : ℂ) + (t : ℂ) * I)) /
        riemannZeta (((σ : ℂ) + (t : ℂ) * I))‖
      ≤ C * Real.log T ^ (2 : ℕ)

/--
Local-window zeta Hadamard/PV remainder after subtracting the zeros with ordinate within
distance one of the selected horizontal line.
-/
noncomputable def kadiriLocalZetaLogDerivPVRemainder (T σ : ℝ) : ℂ :=
  deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
      riemannZeta (((σ : ℂ) + (T : ℂ) * I)) -
    ∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
      ((riemannZeta.order (rho : ℂ) : ℂ) /
        (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))

/--
Algebraic handoff from a bounded local zero-principal block and a bounded local
Hadamard/PV remainder to the endpoint segment-bound shape.
-/
theorem kadiriHorizontalSegmentLogDerivBound_of_localPrincipal_and_localPVRemainder
    {Cprincipal Cremainder T : ℝ}
    (hprincipal : ∀ σ ∈ Set.uIcc (-1 : ℝ) 2, ∀ t : ℝ, |t| = T →
      ‖∑ rho ∈ (kadiriLocalZeroWindow_finite t).toFinset,
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + (t : ℂ) * I) - (rho : ℂ)))‖ ≤
        Cprincipal * Real.log T ^ (2 : ℕ))
    (hremainder : ∀ σ ∈ Set.uIcc (-1 : ℝ) 2, ∀ t : ℝ, |t| = T →
      ‖kadiriLocalZetaLogDerivPVRemainder t σ‖ ≤
        Cremainder * Real.log T ^ (2 : ℕ)) :
    kadiriHorizontalSegmentLogDerivBound (-1) 2 T (Cprincipal + Cremainder) := by
  intro σ hσ t ht
  let principal : ℂ :=
    ∑ rho ∈ (kadiriLocalZeroWindow_finite t).toFinset,
      ((riemannZeta.order (rho : ℂ) : ℂ) /
        (((σ : ℂ) + (t : ℂ) * I) - (rho : ℂ)))
  let remainder : ℂ := kadiriLocalZetaLogDerivPVRemainder t σ
  have hdecomp :
      deriv riemannZeta (((σ : ℂ) + (t : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (t : ℂ) * I)) =
        principal + remainder := by
    dsimp [principal, remainder, kadiriLocalZetaLogDerivPVRemainder]
    ring
  calc
    ‖deriv riemannZeta (((σ : ℂ) + (t : ℂ) * I)) /
        riemannZeta (((σ : ℂ) + (t : ℂ) * I))‖
        = ‖principal + remainder‖ := by rw [hdecomp]
    _ ≤ ‖principal‖ + ‖remainder‖ := norm_add_le principal remainder
    _ ≤ Cprincipal * Real.log T ^ (2 : ℕ) +
          Cremainder * Real.log T ^ (2 : ℕ) := by
        exact add_le_add (by simpa [principal] using hprincipal σ hσ t ht)
          (by simpa [remainder] using hremainder σ hσ t ht)
    _ = (Cprincipal + Cremainder) * Real.log T ^ (2 : ℕ) := by ring

/--
One signed horizontal line version of the endpoint logarithmic-derivative bound.

The dyadic good-height selector chooses positive heights, so this is the honest
intermediate shape before any later symmetry argument upgrades it to the two-sided
absolute-height predicate.
-/
def kadiriPositiveHorizontalSegmentLogDerivBound (σ₁ σ₂ T C : ℝ) : Prop :=
  ∀ σ ∈ Set.uIcc σ₁ σ₂,
    ‖deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
        riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
      ≤ C * Real.log |T| ^ (2 : ℕ)

/--
One-sided algebraic handoff from the local principal block plus local Hadamard/PV
remainder to the signed horizontal segment bound.
-/
theorem kadiriPositiveHorizontalSegmentLogDerivBound_of_localPrincipal_and_localPVRemainder
    {Cprincipal Cremainder T : ℝ}
    (hprincipal : ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
      ‖∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖ ≤
        Cprincipal * Real.log |T| ^ (2 : ℕ))
    (hremainder : ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
      ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
        Cremainder * Real.log |T| ^ (2 : ℕ)) :
    kadiriPositiveHorizontalSegmentLogDerivBound (-1) 2 T (Cprincipal + Cremainder) := by
  intro σ hσ
  let principal : ℂ :=
    ∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
      ((riemannZeta.order (rho : ℂ) : ℂ) /
        (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))
  let remainder : ℂ := kadiriLocalZetaLogDerivPVRemainder T σ
  have hdecomp :
      deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I)) =
        principal + remainder := by
    dsimp [principal, remainder, kadiriLocalZetaLogDerivPVRemainder]
    ring
  calc
    ‖deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
        riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        = ‖principal + remainder‖ := by rw [hdecomp]
    _ ≤ ‖principal‖ + ‖remainder‖ := norm_add_le principal remainder
    _ ≤ Cprincipal * Real.log |T| ^ (2 : ℕ) +
          Cremainder * Real.log |T| ^ (2 : ℕ) := by
        exact add_le_add (by simpa [principal] using hprincipal σ hσ)
          (by simpa [remainder] using hremainder σ hσ)
    _ = (Cprincipal + Cremainder) * Real.log |T| ^ (2 : ℕ) := by ring

/--
Selected dyadic good heights give the signed horizontal `log^2` bound once the local
Hadamard/PV remainder has the matching `log^2` bound on candidate heights.
-/
theorem exists_kadiriDyadicGoodHeightSelector_positiveLogDeriv_logSq_of_localPVRemainder
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ k : ℕ in atTop,
      ∀ T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)),
        kadiriHorizontalZetaOffPoleHeight T →
          ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
            ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
              R * Real.log |T| ^ (2 : ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop,
      ∃ T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)),
        kadiriHorizontalZetaOffPoleHeight T ∧
          kadiriPositiveHorizontalSegmentLogDerivBound (-1) 2 T C := by
  obtain ⟨P, hP, hprincipal⟩ :=
    exists_kadiriDyadicGoodHeightSelector_localPrincipal_logSq hsrc
  obtain ⟨R, hR, hremainder⟩ := hrem
  refine ⟨P + R, add_nonneg hP hR, ?_⟩
  filter_upwards [hprincipal, hremainder] with k hprincipal_k hremainder_k
  obtain ⟨T, hT, hoff, hprincipal_T⟩ := hprincipal_k
  refine ⟨T, hT, hoff, ?_⟩
  exact kadiriPositiveHorizontalSegmentLogDerivBound_of_localPrincipal_and_localPVRemainder
    (Cprincipal := P) (Cremainder := R) (T := T)
    (fun σ hσ => hprincipal_T σ)
    (fun σ hσ => hremainder_k T hT hoff σ hσ)

/--
On the selected good-height filter, local PV `log^2` control upgrades the selected local
principal bound to the signed horizontal logarithmic-derivative bound.
-/
theorem eventually_kadiriDyadicGoodHeightFilter_positiveLogDeriv_logSq_of_localPVRemainder
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
          ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
            R * Real.log |T| ^ (2 : ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        kadiriPositiveHorizontalSegmentLogDerivBound (-1) 2 T C := by
  obtain ⟨P, hP, hprincipal⟩ :=
    eventually_kadiriDyadicGoodHeightFilter_localPrincipal_logSq hsrc
  obtain ⟨R, hR, hremainder⟩ := hrem
  refine ⟨P + R, add_nonneg hP hR, ?_⟩
  filter_upwards [hprincipal, hremainder] with T hprincipal_T hremainder_T
  exact kadiriPositiveHorizontalSegmentLogDerivBound_of_localPrincipal_and_localPVRemainder
    (Cprincipal := P) (Cremainder := R) (T := T)
    (fun σ hσ => hprincipal_T σ)
    (fun σ hσ => hremainder_T σ hσ)

theorem eventually_kadiriDyadicGoodHeightFilter_localPVRemainder_logSq_of_candidate
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ k : ℕ in atTop,
      ∀ T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)),
        kadiriHorizontalZetaOffPoleHeight T →
          ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
            ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
              R * Real.log |T| ^ (2 : ℕ)) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
          ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
            R * Real.log |T| ^ (2 : ℕ) := by
  obtain ⟨R, hR, hrem_event⟩ := hrem
  refine ⟨R, hR, ?_⟩
  rw [kadiriDyadicGoodHeightFilter]
  change ∀ᶠ k : ℕ in atTop,
    ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
      ‖kadiriLocalZetaLogDerivPVRemainder (kadiriDyadicGoodHeightSequence hsrc k) σ‖ ≤
        R * Real.log |kadiriDyadicGoodHeightSequence hsrc k| ^ (2 : ℕ)
  filter_upwards [eventually_kadiriDyadicGoodHeightSequence_spec hsrc, hrem_event]
    with k hspec hrem_k
  exact hrem_k (kadiriDyadicGoodHeightSequence hsrc k) hspec.1 hspec.2.1

theorem eventually_kadiriDyadicGoodHeightFilter_positiveHorizontalSegmentLogDerivBound_of_localPVRemainder
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
          ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
            R * Real.log |T| ^ (2 : ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        kadiriPositiveHorizontalSegmentLogDerivBound (-1) 2 T C :=
  eventually_kadiriDyadicGoodHeightFilter_positiveLogDeriv_logSq_of_localPVRemainder hsrc hrem

theorem
    eventually_kadiriDyadicGoodHeightFilter_positiveHorizontalSegmentLogDerivBound_of_candidate_localPVRemainder
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ k : ℕ in atTop,
      ∀ T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)),
        kadiriHorizontalZetaOffPoleHeight T →
          ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
            ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
              R * Real.log |T| ^ (2 : ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        kadiriPositiveHorizontalSegmentLogDerivBound (-1) 2 T C :=
  eventually_kadiriDyadicGoodHeightFilter_positiveHorizontalSegmentLogDerivBound_of_localPVRemainder
    hsrc (eventually_kadiriDyadicGoodHeightFilter_localPVRemainder_logSq_of_candidate
      hsrc hrem)

theorem kadiriHorizontalSegmentLogDerivBound_of_positiveHorizontalSegmentLogDerivBound
    {C T : ℝ}
    (hseg : kadiriPositiveHorizontalSegmentLogDerivBound (-1) 2 T C) :
    kadiriHorizontalSegmentLogDerivBound (-1) 2 T C := by
  intro σ hσ t ht
  have hT_nonneg : 0 ≤ T := by
    rw [← ht]
    exact abs_nonneg t
  have hlog_absT : Real.log |T| = Real.log T := by
    rw [abs_of_nonneg hT_nonneg]
  by_cases ht_nonneg : 0 ≤ t
  · have ht_eq : t = T := by
      rw [← ht]
      exact (abs_of_nonneg ht_nonneg).symm
    subst t
    simpa [hlog_absT] using hseg σ hσ
  · have ht_neg : t < 0 := lt_of_not_ge ht_nonneg
    have ht_eq : t = -T := by
      have habs : |t| = -t := abs_of_neg ht_neg
      linarith
    let sT : ℂ := (σ : ℂ) + (T : ℂ) * I
    let st : ℂ := (σ : ℂ) + (t : ℂ) * I
    have hst_conj : st = (starRingEnd ℂ) sT := by
      apply Complex.ext <;> simp [st, sT, ht_eq]
    have hlogderiv_conj :
        deriv riemannZeta st / riemannZeta st =
          (starRingEnd ℂ) (deriv riemannZeta sT / riemannZeta sT) := by
      have h := logDerivZeta_conj sT
      change (deriv riemannZeta / riemannZeta) st =
        (starRingEnd ℂ) ((deriv riemannZeta / riemannZeta) sT)
      simpa [hst_conj] using h
    calc
      ‖deriv riemannZeta (((σ : ℂ) + (t : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (t : ℂ) * I))‖
          = ‖deriv riemannZeta st / riemannZeta st‖ := by rfl
      _ = ‖(starRingEnd ℂ) (deriv riemannZeta sT / riemannZeta sT)‖ := by
            rw [hlogderiv_conj]
      _ = ‖deriv riemannZeta sT / riemannZeta sT‖ := by rw [RCLike.norm_conj]
      _ ≤ C * Real.log |T| ^ (2 : ℕ) := by
            simpa [sT] using hseg σ hσ
      _ = C * Real.log T ^ (2 : ℕ) := by rw [hlog_absT]

theorem
    eventually_kadiriDyadicGoodHeightFilter_horizontalSegmentLogDerivBound_of_positiveHorizontalSegmentLogDerivBound
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hseg : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        kadiriPositiveHorizontalSegmentLogDerivBound (-1) 2 T C) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        kadiriHorizontalSegmentLogDerivBound (-1) 2 T C := by
  obtain ⟨C, hC, hseg_event⟩ := hseg
  refine ⟨C, hC, ?_⟩
  filter_upwards [hseg_event] with T hseg_T
  exact kadiriHorizontalSegmentLogDerivBound_of_positiveHorizontalSegmentLogDerivBound hseg_T

theorem
    eventually_kadiriDyadicGoodHeightFilter_horizontalSegmentLogDerivBound_of_localPVRemainder
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
          ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
            R * Real.log |T| ^ (2 : ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        kadiriHorizontalSegmentLogDerivBound (-1) 2 T C :=
  eventually_kadiriDyadicGoodHeightFilter_horizontalSegmentLogDerivBound_of_positiveHorizontalSegmentLogDerivBound
    hsrc
    (eventually_kadiriDyadicGoodHeightFilter_positiveHorizontalSegmentLogDerivBound_of_localPVRemainder
      hsrc hrem)

theorem
    eventually_kadiriDyadicGoodHeightFilter_horizontalSegmentLogDerivBound_of_candidate_localPVRemainder
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ k : ℕ in atTop,
      ∀ T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)),
        kadiriHorizontalZetaOffPoleHeight T →
          ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
            ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
              R * Real.log |T| ^ (2 : ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        kadiriHorizontalSegmentLogDerivBound (-1) 2 T C :=
  eventually_kadiriDyadicGoodHeightFilter_horizontalSegmentLogDerivBound_of_localPVRemainder
    hsrc (eventually_kadiriDyadicGoodHeightFilter_localPVRemainder_logSq_of_candidate
      hsrc hrem)

theorem
    eventually_kadiriDyadicGoodHeightFilter_abs_horizontalSegmentLogDerivBound_of_horizontalSegmentLogDerivBound
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hseg : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        kadiriHorizontalSegmentLogDerivBound (-1) 2 T C) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        kadiriHorizontalSegmentLogDerivBound (-1) 2 |T| C := by
  obtain ⟨C, hC, hseg_event⟩ := hseg
  refine ⟨C, hC, ?_⟩
  have hpos : ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc, 0 ≤ T := by
    filter_upwards [eventually_kadiriDyadicGoodHeightFilter_scale hsrc] with T hscale
    obtain ⟨k, _hEq, hT⟩ := hscale
    have hpow_pos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
    exact (hpow_pos.trans hT.1).le
  filter_upwards [hseg_event, hpos] with T hseg_T hT_nonneg
  simpa [abs_of_nonneg hT_nonneg] using hseg_T

/-- Along the selected dyadic good-height filter, the height tends to infinity. -/
theorem eventually_kadiriDyadicGoodHeightFilter_large
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc, 3 < |T| := by
  have htop : ∀ᶠ T : ℝ in atTop, 3 < |T| := by
    filter_upwards [Filter.eventually_gt_atTop (3 : ℝ)] with T hT
    exact lt_of_lt_of_le hT (le_abs_self T)
  exact htop.filter_mono (kadiriDyadicGoodHeightFilter_le_atTop hsrc)

/--
A one-sided positive horizontal `log^2` bound supplies the moving nonterminal
pointwise `log^9` input for the endpoint layer.
-/
theorem
    kadiri_nonterminal_neg_zeta_logDeriv_pointwise_log_bound_of_positiveHorizontalSegmentLogDerivBound
    {A C T : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hT : 3 < |T|)
    (hleft : A / Real.log |T| ^ (9 : ℕ) ≤ 2)
    (hseg : kadiriPositiveHorizontalSegmentLogDerivBound (-1) 2 T C) :
    ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
      ‖-deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ C * Real.log |T| ^ (9 : ℕ) := by
  intro σ hσ
  let x : ℝ := 1 - A / Real.log |T| ^ (9 : ℕ)
  have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hT.le
  have hlog_pow_pos : 0 < Real.log |T| ^ (9 : ℕ) := by
    positivity
  have hshift_nonneg : 0 ≤ A / Real.log |T| ^ (9 : ℕ) :=
    div_nonneg hA hlog_pow_pos.le
  have hx_upper : x ≤ 2 := by
    dsimp [x]
    linarith
  have hx_lower : -1 ≤ x := by
    dsimp [x]
    linarith
  have hσ_uIcc : σ ∈ Set.uIcc 0 x :=
    Set.uIoc_subset_uIcc hσ
  have hσ_strip : σ ∈ Set.uIcc (-1 : ℝ) 2 := by
    rw [Set.mem_uIcc] at hσ_uIcc ⊢
    rcases hσ_uIcc with hσ_uIcc | hσ_uIcc
    · exact Or.inl ⟨by linarith [hσ_uIcc.1], le_trans hσ_uIcc.2 hx_upper⟩
    · exact Or.inl ⟨le_trans hx_lower hσ_uIcc.1, by linarith [hσ_uIcc.2]⟩
  have hraw :
      ‖deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ C * Real.log |T| ^ (2 : ℕ) :=
    hseg σ hσ_strip
  have hpow : Real.log |T| ^ (2 : ℕ) ≤ Real.log |T| ^ (9 : ℕ) :=
    pow_le_pow_right₀ hlog_one.le (by norm_num)
  have hraw_log9 :
      ‖deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ C * Real.log |T| ^ (9 : ℕ) :=
    hraw.trans (mul_le_mul_of_nonneg_left hpow hC)
  simpa [neg_div, norm_neg] using hraw_log9

theorem
    eventually_kadiri_neg_zeta_logDeriv_nonterminal_pointwise_log_bound_of_positiveHorizontalSegmentLogDerivBound_on_filter
    (L : Filter ℝ) (hL : L ≤ atTop)
    (hlarge : ∀ᶠ T : ℝ in L, 3 < |T|)
    (hseg : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in L,
        kadiriPositiveHorizontalSegmentLogDerivBound (-1) 2 T C) :
    ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in L,
          ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
            ‖-deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
              ≤ Z * Real.log |T| ^ (9 : ℕ) := by
  obtain ⟨C, hC, hseg_event⟩ := hseg
  intro A hA
  refine ⟨C, hC, ?_⟩
  have hsmall : ∀ᶠ T : ℝ in L, A / Real.log |T| ^ (9 : ℕ) ≤ 2 :=
    ((eventually_const_div_log_abs_pow_lt_atTop A 2 (by norm_num)).filter_mono
      hL).mono fun _ hT => le_of_lt hT
  filter_upwards [hlarge, hseg_event, hsmall] with T hlarge_T hseg_T hsmall_T
  exact
    kadiri_nonterminal_neg_zeta_logDeriv_pointwise_log_bound_of_positiveHorizontalSegmentLogDerivBound
      (A := A) (C := C) (T := T) hA hC hlarge_T hsmall_T hseg_T

theorem eventually_kadiriDyadicGoodHeightFilter_nonterminal_pointwise_log_bound_of_localPVRemainder
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
          ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
            R * Real.log |T| ^ (2 : ℕ)) :
    ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
          ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
            ‖-deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
              ≤ Z * Real.log |T| ^ (9 : ℕ) := by
  exact
    eventually_kadiri_neg_zeta_logDeriv_nonterminal_pointwise_log_bound_of_positiveHorizontalSegmentLogDerivBound_on_filter
      (L := kadiriDyadicGoodHeightFilter hsrc)
      (kadiriDyadicGoodHeightFilter_le_atTop hsrc)
      (eventually_kadiriDyadicGoodHeightFilter_large hsrc)
      (eventually_kadiriDyadicGoodHeightFilter_positiveLogDeriv_logSq_of_localPVRemainder
        hsrc hrem)

theorem eventually_kadiriDyadicGoodHeightFilter_nonterminal_pointwise_log_bound_of_candidate_localPVRemainder
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ k : ℕ in atTop,
      ∀ T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)),
        kadiriHorizontalZetaOffPoleHeight T →
          ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
            ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
              R * Real.log |T| ^ (2 : ℕ)) :
    ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
          ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
            ‖-deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
              ≤ Z * Real.log |T| ^ (9 : ℕ) :=
  eventually_kadiriDyadicGoodHeightFilter_nonterminal_pointwise_log_bound_of_localPVRemainder
    hsrc (eventually_kadiriDyadicGoodHeightFilter_localPVRemainder_logSq_of_candidate
      hsrc hrem)

theorem
    kadiri_nonterminal_neg_zeta_logDeriv_pointwise_log_bound_of_horizontalSegmentLogDerivBound
    {A C T : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hT : 3 < |T|)
    (hleft : A / Real.log |T| ^ (9 : ℕ) ≤ 2)
    (hseg : kadiriHorizontalSegmentLogDerivBound (-1) 2 |T| C) :
    ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
      ‖-deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ C * Real.log |T| ^ (9 : ℕ) := by
  intro σ hσ
  let x : ℝ := 1 - A / Real.log |T| ^ (9 : ℕ)
  have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hT.le
  have hlog_pow_pos : 0 < Real.log |T| ^ (9 : ℕ) := by
    positivity
  have hshift_nonneg : 0 ≤ A / Real.log |T| ^ (9 : ℕ) :=
    div_nonneg hA hlog_pow_pos.le
  have hx_upper : x ≤ 2 := by
    dsimp [x]
    linarith
  have hx_lower : -1 ≤ x := by
    dsimp [x]
    linarith
  have hσ_uIcc : σ ∈ Set.uIcc 0 x :=
    Set.uIoc_subset_uIcc hσ
  have hσ_strip : σ ∈ Set.uIcc (-1 : ℝ) 2 := by
    rw [Set.mem_uIcc] at hσ_uIcc ⊢
    rcases hσ_uIcc with hσ_uIcc | hσ_uIcc
    · exact Or.inl ⟨by linarith [hσ_uIcc.1], le_trans hσ_uIcc.2 hx_upper⟩
    · exact Or.inl ⟨le_trans hx_lower hσ_uIcc.1, by linarith [hσ_uIcc.2]⟩
  have hraw :
      ‖deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ C * Real.log |T| ^ (2 : ℕ) :=
    hseg σ hσ_strip T rfl
  have hpow : Real.log |T| ^ (2 : ℕ) ≤ Real.log |T| ^ (9 : ℕ) :=
    pow_le_pow_right₀ hlog_one.le (by norm_num)
  have hraw_log9 :
      ‖deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ C * Real.log |T| ^ (9 : ℕ) :=
    hraw.trans (mul_le_mul_of_nonneg_left hpow hC)
  simpa [neg_div, norm_neg] using hraw_log9

theorem
    eventually_kadiri_neg_zeta_logDeriv_nonterminal_pointwise_log_bound_of_horizontalSegmentLogDerivBound_on_large_offPole_filter
    (hseg : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        kadiriHorizontalSegmentLogDerivBound (-1) 2 |T| C) :
    ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
          ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
            ‖-deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
              ≤ Z * Real.log |T| ^ (9 : ℕ) := by
  obtain ⟨C, hC, hseg_event⟩ := hseg
  intro A hA
  refine ⟨C, hC, ?_⟩
  have hsmall : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      A / Real.log |T| ^ (9 : ℕ) ≤ 2 :=
    ((eventually_const_div_log_abs_pow_lt_atTop A 2 (by norm_num)).filter_mono
      kadiriLargeHorizontalZetaOffPoleFilter_le_atTop).mono fun _ hT => le_of_lt hT
  filter_upwards [eventually_kadiriLargeHorizontalZetaOffPoleFilter_large,
    hseg_event, hsmall] with T hlarge hseg_T hsmall_T
  exact
    kadiri_nonterminal_neg_zeta_logDeriv_pointwise_log_bound_of_horizontalSegmentLogDerivBound
      (A := A) (C := C) (T := T) hA hC hlarge hsmall_T hseg_T

theorem
    eventually_kadiri_neg_zeta_logDeriv_nonterminal_pointwise_log_bound_of_horizontalSegmentLogDerivBound_on_filter
    (L : Filter ℝ) (hL : L ≤ atTop)
    (hlarge : ∀ᶠ T : ℝ in L, 3 < |T|)
    (hseg : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in L,
        kadiriHorizontalSegmentLogDerivBound (-1) 2 |T| C) :
    ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in L,
          ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
            ‖-deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
              ≤ Z * Real.log |T| ^ (9 : ℕ) := by
  obtain ⟨C, hC, hseg_event⟩ := hseg
  intro A hA
  refine ⟨C, hC, ?_⟩
  have hsmall : ∀ᶠ T : ℝ in L, A / Real.log |T| ^ (9 : ℕ) ≤ 2 :=
    ((eventually_const_div_log_abs_pow_lt_atTop A 2 (by norm_num)).filter_mono
      hL).mono fun _ hT => le_of_lt hT
  filter_upwards [hlarge, hseg_event, hsmall] with T hlarge_T hseg_T hsmall_T
  exact
    kadiri_nonterminal_neg_zeta_logDeriv_pointwise_log_bound_of_horizontalSegmentLogDerivBound
      (A := A) (C := C) (T := T) hA hC hlarge_T hsmall_T hseg_T

theorem eventually_kadiriDyadicGoodHeightFilter_nonterminal_pointwise_log_bound_of_horizontalSegmentLogDerivBound
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hseg : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        kadiriHorizontalSegmentLogDerivBound (-1) 2 |T| C) :
    ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
          ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
            ‖-deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
              ≤ Z * Real.log |T| ^ (9 : ℕ) :=
  eventually_kadiri_neg_zeta_logDeriv_nonterminal_pointwise_log_bound_of_horizontalSegmentLogDerivBound_on_filter
    (L := kadiriDyadicGoodHeightFilter hsrc)
    (kadiriDyadicGoodHeightFilter_le_atTop hsrc)
    (eventually_kadiriDyadicGoodHeightFilter_large hsrc)
    hseg

/--
Large off-pole specialization of the dyadic right-boundary selector: for fixed `k`, the
finite truncated zero family is eventually strictly left of `1 - A / log |T|^9`.
-/
theorem
    eventually_kadiri_truncated_zero_family_left_of_log_terminal_on_large_offPole_filter
    (A : ℝ) (k : ℕ) :
    ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ∀ rho : NontrivialZeros,
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1) →
          (rho : ℂ).re < 1 - A / Real.log |T| ^ (9 : ℕ) :=
  eventually_kadiri_truncated_zero_family_left_of_log_terminal_on_filter
    A k kadiriLargeHorizontalZetaOffPoleFilter kadiriLargeHorizontalZetaOffPoleFilter_le_atTop

/--
On the large off-pole filter, the digamma pair from the functional equation is eventually
integrable on the nonpositive horizontal segment.
-/
theorem
    eventually_kadiri_digamma_pair_nonpositive_horizontal_intervalIntegrable_on_large_offPole_filter
    (a : ℝ) (ha : 0 ≤ a) :
    ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      IntervalIntegrable
        (fun σ : ℝ =>
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2))))
        volume (-a) 0 := by
  filter_upwards [eventually_kadiriLargeHorizontalZetaOffPoleHeight] with T hT
  exact kadiri_digamma_pair_nonpositive_horizontal_intervalIntegrable a T ha hT.1

/-- Iterating `digamma (z + 1) = digamma z + z⁻¹` over a finite shift. -/
theorem kadiri_digamma_add_nat_eq_add_sum
    (z : ℂ) (n : ℕ) (hpoles : ∀ i m : ℕ, z + i ≠ -(m : ℂ)) :
    digamma (z + n) = digamma z + ∑ i ∈ Finset.range n, (z + i)⁻¹ := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hstep :
          digamma (z + (n + 1 : ℕ)) = digamma (z + n) + (z + n)⁻¹ := by
        simpa [Nat.cast_succ, add_assoc, add_comm, add_left_comm] using
          (Complex.digamma_apply_add_one (z + n) (hpoles n))
      rw [hstep, ih]
      rw [Finset.sum_range_succ]
      ring

/--
A pointwise bound for the digamma pair controls its nonpositive horizontal-segment
integral.
-/
theorem kadiri_digamma_pair_nonpositive_horizontal_integral_bound_of_pointwise_bound
    (a T G : ℝ) (ha : 0 ≤ a)
    (hpoint : ∀ σ ∈ Ι (-a) 0,
      ‖(1 / 2 : ℂ) *
          (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
            digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖ ≤ G) :
    ‖∫ σ in (-a)..0,
        (1 / 2 : ℂ) *
          (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
            digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖ ≤ G * a := by
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -a) (b := 0) (C := G)
      (f := fun σ : ℝ =>
        (1 / 2 : ℂ) *
          (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
            digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))) hpoint
  simpa [sub_eq_add_neg, abs_of_nonneg ha] using hnorm

/--
Pointwise logarithmic bound for the digamma pair on the nonpositive horizontal segment.

The first argument is shifted a fixed finite number of steps into the right half-plane;
the second argument is already in the right half-plane after reflection.
-/
theorem
    eventually_kadiri_digamma_pair_nonpositive_horizontal_pointwise_log_bound_on_large_offPole_filter
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ G : ℝ, 0 ≤ G ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ∀ σ ∈ Ι (-a) 0,
          ‖(1 / 2 : ℂ) *
              (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
                digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖
            ≤ G * Real.log |T| ^ 9 := by
  let n : ℕ := ⌈a⌉₊ + 1
  obtain ⟨Cleft, hCleft_pos, hCleft_bound⟩ :=
    Complex.exists_norm_digamma_le_log (a := 1) (b := (n : ℝ)) one_pos
  obtain ⟨Cright, hCright_pos, hCright_bound⟩ :=
    Complex.exists_norm_digamma_div_two_le_log (a := 1) (b := 1 + a) one_pos
  refine ⟨Cleft + Cright + n, by positivity, ?_⟩
  have hlog_ge_two : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      (2 : ℝ) ≤ Real.log |T| := by
    have hlog_abs :
        Filter.Tendsto (fun T : ℝ => Real.log |T|) Filter.atTop Filter.atTop := by
      exact Real.tendsto_log_atTop.comp tendsto_norm_atTop_atTop
    exact (hlog_abs.eventually_ge_atTop 2).filter_mono
      kadiriLargeHorizontalZetaOffPoleFilter_le_atTop
  filter_upwards [eventually_kadiriLargeHorizontalZetaOffPoleFilter_large, hlog_ge_two]
    with T hlarge hlog_two σ hσ
  have hle : -a ≤ 0 := by linarith
  have hσI : σ ∈ Set.Ioc (-a) 0 := by
    rw [Set.uIoc_of_le hle] at hσ
    exact hσ
  have hσ_left : -a ≤ σ := hσI.1.le
  have hσ_right : σ ≤ 0 := hσI.2
  have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hlarge.le
  have hlog_pow_one : (1 : ℝ) ≤ Real.log |T| ^ (9 : ℕ) :=
    one_le_pow₀ hlog_one.le
  have hlog_pow_nonneg : 0 ≤ Real.log |T| ^ (9 : ℕ) := by positivity
  have hT_abs_pos : 0 < |T| := by linarith
  have hT_abs_one : 1 ≤ |T| := by linarith
  have hT_abs_add_le_pow : |T| + 2 ≤ |T| ^ (9 : ℕ) := by
    have hsq : |T| + 2 ≤ |T| ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (|T| - 2)]
    have hpow : |T| ^ (2 : ℕ) ≤ |T| ^ (9 : ℕ) :=
      pow_le_pow_right₀ hT_abs_one (by norm_num)
    exact le_trans hsq hpow
  have hT_abs_add_le_sq : |T| + 2 ≤ |T| ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (|T| - 2)]
  have hlog_abs_add_le_two_log :
      Real.log (|T| + 2) ≤ 2 * Real.log |T| := by
    calc
      Real.log (|T| + 2) ≤ Real.log (|T| ^ (2 : ℕ)) :=
        Real.log_le_log (by positivity) hT_abs_add_le_sq
      _ = 2 * Real.log |T| := by
        rw [Real.log_pow]
        norm_num
  have htwo_log_le_log_pow :
      2 * Real.log |T| ≤ Real.log |T| ^ (9 : ℕ) := by
    have hlog_one' : 1 ≤ Real.log |T| := by linarith
    have hsq : 2 * Real.log |T| ≤ Real.log |T| ^ (2 : ℕ) := by
      nlinarith
    have hpow : Real.log |T| ^ (2 : ℕ) ≤ Real.log |T| ^ (9 : ℕ) :=
      pow_le_pow_right₀ hlog_one' (by norm_num)
    exact le_trans hsq hpow
  have hlog_abs_add :
      Real.log (|T| + 2) ≤ Real.log |T| ^ (9 : ℕ) :=
    le_trans hlog_abs_add_le_two_log htwo_log_le_log_pow
  have hhalf_abs_add :
      |T / 2| + 2 ≤ |T| + 2 := by
    rw [abs_div]
    have htwo : |(2 : ℝ)| = 2 := by norm_num
    rw [htwo]
    linarith [abs_nonneg T]
  have hlog_half_abs_add :
      Real.log (|T / 2| + 2) ≤ Real.log |T| ^ (9 : ℕ) :=
    le_trans (Real.log_le_log (by positivity) hhalf_abs_add) hlog_abs_add
  let z : ℂ := (((σ : ℂ) + (T : ℂ) * I) / 2)
  have hpoles : ∀ i m : ℕ, z + i ≠ -(m : ℂ) := by
    intro i m h
    have him := congrArg Complex.im h
    have hT0 : T = 0 := by
      have : T / 2 = 0 := by
        simpa [z] using him
      linarith
    rw [hT0, abs_zero] at hlarge
    norm_num at hlarge
  have hshift :
      digamma z = digamma (z + n) - ∑ i ∈ Finset.range n, (z + i)⁻¹ := by
    have h := kadiri_digamma_add_nat_eq_add_sum z n hpoles
    rw [h]
    abel
  have hn_ge : a + 1 ≤ (n : ℝ) := by
    dsimp [n]
    push_cast
    linarith [Nat.le_ceil a]
  have hshift_re_left : 1 ≤ (z + n).re := by
    dsimp [z]
    simp
    linarith
  have hshift_re_right : (z + n).re ≤ (n : ℝ) := by
    dsimp [z]
    simp
    linarith
  have hshift_im : (z + n).im = T / 2 := by
    simp [z]
  have hshift_bound :
      ‖digamma (z + n)‖ ≤ Cleft * Real.log |T| ^ (9 : ℕ) := by
    calc
      ‖digamma (z + n)‖
          ≤ Cleft * Real.log (|(z + n).im| + 2) :=
            hCleft_bound (z + n) hshift_re_left hshift_re_right
      _ = Cleft * Real.log (|T / 2| + 2) := by
            rw [hshift_im]
      _ ≤ Cleft * Real.log |T| ^ (9 : ℕ) :=
            mul_le_mul_of_nonneg_left hlog_half_abs_add hCleft_pos.le
  have hsum_bound :
      ‖∑ i ∈ Finset.range n, (z + i)⁻¹‖ ≤ (n : ℝ) := by
    calc
      ‖∑ i ∈ Finset.range n, (z + i)⁻¹‖
          ≤ ∑ i ∈ Finset.range n, ‖(z + i)⁻¹‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range n, (1 : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            rw [norm_inv]
            apply inv_le_one_of_one_le₀
            have him_ge : 1 ≤ |(z + i).im| := by
              have hhalf : 1 < |T / 2| := by
                rw [abs_div]
                have htwo : |(2 : ℝ)| = 2 := by norm_num
                rw [htwo]
                nlinarith
              have him : (z + i).im = T / 2 := by
                simp [z]
              rw [him]
              exact hhalf.le
            exact le_trans him_ge (Complex.abs_im_le_norm (z + i))
      _ = (n : ℝ) := by
            simp
  have hleft :
      ‖digamma z‖ ≤ (Cleft + n) * Real.log |T| ^ (9 : ℕ) := by
    calc
      ‖digamma z‖
          = ‖digamma (z + n) - ∑ i ∈ Finset.range n, (z + i)⁻¹‖ := by
            rw [hshift]
      _ ≤ ‖digamma (z + n)‖ + ‖∑ i ∈ Finset.range n, (z + i)⁻¹‖ :=
            norm_sub_le _ _
      _ ≤ Cleft * Real.log |T| ^ (9 : ℕ) + (n : ℝ) :=
            add_le_add hshift_bound hsum_bound
      _ ≤ Cleft * Real.log |T| ^ (9 : ℕ) +
            (n : ℝ) * Real.log |T| ^ (9 : ℕ) := by
            have hn_absorb :
                (n : ℝ) ≤ (n : ℝ) * Real.log |T| ^ (9 : ℕ) := by
              calc
                (n : ℝ) = (n : ℝ) * 1 := by ring
                _ ≤ (n : ℝ) * Real.log |T| ^ (9 : ℕ) :=
                    mul_le_mul_of_nonneg_left hlog_pow_one (Nat.cast_nonneg n)
            exact add_le_add_right hn_absorb _
      _ = (Cleft + n) * Real.log |T| ^ (9 : ℕ) := by
            ring
  let w : ℂ := 1 - (((σ : ℂ) + (T : ℂ) * I))
  have hw_re_left : 1 ≤ w.re := by
    dsimp [w]
    simp
    linarith
  have hw_re_right : w.re ≤ 1 + a := by
    dsimp [w]
    simp
    linarith
  have hw_im : w.im = -T := by
    simp [w]
  have hright :
      ‖digamma (w / 2)‖ ≤ Cright * Real.log |T| ^ (9 : ℕ) := by
    calc
      ‖digamma (w / 2)‖
          ≤ Cright * Real.log (|w.im| + 2) :=
            hCright_bound w hw_re_left hw_re_right
      _ = Cright * Real.log (|T| + 2) := by
            rw [hw_im, abs_neg]
      _ ≤ Cright * Real.log |T| ^ (9 : ℕ) :=
            mul_le_mul_of_nonneg_left hlog_abs_add hCright_pos.le
  have hpair :
      ‖(1 / 2 : ℂ) * (digamma z + digamma (w / 2))‖
        ≤ (Cleft + Cright + n) * Real.log |T| ^ (9 : ℕ) := by
    calc
      ‖(1 / 2 : ℂ) * (digamma z + digamma (w / 2))‖
          ≤ ‖digamma z + digamma (w / 2)‖ := by
            have hhalf_norm : ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) := by norm_num
            calc
              ‖(1 / 2 : ℂ) * (digamma z + digamma (w / 2))‖
                  = ‖(1 / 2 : ℂ)‖ * ‖digamma z + digamma (w / 2)‖ := norm_mul _ _
              _ ≤ 1 * ‖digamma z + digamma (w / 2)‖ :=
                    mul_le_mul_of_nonneg_right hhalf_norm (norm_nonneg _)
              _ = ‖digamma z + digamma (w / 2)‖ := by ring
      _ ≤ ‖digamma z‖ + ‖digamma (w / 2)‖ := norm_add_le _ _
      _ ≤ (Cleft + n) * Real.log |T| ^ (9 : ℕ) +
            Cright * Real.log |T| ^ (9 : ℕ) :=
            add_le_add hleft hright
      _ = (Cleft + Cright + n) * Real.log |T| ^ (9 : ℕ) := by
            ring
  simpa [z, w, add_comm, add_left_comm, add_assoc] using hpair

/--
Eventual pointwise logarithmic control of the digamma pair supplies the nonpositive
horizontal-segment digamma budget with the same logarithmic growth.
-/
theorem
    eventually_kadiri_digamma_pair_nonpositive_horizontal_integral_bound_of_pointwise_log_bound_on_filter
    (a G : ℝ) (ha : 0 ≤ a) (L : Filter ℝ)
    (hpoint : ∀ᶠ T : ℝ in L,
      ∀ σ ∈ Ι (-a) 0,
        ‖(1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖
          ≤ G * Real.log |T| ^ 9) :
    ∀ᶠ T : ℝ in L,
      ‖∫ σ in (-a)..0,
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖
        ≤ (G * Real.log |T| ^ 9) * a := by
  filter_upwards [hpoint] with T hT_point
  exact kadiri_digamma_pair_nonpositive_horizontal_integral_bound_of_pointwise_bound
    a T (G * Real.log |T| ^ 9) ha hT_point

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

/-- The actual zeta logarithmic-derivative integrand is integrable on the right segment. -/
theorem kadiri_neg_zeta_logDeriv_right_intervalIntegrable_of_offPole
    (a T : ℝ) (ha : 0 ≤ a) (hT : kadiriHorizontalZetaOffPoleHeight T) :
    IntervalIntegrable
      (fun σ : ℝ =>
        -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I)))
      volume 0 (1 + a) := by
  have hfull :=
    kadiri_neg_zeta_logDeriv_horizontal_intervalIntegrable_of_offPole a T ha hT
  have hright : 0 ≤ 1 + a := by linarith
  have hfull_interval : -a ≤ 1 + a := by linarith
  refine hfull.mono_set ?_
  intro σ hσ
  rw [Set.uIcc_of_le hright] at hσ
  rw [Set.uIcc_of_le hfull_interval]
  exact ⟨by linarith [hσ.1], hσ.2⟩

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

/-- The sign-correct dyadic zeta Hadamard/PV remainder is integrable off the zero heights. -/
theorem kadiriDyadicZetaLogDerivPVRemainder_intervalIntegrable_of_offPole
    (a T : ℝ) (ha : 0 ≤ a) (k : ℕ) (hT : kadiriHorizontalZetaOffPoleHeight T) :
    IntervalIntegrable (fun σ : ℝ => kadiriDyadicZetaLogDerivPVRemainder k T σ)
      volume (-a) (1 + a) := by
  have hactual :=
    kadiri_neg_zeta_logDeriv_horizontal_intervalIntegrable_of_offPole a T ha hT
  have hderiv :
      IntervalIntegrable
        (fun σ : ℝ =>
          deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I)))
        volume (-a) (1 + a) := by
    convert hactual.neg using 1
    ext σ
    simp
    ring
  have hprincipal :=
    kadiriDyadicPrincipalPart_intervalIntegrable_of_offPole a T k hT
  simpa [kadiriDyadicZetaLogDerivPVRemainder] using hderiv.sub hprincipal

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
Filter-parametric version of the concrete Kadiri remainder budget from the sign-correct
zeta remainder budget and the already-proved moving-pole weighted-count estimate.

This is the analytic handoff: it is enough to control the integral of the genuinely
Hadamard-local remainder for `ζ'/ζ`; the extra principal part caused by the `-ζ'/ζ`
sign is absorbed by the same finite moving-pole estimate used in the full-segment assembly.
-/
theorem
    eventually_kadiriDyadicHadamardPVRemainder_integral_bound_of_zeta_remainder_bound_on_filter
    (a e : ℝ) (ha : 0 ≤ a) (he : 0 < e) (hea : e ≤ a) (k : ℕ) (B : ℝ)
    (L : Filter ℝ) (hL : L ≤ Filter.cofinite)
    (hoff : ∀ᶠ T : ℝ in L, kadiriHorizontalZetaOffPoleHeight T)
    (hzeta_rem_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in (-a)..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in L,
        ‖∫ σ in (-a)..(1 + a), kadiriDyadicHadamardPVRemainder k T σ‖
          ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
              weightedZeroHeightBucket) * C + B := by
  classical
  obtain ⟨C, hC, hprincipal_bound⟩ :=
    kadiri_moving_pole_zeta_principal_part_dyadic_horizontal_integral_weighted_count_eventually
      a e he hea k
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hprincipal_bound.filter_mono hL, hzeta_rem_bound, hoff]
    with T hprincipal hzeta_rem hT
  let principal : ℝ → ℂ := fun σ =>
    ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
      ((riemannZeta.order (rho : ℂ) : ℂ) /
        (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))
  let zetaRem : ℝ → ℂ := fun σ => kadiriDyadicZetaLogDerivPVRemainder k T σ
  have hprincipal_int :
      IntervalIntegrable principal volume (-a) (1 + a) := by
    simpa [principal] using
      kadiriDyadicPrincipalPart_intervalIntegrable_of_offPole a T k hT
  have hzetaRem_int :
      IntervalIntegrable zetaRem volume (-a) (1 + a) := by
    simpa [zetaRem] using
      kadiriDyadicZetaLogDerivPVRemainder_intervalIntegrable_of_offPole a T ha k hT
  have hscaled_int :
      IntervalIntegrable (fun σ : ℝ => (2 : ℂ) * principal σ) volume (-a) (1 + a) :=
    hprincipal_int.const_mul (2 : ℂ)
  have hEq :
      Set.EqOn
        (fun σ : ℝ => kadiriDyadicHadamardPVRemainder k T σ)
        (fun σ : ℝ => -zetaRem σ - (2 : ℂ) * principal σ)
        [[-a, 1 + a]] := by
    intro σ _hσ
    simp [kadiriDyadicHadamardPVRemainder, kadiriDyadicZetaLogDerivPVRemainder,
      zetaRem, principal]
    ring
  have hsplit :
      (∫ σ in (-a)..(1 + a), -zetaRem σ - (2 : ℂ) * principal σ) =
        -(∫ σ in (-a)..(1 + a), zetaRem σ) -
          (2 : ℂ) * ∫ σ in (-a)..(1 + a), principal σ := by
    calc
      (∫ σ in (-a)..(1 + a), -zetaRem σ - (2 : ℂ) * principal σ)
          = ∫ σ in (-a)..(1 + a),
              ((-zetaRem) - fun τ : ℝ => (2 : ℂ) * principal τ) σ := by
            rfl
      _ = (∫ σ in (-a)..(1 + a), (-zetaRem) σ) -
            ∫ σ in (-a)..(1 + a), (fun τ : ℝ => (2 : ℂ) * principal τ) σ := by
            exact intervalIntegral.integral_sub hzetaRem_int.neg hscaled_int
      _ = -(∫ σ in (-a)..(1 + a), zetaRem σ) -
            (2 : ℂ) * ∫ σ in (-a)..(1 + a), principal σ := by
            simp
  have hprincipal' :
      ‖∫ σ in (-a)..(1 + a), principal σ‖
        ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
            weightedZeroHeightBucket) * C := by
    simpa [principal] using hprincipal
  calc
    ‖∫ σ in (-a)..(1 + a), kadiriDyadicHadamardPVRemainder k T σ‖
        = ‖∫ σ in (-a)..(1 + a), -zetaRem σ - (2 : ℂ) * principal σ‖ := by
          rw [intervalIntegral.integral_congr hEq]
    _ = ‖-(∫ σ in (-a)..(1 + a), zetaRem σ) -
          (2 : ℂ) * ∫ σ in (-a)..(1 + a), principal σ‖ := by
          rw [hsplit]
    _ ≤ ‖∫ σ in (-a)..(1 + a), zetaRem σ‖ +
          ‖(2 : ℂ) * ∫ σ in (-a)..(1 + a), principal σ‖ := by
          simpa [sub_eq_add_neg, norm_neg, add_comm, add_left_comm, add_assoc] using
            norm_add_le (-(∫ σ in (-a)..(1 + a), zetaRem σ))
              (-((2 : ℂ) * ∫ σ in (-a)..(1 + a), principal σ))
    _ ≤ B + 2 * ((2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
          weightedZeroHeightBucket) * C) := by
          refine add_le_add hzeta_rem ?_
          calc
            ‖(2 : ℂ) * ∫ σ in (-a)..(1 + a), principal σ‖
                = 2 * ‖∫ σ in (-a)..(1 + a), principal σ‖ := by
                  simp
            _ ≤ 2 * ((2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
                  weightedZeroHeightBucket) * C) := by
                  exact mul_le_mul_of_nonneg_left hprincipal' (by norm_num)
    _ = (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
          weightedZeroHeightBucket) * (2 * C) + B := by
          ring

/--
The concrete Kadiri remainder budget on the canonical off-pole filter follows from the
sign-correct zeta remainder budget.
-/
theorem
    eventually_kadiriDyadicHadamardPVRemainder_integral_bound_of_zeta_remainder_bound
    (a e : ℝ) (ha : 0 ≤ a) (he : 0 < e) (hea : e ≤ a) (k : ℕ) (B : ℝ)
    (hzeta_rem_bound : ∀ᶠ T : ℝ in kadiriHorizontalZetaOffPoleFilter,
      ‖∫ σ in (-a)..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a), kadiriDyadicHadamardPVRemainder k T σ‖
          ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
              weightedZeroHeightBucket) * C + B := by
  exact
    eventually_kadiriDyadicHadamardPVRemainder_integral_bound_of_zeta_remainder_bound_on_filter
      a e ha he hea k B kadiriHorizontalZetaOffPoleFilter
      kadiriHorizontalZetaOffPoleFilter_le_cofinite
      eventually_kadiriHorizontalZetaOffPoleHeight hzeta_rem_bound

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
Full-segment dyadic off-pole bound from an integral budget for the sign-correct zeta
Hadamard/PV remainder.

This filter-parametric form is the moving-pole PV handoff: once the sign-correct zeta
remainder is controlled on any off-pole height filter, the finite pole-sum estimate and
the concrete full-segment assembly give the corresponding off-pole bound.
-/
theorem
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_zeta_remainder_bound_on_filter
    (a e : ℝ) (ha : 0 ≤ a) (he : 0 < e) (hea : e ≤ a) (k : ℕ) (B : ℝ)
    (L : Filter ℝ) (hL : L ≤ Filter.cofinite)
    (hoff : ∀ᶠ T : ℝ in L, kadiriHorizontalZetaOffPoleHeight T)
    (hzeta_rem_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in (-a)..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in L,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
              weightedZeroHeightBucket) * C + B := by
  obtain ⟨Crem, hCrem, hrem_bound⟩ :=
    eventually_kadiriDyadicHadamardPVRemainder_integral_bound_of_zeta_remainder_bound_on_filter
      a e ha he hea k B L hL hoff hzeta_rem_bound
  have hrem_int : ∀ᶠ T : ℝ in L,
      IntervalIntegrable (fun σ : ℝ => kadiriDyadicHadamardPVRemainder k T σ)
        volume (-a) (1 + a) := by
    filter_upwards [hoff] with T hT
    exact kadiriDyadicHadamardPVRemainder_intervalIntegrable_of_offPole a T ha k hT
  obtain ⟨Cmain, hCmain, hmain⟩ :=
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_concrete_remainder_budget_on_filter
      a e he hea k
      ((2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| + weightedZeroHeightBucket) * Crem + B)
      L hL hrem_int hrem_bound
  refine ⟨Cmain + Crem, add_nonneg hCmain hCrem, ?_⟩
  filter_upwards [hmain] with T hT
  calc
    ‖∫ σ in (-a)..(1 + a),
        -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
            weightedZeroHeightBucket) * Cmain +
          ((2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
              weightedZeroHeightBucket) * Crem + B) := hT
    _ = (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
          weightedZeroHeightBucket) * (Cmain + Crem) + B := by
          ring

/--
Full-segment dyadic off-pole bound from an integral budget for the sign-correct zeta
Hadamard/PV remainder.

This is the non-pointwise route needed for the moving-pole PV lane: the singular principal
part is integrated and paid for by the finite zero-counting budget, while the analytic
Hadamard remainder only has to be controlled after integration on the segment.
-/
theorem
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_zeta_remainder_bound
    (a e : ℝ) (ha : 0 ≤ a) (he : 0 < e) (hea : e ≤ a) (k : ℕ) (B : ℝ)
    (hzeta_rem_bound : ∀ᶠ T : ℝ in kadiriHorizontalZetaOffPoleFilter,
      ‖∫ σ in (-a)..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
              weightedZeroHeightBucket) * C + B := by
  exact
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_zeta_remainder_bound_on_filter
      a e ha he hea k B kadiriHorizontalZetaOffPoleFilter
      kadiriHorizontalZetaOffPoleFilter_le_cofinite
      eventually_kadiriHorizontalZetaOffPoleHeight hzeta_rem_bound

/--
Right-segment actual zeta logarithmic-derivative bound from the sign-correct zeta
Hadamard/PV remainder and the finite principal-part budget on the same right segment.
-/
theorem kadiri_right_segment_logDeriv_integral_bound_of_zeta_remainder_and_principal
    (a T : ℝ) (ha : 0 ≤ a) (k : ℕ) (P B : ℝ)
    (hT : kadiriHorizontalZetaOffPoleHeight T)
    (hprincipal_bound :
      ‖∫ σ in 0..(1 + a),
          ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
            ((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖ ≤ P)
    (hzeta_rem_bound :
      ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ‖∫ σ in 0..(1 + a),
        -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖ ≤ B + P := by
  let principal : ℝ → ℂ := fun σ =>
    ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
      ((riemannZeta.order (rho : ℂ) : ℂ) /
        (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))
  let zetaRem : ℝ → ℂ := fun σ => kadiriDyadicZetaLogDerivPVRemainder k T σ
  have hright : 0 ≤ 1 + a := by linarith
  have hfull_interval : -a ≤ 1 + a := by linarith
  have hsubset : Set.uIcc 0 (1 + a) ⊆ Set.uIcc (-a) (1 + a) := by
    intro σ hσ
    rw [Set.uIcc_of_le hright] at hσ
    rw [Set.uIcc_of_le hfull_interval]
    exact ⟨by linarith [hσ.1], hσ.2⟩
  have hprincipal_int :
      IntervalIntegrable principal volume 0 (1 + a) := by
    have hprincipal_full :
        IntervalIntegrable principal volume (-a) (1 + a) := by
      simpa [principal] using
        kadiriDyadicPrincipalPart_intervalIntegrable_of_offPole a T k hT
    exact hprincipal_full.mono_set hsubset
  have hzetaRem_int :
      IntervalIntegrable zetaRem volume 0 (1 + a) := by
    have hzetaRem_full :
        IntervalIntegrable zetaRem volume (-a) (1 + a) := by
      simpa [zetaRem] using
        kadiriDyadicZetaLogDerivPVRemainder_intervalIntegrable_of_offPole a T ha k hT
    exact hzetaRem_full.mono_set hsubset
  have hEq :
      Set.EqOn
        (fun σ : ℝ =>
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I)))
        (fun σ : ℝ => -zetaRem σ - principal σ)
        [[0, 1 + a]] := by
    intro σ _hσ
    simp [kadiriDyadicZetaLogDerivPVRemainder, zetaRem, principal]
    ring
  have hsplit :
      (∫ σ in 0..(1 + a), -zetaRem σ - principal σ) =
        -(∫ σ in 0..(1 + a), zetaRem σ) -
          ∫ σ in 0..(1 + a), principal σ := by
    calc
      (∫ σ in 0..(1 + a), -zetaRem σ - principal σ)
          = ∫ σ in 0..(1 + a), ((-zetaRem) - principal) σ := by
            rfl
      _ = (∫ σ in 0..(1 + a), (-zetaRem) σ) -
            ∫ σ in 0..(1 + a), principal σ := by
            exact intervalIntegral.integral_sub hzetaRem_int.neg hprincipal_int
      _ = -(∫ σ in 0..(1 + a), zetaRem σ) -
            ∫ σ in 0..(1 + a), principal σ := by
            simp
  have hprincipal' :
      ‖∫ σ in 0..(1 + a), principal σ‖ ≤ P := by
    simpa [principal] using hprincipal_bound
  calc
    ‖∫ σ in 0..(1 + a),
        -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        = ‖∫ σ in 0..(1 + a), -zetaRem σ - principal σ‖ := by
          rw [intervalIntegral.integral_congr hEq]
    _ = ‖-(∫ σ in 0..(1 + a), zetaRem σ) -
          ∫ σ in 0..(1 + a), principal σ‖ := by
          rw [hsplit]
    _ ≤ ‖∫ σ in 0..(1 + a), zetaRem σ‖ +
          ‖∫ σ in 0..(1 + a), principal σ‖ := by
          simpa [sub_eq_add_neg, norm_neg, add_comm, add_left_comm, add_assoc] using
            norm_add_le (-(∫ σ in 0..(1 + a), zetaRem σ))
              (-(∫ σ in 0..(1 + a), principal σ))
    _ ≤ B + P := add_le_add hzeta_rem_bound hprincipal'

/--
Eventual right-segment actual zeta logarithmic-derivative bound from right-segment
principal-part and sign-correct zeta remainder budgets.
-/
theorem
    eventually_kadiri_right_segment_logDeriv_integral_bound_of_zeta_remainder_and_principal_on_filter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (P B : ℝ) (L : Filter ℝ)
    (hoff : ∀ᶠ T : ℝ in L, kadiriHorizontalZetaOffPoleHeight T)
    (hprincipal_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in 0..(1 + a),
          ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
            ((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖ ≤ P)
    (hzeta_rem_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ∀ᶠ T : ℝ in L,
      ‖∫ σ in 0..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖ ≤ B + P := by
  filter_upwards [hoff, hprincipal_bound, hzeta_rem_bound]
    with T hT hprincipal_T hzeta_T
  exact
    kadiri_right_segment_logDeriv_integral_bound_of_zeta_remainder_and_principal
      a T ha k P B hT hprincipal_T hzeta_T

/--
Right-segment sign-correct zeta PV remainder bound from the actual right `-ζ'/ζ`
integral and the moving-pole principal-part integral.

This is the reverse algebraic handoff to
`kadiri_right_segment_logDeriv_integral_bound_of_zeta_remainder_and_principal`: it
turns a direct right-strip logarithmic-derivative estimate plus the finite moving-pole
budget into the integral budget for `kadiriDyadicZetaLogDerivPVRemainder`.
-/
theorem
    kadiriDyadicZetaLogDerivPVRemainder_right_integral_bound_of_logDeriv_and_principal
    (a T : ℝ) (ha : 0 ≤ a) (k : ℕ) (Q P : ℝ)
    (hT : kadiriHorizontalZetaOffPoleHeight T)
    (hlogDeriv_bound :
      ‖∫ σ in 0..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖ ≤ Q)
    (hprincipal_bound :
      ‖∫ σ in 0..(1 + a),
          ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
            ((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖ ≤ P) :
    ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ Q + P := by
  let actual : ℝ → ℂ := fun σ =>
    -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
      riemannZeta (((σ : ℂ) + (T : ℂ) * I))
  let principal : ℝ → ℂ := fun σ =>
    ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
      ((riemannZeta.order (rho : ℂ) : ℂ) /
        (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))
  let zetaRem : ℝ → ℂ := fun σ => kadiriDyadicZetaLogDerivPVRemainder k T σ
  have hright : 0 ≤ 1 + a := by linarith
  have hfull_interval : -a ≤ 1 + a := by linarith
  have hsubset : Set.uIcc 0 (1 + a) ⊆ Set.uIcc (-a) (1 + a) := by
    intro σ hσ
    rw [Set.uIcc_of_le hright] at hσ
    rw [Set.uIcc_of_le hfull_interval]
    exact ⟨by linarith [hσ.1], hσ.2⟩
  have hactual_int :
      IntervalIntegrable actual volume 0 (1 + a) := by
    simpa [actual] using
      kadiri_neg_zeta_logDeriv_right_intervalIntegrable_of_offPole a T ha hT
  have hprincipal_int :
      IntervalIntegrable principal volume 0 (1 + a) := by
    have hprincipal_full :
        IntervalIntegrable principal volume (-a) (1 + a) := by
      simpa [principal] using
        kadiriDyadicPrincipalPart_intervalIntegrable_of_offPole a T k hT
    exact hprincipal_full.mono_set hsubset
  have hEq :
      Set.EqOn zetaRem (fun σ : ℝ => -actual σ - principal σ) [[0, 1 + a]] := by
    intro σ _hσ
    simp [kadiriDyadicZetaLogDerivPVRemainder, zetaRem, actual, principal]
    ring
  have hsplit :
      (∫ σ in 0..(1 + a), zetaRem σ) =
        -(∫ σ in 0..(1 + a), actual σ) -
          ∫ σ in 0..(1 + a), principal σ := by
    calc
      (∫ σ in 0..(1 + a), zetaRem σ)
          = ∫ σ in 0..(1 + a), -actual σ - principal σ := by
            rw [intervalIntegral.integral_congr hEq]
      _ = ∫ σ in 0..(1 + a), ((-actual) - principal) σ := by
            rfl
      _ = (∫ σ in 0..(1 + a), (-actual) σ) -
            ∫ σ in 0..(1 + a), principal σ := by
            exact intervalIntegral.integral_sub hactual_int.neg hprincipal_int
      _ = -(∫ σ in 0..(1 + a), actual σ) -
            ∫ σ in 0..(1 + a), principal σ := by
            simp
  have hactual' :
      ‖∫ σ in 0..(1 + a), actual σ‖ ≤ Q := by
    simpa [actual] using hlogDeriv_bound
  have hprincipal' :
      ‖∫ σ in 0..(1 + a), principal σ‖ ≤ P := by
    simpa [principal] using hprincipal_bound
  calc
    ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        = ‖-(∫ σ in 0..(1 + a), actual σ) -
            ∫ σ in 0..(1 + a), principal σ‖ := by
          simp [zetaRem, hsplit]
    _ ≤ ‖∫ σ in 0..(1 + a), actual σ‖ +
          ‖∫ σ in 0..(1 + a), principal σ‖ := by
          simpa [sub_eq_add_neg, norm_neg, add_comm, add_left_comm, add_assoc] using
            norm_add_le (-(∫ σ in 0..(1 + a), actual σ))
              (-(∫ σ in 0..(1 + a), principal σ))
    _ ≤ Q + P := add_le_add hactual' hprincipal'

/--
Filter form of
`kadiriDyadicZetaLogDerivPVRemainder_right_integral_bound_of_logDeriv_and_principal`.
-/
theorem
    eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_bound_of_logDeriv_and_principal_on_filter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (Q P : ℝ) (L : Filter ℝ)
    (hoff : ∀ᶠ T : ℝ in L, kadiriHorizontalZetaOffPoleHeight T)
    (hlogDeriv_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in 0..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖ ≤ Q)
    (hprincipal_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in 0..(1 + a),
          ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
            ((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖ ≤ P) :
    ∀ᶠ T : ℝ in L,
      ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ Q + P := by
  filter_upwards [hoff, hlogDeriv_bound, hprincipal_bound]
    with T hT hlog_T hprincipal_T
  exact
    kadiriDyadicZetaLogDerivPVRemainder_right_integral_bound_of_logDeriv_and_principal
      a T ha k Q P hT hlog_T hprincipal_T

/--
Terminal-subsegment version of the sign-correct zeta PV remainder bound.

It is the same algebra as the full right-segment handoff, but localized to
`[x, 1 + a]` so the terminal right-half-plane estimate can be used before the
hard nonterminal PV piece is proved.
-/
theorem
    kadiriDyadicZetaLogDerivPVRemainder_terminal_right_integral_bound_of_logDeriv_and_principal
    (a x T : ℝ) (ha : 0 ≤ a) (hx_left : -a ≤ x) (hx_right : x ≤ 1 + a)
    (k : ℕ) (Q P : ℝ)
    (hT : kadiriHorizontalZetaOffPoleHeight T)
    (hlogDeriv_bound :
      ‖∫ σ in x..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖ ≤ Q)
    (hprincipal_bound :
      ‖∫ σ in x..(1 + a),
          ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
            ((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖ ≤ P) :
    ‖∫ σ in x..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ Q + P := by
  let actual : ℝ → ℂ := fun σ =>
    -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
      riemannZeta (((σ : ℂ) + (T : ℂ) * I))
  let principal : ℝ → ℂ := fun σ =>
    ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
      ((riemannZeta.order (rho : ℂ) : ℂ) /
        (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))
  let zetaRem : ℝ → ℂ := fun σ => kadiriDyadicZetaLogDerivPVRemainder k T σ
  have hfull_interval : -a ≤ 1 + a := by linarith
  have hsubset : Set.uIcc x (1 + a) ⊆ Set.uIcc (-a) (1 + a) := by
    intro σ hσ
    rw [Set.uIcc_of_le hx_right] at hσ
    rw [Set.uIcc_of_le hfull_interval]
    exact ⟨le_trans hx_left hσ.1, hσ.2⟩
  have hactual_int :
      IntervalIntegrable actual volume x (1 + a) := by
    have hactual_full :
        IntervalIntegrable actual volume (-a) (1 + a) := by
      simpa [actual] using
        kadiri_neg_zeta_logDeriv_horizontal_intervalIntegrable_of_offPole a T ha hT
    exact hactual_full.mono_set hsubset
  have hprincipal_int :
      IntervalIntegrable principal volume x (1 + a) := by
    have hprincipal_full :
        IntervalIntegrable principal volume (-a) (1 + a) := by
      simpa [principal] using
        kadiriDyadicPrincipalPart_intervalIntegrable_of_offPole a T k hT
    exact hprincipal_full.mono_set hsubset
  have hEq :
      Set.EqOn zetaRem (fun σ : ℝ => -actual σ - principal σ) [[x, 1 + a]] := by
    intro σ _hσ
    simp [kadiriDyadicZetaLogDerivPVRemainder, zetaRem, actual, principal]
    ring
  have hsplit :
      (∫ σ in x..(1 + a), zetaRem σ) =
        -(∫ σ in x..(1 + a), actual σ) -
          ∫ σ in x..(1 + a), principal σ := by
    calc
      (∫ σ in x..(1 + a), zetaRem σ)
          = ∫ σ in x..(1 + a), -actual σ - principal σ := by
            rw [intervalIntegral.integral_congr hEq]
      _ = ∫ σ in x..(1 + a), ((-actual) - principal) σ := by
            rfl
      _ = (∫ σ in x..(1 + a), (-actual) σ) -
            ∫ σ in x..(1 + a), principal σ := by
            exact intervalIntegral.integral_sub hactual_int.neg hprincipal_int
      _ = -(∫ σ in x..(1 + a), actual σ) -
            ∫ σ in x..(1 + a), principal σ := by
            simp
  have hactual' :
      ‖∫ σ in x..(1 + a), actual σ‖ ≤ Q := by
    simpa [actual] using hlogDeriv_bound
  have hprincipal' :
      ‖∫ σ in x..(1 + a), principal σ‖ ≤ P := by
    simpa [principal] using hprincipal_bound
  calc
    ‖∫ σ in x..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        = ‖-(∫ σ in x..(1 + a), actual σ) -
            ∫ σ in x..(1 + a), principal σ‖ := by
          simp [zetaRem, hsplit]
    _ ≤ ‖∫ σ in x..(1 + a), actual σ‖ +
          ‖∫ σ in x..(1 + a), principal σ‖ := by
          simpa [sub_eq_add_neg, norm_neg, add_comm, add_left_comm, add_assoc] using
            norm_add_le (-(∫ σ in x..(1 + a), actual σ))
              (-(∫ σ in x..(1 + a), principal σ))
    _ ≤ Q + P := add_le_add hactual' hprincipal'

/--
Right-segment split for the sign-correct zeta PV remainder.

It turns a nonterminal bound on `[0, x]` and a terminal bound on `[x, 1 + a]`
into the full right-segment bound on `[0, 1 + a]`.
-/
theorem kadiriDyadicZetaLogDerivPVRemainder_right_integral_bound_of_split
    (a x T : ℝ) (ha : 0 ≤ a) (hx0 : 0 ≤ x) (hx_right : x ≤ 1 + a)
    (k : ℕ) (B E : ℝ)
    (hT : kadiriHorizontalZetaOffPoleHeight T)
    (hleft_bound :
      ‖∫ σ in 0..x, kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B)
    (hterminal_bound :
      ‖∫ σ in x..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ E) :
    ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B + E := by
  let rem : ℝ → ℂ := fun σ => kadiriDyadicZetaLogDerivPVRemainder k T σ
  have hfull_interval : -a ≤ 1 + a := by linarith
  have hleft_subset : Set.uIcc 0 x ⊆ Set.uIcc (-a) (1 + a) := by
    intro σ hσ
    rw [Set.uIcc_of_le hx0] at hσ
    rw [Set.uIcc_of_le hfull_interval]
    exact ⟨by linarith [ha, hσ.1], le_trans hσ.2 hx_right⟩
  have hterminal_subset : Set.uIcc x (1 + a) ⊆ Set.uIcc (-a) (1 + a) := by
    intro σ hσ
    rw [Set.uIcc_of_le hx_right] at hσ
    rw [Set.uIcc_of_le hfull_interval]
    exact ⟨by linarith [ha, hx0, hσ.1], hσ.2⟩
  have hfull_int :
      IntervalIntegrable rem volume (-a) (1 + a) := by
    simpa [rem] using
      kadiriDyadicZetaLogDerivPVRemainder_intervalIntegrable_of_offPole a T ha k hT
  have hleft_int : IntervalIntegrable rem volume 0 x :=
    hfull_int.mono_set hleft_subset
  have hterminal_int : IntervalIntegrable rem volume x (1 + a) :=
    hfull_int.mono_set hterminal_subset
  have hsplit :
      (∫ σ in 0..x, rem σ) + (∫ σ in x..(1 + a), rem σ) =
        ∫ σ in 0..(1 + a), rem σ := by
    exact intervalIntegral.integral_add_adjacent_intervals hleft_int hterminal_int
  have hleft' : ‖∫ σ in 0..x, rem σ‖ ≤ B := by
    simpa [rem] using hleft_bound
  have hterminal' : ‖∫ σ in x..(1 + a), rem σ‖ ≤ E := by
    simpa [rem] using hterminal_bound
  calc
    ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        = ‖∫ σ in 0..(1 + a), rem σ‖ := by
          simp [rem]
    _ = ‖(∫ σ in 0..x, rem σ) + (∫ σ in x..(1 + a), rem σ)‖ := by
          rw [← hsplit]
    _ ≤ ‖∫ σ in 0..x, rem σ‖ + ‖∫ σ in x..(1 + a), rem σ‖ :=
          norm_add_le _ _
    _ ≤ B + E := add_le_add hleft' hterminal'

/--
A pointwise bound for the sign-correct zeta Hadamard/PV remainder controls its
right-segment integral.
-/
theorem kadiriDyadicZetaLogDerivPVRemainder_right_integral_bound_of_pointwise_bound
    (a T : ℝ) (ha : 0 ≤ a) (k : ℕ) (B : ℝ)
    (hpoint : ∀ σ ∈ Ι 0 (1 + a),
      ‖kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤
      B * (1 + a) := by
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := 1 + a) (C := B)
      (f := fun σ : ℝ => kadiriDyadicZetaLogDerivPVRemainder k T σ) hpoint
  have hlen_abs : |1 + a| = 1 + a := by
    rw [abs_of_nonneg]
    linarith
  simpa [hlen_abs] using hnorm

/--
Eventual pointwise control of the sign-correct zeta Hadamard/PV remainder supplies the
right-segment integral budget expected by the full-segment assembly.
-/
theorem
    eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_bound_of_pointwise_bound_on_filter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (B : ℝ) (L : Filter ℝ)
    (hpoint : ∀ᶠ T : ℝ in L,
      ∀ σ ∈ Ι 0 (1 + a),
        ‖kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ∀ᶠ T : ℝ in L,
      ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤
        B * (1 + a) := by
  filter_upwards [hpoint] with T hT_point
  exact kadiriDyadicZetaLogDerivPVRemainder_right_integral_bound_of_pointwise_bound
    a T ha k B hT_point

/--
Eventual pointwise logarithmic control of the sign-correct zeta Hadamard/PV remainder
supplies a right-segment integral budget with the same logarithmic growth.
-/
theorem
    eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_bound_of_pointwise_log_bound_on_filter
    (a Z : ℝ) (ha : 0 ≤ a) (k : ℕ) (L : Filter ℝ)
    (hpoint : ∀ᶠ T : ℝ in L,
      ∀ σ ∈ Ι 0 (1 + a),
        ‖kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ Z * Real.log |T| ^ 9) :
    ∀ᶠ T : ℝ in L,
      ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤
        (Z * Real.log |T| ^ 9) * (1 + a) := by
  filter_upwards [hpoint] with T hT_point
  exact kadiriDyadicZetaLogDerivPVRemainder_right_integral_bound_of_pointwise_bound
    a T ha k (Z * Real.log |T| ^ 9) hT_point

/--
Full-segment assembly from reflected nonpositive control and right-segment zeta
Hadamard/PV plus principal-part budgets.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_reflected_and_right_zeta_remainder_on_filter
    (a D P B : ℝ) (ha : 0 ≤ a) (k : ℕ) (L : Filter ℝ)
    (hlarge : ∀ᶠ T : ℝ in L, 3 < |T|)
    (hoff : ∀ᶠ T : ℝ in L, kadiriHorizontalZetaOffPoleHeight T)
    (hdigamma_int : ∀ᶠ T : ℝ in L,
      IntervalIntegrable
        (fun σ : ℝ =>
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2))))
        volume (-a) 0)
    (hdigamma_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in (-a)..0,
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖ ≤ D)
    (hprincipal_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in 0..(1 + a), (
          ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
            ((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖ ≤ P)
    (hzeta_rem_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in L,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ ((C * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a + D) + (B + P) := by
  have hright_int : ∀ᶠ T : ℝ in L,
      IntervalIntegrable
        (fun σ : ℝ =>
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I)))
        volume 0 (1 + a) := by
    filter_upwards [hoff] with T hT
    exact kadiri_neg_zeta_logDeriv_right_intervalIntegrable_of_offPole a T ha hT
  have hright_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in 0..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖ ≤ B + P :=
    eventually_kadiri_right_segment_logDeriv_integral_bound_of_zeta_remainder_and_principal_on_filter
      a ha k P B L hoff hprincipal_bound hzeta_rem_bound
  exact
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_nonpositive_and_right_budget_on_filter
      a D (B + P) ha L hlarge hdigamma_int hdigamma_bound hright_int hright_bound

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

/--
Concrete truncated-zero right-segment version of the finite-family moving-pole bound.

The endpoint margin is an explicit real hypothesis on the truncated family. This is the
remaining selector obligation for plugging the right-segment pole budget into the
full-segment assembly.
-/
theorem kadiri_moving_pole_zeta_principal_part_truncated_right_integral_card_bound
    (a e R : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T M : ℝ),
        (∀ rho : NontrivialZeros,
          |(rho : ℂ).im| < R →
            (rho : ℂ).re ∈ Set.Icc e (1 + a - e) ∧ (rho : ℂ).im ≠ T) →
        (∀ rho : NontrivialZeros,
          |(rho : ℂ).im| < R →
            ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ ≤ M) →
          ‖∫ σ in 0..(1 + a), (
              ∑ rho ∈ kadiriTruncatedNontrivialZeros R,
                ((riemannZeta.order (rho : ℂ) : ℂ) /
                  (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
            ≤ (((kadiriTruncatedNontrivialZeros R).card : ℝ) * M) * C := by
  classical
  obtain ⟨C, hC, hcard⟩ :=
    kadiri_moving_pole_zeta_principal_part_finite_sum_right_integral_card_bound a e he
  refine ⟨C, hC, ?_⟩
  intro T M hmargin_off hM
  refine hcard (kadiriTruncatedNontrivialZeros R) T M ?_ ?_
  · intro rho hrho
    have him : |(rho : ℂ).im| < R := by
      simpa using (mem_kadiriTruncatedNontrivialZeros (R := R) (rho := rho)).mp hrho
    exact hmargin_off rho him
  · intro rho hrho
    have him : |(rho : ℂ).im| < R := by
      simpa using (mem_kadiriTruncatedNontrivialZeros (R := R) (rho := rho)).mp hrho
    exact hM rho him

/--
Eventual concrete right-segment pole budget for a truncated zero family.

This packages the moving-pole PV integral into the exact budget shape expected by the
right-segment zeta remainder assembly; the real-part margin and multiplicity cap are still
separate obligations.
-/
theorem
    eventually_kadiri_moving_pole_zeta_principal_part_truncated_right_integral_card_bound_on_filter
    (a e R M : ℝ) (he : 0 < e) (L : Filter ℝ)
    (hmargin_off : ∀ᶠ T : ℝ in L,
      ∀ rho : NontrivialZeros,
        |(rho : ℂ).im| < R →
          (rho : ℂ).re ∈ Set.Icc e (1 + a - e) ∧ (rho : ℂ).im ≠ T)
    (hM : ∀ rho : NontrivialZeros,
      |(rho : ℂ).im| < R →
        ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in L,
        ‖∫ σ in 0..(1 + a), (
            ∑ rho ∈ kadiriTruncatedNontrivialZeros R,
              ((riemannZeta.order (rho : ℂ) : ℂ) /
                (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
          ≤ (((kadiriTruncatedNontrivialZeros R).card : ℝ) * M) * C := by
  obtain ⟨C, hC, hcard⟩ :=
    kadiri_moving_pole_zeta_principal_part_truncated_right_integral_card_bound a e R he
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmargin_off] with T hT
  exact hcard T M hT hM

/--
Nonterminal right-subsegment principal-part bound for a truncated zero family.

The retained zeros may lie inside `[0, x]`; the transversal crossing kernel gives a
uniform integral bound as long as they stay a fixed distance from both endpoints.
-/
theorem
    kadiri_moving_pole_zeta_principal_part_truncated_nonterminal_right_integral_card_bound
    (a e d R : ℝ) (ha : 0 ≤ a) (he : 0 < e) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x T M : ℝ), 0 ≤ x → x ≤ 1 + a →
        (∀ rho : NontrivialZeros,
          |(rho : ℂ).im| < R →
            e ≤ (rho : ℂ).re ∧ (rho : ℂ).re + d ≤ x ∧ (rho : ℂ).im ≠ T) →
        (∀ rho : NontrivialZeros,
          |(rho : ℂ).im| < R →
            ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ ≤ M) →
          ‖∫ σ in 0..x, (
              ∑ rho ∈ kadiriTruncatedNontrivialZeros R,
                ((riemannZeta.order (rho : ℂ) : ℂ) /
                  (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
            ≤ (((kadiriTruncatedNontrivialZeros R).card : ℝ) * M) * C := by
  classical
  obtain ⟨C, hC, hcross⟩ :=
    transversal_pole_crossing_zero_to_norm_le a e d ha he hd
  refine ⟨C, hC, ?_⟩
  intro x T M hx0 hxle hmargin_off hM
  let S : Finset NontrivialZeros := kadiriTruncatedNontrivialZeros R
  let p : NontrivialZeros → ℝ → ℂ := fun rho σ =>
    ((riemannZeta.order (rho : ℂ) : ℂ) /
      (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))
  have hp_int : ∀ rho ∈ S, IntervalIntegrable (p rho) volume 0 x := by
    intro rho hrho
    have him : |(rho : ℂ).im| < R := by
      simpa [S] using (mem_kadiriTruncatedNontrivialZeros (R := R) (rho := rho)).mp hrho
    have hheight : (rho : ℂ).im ≠ T := (hmargin_off rho him).2.2
    simpa [p, sub_eq_add_neg] using
      (kadiri_moving_pole_principal_part_right_intervalIntegrable
        (a := x - 1) ((riemannZeta.order (rho : ℂ) : ℂ)) T (rho : ℂ) hheight)
  have hintegral_sum :
      (∫ σ in 0..x, ∑ rho ∈ S, p rho σ) =
        ∑ rho ∈ S, ∫ σ in 0..x, p rho σ := by
    exact intervalIntegral.integral_finsetSum hp_int
  have hsingle : ∀ rho ∈ S,
      ‖∫ σ in 0..x, p rho σ‖ ≤
        ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ * C := by
    intro rho hrho
    have him : |(rho : ℂ).im| < R := by
      simpa [S] using (mem_kadiriTruncatedNontrivialZeros (R := R) (rho := rho)).mp hrho
    let β : ℝ := (rho : ℂ).re
    let δ : ℝ := T - (rho : ℂ).im
    have hδ : δ ≠ 0 := by
      intro hδ0
      exact (hmargin_off rho him).2.2 (sub_eq_zero.mp hδ0).symm
    have hline (σ : ℝ) :
        (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)) =
          (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I) := by
      rw [Complex.ext_iff]
      constructor <;> simp [β, δ]
    have hfun :
        (fun σ : ℝ => p rho σ) =
          fun σ : ℝ =>
            (riemannZeta.order (rho : ℂ) : ℂ) *
              ((((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹) := by
      funext σ
      simp [p, hline σ, div_eq_mul_inv]
    rw [hfun, intervalIntegral.integral_const_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hcross x δ β hx0 hxle hδ (by simpa [β] using (hmargin_off rho him).1)
        (by simpa [β] using (hmargin_off rho him).2.1))
      (norm_nonneg _)
  calc
    ‖∫ σ in 0..x, (
        ∑ rho ∈ kadiriTruncatedNontrivialZeros R,
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
        = ‖∫ σ in 0..x, ∑ rho ∈ S, p rho σ‖ := by
          simp [S, p]
    _ = ‖∑ rho ∈ S, ∫ σ in 0..x, p rho σ‖ := by
          rw [hintegral_sum]
    _ ≤ ∑ rho ∈ S, ‖∫ σ in 0..x, p rho σ‖ :=
          norm_sum_le _ _
    _ ≤ ∑ rho ∈ S, M * C := by
          refine Finset.sum_le_sum fun rho hrho => ?_
          have him : |(rho : ℂ).im| < R := by
            simpa [S] using
              (mem_kadiriTruncatedNontrivialZeros (R := R) (rho := rho)).mp hrho
          exact (hsingle rho hrho).trans
            (mul_le_mul_of_nonneg_right (hM rho him) hC)
    _ = (((kadiriTruncatedNontrivialZeros R).card : ℝ) * M) * C := by
          simp [S, Finset.sum_const, nsmul_eq_mul]
          ring

/--
Large off-pole nonterminal principal-part budget with all finite selectors instantiated.

This is the crossing counterpart to the terminal no-crossing estimate: retained zeros may
lie inside the nonterminal interval, so the proof uses the transversal crossing kernel and
the off-height deletion.
-/
theorem
    eventually_kadiri_moving_pole_zeta_principal_part_dyadic_nonterminal_right_integral_card_bound_on_large_offPole_filter
    (a A : ℝ) (ha : 0 ≤ a) (hA : 0 ≤ A) (k : ℕ) :
    ∃ e d M C : ℝ, 0 < e ∧ 0 < d ∧ 0 ≤ M ∧ 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)), (
            ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
              ((riemannZeta.order (rho : ℂ) : ℂ) /
                (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
          ≤ (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) * C := by
  let R : ℝ := (2 : ℝ) ^ (k + 1)
  obtain ⟨e, he, hmargin⟩ := kadiriTruncatedNontrivialZeros_endpoint_margin_exists a R ha
  obtain ⟨d, hd, hgap⟩ :=
    eventually_kadiri_truncated_zero_family_gap_left_of_log_terminal_on_filter
      A k kadiriLargeHorizontalZetaOffPoleFilter kadiriLargeHorizontalZetaOffPoleFilter_le_atTop
  obtain ⟨M, hM_nonneg, hM⟩ := kadiriTruncatedNontrivialZeros_order_norm_bound_exists R
  obtain ⟨C, hC, hcard⟩ :=
    kadiri_moving_pole_zeta_principal_part_truncated_nonterminal_right_integral_card_bound
      a e d R ha he hd
  refine ⟨e, d, M, C, he, hd, hM_nonneg, hC, ?_⟩
  have hsmall_one : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      A / Real.log |T| ^ (9 : ℕ) < 1 :=
    (eventually_const_div_log_abs_pow_lt_atTop A 1 zero_lt_one).filter_mono
      kadiriLargeHorizontalZetaOffPoleFilter_le_atTop
  filter_upwards [hgap, eventually_kadiriLargeHorizontalZetaOffPoleFilter_large,
    eventually_kadiriLargeHorizontalZetaOffPoleHeight, hsmall_one]
    with T hgap_T hlarge hT hsmall_one_T
  let x : ℝ := 1 - A / Real.log |T| ^ (9 : ℕ)
  have hlog_pos : 0 < Real.log |T| ^ (9 : ℕ) := by
    have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hlarge.le
    positivity
  have hshift_nonneg : 0 ≤ A / Real.log |T| ^ (9 : ℕ) :=
    div_nonneg hA hlog_pos.le
  have hx0 : 0 ≤ x := by
    dsimp [x]
    linarith [le_of_lt hsmall_one_T]
  have hxle : x ≤ 1 + a := by
    dsimp [x]
    linarith
  have hmargin_off_T :
      ∀ rho : NontrivialZeros,
        |(rho : ℂ).im| < R →
          e ≤ (rho : ℂ).re ∧ (rho : ℂ).re + d ≤ x ∧ (rho : ℂ).im ≠ T := by
    intro rho hrho
    exact ⟨(hmargin rho hrho).1, by simpa [x, R] using hgap_T rho (by simpa [R] using hrho),
      hT.2 rho⟩
  simpa [x, R] using
    hcard x T M hx0 hxle hmargin_off_T (by simpa [R] using hM)

/--
Nonterminal-subsegment version of the sign-correct zeta PV remainder bound.

It is the same algebra as the terminal handoff, but on `[0, x]`: a direct
actual-log-derivative integral estimate plus the finite moving-pole principal budget
control the sign-correct zeta remainder on the nonterminal interval.
-/
theorem
    kadiriDyadicZetaLogDerivPVRemainder_nonterminal_right_integral_bound_of_logDeriv_and_principal
    (a x T : ℝ) (ha : 0 ≤ a) (hx0 : 0 ≤ x) (hx_right : x ≤ 1 + a)
    (k : ℕ) (Q P : ℝ)
    (hT : kadiriHorizontalZetaOffPoleHeight T)
    (hlogDeriv_bound :
      ‖∫ σ in 0..x,
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖ ≤ Q)
    (hprincipal_bound :
      ‖∫ σ in 0..x,
          ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
            ((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖ ≤ P) :
    ‖∫ σ in 0..x, kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ Q + P := by
  let actual : ℝ → ℂ := fun σ =>
    -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
      riemannZeta (((σ : ℂ) + (T : ℂ) * I))
  let principal : ℝ → ℂ := fun σ =>
    ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
      ((riemannZeta.order (rho : ℂ) : ℂ) /
        (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))
  let zetaRem : ℝ → ℂ := fun σ => kadiriDyadicZetaLogDerivPVRemainder k T σ
  have hfull_interval : -a ≤ 1 + a := by linarith
  have hsubset : Set.uIcc 0 x ⊆ Set.uIcc (-a) (1 + a) := by
    intro σ hσ
    rw [Set.uIcc_of_le hx0] at hσ
    rw [Set.uIcc_of_le hfull_interval]
    exact ⟨by linarith [ha, hσ.1], le_trans hσ.2 hx_right⟩
  have hactual_int :
      IntervalIntegrable actual volume 0 x := by
    have hactual_full :
        IntervalIntegrable actual volume (-a) (1 + a) := by
      simpa [actual] using
        kadiri_neg_zeta_logDeriv_horizontal_intervalIntegrable_of_offPole a T ha hT
    exact hactual_full.mono_set hsubset
  have hprincipal_int :
      IntervalIntegrable principal volume 0 x := by
    have hprincipal_full :
        IntervalIntegrable principal volume (-a) (1 + a) := by
      simpa [principal] using
        kadiriDyadicPrincipalPart_intervalIntegrable_of_offPole a T k hT
    exact hprincipal_full.mono_set hsubset
  have hEq :
      Set.EqOn zetaRem (fun σ : ℝ => -actual σ - principal σ) [[0, x]] := by
    intro σ _hσ
    simp [kadiriDyadicZetaLogDerivPVRemainder, zetaRem, actual, principal]
    ring
  have hsplit :
      (∫ σ in 0..x, zetaRem σ) =
        -(∫ σ in 0..x, actual σ) - ∫ σ in 0..x, principal σ := by
    calc
      (∫ σ in 0..x, zetaRem σ)
          = ∫ σ in 0..x, -actual σ - principal σ := by
            rw [intervalIntegral.integral_congr hEq]
      _ = ∫ σ in 0..x, ((-actual) - principal) σ := by
            rfl
      _ = (∫ σ in 0..x, (-actual) σ) - ∫ σ in 0..x, principal σ := by
            exact intervalIntegral.integral_sub hactual_int.neg hprincipal_int
      _ = -(∫ σ in 0..x, actual σ) - ∫ σ in 0..x, principal σ := by
            simp
  have hactual' :
      ‖∫ σ in 0..x, actual σ‖ ≤ Q := by
    simpa [actual] using hlogDeriv_bound
  have hprincipal' :
      ‖∫ σ in 0..x, principal σ‖ ≤ P := by
    simpa [principal] using hprincipal_bound
  calc
    ‖∫ σ in 0..x, kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        = ‖-(∫ σ in 0..x, actual σ) - ∫ σ in 0..x, principal σ‖ := by
          simp [zetaRem, hsplit]
    _ ≤ ‖∫ σ in 0..x, actual σ‖ + ‖∫ σ in 0..x, principal σ‖ := by
          simpa [sub_eq_add_neg, norm_neg, add_comm, add_left_comm, add_assoc] using
            norm_add_le (-(∫ σ in 0..x, actual σ))
              (-(∫ σ in 0..x, principal σ))
    _ ≤ Q + P := add_le_add hactual' hprincipal'

/--
Large off-pole nonterminal zeta PV remainder bound after the finite principal block
has been selected and bounded.

The remaining analytic input is the actual `-ζ'/ζ` integral over the same moving
nonterminal interval.
-/
theorem
    eventually_kadiriDyadicZetaLogDerivPVRemainder_nonterminal_right_integral_bound_of_logDeriv_on_large_offPole_filter
    (a A : ℝ) (ha : 0 ≤ a) (hA : 0 ≤ A) (k : ℕ) (Q : ℝ → ℝ)
    (hlogDeriv_bound : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖ ≤ Q T) :
    ∃ e d M C : ℝ, 0 < e ∧ 0 < d ∧ 0 ≤ M ∧ 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
            kadiriDyadicZetaLogDerivPVRemainder k T σ‖
          ≤ Q T +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) * C := by
  obtain ⟨e, d, M, C, he, hd, hM, hC, hprincipal_bound⟩ :=
    eventually_kadiri_moving_pole_zeta_principal_part_dyadic_nonterminal_right_integral_card_bound_on_large_offPole_filter
      a A ha hA k
  refine ⟨e, d, M, C, he, hd, hM, hC, ?_⟩
  have hsmall_one : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      A / Real.log |T| ^ (9 : ℕ) < 1 :=
    (eventually_const_div_log_abs_pow_lt_atTop A 1 zero_lt_one).filter_mono
      kadiriLargeHorizontalZetaOffPoleFilter_le_atTop
  filter_upwards [eventually_kadiriLargeHorizontalZetaOffPoleFilter_large,
    eventually_kadiriLargeHorizontalZetaOffPoleHeight, hlogDeriv_bound,
    hprincipal_bound, hsmall_one]
    with T hlarge hT hlog_T hprincipal_T hsmall_one_T
  let x : ℝ := 1 - A / Real.log |T| ^ (9 : ℕ)
  have hlog_pos : 0 < Real.log |T| ^ (9 : ℕ) := by
    have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hlarge.le
    positivity
  have hshift_nonneg : 0 ≤ A / Real.log |T| ^ (9 : ℕ) :=
    div_nonneg hA hlog_pos.le
  have hx0 : 0 ≤ x := by
    dsimp [x]
    linarith [le_of_lt hsmall_one_T]
  have hx_right : x ≤ 1 + a := by
    dsimp [x]
    linarith
  have hlog_T' :
      ‖∫ σ in 0..x,
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖ ≤ Q T := by
    simpa [x] using hlog_T
  have hprincipal_T' :
      ‖∫ σ in 0..x, (
          ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
            ((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
        ≤ (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) * C := by
    simpa [x] using hprincipal_T
  simpa [x] using
    (kadiriDyadicZetaLogDerivPVRemainder_nonterminal_right_integral_bound_of_logDeriv_and_principal
      a x T ha hx0 hx_right k (Q T)
      ((((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) * C)
      hT hlog_T' hprincipal_T')

/--
Terminal right-subsegment principal-part bound when the retained zeros are separated to the
left of the moving terminal line.

Unlike the crossing bound on `[0, 1 + a]`, this estimate has no off-height hypothesis:
the real gap `d` keeps every retained pole away from the terminal segment.
-/
theorem kadiri_moving_pole_zeta_principal_part_truncated_terminal_right_integral_card_bound
    (a x d R M T : ℝ) (hxd : x ≤ 1 + a) (hd : 0 < d)
    (hleft : ∀ rho : NontrivialZeros,
      |(rho : ℂ).im| < R → (rho : ℂ).re + d ≤ x)
    (hM : ∀ rho : NontrivialZeros,
      |(rho : ℂ).im| < R →
        ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ ≤ M) :
    ‖∫ σ in x..(1 + a), (
        ∑ rho ∈ kadiriTruncatedNontrivialZeros R,
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
      ≤ ((((kadiriTruncatedNontrivialZeros R).card : ℝ) * M) / d) *
          |1 + a - x| := by
  classical
  let S : Finset NontrivialZeros := kadiriTruncatedNontrivialZeros R
  have hpoint :
      ∀ σ ∈ Ι x (1 + a),
        ‖∑ rho ∈ S,
            ((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖
          ≤ (((S.card : ℝ) * M) / d) := by
    intro σ hσ
    have hσ_mem : σ ∈ Set.Ioc x (1 + a) := by
      rw [Set.uIoc_of_le hxd] at hσ
      exact hσ
    calc
      ‖∑ rho ∈ S,
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖
          ≤ ∑ rho ∈ S,
              ‖((riemannZeta.order (rho : ℂ) : ℂ) /
                (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖ :=
            norm_sum_le _ _
      _ ≤ ∑ rho ∈ S, M / d := by
            refine Finset.sum_le_sum fun rho hrho => ?_
            have him : |(rho : ℂ).im| < R := by
              simpa [S] using
                (mem_kadiriTruncatedNontrivialZeros (R := R) (rho := rho)).mp hrho
            let z : ℂ := (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))
            have hz_re : z.re = σ - (rho : ℂ).re := by
              simp [z]
            have hz_re_nonneg : 0 ≤ z.re := by
              rw [hz_re]
              linarith [hleft rho him, hσ_mem.1.le, hd]
            have hz_norm_ge : d ≤ ‖z‖ := by
              have hd_re : d ≤ z.re := by
                rw [hz_re]
                linarith [hleft rho him, hσ_mem.1.le]
              calc
                d ≤ |z.re| := by simpa [abs_of_nonneg hz_re_nonneg] using hd_re
                _ ≤ ‖z‖ := Complex.abs_re_le_norm z
            have hz_norm_pos : 0 < ‖z‖ := lt_of_lt_of_le hd hz_norm_ge
            calc
              ‖((riemannZeta.order (rho : ℂ) : ℂ) /
                  (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))‖
                  = ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ / ‖z‖ := by
                    simp [z]
              _ ≤ ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ / d := by
                    exact div_le_div_of_nonneg_left (norm_nonneg _) hd hz_norm_ge
              _ ≤ M / d := by
                    exact div_le_div_of_nonneg_right (hM rho him) hd.le
      _ = (((S.card : ℝ) * M) / d) := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ring
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := x) (b := 1 + a) (C := (((S.card : ℝ) * M) / d))
      (f := fun σ : ℝ =>
        ∑ rho ∈ S,
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))) hpoint
  simpa [S] using hnorm

/--
Large off-pole terminal principal-part budget with both finite selectors instantiated: a
positive right-boundary gap for the dyadic zero family and a finite multiplicity cap.
-/
theorem
    eventually_kadiri_moving_pole_zeta_principal_part_dyadic_terminal_right_integral_card_bound_on_large_offPole_filter
    (a A : ℝ) (ha : 0 ≤ a) (hA : 0 ≤ A) (k : ℕ) :
    ∃ d M : ℝ, 0 < d ∧ 0 ≤ M ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in (1 - A / Real.log |T| ^ (9 : ℕ))..(1 + a), (
            ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
              ((riemannZeta.order (rho : ℂ) : ℂ) /
                (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
          ≤ ((((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) / d) *
              |1 + a - (1 - A / Real.log |T| ^ (9 : ℕ))| := by
  let R : ℝ := (2 : ℝ) ^ (k + 1)
  obtain ⟨d, hd, hgap⟩ :=
    eventually_kadiri_truncated_zero_family_gap_left_of_log_terminal_on_filter
      A k kadiriLargeHorizontalZetaOffPoleFilter kadiriLargeHorizontalZetaOffPoleFilter_le_atTop
  obtain ⟨M, hM_nonneg, hM⟩ := kadiriTruncatedNontrivialZeros_order_norm_bound_exists R
  refine ⟨d, M, hd, hM_nonneg, ?_⟩
  filter_upwards [hgap, eventually_kadiriLargeHorizontalZetaOffPoleFilter_large]
    with T hgap_T hlarge
  let x : ℝ := 1 - A / Real.log |T| ^ (9 : ℕ)
  have hlog_pos : 0 < Real.log |T| ^ (9 : ℕ) := by
    have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hlarge.le
    positivity
  have hshift_nonneg : 0 ≤ A / Real.log |T| ^ (9 : ℕ) :=
    div_nonneg hA hlog_pos.le
  have hxd : x ≤ 1 + a := by
    dsimp [x]
    linarith
  exact
    kadiri_moving_pole_zeta_principal_part_truncated_terminal_right_integral_card_bound
      a x d R M T hxd hd
      (by simpa [x, R] using hgap_T)
      (by simpa [R] using hM)

/--
Terminal-subsegment bound for the sign-correct zeta PV remainder on the large off-pole
filter.

This closes the terminal part of the right-segment PV remainder: the actual `-ζ'/ζ`
term is controlled by `LogDerivZetaBndUnif`, and the finite principal block is controlled
by the dyadic right-boundary gap and multiplicity cap.
-/
theorem
    eventually_kadiriDyadicZetaLogDerivPVRemainder_terminal_right_integral_bound_on_large_offPole_filter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    ∃ A C d M : ℝ, 0 ≤ A ∧ 0 < C ∧ 0 < d ∧ 0 ≤ M ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in (1 - A / Real.log |T| ^ (9 : ℕ))..(1 + a),
            kadiriDyadicZetaLogDerivPVRemainder k T σ‖
          ≤ (C * Real.log |T| ^ (9 : ℕ)) *
                |1 + a - (1 - A / Real.log |T| ^ (9 : ℕ))| +
              ((((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) /
                d) * |1 + a - (1 - A / Real.log |T| ^ (9 : ℕ))| := by
  obtain ⟨A, C, hA, hC, hlog_bound⟩ :=
    kadiri_right_terminal_neg_logDeriv_integral_bound_from_right_halfplane
  obtain ⟨d, M, hd, hM, hprincipal_bound⟩ :=
    eventually_kadiri_moving_pole_zeta_principal_part_dyadic_terminal_right_integral_card_bound_on_large_offPole_filter
      a A ha hA k
  refine ⟨A, C, d, M, hA, hC, hd, hM, ?_⟩
  have hsmall : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      A / Real.log |T| ^ (9 : ℕ) < 1 + a :=
    (eventually_const_div_log_abs_pow_lt_atTop A (1 + a) (by linarith)).filter_mono
      kadiriLargeHorizontalZetaOffPoleFilter_le_atTop
  filter_upwards [eventually_kadiriLargeHorizontalZetaOffPoleFilter_large,
    eventually_kadiriLargeHorizontalZetaOffPoleHeight, hprincipal_bound, hsmall]
    with T hlarge hT hprincipal_T hsmall_T
  let x : ℝ := 1 - A / Real.log |T| ^ (9 : ℕ)
  have hlog_pos : 0 < Real.log |T| ^ (9 : ℕ) := by
    have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hlarge.le
    positivity
  have hshift_nonneg : 0 ≤ A / Real.log |T| ^ (9 : ℕ) :=
    div_nonneg hA hlog_pos.le
  have hx_left : -a ≤ x := by
    dsimp [x]
    linarith
  have hx_right : x ≤ 1 + a := by
    dsimp [x]
    linarith
  have hx_region : x ∈ Set.Ici (1 - A / Real.log |T| ^ (9 : ℕ)) := by
    change 1 - A / Real.log |T| ^ (9 : ℕ) ≤ x
    rfl
  have hlog_T :
      ‖∫ σ in x..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ (C * Real.log |T| ^ (9 : ℕ)) * |1 + a - x| :=
    hlog_bound (a := a) (T := T) (x := x) hx_right hlarge hx_region
  have hprincipal_T' :
      ‖∫ σ in x..(1 + a), (
          ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
            ((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
        ≤ ((((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) /
              d) * |1 + a - x| := by
    simpa [x] using hprincipal_T
  simpa [x] using
    (kadiriDyadicZetaLogDerivPVRemainder_terminal_right_integral_bound_of_logDeriv_and_principal
      a x T ha hx_left hx_right k
      ((C * Real.log |T| ^ (9 : ℕ)) * |1 + a - x|)
      (((((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) / d) *
        |1 + a - x|)
      hT hlog_T hprincipal_T')

/--
Right-segment sign-correct zeta PV bound from the selected terminal moving-pole bound
and an explicit nonterminal moving-boundary input.

The theorem closes the terminal side and leaves only the analytic `[0, x(T)]` estimate
as an assumption, where `x(T) = 1 - A / log |T|^9`.
-/
theorem
    eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_bound_of_nonterminal_and_terminal_on_large_offPole_filter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (N : ℝ → ℝ → ℝ)
    (hnonterminal : ∀ A : ℝ, 0 ≤ A →
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
            kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ N A T) :
    ∃ A C d M : ℝ, 0 ≤ A ∧ 0 < C ∧ 0 < d ∧ 0 ≤ M ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
          ≤ N A T +
              ((C * Real.log |T| ^ (9 : ℕ)) *
                  |1 + a - (1 - A / Real.log |T| ^ (9 : ℕ))| +
                ((((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                    M) / d) *
                  |1 + a - (1 - A / Real.log |T| ^ (9 : ℕ))|) := by
  obtain ⟨A, C, d, M, hA, hC, hd, hM, hterminal_bound⟩ :=
    eventually_kadiriDyadicZetaLogDerivPVRemainder_terminal_right_integral_bound_on_large_offPole_filter
      a ha k
  refine ⟨A, C, d, M, hA, hC, hd, hM, ?_⟩
  have hsmall_one : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      A / Real.log |T| ^ (9 : ℕ) < 1 :=
    (eventually_const_div_log_abs_pow_lt_atTop A 1 zero_lt_one).filter_mono
      kadiriLargeHorizontalZetaOffPoleFilter_le_atTop
  filter_upwards [eventually_kadiriLargeHorizontalZetaOffPoleFilter_large,
    eventually_kadiriLargeHorizontalZetaOffPoleHeight,
    hnonterminal A hA, hterminal_bound, hsmall_one]
    with T hlarge hT hnonterminal_T hterminal_T hsmall_one_T
  let x : ℝ := 1 - A / Real.log |T| ^ (9 : ℕ)
  have hlog_pos : 0 < Real.log |T| ^ (9 : ℕ) := by
    have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hlarge.le
    positivity
  have hshift_nonneg : 0 ≤ A / Real.log |T| ^ (9 : ℕ) :=
    div_nonneg hA hlog_pos.le
  have hx0 : 0 ≤ x := by
    dsimp [x]
    linarith [le_of_lt hsmall_one_T]
  have hx_right : x ≤ 1 + a := by
    dsimp [x]
    linarith
  have hleft_T :
      ‖∫ σ in 0..x, kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ N A T := by
    simpa [x] using hnonterminal_T
  have hterminal_T' :
      ‖∫ σ in x..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        ≤ (C * Real.log |T| ^ (9 : ℕ)) * |1 + a - x| +
            ((((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) /
              d) * |1 + a - x| := by
    simpa [x] using hterminal_T
  simpa [x] using
    (kadiriDyadicZetaLogDerivPVRemainder_right_integral_bound_of_split
      a x T ha hx0 hx_right k (N A T)
      ((C * Real.log |T| ^ (9 : ℕ)) * |1 + a - x| +
        ((((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) / d) *
          |1 + a - x|)
      hT hleft_T hterminal_T')

/--
Right-segment sign-correct zeta PV logarithmic-growth bound from a nonterminal
moving-boundary logarithmic input.

The terminal moving-pole part is fully discharged here.  The remaining analytic input is
only the nonterminal interval `[0, 1 - A / log |T|^9]`.
-/
theorem
    eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_log_bound_of_nonterminal_log_bound_on_large_offPole_filter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hnonterminal : ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
          ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
              kadiriDyadicZetaLogDerivPVRemainder k T σ‖
            ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a)) :
    ∃ Z : ℝ, 0 ≤ Z ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
          ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a) := by
  obtain ⟨A, C, d, M, hA, hC, hd, hM, hterminal_bound⟩ :=
    eventually_kadiriDyadicZetaLogDerivPVRemainder_terminal_right_integral_bound_on_large_offPole_filter
      a ha k
  obtain ⟨Z0, hZ0, hnonterminal_bound⟩ := hnonterminal A hA
  let K : ℝ :=
    ((((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) / d)
  refine ⟨Z0 + C + K, ?_, ?_⟩
  · have hcard_nonneg :
        0 ≤ ((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) := by
      positivity
    have hK_nonneg : 0 ≤ K := by
      dsimp [K]
      exact div_nonneg (mul_nonneg hcard_nonneg hM) hd.le
    positivity
  have hsmall_one : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      A / Real.log |T| ^ (9 : ℕ) < 1 :=
    (eventually_const_div_log_abs_pow_lt_atTop A 1 zero_lt_one).filter_mono
      kadiriLargeHorizontalZetaOffPoleFilter_le_atTop
  filter_upwards [eventually_kadiriLargeHorizontalZetaOffPoleFilter_large,
    eventually_kadiriLargeHorizontalZetaOffPoleHeight,
    hnonterminal_bound, hterminal_bound, hsmall_one]
    with T hlarge hT hnonterminal_T hterminal_T hsmall_one_T
  let L : ℝ := Real.log |T| ^ (9 : ℕ)
  let x : ℝ := 1 - A / L
  have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hlarge.le
  have hL_pos : 0 < L := by
    dsimp [L]
    positivity
  have hL_nonneg : 0 ≤ L := hL_pos.le
  have hL_one : 1 ≤ L := by
    dsimp [L]
    exact one_le_pow₀ hlog_one.le
  have hshift_nonneg : 0 ≤ A / L :=
    div_nonneg hA hL_nonneg
  have honea_nonneg : 0 ≤ 1 + a := by linarith
  have hx0 : 0 ≤ x := by
    dsimp [x]
    linarith [le_of_lt hsmall_one_T]
  have hx_right : x ≤ 1 + a := by
    dsimp [x]
    linarith
  have hlen_eq : |1 + a - x| = a + A / L := by
    dsimp [x]
    rw [abs_of_nonneg]
    · ring
    · linarith
  have hlen_nonneg : 0 ≤ |1 + a - x| := abs_nonneg _
  have hlen_le : |1 + a - x| ≤ 1 + a := by
    rw [hlen_eq]
    linarith [le_of_lt hsmall_one_T]
  have hleft_T :
      ‖∫ σ in 0..x, kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        ≤ (Z0 * L) * (1 + a) := by
    simpa [x, L] using hnonterminal_T
  have hterminal_T' :
      ‖∫ σ in x..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        ≤ (C * L) * |1 + a - x| + K * |1 + a - x| := by
    simpa [x, L, K] using hterminal_T
  have hright_split :
      ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        ≤ (Z0 * L) * (1 + a) +
            ((C * L) * |1 + a - x| + K * |1 + a - x|) :=
    kadiriDyadicZetaLogDerivPVRemainder_right_integral_bound_of_split
      a x T ha hx0 hx_right k ((Z0 * L) * (1 + a))
      ((C * L) * |1 + a - x| + K * |1 + a - x|)
      hT hleft_T hterminal_T'
  have hK_nonneg : 0 ≤ K := by
    have hcard_nonneg :
        0 ≤ ((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) := by
      positivity
    dsimp [K]
    exact div_nonneg (mul_nonneg hcard_nonneg hM) hd.le
  have hCL_nonneg : 0 ≤ C * L := mul_nonneg hC.le hL_nonneg
  have hterm_C :
      (C * L) * |1 + a - x| ≤ (C * L) * (1 + a) :=
    mul_le_mul_of_nonneg_left hlen_le hCL_nonneg
  have hterm_K :
      K * |1 + a - x| ≤ (K * L) * (1 + a) := by
    have hK_len : K * |1 + a - x| ≤ K * (1 + a) :=
      mul_le_mul_of_nonneg_left hlen_le hK_nonneg
    have hK_absorb : K * (1 + a) ≤ (K * L) * (1 + a) := by
      have hK_le : K ≤ K * L := by
        calc
          K = K * 1 := by ring
          _ ≤ K * L := mul_le_mul_of_nonneg_left hL_one hK_nonneg
      exact mul_le_mul_of_nonneg_right hK_le honea_nonneg
    exact le_trans hK_len hK_absorb
  have hterminal_absorb :
      (C * L) * |1 + a - x| + K * |1 + a - x|
        ≤ (C * L) * (1 + a) + (K * L) * (1 + a) :=
    add_le_add hterm_C hterm_K
  calc
    ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        ≤ (Z0 * L) * (1 + a) +
            ((C * L) * |1 + a - x| + K * |1 + a - x|) := hright_split
    _ ≤ (Z0 * L) * (1 + a) +
          ((C * L) * (1 + a) + (K * L) * (1 + a)) :=
          add_le_add_right hterminal_absorb _
    _ = ((Z0 + C + K) * L) * (1 + a) := by
          ring

/--
Full-segment off-pole assembly with the right-segment truncated pole budget instantiated.

The hypotheses now isolate the still-open analytic obligations: reflected/digamma control,
right-segment zeta remainder control, a real endpoint-margin selector for the truncated
zeros, and a multiplicity cap.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_reflected_right_zeta_remainder_and_truncated_principal_card_on_filter
    (a e D B M : ℝ) (ha : 0 ≤ a) (he : 0 < e) (k : ℕ) (L : Filter ℝ)
    (hlarge : ∀ᶠ T : ℝ in L, 3 < |T|)
    (hoff : ∀ᶠ T : ℝ in L, kadiriHorizontalZetaOffPoleHeight T)
    (hdigamma_int : ∀ᶠ T : ℝ in L,
      IntervalIntegrable
        (fun σ : ℝ =>
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2))))
        volume (-a) 0)
    (hdigamma_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in (-a)..0,
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖ ≤ D)
    (hmargin_off : ∀ᶠ T : ℝ in L,
      ∀ rho : NontrivialZeros,
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1) →
          (rho : ℂ).re ∈ Set.Icc e (1 + a - e) ∧ (rho : ℂ).im ≠ T)
    (hM : ∀ rho : NontrivialZeros,
      |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1) →
        ‖(riemannZeta.order (rho : ℂ) : ℂ)‖ ≤ M)
    (hzeta_rem_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ∃ C Cp : ℝ, 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in L,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ ((C * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a + D) +
              (B + (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp) := by
  let R : ℝ := (2 : ℝ) ^ (k + 1)
  obtain ⟨Cp, hCp, hprincipal_bound⟩ :=
    eventually_kadiri_moving_pole_zeta_principal_part_truncated_right_integral_card_bound_on_filter
      a e R M he L (by simpa [R] using hmargin_off) (by simpa [R] using hM)
  let P : ℝ := (((kadiriTruncatedNontrivialZeros R).card : ℝ) * M) * Cp
  obtain ⟨C, hC, hfull⟩ :=
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_reflected_and_right_zeta_remainder_on_filter
      a D P B ha k L hlarge hoff hdigamma_int hdigamma_bound
      (by simpa [P, R] using hprincipal_bound)
      hzeta_rem_bound
  refine ⟨C, Cp, hC, hCp, ?_⟩
  simpa [P, R] using hfull

/--
Full-segment off-pole assembly with the dyadic endpoint-margin selector and multiplicity
cap selected from the finite truncated zero family.

After this step, the right-segment principal-part hypotheses are discharged. The remaining
inputs are the analytic right-segment zeta PV remainder budget and the reflected/digamma
budgets.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_selected_truncated_principal_on_filter
    (a D B : ℝ) (ha : 0 ≤ a) (k : ℕ) (L : Filter ℝ) (hL : L ≤ Filter.cofinite)
    (hlarge : ∀ᶠ T : ℝ in L, 3 < |T|)
    (hoff : ∀ᶠ T : ℝ in L, kadiriHorizontalZetaOffPoleHeight T)
    (hdigamma_int : ∀ᶠ T : ℝ in L,
      IntervalIntegrable
        (fun σ : ℝ =>
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2))))
        volume (-a) 0)
    (hdigamma_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in (-a)..0,
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖ ≤ D)
    (hzeta_rem_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in L,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ ((C * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a + D) +
              (B + (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp) := by
  obtain ⟨e, M, he, hM_nonneg, hmargin_off, hM⟩ :=
    kadiri_dyadic_truncated_zero_family_margin_and_multiplicity_selector_on_filter
      a ha k L hL
  obtain ⟨C, Cp, hC, hCp, hfull⟩ :=
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_reflected_right_zeta_remainder_and_truncated_principal_card_on_filter
      a e D B M ha he k L hlarge hoff hdigamma_int hdigamma_bound hmargin_off hM
      hzeta_rem_bound
  exact ⟨e, M, C, Cp, he, hM_nonneg, hC, hCp, hfull⟩

/--
Large off-pole full-segment assembly with the dyadic principal budget selected from the
finite truncated zero family.

This discharges the filter large-height condition, off-pole condition, endpoint-margin
selector, and multiplicity cap. The remaining assumptions are exactly the digamma-pair
budget and the right-segment zeta PV remainder budget on the large off-pole filter.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_selected_truncated_principal_on_large_offPole_filter
    (a D B : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hdigamma_int : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      IntervalIntegrable
        (fun σ : ℝ =>
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2))))
        volume (-a) 0)
    (hdigamma_bound : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ‖∫ σ in (-a)..0,
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖ ≤ D)
    (hzeta_rem_bound : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ ((C * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a + D) +
              (B + (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp) := by
  exact
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_selected_truncated_principal_on_filter
      a D B ha k kadiriLargeHorizontalZetaOffPoleFilter
      kadiriLargeHorizontalZetaOffPoleFilter_le_cofinite
      eventually_kadiriLargeHorizontalZetaOffPoleFilter_large
      eventually_kadiriLargeHorizontalZetaOffPoleHeight
      hdigamma_int hdigamma_bound hzeta_rem_bound

/--
Large off-pole full-segment assembly after discharging digamma-pair integrability.

The remaining analytic inputs are now the digamma-pair norm budget and the right-segment
zeta PV remainder budget on the large off-pole filter.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_digamma_bound_and_zeta_remainder_on_large_offPole_filter
    (a D B : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hdigamma_bound : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ‖∫ σ in (-a)..0,
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖ ≤ D)
    (hzeta_rem_bound : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ ((C * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a + D) +
              (B + (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp) := by
  exact
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_selected_truncated_principal_on_large_offPole_filter
      a D B ha k
      (eventually_kadiri_digamma_pair_nonpositive_horizontal_intervalIntegrable_on_large_offPole_filter
        a ha)
      hdigamma_bound hzeta_rem_bound

/--
Large off-pole full-segment assembly with logarithmic digamma growth absorbed into the
same `log |T| ^ 9` envelope as the reflected zeta term.

This is the nonconstant digamma-budget route: the digamma integral may grow like
`G * log |T| ^ 9` times the segment length.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_digamma_log_bound_and_zeta_remainder_on_large_offPole_filter
    (a G B : ℝ) (ha : 0 ≤ a) (hG : 0 ≤ G) (k : ℕ)
    (hdigamma_log_bound : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ‖∫ σ in (-a)..0,
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖
        ≤ (G * Real.log |T| ^ 9) * a)
    (hzeta_rem_bound : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ ((C * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a) +
              (B + (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp) := by
  obtain ⟨e, M, he, hM_nonneg, hmargin_off, hM⟩ :=
    kadiri_dyadic_truncated_zero_family_margin_and_multiplicity_selector_on_filter
      a ha k kadiriLargeHorizontalZetaOffPoleFilter
      kadiriLargeHorizontalZetaOffPoleFilter_le_cofinite
  let R : ℝ := (2 : ℝ) ^ (k + 1)
  obtain ⟨Cp, hCp, hprincipal_bound⟩ :=
    eventually_kadiri_moving_pole_zeta_principal_part_truncated_right_integral_card_bound_on_filter
      a e R M he kadiriLargeHorizontalZetaOffPoleFilter
      (by simpa [R] using hmargin_off) (by simpa [R] using hM)
  let P : ℝ := (((kadiriTruncatedNontrivialZeros R).card : ℝ) * M) * Cp
  have hright_int : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      IntervalIntegrable
        (fun σ : ℝ =>
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I)))
        volume 0 (1 + a) := by
    filter_upwards [eventually_kadiriLargeHorizontalZetaOffPoleHeight] with T hT
    exact kadiri_neg_zeta_logDeriv_right_intervalIntegrable_of_offPole a T ha hT
  have hright_bound : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ‖∫ σ in 0..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖ ≤ B + P :=
    eventually_kadiri_right_segment_logDeriv_integral_bound_of_zeta_remainder_and_principal_on_filter
      a ha k P B kadiriLargeHorizontalZetaOffPoleFilter
      eventually_kadiriLargeHorizontalZetaOffPoleHeight
      (by simpa [P, R] using hprincipal_bound) hzeta_rem_bound
  obtain ⟨C0, hC0, hfull_point⟩ :=
    kadiri_logDeriv_zeta_full_segment_bound_of_nonpositive_and_right_budget a ha
  refine ⟨e, M, C0 + G, Cp, he, hM_nonneg, add_nonneg hC0 hG, hCp, ?_⟩
  filter_upwards [eventually_kadiriLargeHorizontalZetaOffPoleFilter_large,
    eventually_kadiri_digamma_pair_nonpositive_horizontal_intervalIntegrable_on_large_offPole_filter
      a ha,
    hdigamma_log_bound, hright_int, hright_bound]
    with T hlarge hdigamma_int_T hdigamma_bound_T hright_int_T hright_bound_T
  have hbase :
      ‖∫ σ in (-a)..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ ((C0 * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a +
              (G * Real.log |T| ^ 9) * a) + (B + P) :=
    hfull_point (T := T) (D := (G * Real.log |T| ^ 9) * a) (R := B + P)
      hlarge hdigamma_int_T hdigamma_bound_T hright_int_T hright_bound_T
  have hfinal :
      ‖∫ σ in (-a)..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ (((C0 + G) * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a) +
            (B + P) := by
    calc
      ‖∫ σ in (-a)..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ ((C0 * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a +
                (G * Real.log |T| ^ 9) * a) + (B + P) := hbase
      _ = (((C0 + G) * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a) +
            (B + P) := by ring
  simpa [P, R] using hfinal

/--
Large off-pole full-segment assembly with both analytic remainder budgets allowed to grow
like `log |T| ^ 9`.

This is the logarithmic-growth handoff for the moving-pole PV lane: the digamma integral
and the right-segment sign-correct zeta PV integral are both absorbed into one
full-segment logarithmic envelope.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_digamma_log_bound_and_zeta_remainder_log_bound_on_large_offPole_filter
    (a G Z : ℝ) (ha : 0 ≤ a) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (k : ℕ)
    (hdigamma_log_bound : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ‖∫ σ in (-a)..0,
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖
        ≤ (G * Real.log |T| ^ 9) * a)
    (hzeta_rem_log_bound : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        ≤ (Z * Real.log |T| ^ 9) * (1 + a)) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp := by
  obtain ⟨e, M, he, hM_nonneg, hmargin_off, hM⟩ :=
    kadiri_dyadic_truncated_zero_family_margin_and_multiplicity_selector_on_filter
      a ha k kadiriLargeHorizontalZetaOffPoleFilter
      kadiriLargeHorizontalZetaOffPoleFilter_le_cofinite
  let R : ℝ := (2 : ℝ) ^ (k + 1)
  obtain ⟨Cp, hCp, hprincipal_bound⟩ :=
    eventually_kadiri_moving_pole_zeta_principal_part_truncated_right_integral_card_bound_on_filter
      a e R M he kadiriLargeHorizontalZetaOffPoleFilter
      (by simpa [R] using hmargin_off) (by simpa [R] using hM)
  let P : ℝ := (((kadiriTruncatedNontrivialZeros R).card : ℝ) * M) * Cp
  have hright_int : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      IntervalIntegrable
        (fun σ : ℝ =>
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I)))
        volume 0 (1 + a) := by
    filter_upwards [eventually_kadiriLargeHorizontalZetaOffPoleHeight] with T hT
    exact kadiri_neg_zeta_logDeriv_right_intervalIntegrable_of_offPole a T ha hT
  have hright_bound : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ‖∫ σ in 0..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ (Z * Real.log |T| ^ 9) * (1 + a) + P :=
    by
      filter_upwards [eventually_kadiriLargeHorizontalZetaOffPoleHeight,
        hprincipal_bound, hzeta_rem_log_bound] with T hT hprincipal_T hzeta_T
      exact
        kadiri_right_segment_logDeriv_integral_bound_of_zeta_remainder_and_principal
          a T ha k P ((Z * Real.log |T| ^ 9) * (1 + a)) hT
          (by simpa [P, R] using hprincipal_T) hzeta_T
  obtain ⟨C0, hC0, hfull_point⟩ :=
    kadiri_logDeriv_zeta_full_segment_bound_of_nonpositive_and_right_budget a ha
  refine ⟨e, M, C0 + G + Z, Cp, he, hM_nonneg,
    add_nonneg (add_nonneg hC0 hG) hZ, hCp, ?_⟩
  filter_upwards [eventually_kadiriLargeHorizontalZetaOffPoleFilter_large,
    eventually_kadiri_digamma_pair_nonpositive_horizontal_intervalIntegrable_on_large_offPole_filter
      a ha,
    hdigamma_log_bound, hright_int, hright_bound]
    with T hlarge hdigamma_int_T hdigamma_bound_T hright_int_T hright_bound_T
  have hbase :
      ‖∫ σ in (-a)..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ ((C0 * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a +
              (G * Real.log |T| ^ 9) * a) +
            ((Z * Real.log |T| ^ 9) * (1 + a) + P) :=
    hfull_point (T := T) (D := (G * Real.log |T| ^ 9) * a)
      (R := (Z * Real.log |T| ^ 9) * (1 + a) + P)
      hlarge hdigamma_int_T hdigamma_bound_T hright_int_T hright_bound_T
  have hlog_nonneg : 0 ≤ Real.log |T| ^ 9 := by
    have hlog_pos : 0 < Real.log |T| ^ 9 := by
      have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hlarge.le
      positivity
    exact hlog_pos.le
  have hshape :
      ((C0 * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a +
            (G * Real.log |T| ^ 9) * a) +
          ((Z * Real.log |T| ^ 9) * (1 + a) + P)
        ≤ ((C0 + G + Z) * Real.log |T| ^ 9) * (1 + 2 * a) +
            |Real.log Real.pi| * a + P := by
    have honea_nonneg : 0 ≤ 1 + a := by linarith
    have hsurplus_coeff :
        0 ≤ C0 * (1 + a) + G * (1 + a) + Z * a := by
      nlinarith [hC0, hG, hZ, ha, honea_nonneg]
    have hsurplus :
        0 ≤ (C0 * (1 + a) + G * (1 + a) + Z * a) *
          Real.log |T| ^ 9 :=
      mul_nonneg hsurplus_coeff hlog_nonneg
    nlinarith [hsurplus]
  have hfinal :
      ‖∫ σ in (-a)..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ ((C0 + G + Z) * Real.log |T| ^ 9) * (1 + 2 * a) +
            |Real.log Real.pi| * a + P :=
    le_trans hbase hshape
  simpa [P, R] using hfinal

/--
Large off-pole full-segment assembly after discharging the digamma-pair logarithmic
budget.

The remaining analytic input is the right-segment sign-correct zeta PV integral bound
with logarithmic growth.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_zeta_remainder_log_bound_on_large_offPole_filter
    (a Z : ℝ) (ha : 0 ≤ a) (hZ : 0 ≤ Z) (k : ℕ)
    (hzeta_rem_log_bound : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        ≤ (Z * Real.log |T| ^ 9) * (1 + a)) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp := by
  obtain ⟨G, hG, hdigamma_point⟩ :=
    eventually_kadiri_digamma_pair_nonpositive_horizontal_pointwise_log_bound_on_large_offPole_filter
      a ha
  exact
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_digamma_log_bound_and_zeta_remainder_log_bound_on_large_offPole_filter
      a G Z ha hG hZ k
      (eventually_kadiri_digamma_pair_nonpositive_horizontal_integral_bound_of_pointwise_log_bound_on_filter
        a G ha kadiriLargeHorizontalZetaOffPoleFilter hdigamma_point)
      hzeta_rem_log_bound

/--
Full-segment off-pole logarithmic-growth bound from the nonterminal zeta PV remainder
input alone.

The dyadic endpoint selector, multiplicity cap, terminal zeta PV segment, and
reflected/digamma bounds have all been discharged before this handoff.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_nonterminal_zeta_remainder_log_bound_on_large_offPole_filter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hnonterminal : ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
          ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
              kadiriDyadicZetaLogDerivPVRemainder k T σ‖
            ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a)) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp := by
  obtain ⟨Z, hZ, hzeta_rem_log_bound⟩ :=
    eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_log_bound_of_nonterminal_log_bound_on_large_offPole_filter
      a ha k hnonterminal
  exact
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_zeta_remainder_log_bound_on_large_offPole_filter
      a Z ha hZ k hzeta_rem_log_bound

/--
Moving nonterminal actual-log-derivative control gives the matching sign-correct zeta
PV remainder budget.

The finite moving-pole principal block has already been selected and bounded. This lemma
only absorbs that finite constant into the same `log |T| ^ 9` envelope as the analytic
nonterminal `-ζ'/ζ` input.
-/
theorem
    eventually_kadiriDyadicZetaLogDerivPVRemainder_nonterminal_integral_log_bound_of_logDeriv_log_bound_on_large_offPole_filter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hlogDeriv_nonterminal : ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
          ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
              -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
            ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a)) :
    ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
          ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
              kadiriDyadicZetaLogDerivPVRemainder k T σ‖
            ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a) := by
  intro A hA
  obtain ⟨Z0, hZ0, hlogDeriv_bound⟩ := hlogDeriv_nonterminal A hA
  obtain ⟨e, d, M, C, he, hd, hM, hC, hzeta_bound⟩ :=
    eventually_kadiriDyadicZetaLogDerivPVRemainder_nonterminal_right_integral_bound_of_logDeriv_on_large_offPole_filter
      a A ha hA k (fun T : ℝ => (Z0 * Real.log |T| ^ (9 : ℕ)) * (1 + a))
      hlogDeriv_bound
  let K : ℝ :=
    (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) * C
  have hK_nonneg : 0 ≤ K := by
    have hcard_nonneg :
        0 ≤ ((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) := by
      positivity
    dsimp [K]
    positivity
  refine ⟨Z0 + K, add_nonneg hZ0 hK_nonneg, ?_⟩
  filter_upwards [eventually_kadiriLargeHorizontalZetaOffPoleFilter_large, hzeta_bound]
    with T hlarge hzeta_T
  let L : ℝ := Real.log |T| ^ (9 : ℕ)
  have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hlarge.le
  have hL_one : 1 ≤ L := by
    dsimp [L]
    exact one_le_pow₀ hlog_one.le
  have hL_nonneg : 0 ≤ L := le_trans zero_le_one hL_one
  have honea_one : 1 ≤ 1 + a := by linarith
  have honea_nonneg : 0 ≤ 1 + a := le_trans zero_le_one honea_one
  have hKL_nonneg : 0 ≤ K * L := mul_nonneg hK_nonneg hL_nonneg
  have hK_absorb : K ≤ (K * L) * (1 + a) := by
    calc
      K = K * 1 := by ring
      _ ≤ K * L := mul_le_mul_of_nonneg_left hL_one hK_nonneg
      _ = (K * L) * 1 := by ring
      _ ≤ (K * L) * (1 + a) :=
          mul_le_mul_of_nonneg_left honea_one hKL_nonneg
  calc
    ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
        kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        ≤ (Z0 * Real.log |T| ^ (9 : ℕ)) * (1 + a) + K := by
          simpa [K] using hzeta_T
    _ ≤ (Z0 * L) * (1 + a) + (K * L) * (1 + a) := by
          simpa [L] using add_le_add_right hK_absorb ((Z0 * L) * (1 + a))
    _ = ((Z0 + K) * Real.log |T| ^ (9 : ℕ)) * (1 + a) := by
          simp [L]
          ring

/--
Pointwise moving nonterminal actual-log-derivative control gives the matching integral
budget on the same moving interval.
-/
theorem
    eventually_kadiri_neg_zeta_logDeriv_nonterminal_integral_log_bound_of_pointwise_log_bound_on_large_offPole_filter
    (a : ℝ) (ha : 0 ≤ a)
    (hlogDeriv_point : ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
          ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
            ‖-deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
              ≤ Z * Real.log |T| ^ (9 : ℕ)) :
    ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
          ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
              -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
            ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a) := by
  intro A hA
  obtain ⟨Z, hZ, hpoint⟩ := hlogDeriv_point A hA
  refine ⟨Z, hZ, ?_⟩
  have hsmall_one : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      A / Real.log |T| ^ (9 : ℕ) < 1 :=
    (eventually_const_div_log_abs_pow_lt_atTop A 1 zero_lt_one).filter_mono
      kadiriLargeHorizontalZetaOffPoleFilter_le_atTop
  filter_upwards [eventually_kadiriLargeHorizontalZetaOffPoleFilter_large,
    hpoint, hsmall_one] with T hlarge hpoint_T hsmall_one_T
  let L : ℝ := Real.log |T| ^ (9 : ℕ)
  let x : ℝ := 1 - A / L
  have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hlarge.le
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    positivity
  have hcoef_nonneg : 0 ≤ Z * L := mul_nonneg hZ hL_nonneg
  have hx_nonneg : 0 ≤ x := by
    dsimp [x, L]
    linarith [le_of_lt hsmall_one_T]
  have hx_le : x ≤ 1 + a := by
    dsimp [x, L]
    have hshift_nonneg : 0 ≤ A / Real.log |T| ^ (9 : ℕ) :=
      div_nonneg hA hL_nonneg
    linarith
  have hnorm :
      ‖∫ σ in 0..x,
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ (Z * L) * |x - 0| := by
    simpa [x, L] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := x) (C := Z * L)
        (f := fun σ : ℝ =>
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I)))
        (by simpa [x, L] using hpoint_T))
  have hlen : |x - 0| ≤ 1 + a := by
    rw [sub_zero, abs_of_nonneg hx_nonneg]
    exact hx_le
  calc
    ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
        -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        = ‖∫ σ in 0..x,
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖ := by
          simp [x, L]
    _ ≤ (Z * L) * |x - 0| := hnorm
    _ ≤ (Z * L) * (1 + a) :=
        mul_le_mul_of_nonneg_left hlen hcoef_nonneg
    _ = (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a) := by
        simp [L]

/--
Pointwise moving nonterminal actual-log-derivative control gives the corresponding
sign-correct zeta PV integral budget after the finite principal block is inserted.
-/
theorem
    eventually_kadiriDyadicZetaLogDerivPVRemainder_nonterminal_integral_log_bound_of_logDeriv_pointwise_log_bound_on_large_offPole_filter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hlogDeriv_point : ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
          ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
            ‖-deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
              ≤ Z * Real.log |T| ^ (9 : ℕ)) :
    ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
          ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
              kadiriDyadicZetaLogDerivPVRemainder k T σ‖
            ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a) := by
  exact
    eventually_kadiriDyadicZetaLogDerivPVRemainder_nonterminal_integral_log_bound_of_logDeriv_log_bound_on_large_offPole_filter
      a ha k
      (eventually_kadiri_neg_zeta_logDeriv_nonterminal_integral_log_bound_of_pointwise_log_bound_on_large_offPole_filter
        a ha hlogDeriv_point)

/--
Full-segment off-pole bound from a moving nonterminal actual-log-derivative input.

All finite moving-pole selectors, terminal PV estimates, and reflected/digamma estimates
are discharged here. The only remaining analytic input is the moving nonterminal
`-ζ'/ζ` logarithmic integral estimate.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_nonterminal_logDeriv_log_bound_on_large_offPole_filter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hlogDeriv_nonterminal : ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
          ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
              -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
            ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a)) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp := by
  exact
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_nonterminal_zeta_remainder_log_bound_on_large_offPole_filter
      a ha k
      (eventually_kadiriDyadicZetaLogDerivPVRemainder_nonterminal_integral_log_bound_of_logDeriv_log_bound_on_large_offPole_filter
        a ha k hlogDeriv_nonterminal)

/--
Full-segment off-pole bound from pointwise moving nonterminal actual-log-derivative
control.

This is the pointwise Hadamard/PV-facing route: once the actual logarithmic derivative is
bounded on `[0, 1 - A / log |T|^9]`, the finite principal block, terminal strip, and
reflected/digamma terms are already wired into the full-segment estimate.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_nonterminal_logDeriv_pointwise_log_bound_on_large_offPole_filter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hlogDeriv_point : ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
          ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
            ‖-deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
              ≤ Z * Real.log |T| ^ (9 : ℕ)) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp := by
  exact
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_nonterminal_logDeriv_log_bound_on_large_offPole_filter
      a ha k
      (eventually_kadiri_neg_zeta_logDeriv_nonterminal_integral_log_bound_of_pointwise_log_bound_on_large_offPole_filter
        a ha hlogDeriv_point)

/--
Endpoint adapter from a selected-line horizontal `log²` estimate.

Once a good-height or partial-fraction argument supplies
`kadiriHorizontalSegmentLogDerivBound (-1) 2 |T| C` eventually on the large off-pole
filter, the current full-segment L2 handoff is discharged.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_horizontalSegmentLogDerivBound_on_large_offPole_filter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hseg : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        kadiriHorizontalSegmentLogDerivBound (-1) 2 |T| C) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp := by
  exact
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_nonterminal_logDeriv_pointwise_log_bound_on_large_offPole_filter
      a ha k
      (eventually_kadiri_neg_zeta_logDeriv_nonterminal_pointwise_log_bound_of_horizontalSegmentLogDerivBound_on_large_offPole_filter
        hseg)

/--
Pointwise control of the sign-correct zeta PV remainder on a moving nonterminal
interval gives the corresponding moving nonterminal integral budget.

This is the exact integration handoff needed before the hard Hadamard/PV estimate:
the analytic input remains pointwise control only on
`[0, 1 - A / log |T|^9]`, not on the terminal strip near `1`.
-/
theorem
    eventually_kadiriDyadicZetaLogDerivPVRemainder_nonterminal_integral_log_bound_of_pointwise_log_bound_on_large_offPole_filter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hnonterminal_point : ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
          ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
            ‖kadiriDyadicZetaLogDerivPVRemainder k T σ‖
              ≤ Z * Real.log |T| ^ (9 : ℕ)) :
    ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
          ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
              kadiriDyadicZetaLogDerivPVRemainder k T σ‖
            ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a) := by
  intro A hA
  obtain ⟨Z, hZ, hpoint⟩ := hnonterminal_point A hA
  refine ⟨Z, hZ, ?_⟩
  have hsmall_one : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      A / Real.log |T| ^ (9 : ℕ) < 1 :=
    (eventually_const_div_log_abs_pow_lt_atTop A 1 zero_lt_one).filter_mono
      kadiriLargeHorizontalZetaOffPoleFilter_le_atTop
  filter_upwards [eventually_kadiriLargeHorizontalZetaOffPoleFilter_large,
    hpoint, hsmall_one] with T hlarge hpoint_T hsmall_one_T
  let L : ℝ := Real.log |T| ^ (9 : ℕ)
  let x : ℝ := 1 - A / L
  have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hlarge.le
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    positivity
  have hcoef_nonneg : 0 ≤ Z * L := mul_nonneg hZ hL_nonneg
  have hx_nonneg : 0 ≤ x := by
    dsimp [x, L]
    linarith [le_of_lt hsmall_one_T]
  have hx_le : x ≤ 1 + a := by
    dsimp [x, L]
    have hshift_nonneg : 0 ≤ A / Real.log |T| ^ (9 : ℕ) :=
      div_nonneg hA hL_nonneg
    linarith
  have hnorm :
      ‖∫ σ in 0..x, kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        ≤ (Z * L) * |x - 0| := by
    simpa [x, L] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := x) (C := Z * L)
        (f := fun σ : ℝ => kadiriDyadicZetaLogDerivPVRemainder k T σ)
        (by simpa [x, L] using hpoint_T))
  have hlen : |x - 0| ≤ 1 + a := by
    rw [sub_zero, abs_of_nonneg hx_nonneg]
    exact hx_le
  calc
    ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
        kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        = ‖∫ σ in 0..x, kadiriDyadicZetaLogDerivPVRemainder k T σ‖ := by
          simp [x, L]
    _ ≤ (Z * L) * |x - 0| := hnorm
    _ ≤ (Z * L) * (1 + a) :=
        mul_le_mul_of_nonneg_left hlen hcoef_nonneg
    _ = (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a) := by
        simp [L]

/--
Right-segment logarithmic bound from a moving nonterminal pointwise estimate.

The terminal strip and moving-pole principal block are already discharged; this theorem
reduces the right-segment PV budget to pointwise control on the nonterminal moving interval.
-/
theorem
    eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_log_bound_of_nonterminal_pointwise_log_bound_on_large_offPole_filter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hnonterminal_point : ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
          ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
            ‖kadiriDyadicZetaLogDerivPVRemainder k T σ‖
              ≤ Z * Real.log |T| ^ (9 : ℕ)) :
    ∃ Z : ℝ, 0 ≤ Z ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
          ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a) := by
  exact
    eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_log_bound_of_nonterminal_log_bound_on_large_offPole_filter
      a ha k
      (eventually_kadiriDyadicZetaLogDerivPVRemainder_nonterminal_integral_log_bound_of_pointwise_log_bound_on_large_offPole_filter
        a ha k hnonterminal_point)

/--
Full-segment off-pole logarithmic-growth bound from a moving nonterminal pointwise
Hadamard/PV remainder estimate.

This is the current end-to-end handoff: all finite selector, terminal, principal-part,
and reflected/digamma obligations are discharged; the remaining input is the pointwise
Hadamard/PV estimate on `[0, 1 - A / log |T|^9]`.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_nonterminal_zeta_remainder_pointwise_log_bound_on_large_offPole_filter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hnonterminal_point : ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
          ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
            ‖kadiriDyadicZetaLogDerivPVRemainder k T σ‖
              ≤ Z * Real.log |T| ^ (9 : ℕ)) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp := by
  obtain ⟨Z, hZ, hzeta_rem_log_bound⟩ :=
    eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_log_bound_of_nonterminal_pointwise_log_bound_on_large_offPole_filter
      a ha k hnonterminal_point
  exact
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_zeta_remainder_log_bound_on_large_offPole_filter
      a Z ha hZ k hzeta_rem_log_bound

/--
Large off-pole full-segment assembly from pointwise control of the sign-correct
right-segment zeta PV remainder.

This trades the remaining zeta-remainder integral hypothesis for the pointwise bound that
the analytic Hadamard/PV estimate is expected to supply.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_digamma_bound_and_zeta_remainder_pointwise_on_large_offPole_filter
    (a D B : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hdigamma_bound : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ‖∫ σ in (-a)..0,
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖ ≤ D)
    (hzeta_rem_point : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ∀ σ ∈ Ι 0 (1 + a),
        ‖kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ ((C * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a + D) +
              (B * (1 + a) +
                (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                  M) * Cp) := by
  exact
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_digamma_bound_and_zeta_remainder_on_large_offPole_filter
      a D (B * (1 + a)) ha k hdigamma_bound
      (eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_bound_of_pointwise_bound_on_filter
        a ha k B kadiriLargeHorizontalZetaOffPoleFilter hzeta_rem_point)

/--
Large off-pole full-segment assembly from pointwise logarithmic control of the digamma
pair and pointwise control of the sign-correct right-segment zeta PV remainder.

The two remaining analytic tasks are now both pointwise estimates on their natural
segments.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_digamma_pointwise_and_zeta_remainder_pointwise_on_large_offPole_filter
    (a G B : ℝ) (ha : 0 ≤ a) (hG : 0 ≤ G) (k : ℕ)
    (hdigamma_point : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ∀ σ ∈ Ι (-a) 0,
        ‖(1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖
          ≤ G * Real.log |T| ^ 9)
    (hzeta_rem_point : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ∀ σ ∈ Ι 0 (1 + a),
        ‖kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ ((C * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a) +
              (B * (1 + a) +
                (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                  M) * Cp) := by
  exact
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_digamma_log_bound_and_zeta_remainder_on_large_offPole_filter
      a G (B * (1 + a)) ha hG k
      (eventually_kadiri_digamma_pair_nonpositive_horizontal_integral_bound_of_pointwise_log_bound_on_filter
        a G ha kadiriLargeHorizontalZetaOffPoleFilter hdigamma_point)
      (eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_bound_of_pointwise_bound_on_filter
        a ha k B kadiriLargeHorizontalZetaOffPoleFilter hzeta_rem_point)

/--
Large off-pole full-segment assembly after discharging the digamma-pair pointwise
logarithmic bound.

The remaining analytic input is pointwise control of the sign-correct zeta PV remainder
on the right segment.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_zeta_remainder_pointwise_on_large_offPole_filter
    (a B : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hzeta_rem_point : ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
      ∀ σ ∈ Ι 0 (1 + a),
        ‖kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriLargeHorizontalZetaOffPoleFilter,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ ((C * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a) +
              (B * (1 + a) +
                (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                  M) * Cp) := by
  obtain ⟨G, hG, hdigamma_point⟩ :=
    eventually_kadiri_digamma_pair_nonpositive_horizontal_pointwise_log_bound_on_large_offPole_filter
      a ha
  exact
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_digamma_pointwise_and_zeta_remainder_pointwise_on_large_offPole_filter
      a G B ha hG k hdigamma_point hzeta_rem_point

/-- The selected dyadic good-height filter is finer than the large off-pole filter. -/
theorem kadiriDyadicGoodHeightFilter_le_kadiriLargeHorizontalZetaOffPoleFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    kadiriDyadicGoodHeightFilter hsrc ≤ kadiriLargeHorizontalZetaOffPoleFilter := by
  rw [kadiriLargeHorizontalZetaOffPoleFilter]
  refine le_inf (kadiriDyadicGoodHeightFilter_le_atTop hsrc) ?_
  rw [Filter.le_principal_iff]
  exact eventually_kadiriDyadicGoodHeightFilter_offPole hsrc

theorem kadiriDyadicGoodHeightFilter_le_cofinite
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    kadiriDyadicGoodHeightFilter hsrc ≤ Filter.cofinite :=
  (kadiriDyadicGoodHeightFilter_le_atTop hsrc).trans Filter.atTop_le_cofinite

theorem
    eventually_kadiri_neg_zeta_logDeriv_nonterminal_integral_log_bound_of_pointwise_log_bound_on_filter
    (a : ℝ) (ha : 0 ≤ a) (L : Filter ℝ) (hL : L ≤ Filter.atTop)
    (hlarge : ∀ᶠ T : ℝ in L, 3 < |T|)
    (hlogDeriv_point : ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in L,
          ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
            ‖-deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
              ≤ Z * Real.log |T| ^ (9 : ℕ)) :
    ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in L,
          ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
              -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
            ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a) := by
  intro A hA
  obtain ⟨Z, hZ, hpoint⟩ := hlogDeriv_point A hA
  refine ⟨Z, hZ, ?_⟩
  have hsmall_one : ∀ᶠ T : ℝ in L,
      A / Real.log |T| ^ (9 : ℕ) < 1 :=
    (eventually_const_div_log_abs_pow_lt_atTop A 1 zero_lt_one).filter_mono hL
  filter_upwards [hlarge, hpoint, hsmall_one] with T hlarge_T hpoint_T hsmall_one_T
  let Lpow : ℝ := Real.log |T| ^ (9 : ℕ)
  let x : ℝ := 1 - A / Lpow
  have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hlarge_T.le
  have hLpow_nonneg : 0 ≤ Lpow := by
    dsimp [Lpow]
    positivity
  have hcoef_nonneg : 0 ≤ Z * Lpow := mul_nonneg hZ hLpow_nonneg
  have hx_nonneg : 0 ≤ x := by
    dsimp [x, Lpow]
    linarith [le_of_lt hsmall_one_T]
  have hx_le : x ≤ 1 + a := by
    dsimp [x, Lpow]
    have hshift_nonneg : 0 ≤ A / Real.log |T| ^ (9 : ℕ) :=
      div_nonneg hA hLpow_nonneg
    linarith
  have hnorm :
      ‖∫ σ in 0..x,
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ (Z * Lpow) * |x - 0| := by
    simpa [x, Lpow] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := x) (C := Z * Lpow)
        (f := fun σ : ℝ =>
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I)))
        (by simpa [x, Lpow] using hpoint_T))
  have hlen : |x - 0| ≤ 1 + a := by
    rw [sub_zero, abs_of_nonneg hx_nonneg]
    exact hx_le
  calc
    ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
        -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        = ‖∫ σ in 0..x,
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖ := by
          simp [x, Lpow]
    _ ≤ (Z * Lpow) * |x - 0| := hnorm
    _ ≤ (Z * Lpow) * (1 + a) :=
        mul_le_mul_of_nonneg_left hlen hcoef_nonneg
    _ = (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a) := by
        simp [Lpow]

theorem
    eventually_kadiriDyadicZetaLogDerivPVRemainder_nonterminal_integral_log_bound_of_logDeriv_log_bound_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hlogDeriv_nonterminal : ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
          ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
              -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
            ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a)) :
    ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
          ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
              kadiriDyadicZetaLogDerivPVRemainder k T σ‖
            ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a) := by
  intro A hA
  obtain ⟨Z0, hZ0, hlogDeriv_bound⟩ := hlogDeriv_nonterminal A hA
  obtain ⟨e, d, M, C, he, hd, hM, hC, hprincipal_bound_large⟩ :=
    eventually_kadiri_moving_pole_zeta_principal_part_dyadic_nonterminal_right_integral_card_bound_on_large_offPole_filter
      a A ha hA k
  let K : ℝ :=
    (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) * C
  have hK_nonneg : 0 ≤ K := by
    have hcard_nonneg :
        0 ≤ ((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) := by
      positivity
    dsimp [K]
    positivity
  refine ⟨Z0 + K, add_nonneg hZ0 hK_nonneg, ?_⟩
  have hprincipal_bound :
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)), (
            ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
              ((riemannZeta.order (rho : ℂ) : ℂ) /
                (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
          ≤ (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) * C :=
    hprincipal_bound_large.filter_mono
      (kadiriDyadicGoodHeightFilter_le_kadiriLargeHorizontalZetaOffPoleFilter hsrc)
  have hsmall_one : ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
      A / Real.log |T| ^ (9 : ℕ) < 1 :=
    (eventually_const_div_log_abs_pow_lt_atTop A 1 zero_lt_one).filter_mono
      (kadiriDyadicGoodHeightFilter_le_atTop hsrc)
  filter_upwards [eventually_kadiriDyadicGoodHeightFilter_large hsrc,
    eventually_kadiriDyadicGoodHeightFilter_offPole hsrc, hlogDeriv_bound,
    hprincipal_bound, hsmall_one] with T hlarge hT hlog_T hprincipal_T hsmall_one_T
  let Lpow : ℝ := Real.log |T| ^ (9 : ℕ)
  let x : ℝ := 1 - A / Lpow
  have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hlarge.le
  have hLpow_pos : 0 < Lpow := by
    dsimp [Lpow]
    positivity
  have hLpow_nonneg : 0 ≤ Lpow := hLpow_pos.le
  have hLpow_one : 1 ≤ Lpow := by
    dsimp [Lpow]
    exact one_le_pow₀ hlog_one.le
  have hshift_nonneg : 0 ≤ A / Lpow :=
    div_nonneg hA hLpow_nonneg
  have hx0 : 0 ≤ x := by
    dsimp [x]
    linarith [le_of_lt hsmall_one_T]
  have hx_right : x ≤ 1 + a := by
    dsimp [x]
    linarith
  have hlog_T' :
      ‖∫ σ in 0..x,
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ (Z0 * Lpow) * (1 + a) := by
    simpa [x, Lpow] using hlog_T
  have hprincipal_T' :
      ‖∫ σ in 0..x, (
          ∑ rho ∈ kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1)),
            ((riemannZeta.order (rho : ℂ) : ℂ) /
              (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ))))‖
        ≤ (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) * C := by
    simpa [x, Lpow] using hprincipal_T
  have hzeta_T :
      ‖∫ σ in 0..x, kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        ≤ (Z0 * Lpow) * (1 + a) + K := by
    simpa [K] using
      (kadiriDyadicZetaLogDerivPVRemainder_nonterminal_right_integral_bound_of_logDeriv_and_principal
        a x T ha hx0 hx_right k ((Z0 * Lpow) * (1 + a))
        ((((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) * C)
        hT hlog_T' hprincipal_T')
  have honea_one : 1 ≤ 1 + a := by linarith
  have honea_nonneg : 0 ≤ 1 + a := le_trans zero_le_one honea_one
  have hKL_nonneg : 0 ≤ K * Lpow := mul_nonneg hK_nonneg hLpow_nonneg
  have hK_absorb : K ≤ (K * Lpow) * (1 + a) := by
    calc
      K = K * 1 := by ring
      _ ≤ K * Lpow := mul_le_mul_of_nonneg_left hLpow_one hK_nonneg
      _ = (K * Lpow) * 1 := by ring
      _ ≤ (K * Lpow) * (1 + a) :=
          mul_le_mul_of_nonneg_left honea_one hKL_nonneg
  calc
    ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
        kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        = ‖∫ σ in 0..x, kadiriDyadicZetaLogDerivPVRemainder k T σ‖ := by
          simp [x, Lpow]
    _ ≤ (Z0 * Lpow) * (1 + a) + K := hzeta_T
    _ ≤ (Z0 * Lpow) * (1 + a) + (K * Lpow) * (1 + a) := by
          exact add_le_add_right hK_absorb _
    _ = ((Z0 + K) * Real.log |T| ^ (9 : ℕ)) * (1 + a) := by
          simp [Lpow]
          ring

theorem
    eventually_kadiriDyadicZetaLogDerivPVRemainder_nonterminal_integral_log_bound_of_logDeriv_pointwise_log_bound_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hlogDeriv_point : ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
          ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
            ‖-deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
              ≤ Z * Real.log |T| ^ (9 : ℕ)) :
    ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
          ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
              kadiriDyadicZetaLogDerivPVRemainder k T σ‖
            ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a) := by
  exact
    eventually_kadiriDyadicZetaLogDerivPVRemainder_nonterminal_integral_log_bound_of_logDeriv_log_bound_on_dyadicGoodHeightFilter
      hsrc a ha k
      (eventually_kadiri_neg_zeta_logDeriv_nonterminal_integral_log_bound_of_pointwise_log_bound_on_filter
        a ha (kadiriDyadicGoodHeightFilter hsrc)
        (kadiriDyadicGoodHeightFilter_le_atTop hsrc)
        (eventually_kadiriDyadicGoodHeightFilter_large hsrc)
        hlogDeriv_point)

theorem
    eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_log_bound_of_nonterminal_log_bound_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hnonterminal : ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
          ‖∫ σ in 0..(1 - A / Real.log |T| ^ (9 : ℕ)),
              kadiriDyadicZetaLogDerivPVRemainder k T σ‖
            ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a)) :
    ∃ Z : ℝ, 0 ≤ Z ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
          ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a) := by
  obtain ⟨A, C, d, M, hA, hC, hd, hM, hterminal_bound_large⟩ :=
    eventually_kadiriDyadicZetaLogDerivPVRemainder_terminal_right_integral_bound_on_large_offPole_filter
      a ha k
  obtain ⟨Z0, hZ0, hnonterminal_bound⟩ := hnonterminal A hA
  let K : ℝ :=
    ((((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) / d)
  refine ⟨Z0 + C + K, ?_, ?_⟩
  · have hcard_nonneg :
        0 ≤ ((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) := by
      positivity
    have hK_nonneg : 0 ≤ K := by
      dsimp [K]
      exact div_nonneg (mul_nonneg hcard_nonneg hM) hd.le
    positivity
  have hterminal_bound :
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ‖∫ σ in (1 - A / Real.log |T| ^ (9 : ℕ))..(1 + a),
            kadiriDyadicZetaLogDerivPVRemainder k T σ‖
          ≤ (C * Real.log |T| ^ (9 : ℕ)) *
                |1 + a - (1 - A / Real.log |T| ^ (9 : ℕ))| +
              ((((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) * M) /
                d) * |1 + a - (1 - A / Real.log |T| ^ (9 : ℕ))| :=
    hterminal_bound_large.filter_mono
      (kadiriDyadicGoodHeightFilter_le_kadiriLargeHorizontalZetaOffPoleFilter hsrc)
  have hsmall_one : ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
      A / Real.log |T| ^ (9 : ℕ) < 1 :=
    (eventually_const_div_log_abs_pow_lt_atTop A 1 zero_lt_one).filter_mono
      (kadiriDyadicGoodHeightFilter_le_atTop hsrc)
  filter_upwards [eventually_kadiriDyadicGoodHeightFilter_large hsrc,
    eventually_kadiriDyadicGoodHeightFilter_offPole hsrc,
    hnonterminal_bound, hterminal_bound, hsmall_one]
    with T hlarge hT hnonterminal_T hterminal_T hsmall_one_T
  let Lpow : ℝ := Real.log |T| ^ (9 : ℕ)
  let x : ℝ := 1 - A / Lpow
  have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hlarge.le
  have hLpow_pos : 0 < Lpow := by
    dsimp [Lpow]
    positivity
  have hLpow_nonneg : 0 ≤ Lpow := hLpow_pos.le
  have hLpow_one : 1 ≤ Lpow := by
    dsimp [Lpow]
    exact one_le_pow₀ hlog_one.le
  have hshift_nonneg : 0 ≤ A / Lpow :=
    div_nonneg hA hLpow_nonneg
  have honea_nonneg : 0 ≤ 1 + a := by linarith
  have hx0 : 0 ≤ x := by
    dsimp [x]
    linarith [le_of_lt hsmall_one_T]
  have hx_right : x ≤ 1 + a := by
    dsimp [x]
    linarith
  have hlen_eq : |1 + a - x| = a + A / Lpow := by
    dsimp [x]
    rw [abs_of_nonneg]
    · ring
    · linarith
  have hlen_le : |1 + a - x| ≤ 1 + a := by
    rw [hlen_eq]
    linarith [le_of_lt hsmall_one_T]
  have hleft_T :
      ‖∫ σ in 0..x, kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        ≤ (Z0 * Lpow) * (1 + a) := by
    simpa [x, Lpow] using hnonterminal_T
  have hterminal_T' :
      ‖∫ σ in x..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        ≤ (C * Lpow) * |1 + a - x| + K * |1 + a - x| := by
    simpa [x, Lpow, K] using hterminal_T
  have hright_split :
      ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        ≤ (Z0 * Lpow) * (1 + a) +
            ((C * Lpow) * |1 + a - x| + K * |1 + a - x|) :=
    kadiriDyadicZetaLogDerivPVRemainder_right_integral_bound_of_split
      a x T ha hx0 hx_right k ((Z0 * Lpow) * (1 + a))
      ((C * Lpow) * |1 + a - x| + K * |1 + a - x|)
      hT hleft_T hterminal_T'
  have hK_nonneg : 0 ≤ K := by
    have hcard_nonneg :
        0 ≤ ((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) := by
      positivity
    dsimp [K]
    exact div_nonneg (mul_nonneg hcard_nonneg hM) hd.le
  have hCL_nonneg : 0 ≤ C * Lpow := mul_nonneg hC.le hLpow_nonneg
  have hterm_C :
      (C * Lpow) * |1 + a - x| ≤ (C * Lpow) * (1 + a) :=
    mul_le_mul_of_nonneg_left hlen_le hCL_nonneg
  have hterm_K :
      K * |1 + a - x| ≤ (K * Lpow) * (1 + a) := by
    have hK_len : K * |1 + a - x| ≤ K * (1 + a) :=
      mul_le_mul_of_nonneg_left hlen_le hK_nonneg
    have hK_absorb : K * (1 + a) ≤ (K * Lpow) * (1 + a) := by
      have hK_le : K ≤ K * Lpow := by
        calc
          K = K * 1 := by ring
          _ ≤ K * Lpow := mul_le_mul_of_nonneg_left hLpow_one hK_nonneg
      exact mul_le_mul_of_nonneg_right hK_le honea_nonneg
    exact le_trans hK_len hK_absorb
  have hterminal_absorb :
      (C * Lpow) * |1 + a - x| + K * |1 + a - x|
        ≤ (C * Lpow) * (1 + a) + (K * Lpow) * (1 + a) :=
    add_le_add hterm_C hterm_K
  calc
    ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        ≤ (Z0 * Lpow) * (1 + a) +
            ((C * Lpow) * |1 + a - x| + K * |1 + a - x|) := hright_split
    _ ≤ (Z0 * Lpow) * (1 + a) +
          ((C * Lpow) * (1 + a) + (K * Lpow) * (1 + a)) :=
          add_le_add_right hterminal_absorb _
    _ = ((Z0 + C + K) * Lpow) * (1 + a) := by
          ring

theorem
    eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_log_bound_of_logDeriv_pointwise_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hlogDeriv_point : ∀ A : ℝ, 0 ≤ A →
      ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
          ∀ σ ∈ Ι 0 (1 - A / Real.log |T| ^ (9 : ℕ)),
            ‖-deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
                riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
              ≤ Z * Real.log |T| ^ (9 : ℕ)) :
    ∃ Z : ℝ, 0 ≤ Z ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
          ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a) := by
  exact
    eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_log_bound_of_nonterminal_log_bound_on_dyadicGoodHeightFilter
      hsrc a ha k
      (eventually_kadiriDyadicZetaLogDerivPVRemainder_nonterminal_integral_log_bound_of_logDeriv_pointwise_log_bound_on_dyadicGoodHeightFilter
        hsrc a ha k hlogDeriv_point)

theorem
    eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_log_bound_of_candidate_localPVRemainder_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ n : ℕ in atTop,
      ∀ T ∈ Set.Ioc ((2 : ℝ) ^ n) (2 * ((2 : ℝ) ^ n)),
        kadiriHorizontalZetaOffPoleHeight T →
          ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
            ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
              R * Real.log |T| ^ (2 : ℕ)) :
    ∃ Z : ℝ, 0 ≤ Z ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
          ≤ (Z * Real.log |T| ^ (9 : ℕ)) * (1 + a) :=
  eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_log_bound_of_logDeriv_pointwise_on_dyadicGoodHeightFilter
    hsrc a ha k
    (eventually_kadiriDyadicGoodHeightFilter_nonterminal_pointwise_log_bound_of_candidate_localPVRemainder
      hsrc hrem)

theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_digamma_log_bound_and_zeta_remainder_log_bound_on_filter
    (a G Z : ℝ) (ha : 0 ≤ a) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (k : ℕ)
    (L : Filter ℝ) (hL : L ≤ Filter.cofinite)
    (hlarge : ∀ᶠ T : ℝ in L, 3 < |T|)
    (hoff : ∀ᶠ T : ℝ in L, kadiriHorizontalZetaOffPoleHeight T)
    (hdigamma_int : ∀ᶠ T : ℝ in L,
      IntervalIntegrable
        (fun σ : ℝ =>
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2))))
        volume (-a) 0)
    (hdigamma_log_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in (-a)..0,
          (1 / 2 : ℂ) *
            (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
              digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖
        ≤ (G * Real.log |T| ^ 9) * a)
    (hzeta_rem_log_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in 0..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖
        ≤ (Z * Real.log |T| ^ 9) * (1 + a)) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in L,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp := by
  obtain ⟨e, M, he, hM_nonneg, hmargin_off, hM⟩ :=
    kadiri_dyadic_truncated_zero_family_margin_and_multiplicity_selector_on_filter
      a ha k L hL
  let R : ℝ := (2 : ℝ) ^ (k + 1)
  obtain ⟨Cp, hCp, hprincipal_bound⟩ :=
    eventually_kadiri_moving_pole_zeta_principal_part_truncated_right_integral_card_bound_on_filter
      a e R M he L (by simpa [R] using hmargin_off) (by simpa [R] using hM)
  let P : ℝ := (((kadiriTruncatedNontrivialZeros R).card : ℝ) * M) * Cp
  have hright_int : ∀ᶠ T : ℝ in L,
      IntervalIntegrable
        (fun σ : ℝ =>
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I)))
        volume 0 (1 + a) := by
    filter_upwards [hoff] with T hT
    exact kadiri_neg_zeta_logDeriv_right_intervalIntegrable_of_offPole a T ha hT
  have hright_bound : ∀ᶠ T : ℝ in L,
      ‖∫ σ in 0..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ (Z * Real.log |T| ^ 9) * (1 + a) + P :=
    by
      filter_upwards [hoff, hprincipal_bound, hzeta_rem_log_bound] with T hT hprincipal_T hzeta_T
      exact
        kadiri_right_segment_logDeriv_integral_bound_of_zeta_remainder_and_principal
          a T ha k P ((Z * Real.log |T| ^ 9) * (1 + a)) hT
          (by simpa [P, R] using hprincipal_T) hzeta_T
  obtain ⟨C0, hC0, hfull_point⟩ :=
    kadiri_logDeriv_zeta_full_segment_bound_of_nonpositive_and_right_budget a ha
  refine ⟨e, M, C0 + G + Z, Cp, he, hM_nonneg,
    add_nonneg (add_nonneg hC0 hG) hZ, hCp, ?_⟩
  filter_upwards [hlarge, hdigamma_int, hdigamma_log_bound, hright_int, hright_bound]
    with T hlarge_T hdigamma_int_T hdigamma_bound_T hright_int_T hright_bound_T
  have hbase :
      ‖∫ σ in (-a)..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ ((C0 * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a +
              (G * Real.log |T| ^ 9) * a) +
            ((Z * Real.log |T| ^ 9) * (1 + a) + P) :=
    hfull_point (T := T) (D := (G * Real.log |T| ^ 9) * a)
      (R := (Z * Real.log |T| ^ 9) * (1 + a) + P)
      hlarge_T hdigamma_int_T hdigamma_bound_T hright_int_T hright_bound_T
  have hlog_nonneg : 0 ≤ Real.log |T| ^ 9 := by
    have hlog_pos : 0 < Real.log |T| ^ 9 := by
      have hlog_one : (1 : ℝ) < Real.log |T| := logt_gt_one hlarge_T.le
      positivity
    exact hlog_pos.le
  have hshape :
      ((C0 * Real.log |T| ^ 9) * a + |Real.log Real.pi| * a +
            (G * Real.log |T| ^ 9) * a) +
          ((Z * Real.log |T| ^ 9) * (1 + a) + P)
        ≤ ((C0 + G + Z) * Real.log |T| ^ 9) * (1 + 2 * a) +
            |Real.log Real.pi| * a + P := by
    have honea_nonneg : 0 ≤ 1 + a := by linarith
    have hsurplus_coeff :
        0 ≤ C0 * (1 + a) + G * (1 + a) + Z * a := by
      nlinarith [hC0, hG, hZ, ha, honea_nonneg]
    have hsurplus :
        0 ≤ (C0 * (1 + a) + G * (1 + a) + Z * a) *
          Real.log |T| ^ 9 :=
      mul_nonneg hsurplus_coeff hlog_nonneg
    nlinarith [hsurplus]
  have hfinal :
      ‖∫ σ in (-a)..(1 + a),
          -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
            riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
        ≤ ((C0 + G + Z) * Real.log |T| ^ 9) * (1 + 2 * a) +
            |Real.log Real.pi| * a + P :=
    le_trans hbase hshape
  simpa [P, R] using hfinal

theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_localPVRemainder_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
          ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
            R * Real.log |T| ^ (2 : ℕ)) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp := by
  obtain ⟨G, hG, hdigamma_point_large⟩ :=
    eventually_kadiri_digamma_pair_nonpositive_horizontal_pointwise_log_bound_on_large_offPole_filter
      a ha
  have hselected_le_large :=
    kadiriDyadicGoodHeightFilter_le_kadiriLargeHorizontalZetaOffPoleFilter hsrc
  have hdigamma_point :
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ∀ σ ∈ Ι (-a) 0,
          ‖(1 / 2 : ℂ) *
              (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
                digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖
            ≤ G * Real.log |T| ^ 9 :=
    hdigamma_point_large.filter_mono hselected_le_large
  obtain ⟨Z, hZ, hzeta_rem_log_bound⟩ :=
    eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_log_bound_of_logDeriv_pointwise_on_dyadicGoodHeightFilter
      hsrc a ha k
      (eventually_kadiriDyadicGoodHeightFilter_nonterminal_pointwise_log_bound_of_localPVRemainder
        hsrc hrem)
  exact
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_digamma_log_bound_and_zeta_remainder_log_bound_on_filter
      a G Z ha hG hZ k (kadiriDyadicGoodHeightFilter hsrc)
      (kadiriDyadicGoodHeightFilter_le_cofinite hsrc)
      (eventually_kadiriDyadicGoodHeightFilter_large hsrc)
      (eventually_kadiriDyadicGoodHeightFilter_offPole hsrc)
      ((eventually_kadiri_digamma_pair_nonpositive_horizontal_intervalIntegrable_on_large_offPole_filter
        a ha).filter_mono hselected_le_large)
      (eventually_kadiri_digamma_pair_nonpositive_horizontal_integral_bound_of_pointwise_log_bound_on_filter
        a G ha (kadiriDyadicGoodHeightFilter hsrc) hdigamma_point)
      hzeta_rem_log_bound

theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_horizontalSegmentLogDerivBound_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hseg : ∃ S : ℝ, 0 ≤ S ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        kadiriHorizontalSegmentLogDerivBound (-1) 2 |T| S) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp := by
  obtain ⟨G, hG, hdigamma_point_large⟩ :=
    eventually_kadiri_digamma_pair_nonpositive_horizontal_pointwise_log_bound_on_large_offPole_filter
      a ha
  have hselected_le_large :=
    kadiriDyadicGoodHeightFilter_le_kadiriLargeHorizontalZetaOffPoleFilter hsrc
  have hdigamma_point :
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ∀ σ ∈ Ι (-a) 0,
          ‖(1 / 2 : ℂ) *
              (digamma ((((σ : ℂ) + (T : ℂ) * I) / 2)) +
                digamma (((1 - (((σ : ℂ) + (T : ℂ) * I))) / 2)))‖
            ≤ G * Real.log |T| ^ 9 :=
    hdigamma_point_large.filter_mono hselected_le_large
  obtain ⟨Z, hZ, hzeta_rem_log_bound⟩ :=
    eventually_kadiriDyadicZetaLogDerivPVRemainder_right_integral_log_bound_of_logDeriv_pointwise_on_dyadicGoodHeightFilter
      hsrc a ha k
      (eventually_kadiriDyadicGoodHeightFilter_nonterminal_pointwise_log_bound_of_horizontalSegmentLogDerivBound
        hsrc hseg)
  exact
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_digamma_log_bound_and_zeta_remainder_log_bound_on_filter
      a G Z ha hG hZ k (kadiriDyadicGoodHeightFilter hsrc)
      (kadiriDyadicGoodHeightFilter_le_cofinite hsrc)
      (eventually_kadiriDyadicGoodHeightFilter_large hsrc)
      (eventually_kadiriDyadicGoodHeightFilter_offPole hsrc)
      ((eventually_kadiri_digamma_pair_nonpositive_horizontal_intervalIntegrable_on_large_offPole_filter
        a ha).filter_mono hselected_le_large)
      (eventually_kadiri_digamma_pair_nonpositive_horizontal_integral_bound_of_pointwise_log_bound_on_filter
        a G ha (kadiriDyadicGoodHeightFilter hsrc) hdigamma_point)
      hzeta_rem_log_bound

theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_candidate_horizontalSegmentLogDerivBound_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ n : ℕ in atTop,
      ∀ T ∈ Set.Ioc ((2 : ℝ) ^ n) (2 * ((2 : ℝ) ^ n)),
        kadiriHorizontalZetaOffPoleHeight T →
          ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
            ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
              R * Real.log |T| ^ (2 : ℕ)) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp :=
  eventually_kadiri_logDeriv_zeta_full_segment_bound_of_horizontalSegmentLogDerivBound_on_dyadicGoodHeightFilter
    hsrc a ha k
    (eventually_kadiriDyadicGoodHeightFilter_abs_horizontalSegmentLogDerivBound_of_horizontalSegmentLogDerivBound
      hsrc
      (eventually_kadiriDyadicGoodHeightFilter_horizontalSegmentLogDerivBound_of_candidate_localPVRemainder
        hsrc hrem))

theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_candidate_localPVRemainder_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ n : ℕ in atTop,
      ∀ T ∈ Set.Ioc ((2 : ℝ) ^ n) (2 * ((2 : ℝ) ^ n)),
        kadiriHorizontalZetaOffPoleHeight T →
          ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
            ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
              R * Real.log |T| ^ (2 : ℕ)) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp :=
  eventually_kadiri_logDeriv_zeta_full_segment_bound_of_localPVRemainder_on_dyadicGoodHeightFilter
    hsrc a ha k
    (eventually_kadiriDyadicGoodHeightFilter_localPVRemainder_logSq_of_candidate hsrc hrem)

end Kadiri
