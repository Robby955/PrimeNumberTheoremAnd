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

open Complex

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

end Kadiri
