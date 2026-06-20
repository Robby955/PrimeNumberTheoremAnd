import PrimeNumberTheoremAnd.IEANTN.KadiriHorizontalConditionB

/-!
# Kadiri q1 horizontal PV close

This downstream sidecar gives the issue-facing q1 horizontal names their
corrected PV-canonical target. The ordinary all-height statements are not valid
at zero ordinates; the bridge back to ordinary integrals is recorded only under
the explicit no-zero-ordinate hypothesis.
-/

namespace Kadiri

open MeasureTheory Complex Filter
open scoped Topology

noncomputable section

/-- Top q1 horizontal close, restated with the canonical PV target. -/
theorem kadiri_thm_3_1_q1_top_horizontal_vanishes
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * Complex.exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * Complex.exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) :
    Filter.Tendsto (kadiriTopHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_top_horizontal_pv_vanishes_of_q1_hypotheses_finalBound
    hφ hb ha hab ha1 hφ_decay hφ'_decay

/-- Bottom q1 horizontal close, restated with the canonical PV target. -/
theorem kadiri_thm_3_1_q1_bot_horizontal_vanishes
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * Complex.exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * Complex.exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) :
    Filter.Tendsto (kadiriBotHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes_of_q1_hypotheses_finalBound
    hφ hb ha hab ha1 hφ_decay hφ'_decay

/-- At a top no-zero ordinate, the ordinary top horizontal integral is the
canonical PV value. -/
theorem kadiriTopHorizontalIntegral_eq_pvCanonical_of_noZero
    {φ : ℝ → ℂ} {a T : ℝ} (hNo : KadiriNoZeroOrdinate T) :
    kadiriTopHorizontalIntegral φ a T = kadiriTopHorizontalPVCanonical φ a T :=
  ((kadiriHorizontalPVCanonical_noZeroBridge (φ := φ) (a := a)).1 T hNo).symm

/-- At a bottom no-zero ordinate, the ordinary bottom horizontal integral is the
canonical PV value. -/
theorem kadiriBotHorizontalIntegral_eq_pvCanonical_of_noZero
    {φ : ℝ → ℂ} {a T : ℝ} (hNo : KadiriNoZeroOrdinate (-T)) :
    kadiriBotHorizontalIntegral φ a T = kadiriBotHorizontalPVCanonical φ a T :=
  ((kadiriHorizontalPVCanonical_noZeroBridge (φ := φ) (a := a)).2 T hNo).symm

/-- The absolute zero-avoidance hypothesis in eq. 12 gives the top no-zero
ordinate condition. -/
theorem kadiriNoZeroOrdinate_of_abs_noZero
    {T : ℝ} (hT : 0 < T)
    (hT_noz : ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im| ≠ T) :
    KadiriNoZeroOrdinate T := by
  intro ρ hρ hρ_im
  exact hT_noz ρ hρ (by simp [hρ_im, abs_of_pos hT])

/-- The absolute zero-avoidance hypothesis in eq. 12 gives the bottom no-zero
ordinate condition. -/
theorem kadiriNoZeroOrdinate_neg_of_abs_noZero
    {T : ℝ} (hT : 0 < T)
    (hT_noz : ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im| ≠ T) :
    KadiriNoZeroOrdinate (-T) := by
  intro ρ hρ hρ_im
  exact hT_noz ρ hρ (by simp [hρ_im, abs_of_pos hT])

/-- Eq. 12 rewritten with canonical PV horizontal terms. The ordinary contour
identity is used only under its explicit no-zero boundary hypothesis. -/
theorem kadiri_thm_3_1_q1_eq_12_pv
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * Complex.exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * Complex.exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    {T : ℝ} (hT : 0 < T)
    (hT_noz : ∀ ρ : ℂ, riemannZeta ρ = 0 → |ρ.im| ≠ T) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * Complex.exp (-s * (y : ℂ)) ∂volume
    kadiri_thm_3_1_q1_I φ a T =
      (1 / (2 * (Real.pi : ℂ))) *
        (∫ t in Set.Ioo (-T) T,
          (-deriv riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I) /
              riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I)) *
            Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I)))
      + kadiriTopHorizontalPVCanonical φ a T
      - kadiriBotHorizontalPVCanonical φ a T
      + Φ (-1)
      - riemannZeta.zeroes_sum (.Ioo 0 1) (.Ioo (-T) T) (fun ρ ↦ Φ (-ρ)) := by
  intro Φ
  have htopNo : KadiriNoZeroOrdinate T :=
    kadiriNoZeroOrdinate_of_abs_noZero hT hT_noz
  have hbotNo : KadiriNoZeroOrdinate (-T) :=
    kadiriNoZeroOrdinate_neg_of_abs_noZero hT hT_noz
  have h :=
    kadiri_thm_3_1_q1_eq_12 hφ hb hφ_decay hφ'_decay ha hab ha1 hT hT_noz
  unfold Φ at h
  have hOrdinary :
      kadiri_thm_3_1_q1_I φ a T =
        (1 / (2 * (Real.pi : ℂ))) *
          (∫ t in Set.Ioo (-T) T,
            (-deriv riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I) /
                riemannZeta (((-a : ℝ) : ℂ) + (t : ℂ) * I)) *
              Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I)))
        + kadiriTopHorizontalIntegral φ a T
        - kadiriBotHorizontalIntegral φ a T
        + Φ (-1)
        - riemannZeta.zeroes_sum (.Ioo 0 1) (.Ioo (-T) T) (fun ρ ↦ Φ (-ρ)) := by
    unfold Φ
    dsimp only at h ⊢
    simpa [kadiriTopHorizontalIntegral, kadiriBotHorizontalIntegral,
      kadiriTopHorizontalPoint, kadiriBotHorizontalPoint, kadiriHorizontalPhi] using h
  simpa [
    kadiriTopHorizontalIntegral_eq_pvCanonical_of_noZero
      (φ := φ) (a := a) (T := T) htopNo,
    kadiriBotHorizontalIntegral_eq_pvCanonical_of_noZero
      (φ := φ) (a := a) (T := T) hbotNo] using hOrdinary

end

end Kadiri
