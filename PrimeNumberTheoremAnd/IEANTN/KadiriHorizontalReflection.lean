import PrimeNumberTheoremAnd.IEANTN.Kadiri

/-!
# Kadiri horizontal reflection input

This sidecar packages the functional-equation reflection input for the
left half of the horizontal segment.  The full all-height horizontal theorem
still needs the principal-value treatment at zero ordinates; this file only
provides the reusable off-zero reflection and gamma-factor growth estimates.
-/

namespace Kadiri

open Complex

noncomputable section

/-- The gamma and constant term in the reflected logarithmic-derivative identity. -/
noncomputable def kadiriReflectionGammaLogTerm (s : ℂ) : ℂ :=
  ((-Real.log Real.pi : ℝ) : ℂ)
    + (1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))

/-- Functional-equation reflection for `-ζ'/ζ`, with the gamma terms named separately. -/
theorem kadiri_reflection_functional_eq {s : ℂ}
    (hs1 : s ≠ 1) (hs0 : s ≠ 0)
    (hζs : riemannZeta s ≠ 0)
    (hζ1s : riemannZeta (1 - s) ≠ 0) :
    -deriv riemannZeta s / riemannZeta s =
      deriv riemannZeta (1 - s) / riemannZeta (1 - s)
        + kadiriReflectionGammaLogTerm s := by
  have h := kadiri_thm_3_1_q1_functional_eq hs1 hs0 hζs hζ1s
  rw [kadiriReflectionGammaLogTerm]
  rw [h]
  ring

private lemma const_le_div_log_five_mul_log_abs_add_two {D T : ℝ}
    (hD : 0 ≤ D) (hT : 3 ≤ |T|) :
    D ≤ (D / Real.log 5) * Real.log (|T| + 2) := by
  have hlog5_pos : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hlog_le : Real.log 5 ≤ Real.log (|T| + 2) := by
    exact Real.log_le_log (by norm_num) (by linarith)
  calc
    D = (D / Real.log 5) * Real.log 5 := by
      field_simp [hlog5_pos.ne']
    _ ≤ (D / Real.log 5) * Real.log (|T| + 2) :=
      mul_le_mul_of_nonneg_left hlog_le (div_nonneg hD hlog5_pos.le)

private lemma norm_inv_half_left_point_le_one {σ T : ℝ}
    (hT : 3 ≤ |T|) :
    ‖((((σ : ℂ) + (T : ℂ) * I) / 2)⁻¹)‖ ≤ 1 := by
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  have him : |s.im| = |T| := by
    simp [s]
  have him_le_norm : |T| ≤ ‖s‖ := by
    rw [← him]
    exact Complex.abs_im_le_norm s
  have hs_norm_ge : 3 ≤ ‖s‖ := le_trans hT him_le_norm
  have hs_norm_pos : 0 < ‖s‖ := lt_of_lt_of_le (by norm_num) hs_norm_ge
  have hhalf_norm : ‖s / 2‖ = ‖s‖ / 2 := by
    rw [norm_div, norm_ofNat]
  calc
    ‖(s / 2)⁻¹‖ = (‖s‖ / 2)⁻¹ := by
      rw [norm_inv, hhalf_norm]
    _ = 2 / ‖s‖ := by
      field_simp [hs_norm_pos.ne']
    _ ≤ 1 := by
      rw [div_le_one hs_norm_pos]
      linarith

private lemma half_left_point_avoid_neg_nat {σ T : ℝ}
    (hT : 3 ≤ |T|) :
    ∀ m : ℕ, (((σ : ℂ) + (T : ℂ) * I) / 2) ≠ -m := by
  intro m hm
  have him_eq : (((σ : ℂ) + (T : ℂ) * I) / 2).im = (-(m : ℂ)).im := by
    exact congrArg Complex.im hm
  have hT_zero : T = 0 := by
    simpa using him_eq
  have : (3 : ℝ) ≤ 0 := by
    simpa [hT_zero] using hT
  norm_num at this

/-- The reflected gamma-factor term is only logarithmic on the left horizontal strip. -/
theorem kadiri_reflection_gammaLogTerm_le_log {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ T : ℝ,
        σ ∈ Set.Icc (-a) 0 →
        3 ≤ |T| →
        ‖kadiriReflectionGammaLogTerm ((σ : ℂ) + (T : ℂ) * I)‖
          ≤ C * Real.log (|T| + 2) := by
  obtain ⟨C₁, hC₁_pos, hC₁⟩ :=
    Complex.exists_norm_digamma_div_two_le_log (a := 2 - a) (b := 2) (by linarith)
  obtain ⟨C₂, hC₂_pos, hC₂⟩ :=
    Complex.exists_norm_digamma_div_two_le_log (a := 1) (b := 1 + a) (by norm_num)
  let Dπ : ℝ := ‖(((-Real.log Real.pi : ℝ) : ℂ))‖
  let C : ℝ := Dπ / Real.log 5 + C₁ + C₂ + 1 / Real.log 5 + 1
  refine ⟨C, ?_, fun σ T hσ hT => ?_⟩
  · have hlog5_pos : 0 < Real.log 5 := Real.log_pos (by norm_num)
    positivity
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  let L : ℝ := Real.log (|T| + 2)
  have hlog5_pos : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hL_ge_log5 : Real.log 5 ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num) (by linarith)
  have hL_nonneg : 0 ≤ L := le_trans hlog5_pos.le hL_ge_log5
  have hDπ_nonneg : 0 ≤ Dπ := norm_nonneg _
  have hDπ_absorb : Dπ ≤ (Dπ / Real.log 5) * L := by
    simpa [L] using const_le_div_log_five_mul_log_abs_add_two hDπ_nonneg hT
  have h_one_absorb : (1 : ℝ) ≤ (1 / Real.log 5) * L := by
    simpa [L] using const_le_div_log_five_mul_log_abs_add_two (by norm_num : (0 : ℝ) ≤ 1) hT
  have hshift_re_left : 2 - a ≤ (s + 2).re := by
    simp [s]
    linarith [hσ.1]
  have hshift_re_right : (s + 2).re ≤ 2 := by
    simp [s]
    linarith [hσ.2]
  have href_re_left : 1 ≤ (1 - s).re := by
    simp [s]
    linarith [hσ.2]
  have href_re_right : (1 - s).re ≤ 1 + a := by
    simp [s]
    linarith [hσ.1]
  have hψ_shift :
      ‖digamma ((s + 2) / 2)‖ ≤ C₁ * L := by
    simpa [s, L] using hC₁ (s + 2) hshift_re_left hshift_re_right
  have hψ_ref :
      ‖digamma ((1 - s) / 2)‖ ≤ C₂ * L := by
    simpa [s, L, abs_neg] using hC₂ (1 - s) href_re_left href_re_right
  have hψs_eq :
      digamma (s / 2) = digamma ((s + 2) / 2) - (s / 2)⁻¹ := by
    have hrec := Complex.digamma_apply_add_one (s / 2)
      (half_left_point_avoid_neg_nat (σ := σ) (T := T) hT)
    have harg : s / 2 + 1 = (s + 2) / 2 := by ring
    rw [harg] at hrec
    rw [hrec]
    ring
  have hψs :
      ‖digamma (s / 2)‖ ≤ C₁ * L + 1 := by
    calc
      ‖digamma (s / 2)‖
          = ‖digamma ((s + 2) / 2) - (s / 2)⁻¹‖ := by rw [hψs_eq]
      _ ≤ ‖digamma ((s + 2) / 2)‖ + ‖(s / 2)⁻¹‖ := norm_sub_le _ _
      _ ≤ C₁ * L + 1 := by
        exact add_le_add hψ_shift
          (by simpa [s] using norm_inv_half_left_point_le_one (σ := σ) (T := T) hT)
  have hhalf :
      ‖(1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))‖
        ≤ ‖digamma (s / 2)‖ + ‖digamma ((1 - s) / 2)‖ := by
    calc
      ‖(1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))‖
          = ‖(1 / 2 : ℂ)‖ * ‖digamma (s / 2) + digamma ((1 - s) / 2)‖ := by
            rw [norm_mul]
      _ ≤ 1 * ‖digamma (s / 2) + digamma ((1 - s) / 2)‖ := by
            exact mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _)
      _ ≤ ‖digamma (s / 2)‖ + ‖digamma ((1 - s) / 2)‖ := by
            simpa using norm_add_le (digamma (s / 2)) (digamma ((1 - s) / 2))
  have hterm :
      ‖kadiriReflectionGammaLogTerm s‖ ≤ Dπ + (C₁ * L + 1 + C₂ * L) := by
    calc
      ‖kadiriReflectionGammaLogTerm s‖
          ≤ Dπ + ‖(1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))‖ := by
            exact norm_add_le _ _
      _ ≤ Dπ + (‖digamma (s / 2)‖ + ‖digamma ((1 - s) / 2)‖) := by
            exact add_le_add_right hhalf Dπ
      _ ≤ Dπ + ((C₁ * L + 1) + C₂ * L) := by
            exact add_le_add_right (add_le_add hψs hψ_ref) Dπ
      _ = Dπ + (C₁ * L + 1 + C₂ * L) := by ring
  have hC₁L_nonneg : 0 ≤ C₁ * L := mul_nonneg hC₁_pos.le hL_nonneg
  have hC₂L_nonneg : 0 ≤ C₂ * L := mul_nonneg hC₂_pos.le hL_nonneg
  calc
    ‖kadiriReflectionGammaLogTerm ((σ : ℂ) + (T : ℂ) * I)‖
        = ‖kadiriReflectionGammaLogTerm s‖ := by rfl
    _ ≤ Dπ + (C₁ * L + 1 + C₂ * L) := hterm
    _ ≤ C * L := by
      dsimp [C]
      nlinarith [hDπ_absorb, h_one_absorb, hC₁L_nonneg, hC₂L_nonneg, hL_nonneg]

/--
Left-strip consequence of the reflection identity: the only remaining analytic
input after reflection is the right-side logarithmic derivative.
-/
theorem kadiri_left_strip_logDeriv_le_reflected_plus_log {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ T : ℝ,
        σ ∈ Set.Icc (-a) 0 →
        3 ≤ |T| →
        riemannZeta ((σ : ℂ) + (T : ℂ) * I) ≠ 0 →
        riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)) ≠ 0 →
        ‖-deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖
          ≤ ‖deriv riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (1 - ((σ : ℂ) + (T : ℂ) * I))‖
            + C * Real.log (|T| + 2) := by
  obtain ⟨C, hC_pos, hC⟩ := kadiri_reflection_gammaLogTerm_le_log ha ha1
  refine ⟨C, hC_pos, fun σ T hσ hT hζ hζref => ?_⟩
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  have hs1 : s ≠ 1 := by
    intro hs
    have him : s.im = (1 : ℂ).im := congrArg Complex.im hs
    have hT_zero : T = 0 := by
      simpa [s] using him
    have : (3 : ℝ) ≤ 0 := by
      simpa [hT_zero] using hT
    norm_num at this
  have hs0 : s ≠ 0 := by
    intro hs
    have him : s.im = (0 : ℂ).im := congrArg Complex.im hs
    have hT_zero : T = 0 := by
      simpa [s] using him
    have : (3 : ℝ) ≤ 0 := by
      simpa [hT_zero] using hT
    norm_num at this
  have hreflect := kadiri_reflection_functional_eq
    (s := s) hs1 hs0 hζ hζref
  calc
    ‖-deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖
        = ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)
            + kadiriReflectionGammaLogTerm s‖ := by
          rw [show ((σ : ℂ) + (T : ℂ) * I) = s by rfl, hreflect]
    _ ≤ ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖
          + ‖kadiriReflectionGammaLogTerm s‖ := norm_add_le _ _
    _ ≤ ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖
          + C * Real.log (|T| + 2) := by
          exact add_le_add_right (hC σ T hσ hT) _

end

end Kadiri
