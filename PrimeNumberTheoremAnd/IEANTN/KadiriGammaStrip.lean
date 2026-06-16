import PrimeNumberTheoremAnd.IEANTN.Kadiri
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-!
# Gamma-factor strip bound for Kadiri

This module isolates the logarithmic growth bound for the gamma-factor part of
Kadiri's logarithmic-derivative identity, without editing the main `Kadiri.lean`
file.
-/

namespace Kadiri

open Complex

noncomputable section

/-- The gamma-factor coefficient in the Kadiri strip has logarithmic growth in height. -/
theorem kadiri_gamma_strip_Olog :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖1 / (s - 1) - (1 / 2 : ℂ) * (Real.log Real.pi : ℂ) +
          (1 / 2 : ℂ) * digamma (s / 2 + 1)‖ ≤
        C * Real.log (|s.im| + 2) := by
  obtain ⟨Cψ, hCψ, hψ⟩ :=
    exists_norm_digamma_div_two_le_log (a := 1) (b := 4) (by norm_num)
  let B : ℝ := ‖(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)‖
  let C : ℝ := Cψ + (1 + B) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    have hconst : 0 < (1 + B) / Real.log 2 := by
      exact div_pos (by linarith) hlog2
    linarith
  refine ⟨C, hC, ?_⟩
  intro s hs_low hs_high him
  let L : ℝ := Real.log (|s.im| + 2)
  have hL_ge_log2 : Real.log 2 ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hs2_re_low : 1 ≤ (s + (2 : ℂ)).re := by
    rw [Complex.add_re]
    norm_num
    linarith
  have hs2_re_high : (s + (2 : ℂ)).re ≤ 4 := by
    rw [Complex.add_re]
    norm_num
    linarith
  have hψs :
      ‖digamma (s / 2 + 1)‖ ≤ Cψ * L := by
    have h := hψ (s + (2 : ℂ)) hs2_re_low hs2_re_high
    have harg : (s + (2 : ℂ)) / 2 = s / 2 + 1 := by ring
    have him_eq : (s + (2 : ℂ)).im = s.im := by
      rw [Complex.add_im]
      norm_num
    simpa [harg, him_eq, L] using h
  have hpole_norm : ‖1 / (s - 1)‖ ≤ 1 := by
    have hnorm_ge : 1 ≤ ‖s - 1‖ := by
      calc
        1 ≤ |s.im| := him
        _ = |(s - 1).im| := by
          simp only [Complex.sub_im, Complex.one_im, sub_zero]
        _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    have hnorm_pos : 0 < ‖s - 1‖ := lt_of_lt_of_le zero_lt_one hnorm_ge
    rw [norm_div, norm_one]
    rw [div_le_iff₀ hnorm_pos]
    simpa using hnorm_ge
  have hψterm :
      ‖(1 / 2 : ℂ) * digamma (s / 2 + 1)‖ ≤ Cψ * L := by
    rw [norm_mul]
    have hhalf : ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) := by
      norm_num [Complex.normSq, Complex.normSq_apply]
    calc
      ‖(1 / 2 : ℂ)‖ * ‖digamma (s / 2 + 1)‖
          ≤ 1 * ‖digamma (s / 2 + 1)‖ :=
            mul_le_mul_of_nonneg_right hhalf (norm_nonneg _)
      _ = ‖digamma (s / 2 + 1)‖ := one_mul _
      _ ≤ Cψ * L := hψs
  have hconst_absorb : 1 + B ≤ ((1 + B) / Real.log 2) * L := by
    calc
      1 + B = ((1 + B) / Real.log 2) * Real.log 2 := by
        field_simp [ne_of_gt hlog2]
      _ ≤ ((1 + B) / Real.log 2) * L :=
        mul_le_mul_of_nonneg_left hL_ge_log2
          (div_nonneg (by linarith) hlog2.le)
  have htriangle :
      ‖1 / (s - 1) - (1 / 2 : ℂ) * (Real.log Real.pi : ℂ) +
          (1 / 2 : ℂ) * digamma (s / 2 + 1)‖ ≤
        (1 + B) + Cψ * L := by
    have h1 := norm_add_le
      (1 / (s - 1) - (1 / 2 : ℂ) * (Real.log Real.pi : ℂ))
      ((1 / 2 : ℂ) * digamma (s / 2 + 1))
    have h2 := norm_sub_le
      (1 / (s - 1)) ((1 / 2 : ℂ) * (Real.log Real.pi : ℂ))
    calc
      ‖1 / (s - 1) - (1 / 2 : ℂ) * (Real.log Real.pi : ℂ) +
          (1 / 2 : ℂ) * digamma (s / 2 + 1)‖
          ≤ ‖1 / (s - 1) - (1 / 2 : ℂ) * (Real.log Real.pi : ℂ)‖ +
              ‖(1 / 2 : ℂ) * digamma (s / 2 + 1)‖ := h1
      _ ≤ (‖1 / (s - 1)‖ + ‖(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)‖) +
              ‖(1 / 2 : ℂ) * digamma (s / 2 + 1)‖ := by
            linarith
      _ ≤ (1 + B) + Cψ * L := by
            dsimp [B]
            linarith
  calc
    ‖1 / (s - 1) - (1 / 2 : ℂ) * (Real.log Real.pi : ℂ) +
        (1 / 2 : ℂ) * digamma (s / 2 + 1)‖
        ≤ (1 + B) + Cψ * L := htriangle
    _ ≤ ((1 + B) / Real.log 2) * L + Cψ * L := by
      exact add_le_add hconst_absorb (le_refl (Cψ * L))
    _ = C * Real.log (|s.im| + 2) := by
      dsimp [C, L]
      ring

end

end Kadiri
