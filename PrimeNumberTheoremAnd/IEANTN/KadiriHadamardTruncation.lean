import PrimeNumberTheoremAnd.IEANTN.Kadiri

/-!
# Hadamard subtraction at `2 + it`

This module packages the algebraic truncation of Kadiri's Hadamard expansion
with the Hadamard identity supplied as a named hypothesis.
-/

namespace Kadiri

open Complex
open scoped BigOperators

/-- The paired zero contribution is summable after subtracting two shifts. Away from the
finite set where either shifted imaginary part is small, the term is bounded by the product
of two reciprocal shifted heights and hence by the sum of their square tails. -/
theorem summable_one_div_sub_one_div_at_zeros (s w : ℂ) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) =>
      1 / (s - ρ.val) - 1 / (w - ρ.val)) := by
  have htails : Summable (fun ρ : NontrivialZeros =>
      ‖w - s‖ / 2 *
        (|(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ) +
          |(w - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ))) :=
    ((summable_zeroImagSquareTail_shifted_unconditional s).add
      (summable_zeroImagSquareTail_shifted_unconditional w)).mul_left _
  refine Summable.of_norm_bounded_eventually htails ?_
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset
    ((nontrivialZeros_shifted_abs_im_lt_one_finite s).union
      (nontrivialZeros_shifted_abs_im_lt_one_finite w))
  intro ρ hbad
  rw [Set.mem_setOf_eq] at hbad
  rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
  by_contra hsmall
  rw [not_or] at hsmall
  obtain ⟨hs_small, hw_small⟩ := hsmall
  have hs_im : 1 ≤ |(s - (ρ : ℂ)).im| := le_of_not_gt hs_small
  have hw_im : 1 ≤ |(w - (ρ : ℂ)).im| := le_of_not_gt hw_small
  apply hbad
  have hs_im_ne : (s - (ρ : ℂ)).im ≠ 0 := by
    intro h
    rw [h] at hs_im
    norm_num at hs_im
  have hw_im_ne : (w - (ρ : ℂ)).im ≠ 0 := by
    intro h
    rw [h] at hw_im
    norm_num at hw_im
  have hsρ : s - (ρ : ℂ) ≠ 0 := by
    intro h
    apply hs_im_ne
    rw [h]
    rfl
  have hwρ : w - (ρ : ℂ) ≠ 0 := by
    intro h
    apply hw_im_ne
    rw [h]
    rfl
  have hs_im_pos : 0 < |(s - (ρ : ℂ)).im| := lt_of_lt_of_le one_pos hs_im
  have hw_im_pos : 0 < |(w - (ρ : ℂ)).im| := lt_of_lt_of_le one_pos hw_im
  have hpacket :
      1 / (s - (ρ : ℂ)) - 1 / (w - (ρ : ℂ)) =
        (w - s) / ((s - (ρ : ℂ)) * (w - (ρ : ℂ))) := by
    field_simp
    ring
  rw [hpacket, norm_div, norm_mul]
  have hstep1 :
      ‖w - s‖ / (‖s - (ρ : ℂ)‖ * ‖w - (ρ : ℂ)‖) ≤
        ‖w - s‖ *
          (|(s - (ρ : ℂ)).im|⁻¹ * |(w - (ρ : ℂ)).im|⁻¹) := by
    rw [div_eq_mul_inv, mul_inv]
    have ha : ‖s - (ρ : ℂ)‖⁻¹ ≤ |(s - (ρ : ℂ)).im|⁻¹ :=
      inv_anti₀ hs_im_pos (Complex.abs_im_le_norm _)
    have hb : ‖w - (ρ : ℂ)‖⁻¹ ≤ |(w - (ρ : ℂ)).im|⁻¹ :=
      inv_anti₀ hw_im_pos (Complex.abs_im_le_norm _)
    have hb0 : 0 ≤ ‖w - (ρ : ℂ)‖⁻¹ := by positivity
    have ha0 : 0 ≤ |(s - (ρ : ℂ)).im|⁻¹ := by positivity
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (w - s))
    exact mul_le_mul ha hb hb0 ha0
  have hstep2 :
      |(s - (ρ : ℂ)).im|⁻¹ * |(w - (ρ : ℂ)).im|⁻¹ ≤
        (|(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ) +
          |(w - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ)) / 2 := by
    nlinarith [two_mul_le_add_sq (|(s - (ρ : ℂ)).im|⁻¹)
      (|(w - (ρ : ℂ)).im|⁻¹)]
  calc
    ‖w - s‖ / (‖s - (ρ : ℂ)‖ * ‖w - (ρ : ℂ)‖)
        ≤ ‖w - s‖ *
          (|(s - (ρ : ℂ)).im|⁻¹ * |(w - (ρ : ℂ)).im|⁻¹) := hstep1
    _ ≤ ‖w - s‖ *
          ((|(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ) +
            |(w - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ)) / 2) :=
        mul_le_mul_of_nonneg_left hstep2 (norm_nonneg _)
    _ = ‖w - s‖ / 2 *
          (|(s - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ) +
            |(w - (ρ : ℂ)).im|⁻¹ ^ (2 : ℕ)) := by
        ring

/-- Regroup the difference of two genus-one zero-packet sums into one paired
difference sum. -/
theorem tsum_hadamard_packets_sub_eq_tsum_one_div_sub (s w : ℂ) :
    (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (ρ.val : ℂ) + 1 / (s - ρ.val))) -
      (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (ρ.val : ℂ) + 1 / (w - ρ.val))) =
    ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (s - ρ.val) - 1 / (w - ρ.val)) := by
  rw [← Summable.tsum_sub (summable_one_div_add_one_div_at_zeros s)
    (summable_one_div_add_one_div_at_zeros w)]
  refine tsum_congr fun ρ => ?_
  ring

/-- Weighted version of `tsum_hadamard_packets_sub_eq_tsum_one_div_sub`, in the
`riemannZeta.zeroes_sum` form used by the clean multiplicity-aware Hadamard identity. -/
theorem zeroes_sum_hadamard_packets_sub_eq_zeroes_sum_one_div_sub (s w : ℂ) :
    riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
        (fun ρ => 1 / ρ + 1 / (s - ρ)) -
      riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
        (fun ρ => 1 / ρ + 1 / (w - ρ)) =
    riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
        (fun ρ => 1 / (s - ρ) - 1 / (w - ρ)) := by
  unfold riemannZeta.zeroes_sum
  rw [← Summable.tsum_sub (summable_weighted_one_div_add_one_div_at_zeros s)
    (summable_weighted_one_div_add_one_div_at_zeros w)]
  refine tsum_congr fun ρ => ?_
  ring

/-- Pointwise far-tail bound for the paired zero term on a horizontal line. If
`s` has imaginary part `t` and real part in the Kadiri strip `[-1, 2]`, then the
subtraction at `2 + it` turns the zero term into an `O(|t - Im ρ|⁻²)` term away
from the unit window around `t`. -/
theorem norm_one_div_sub_one_div_at_zero_le_far_height_sq {s : ℂ} {t : ℝ}
    (hsim : s.im = t) (hsre_lo : -1 ≤ s.re) (hsre_hi : s.re ≤ 2)
    (ρ : NontrivialZeros) (hfar : 1 ≤ |t - (ρ : ℂ).im|) :
    ‖1 / (s - (ρ : ℂ)) - 1 / (((2 : ℂ) + (t : ℂ) * I) - (ρ : ℂ))‖ ≤
      3 * |t - (ρ : ℂ).im|⁻¹ ^ (2 : ℕ) := by
  let w : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hheight_pos : 0 < |t - (ρ : ℂ).im| := lt_of_lt_of_le one_pos hfar
  have hs_im : (s - (ρ : ℂ)).im = t - (ρ : ℂ).im := by
    rw [Complex.sub_im, hsim]
  have hw_im : (w - (ρ : ℂ)).im = t - (ρ : ℂ).im := by
    simp [w, Complex.sub_im]
  have hs_im_ne : (s - (ρ : ℂ)).im ≠ 0 := by
    intro h
    have hzero : t - (ρ : ℂ).im = 0 := by
      rw [← hs_im, h]
    rw [hzero, abs_zero] at hheight_pos
    exact (lt_irrefl (0 : ℝ)) hheight_pos
  have hw_im_ne : (w - (ρ : ℂ)).im ≠ 0 := by
    intro h
    have hzero : t - (ρ : ℂ).im = 0 := by
      rw [← hw_im, h]
    rw [hzero, abs_zero] at hheight_pos
    exact (lt_irrefl (0 : ℝ)) hheight_pos
  have hsρ : s - (ρ : ℂ) ≠ 0 := by
    intro h
    apply hs_im_ne
    rw [h]
    rfl
  have hwρ : w - (ρ : ℂ) ≠ 0 := by
    intro h
    apply hw_im_ne
    rw [h]
    rfl
  have hpacket :
      1 / (s - (ρ : ℂ)) - 1 / (w - (ρ : ℂ)) =
        (w - s) / ((s - (ρ : ℂ)) * (w - (ρ : ℂ))) := by
    field_simp
    ring
  have hws : w - s = ((2 - s.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [w]
    · simp [w, hsim]
  have hnum : ‖w - s‖ ≤ 3 := by
    have hreal : |2 - s.re| ≤ (3 : ℝ) := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    rw [hws]
    change ‖((2 - s.re : ℝ) : ℂ)‖ ≤ (3 : ℝ)
    rw [Complex.norm_real]
    exact hreal
  have hs_inv : ‖s - (ρ : ℂ)‖⁻¹ ≤ |t - (ρ : ℂ).im|⁻¹ := by
    refine inv_anti₀ hheight_pos ?_
    rw [← hs_im]
    exact Complex.abs_im_le_norm _
  have hw_inv : ‖w - (ρ : ℂ)‖⁻¹ ≤ |t - (ρ : ℂ).im|⁻¹ := by
    refine inv_anti₀ hheight_pos ?_
    rw [← hw_im]
    exact Complex.abs_im_le_norm _
  rw [show ((2 : ℂ) + (t : ℂ) * I) = w by rfl, hpacket, norm_div, norm_mul]
  rw [div_eq_mul_inv, mul_inv]
  have hden :
      ‖s - (ρ : ℂ)‖⁻¹ * ‖w - (ρ : ℂ)‖⁻¹ ≤
        |t - (ρ : ℂ).im|⁻¹ * |t - (ρ : ℂ).im|⁻¹ := by
    exact mul_le_mul hs_inv hw_inv (by positivity) (by positivity)
  calc
    ‖w - s‖ * (‖s - (ρ : ℂ)‖⁻¹ * ‖w - (ρ : ℂ)‖⁻¹)
        ≤ 3 * (|t - (ρ : ℂ).im|⁻¹ * |t - (ρ : ℂ).im|⁻¹) := by
          exact mul_le_mul hnum hden (by positivity) (by norm_num)
    _ = 3 * |t - (ρ : ℂ).im|⁻¹ ^ (2 : ℕ) := by ring

/-- Subtract Kadiri's Hadamard identity at `2 + it`, supplied as a hypothesis, from
the same identity at `s`. The zero contribution is expressed as one paired difference
sum. -/
theorem kadiri_subtract_at_two_add_it_truncation
    (s : ℂ) (t : ℝ)
    (hs1 : s ≠ 1)
    (hsZ : s ∉ riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ))
    (hadamard_identity :
      ∀ z : ℂ, z ≠ 1 →
        z ∉ riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) →
        -deriv riemannZeta z / riemannZeta z =
          -hadamardB - (1 / 2 : ℂ) * Real.log Real.pi + 1 / (z - 1) +
          (1 / 2 : ℂ) * digamma (z / 2 + 1) -
          ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
            (1 / (ρ.val : ℂ) + 1 / (z - ρ.val))) :
    -deriv riemannZeta s / riemannZeta s -
        (-deriv riemannZeta ((2 : ℂ) + (t : ℂ) * I) /
          riemannZeta ((2 : ℂ) + (t : ℂ) * I)) =
      (1 / (s - 1) - 1 / (1 + (t : ℂ) * I)) +
        ((1 / 2 : ℂ) * digamma (s / 2 + 1) -
          (1 / 2 : ℂ) * digamma (((2 : ℂ) + (t : ℂ) * I) / 2 + 1)) -
        ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          (1 / (s - ρ.val) -
            1 / (((2 : ℂ) + (t : ℂ) * I) - ρ.val)) := by
  let w : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hw1 : w ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [w] at hre
  have hwZ : w ∉ riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) := by
    intro hz
    have hlt : w.re < 1 := hz.1.2
    simp [w] at hlt
  have hs_id := hadamard_identity s hs1 hsZ
  have hw_id := hadamard_identity w hw1 hwZ
  have hsum := tsum_hadamard_packets_sub_eq_tsum_one_div_sub s w
  rw [hs_id, hw_id, ← hsum]
  simp [w]
  ring

/-- Subtract the clean multiplicity-aware Kadiri Hadamard identity at `2 + it`
from the same identity at `s`. The zero contribution stays in `zeroes_sum`
form, so all zero multiplicities are retained. -/
theorem kadiri_subtract_at_two_add_it_truncation_clean
    (s : ℂ) (t : ℝ)
    (hs0 : s ≠ 0)
    (hs1 : s ≠ 1)
    (hsZ : s ∉ riemannZeta.zeroes) :
    -deriv riemannZeta s / riemannZeta s -
        (-deriv riemannZeta ((2 : ℂ) + (t : ℂ) * I) /
          riemannZeta ((2 : ℂ) + (t : ℂ) * I)) =
      (1 / (s - 1) - 1 / (1 + (t : ℂ) * I)) +
        ((1 / 2 : ℂ) * digamma (s / 2 + 1) -
          (1 / 2 : ℂ) * digamma (((2 : ℂ) + (t : ℂ) * I) / 2 + 1)) -
        riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
          (fun ρ => 1 / (s - ρ) -
            1 / (((2 : ℂ) + (t : ℂ) * I) - ρ)) := by
  let w : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hw0 : w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [w] at hre
  have hw1 : w ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [w] at hre
  have hwZ : w ∉ riemannZeta.zeroes := by
    intro hz
    exact (riemannZeta_ne_zero_of_one_le_re (s := w) (by simp [w])) (by
      simpa [riemannZeta.zeroes] using hz)
  have hs_id := hadamard_identity s hs0 hs1 hsZ
  have hw_id := hadamard_identity w hw0 hw1 hwZ
  have hsum := zeroes_sum_hadamard_packets_sub_eq_zeroes_sum_one_div_sub s w
  rw [hs_id, hw_id, ← hsum]
  simp [w]
  ring

end Kadiri
