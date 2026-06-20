import PrimeNumberTheoremAnd.IEANTN.KadiriWideStripZeta
import PrimeNumberTheoremAnd.IEANTN.KadiriGammaDecay

/-!
# Kadiri vertical Gamma decay: the unconditional strip-fill

This module discharges the vertical `Γ`-decay estimate that feeds the χ-factor
route.  It records two versions:

* a sharp-degree route using the second-order digamma Binet correction, proving
  the named `KadiriChiFactorPolyBound` contract;
* a loose-degree route using the strip growth bound
  `Complex.exists_norm_digamma_le_log`, proving the all-`A` polynomial
  wide-strip estimate used by the `FinalBound` assembly.

The sharp route keeps the Kadiri contract exponent `A + 1 / 2`.  The capstone
only needs a *fixed* polynomial exponent: the wide-strip `ζ` growth feeds
`FinalBound` through `log B = O(log U)`, where the exact power of `U` is
irrelevant to the `→ 0` conclusion.  The loose route uses the fundamental theorem
of calculus on `log‖Γ(u + iτ)‖` plus the strip bound
`‖ψ‖ ≤ C·log(|τ| + 2)`, then reflects through the functional equation and
cancels the `cos(πw/2)` growth.
-/

open Complex Real

namespace Kadiri

/-! ## Reusable Gamma/digamma wrappers -/

/-- `d/du log‖g u‖ = Re(g'/g)` when `g u ≠ 0` (`g : ℝ → ℂ`). -/
theorem hasDerivAt_log_norm {g : ℝ → ℂ} {g' : ℂ} {u : ℝ}
    (h : HasDerivAt g g' u) (hne : g u ≠ 0) :
    HasDerivAt (fun x => Real.log ‖g x‖) (g' / g u).re u :=
  Complex.hasDerivAt_log_norm h hne

/-- The log-norm of Γ along the vertical line has derivative `Re ψ(u + iτ)`. -/
theorem hasDerivAt_log_norm_gamma {τ u : ℝ} (hu : 0 < u) :
    HasDerivAt
      (fun x : ℝ => Real.log ‖Complex.Gamma ((x : ℂ) + (τ : ℂ) * I)‖)
      (Complex.digamma ((u : ℂ) + (τ : ℂ) * I)).re u :=
  Complex.hasDerivAt_log_norm_gamma hu

/-- **Vertical Gamma decay (`u + iτ`) with sharp `u - 1/2` power.** -/
theorem gamma_vertical_decay_add {A : ℝ} (hA0 : 0 ≤ A) :
    ∃ CΓ : ℝ, 0 ≤ CΓ ∧
      ∀ σ' τ : ℝ, σ' ∈ Set.Icc (1 / 2 : ℝ) (A + 1) → (1 : ℝ) ≤ |τ| →
        ‖Complex.Gamma ((σ' : ℂ) + (τ : ℂ) * I)‖ ≤
          CΓ * (|τ| + 2) ^ (σ' - 1 / 2) *
            Real.exp (-(Real.pi * |τ| / 2)) :=
  Complex.gamma_vertical_decay_add hA0

/-- The sharp-coefficient vertical Gamma decay contract used by the χ-factor route. -/
theorem kadiriVerticalGammaDecay {A : ℝ} (hA0 : 0 ≤ A) : KadiriVerticalGammaDecay A := by
  obtain ⟨CΓ, hCΓ, hbd⟩ := gamma_vertical_decay_add hA0
  refine ⟨CΓ, hCΓ, fun u t hu ht => ?_⟩
  have hconj : ‖Complex.Gamma ((u : ℂ) - (t : ℂ) * I)‖ =
      ‖Complex.Gamma ((u : ℂ) + (t : ℂ) * I)‖ := by
    rw [show ((u : ℂ) - (t : ℂ) * I) = (starRingEnd ℂ) ((u : ℂ) + (t : ℂ) * I) by
      apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im], Complex.Gamma_conj, norm_conj]
  rw [hconj]
  exact hbd u t hu ht

/-- The corrected χ-factor polynomial contract, now discharged from vertical Gamma decay. -/
theorem kadiriChiFactorPolyBound {A : ℝ} (hA0 : 0 ≤ A) : KadiriChiFactorPolyBound A :=
  kadiriChiFactorPolyBound_of_verticalGammaDecay hA0 (kadiriVerticalGammaDecay hA0)

/-- Unconditional sharp-degree wide-strip bound for `riemannZeta`. -/
theorem riemannZeta_wideStrip_poly_bound_unconditional {A : ℝ} (hA0 : 0 ≤ A) (hA2 : A < 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (-A) (1 / 2) → (1 : ℝ) ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ (A + 3 / 2) :=
  riemannZeta_wideStrip_poly_bound hA0 hA2 (kadiriChiFactorPolyBound hA0)

/-! ## The loose vertical Gamma bound -/

/-- **Loose vertical Gamma decay (`u + iτ`).** On `1/2 ≤ σ' ≤ A + 1` with `|τ| ≥ 1`,
`‖Γ(σ' + iτ)‖ ≤ √(2π)·(|τ| + 2)^d·e^{-π|τ|/2}` for the fixed power `d = C·(A + 1/2)`,
`C` the in-tree digamma log-growth constant on `[1/2, A + 1]`. -/
theorem gamma_vertical_loose_bound_add {A : ℝ} (hA0 : 0 ≤ A) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ σ' τ : ℝ, σ' ∈ Set.Icc (1 / 2 : ℝ) (A + 1) → (1 : ℝ) ≤ |τ| →
      ‖Complex.Gamma ((σ' : ℂ) + (τ : ℂ) * I)‖ ≤
        Real.sqrt (2 * Real.pi) * (|τ| + 2) ^ d * Real.exp (-(Real.pi * |τ| / 2)) :=
  Complex.gamma_vertical_loose_bound_add hA0

/-- The same loose decay for the conjugated argument `Γ(u - iτ)` used by the
χ-factor route (`‖Γ(u - iτ)‖ = ‖Γ(u + iτ)‖`). -/
theorem kadiriVerticalGammaDecay_loose {A : ℝ} (hA0 : 0 ≤ A) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ u t : ℝ, u ∈ Set.Icc (1 / 2 : ℝ) (A + 1) → (1 : ℝ) ≤ |t| →
      ‖Complex.Gamma ((u : ℂ) - (t : ℂ) * I)‖ ≤
        Real.sqrt (2 * Real.pi) * (|t| + 2) ^ d * Real.exp (-(Real.pi * |t| / 2)) := by
  obtain ⟨d, hd0, hbd⟩ := gamma_vertical_loose_bound_add hA0
  refine ⟨d, hd0, fun u t hu ht => ?_⟩
  have hconj : ‖Complex.Gamma ((u : ℂ) - (t : ℂ) * I)‖
      = ‖Complex.Gamma ((u : ℂ) + (t : ℂ) * I)‖ := by
    rw [show ((u : ℂ) - (t : ℂ) * I) = (starRingEnd ℂ) ((u : ℂ) + (t : ℂ) * I) by
      apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im], Complex.Gamma_conj, norm_conj]
  rw [hconj]
  exact hbd u t hu ht

/-! ## The unconditional χ-factor polynomial bound

The reflection factor `Γ(1-s)·cos(π(1-s)/2)` at `s = σ + it`, `σ ∈ [-A, 1/2]`,
is polynomial in `|t|` with a fixed power: the `e^{π|t|/2}` growth of `cos(π(1-s)/2)`
is cancelled by the `e^{-π|t|/2}` decay carried by the loose vertical `Γ` bound. -/

/-- **χ-factor polynomial bound (unconditional, loose degree).**  There is a
constant `Cχ` and fixed power `d` so that for `σ ∈ [-A, 1/2]`, `|t| ≥ 1`,
`‖Γ(1-s)·cos(π(1-s)/2)‖ ≤ Cχ·(|t| + 2)^d`. -/
theorem kadiriChiFactorPolyBound_loose {A : ℝ} (hA0 : 0 ≤ A) :
    ∃ Cχ d : ℝ, 0 ≤ Cχ ∧ 0 ≤ d ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (-A) (1 / 2 : ℝ) → (1 : ℝ) ≤ |t| →
        ‖Complex.Gamma (1 - ((σ : ℂ) + (t : ℂ) * I)) *
            Complex.cos ((Real.pi : ℂ) * (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2)‖
          ≤ Cχ * (|t| + 2) ^ d := by
  obtain ⟨d, hd0, hΓbd⟩ := kadiriVerticalGammaDecay_loose hA0
  refine ⟨Real.sqrt (2 * Real.pi), d, Real.sqrt_nonneg _, hd0, fun σ t hσ ht => ?_⟩
  obtain ⟨hσlo, hσhi⟩ := hσ
  set u : ℝ := 1 - σ with hu_def
  have hu : u ∈ Set.Icc (1 / 2 : ℝ) (A + 1) := ⟨by linarith, by linarith⟩
  -- `1 - s = u - it`.
  have h1s : (1 - ((σ : ℂ) + (t : ℂ) * I)) = ((u : ℂ) - (t : ℂ) * I) := by
    rw [hu_def]; push_cast; ring
  have hΓline : ‖Complex.Gamma (1 - ((σ : ℂ) + (t : ℂ) * I))‖ ≤
      Real.sqrt (2 * Real.pi) * (|t| + 2) ^ d * Real.exp (-(Real.pi * |t| / 2)) := by
    rw [h1s]; exact hΓbd u t hu ht
  -- `cos` reflection bound (same as in-tree).
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2)‖ ≤
      Real.exp (Real.pi * |t| / 2) := by
    have hcosb := Complex.norm_cos_le_exp_abs_im
      ((Real.pi : ℂ) * (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2)
    refine hcosb.trans (Real.exp_le_exp.mpr ?_)
    have him : (((Real.pi : ℂ) * (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2).im) = -Real.pi * t / 2 := by
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
    rw [him]
    have habs : |(-Real.pi * t) / 2| = Real.pi * |t| / 2 := by
      rw [abs_div, abs_mul, abs_neg, abs_of_pos Real.pi_pos,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact le_of_eq habs
  have hΓrhs_nonneg :
      0 ≤ Real.sqrt (2 * Real.pi) * (|t| + 2) ^ d * Real.exp (-(Real.pi * |t| / 2)) := by
    have : 0 ≤ (|t| + 2) ^ d := Real.rpow_nonneg (by linarith [abs_nonneg t]) d
    positivity
  calc ‖Complex.Gamma (1 - ((σ : ℂ) + (t : ℂ) * I)) *
        Complex.cos ((Real.pi : ℂ) * (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2)‖
      = ‖Complex.Gamma (1 - ((σ : ℂ) + (t : ℂ) * I))‖ *
          ‖Complex.cos ((Real.pi : ℂ) * (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2)‖ := by rw [norm_mul]
    _ ≤ (Real.sqrt (2 * Real.pi) * (|t| + 2) ^ d * Real.exp (-(Real.pi * |t| / 2))) *
          Real.exp (Real.pi * |t| / 2) :=
        mul_le_mul hΓline hcos (norm_nonneg _) hΓrhs_nonneg
    _ = Real.sqrt (2 * Real.pi) * (|t| + 2) ^ d := by
        rw [mul_assoc, ← Real.exp_add, show -(Real.pi * |t| / 2) + Real.pi * |t| / 2 = 0 by ring,
          Real.exp_zero, mul_one]

/-! ## The unconditional wide-strip polynomial-in-`t` bound for `riemannZeta` -/

/-- **Unconditional wide-strip polynomial bound for `riemannZeta`.**  There are
`C ≥ 0` and a fixed power `e ≥ 0` so that on the wide strip `σ ∈ [-A, 1/2]`
(`0 ≤ A`), for every `|t| ≥ 1`,
`‖ζ(σ + it)‖ ≤ C·(|t| + 2)^e`.
The χ-factor cancellation is now in-tree (no contract), so this is unconditional.
The left-half reflection uses the bounded right-half Abel estimate, valid for all
`A ≥ 0` with no `A < 2` cutoff. -/
theorem riemannZeta_wideStrip_poly_bound_uncond {A : ℝ} (hA0 : 0 ≤ A) :
    ∃ C e : ℝ, 0 ≤ C ∧ 0 ≤ e ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (-A) (1 / 2 : ℝ) → (1 : ℝ) ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ e := by
  obtain ⟨Cχ, d, hCχ, hd0, hχbd⟩ := kadiriChiFactorPolyBound_loose hA0
  obtain ⟨Cr, hCr, hright⟩ := norm_riemannZeta_le_linear_on_right_half (B := A + 1) (by linarith)
  refine ⟨2 * Cχ * Cr, d + 1, by positivity, by linarith, fun σ t hσ ht => ?_⟩
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  set w : ℂ := 1 - s with hw
  obtain ⟨hσlo, hσhi⟩ := hσ
  have hw_re : w.re = 1 - σ := by
    rw [hw, hs]; simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
  have hw_im : w.im = -t := by
    rw [hw, hs]; simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
  have hw_lo : (1 / 2 : ℝ) ≤ w.re := by rw [hw_re]; linarith
  have hw_hi : w.re ≤ A + 1 := by rw [hw_re]; linarith
  have hw_im_abs : |w.im| = |t| := by rw [hw_im, abs_neg]
  have hwn : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n hn
    have h := congrArg Complex.re hn
    simp only [Complex.neg_re, Complex.natCast_re] at h
    rw [hw_re] at hw_lo h
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hw1 : w ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    rw [hw_im] at hi
    simp at hi
    have : |t| = 0 := by rw [show t = 0 by linarith]; simp
    linarith
  have hfe := riemannZeta_one_sub hwn hw1
  have h1w : (1 : ℂ) - w = s := by rw [hw]; ring
  rw [h1w] at hfe
  have hw_re_nonneg : (0 : ℝ) ≤ w.re := by linarith
  have hpow : ‖((2 : ℂ) * (Real.pi : ℂ)) ^ (-w)‖ ≤ 1 :=
    Complex.Gammaℝ.Stirling.norm_cpow_two_mul_pi_neg_le_one hw_re_nonneg
  have hζw : ‖riemannZeta w‖ ≤ Cr * (|t| + 2) := by
    have hb := hright w.re w.im hw_lo hw_hi ?_
    · have hw_rect : ((w.re : ℂ) + ((w.im : ℝ) : ℂ) * I) = w := by
        apply Complex.ext <;> simp
      rw [hw_rect] at hb
      rwa [hw_im_abs] at hb
    · rw [hw_im_abs]; exact ht
  have hχval :
      ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ ≤ Cχ * (|t| + 2) ^ d := by
    have := hχbd σ t ⟨hσlo, hσhi⟩ ht
    rwa [show (1 - ((σ : ℂ) + (t : ℂ) * I)) = w by rw [hw, hs]] at this
  have hsplit : ‖riemannZeta s‖
      = 2 * ‖((2 : ℂ) * (Real.pi : ℂ)) ^ (-w)‖
          * ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ * ‖riemannZeta w‖ := by
    rw [hfe]
    rw [show (2 : ℂ) * ((2 : ℂ) * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w
          * Complex.cos ((Real.pi : ℂ) * w / 2) * riemannZeta w
        = (2 : ℂ) * (((2 : ℂ) * (Real.pi : ℂ)) ^ (-w)
            * (Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)) * riemannZeta w) by ring]
    rw [norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat]
    ring
  have hbase1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hrpow_add : (|t| + 2) ^ d * (|t| + 2) = (|t| + 2) ^ (d + 1) := by
    rw [← Real.rpow_add_one (by linarith [hbase1] : (|t| + 2) ≠ 0) d]
  calc ‖riemannZeta s‖
      = 2 * ‖((2 : ℂ) * (Real.pi : ℂ)) ^ (-w)‖
          * ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ * ‖riemannZeta w‖ := hsplit
    _ ≤ 2 * 1 * (Cχ * (|t| + 2) ^ d) * (Cr * (|t| + 2)) := by
        have hχ_nonneg :
            (0 : ℝ) ≤ ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ := norm_nonneg _
        have hζ_nonneg : (0 : ℝ) ≤ ‖riemannZeta w‖ := norm_nonneg _
        have step :
            2 * ‖((2 : ℂ) * (Real.pi : ℂ)) ^ (-w)‖ *
                ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖
              ≤ 2 * 1 * (Cχ * (|t| + 2) ^ d) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num)) hχval hχ_nonneg (by positivity)
        exact mul_le_mul step hζw hζ_nonneg (by positivity)
    _ = 2 * Cχ * Cr * ((|t| + 2) ^ d * (|t| + 2)) := by ring
    _ = 2 * Cχ * Cr * (|t| + 2) ^ (d + 1) := by rw [hrpow_add]

/-- **Unconditional fixed-strip polynomial bound.**  For any left edge `-A`
(`0 ≤ A`) and right edge `B ≥ 1/2`, there are `C ≥ 0` and a fixed power `e ≥ 0`
with `‖ζ(σ + it)‖ ≤ C·(|t| + 2)^e` for all `σ ∈ [-A, B]`, `|t| ≥ 1`.  No contract:
the left half uses the now-unconditional wide-strip bound, the right half the
in-tree bounded right-half Abel estimate. -/
theorem riemannZeta_fixedStrip_poly_bound_uncond {A B : ℝ} (hA0 : 0 ≤ A)
    (hB : (1 / 2 : ℝ) ≤ B) :
    ∃ C e : ℝ, 0 ≤ C ∧ 0 ≤ e ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (-A) B → (1 : ℝ) ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ e := by
  obtain ⟨Cl, el, hCl, hel0, hleft⟩ := riemannZeta_wideStrip_poly_bound_uncond hA0
  obtain ⟨Cr, hCr, hright⟩ := norm_riemannZeta_le_linear_on_right_half hB
  refine ⟨max Cl Cr, max el 1, by positivity, le_trans zero_le_one (le_max_right _ _),
    fun σ t hσ ht => ?_⟩
  have hbase1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hpow_max : (0 : ℝ) ≤ (|t| + 2) ^ (max el 1) :=
    Real.rpow_nonneg (by linarith [abs_nonneg t]) _
  by_cases hleftcase : σ ≤ (1 / 2 : ℝ)
  · have hbound := hleft σ t ⟨hσ.1, hleftcase⟩ ht
    have hmono : (|t| + 2) ^ el ≤ (|t| + 2) ^ (max el 1) :=
      Real.rpow_le_rpow_of_exponent_le hbase1 (le_max_left _ _)
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cl * (|t| + 2) ^ el := hbound
      _ ≤ Cl * (|t| + 2) ^ (max el 1) := mul_le_mul_of_nonneg_left hmono hCl
      _ ≤ max Cl Cr * (|t| + 2) ^ (max el 1) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpow_max
  · have hσlo : (1 / 2 : ℝ) ≤ σ := by linarith
    have hb := hright σ t hσlo hσ.2 ht
    have hpow1 : |t| + 2 ≤ (|t| + 2) ^ (max el 1) := by
      nth_rw 1 [← Real.rpow_one (|t| + 2)]
      exact Real.rpow_le_rpow_of_exponent_le hbase1 (le_max_right _ _)
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cr * (|t| + 2) := hb
      _ ≤ Cr * (|t| + 2) ^ (max el 1) := mul_le_mul_of_nonneg_left hpow1 hCr
      _ ≤ max Cl Cr * (|t| + 2) ^ (max el 1) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpow_max

end Kadiri
