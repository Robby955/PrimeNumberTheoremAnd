import PrimeNumberTheoremAnd.IEANTN.KadiriHorizontalPVPackageConstruction
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Trigonometric
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaConvexity
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.StripBounds
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Kadiri wide-strip polynomial-in-`t` growth bound for `riemannZeta`

The scaled-disk `FinalBound` specialization that discharges the Kadiri horizontal
partial-fraction remainder consumes a polynomial-in-`t` upper bound for
`riemannZeta` on a fixed vertical strip reaching *left* of `re = 1/2`.  Inside the
strip `re ∈ [1/2, 3)` the sharp linear bound `norm_riemannZeta_lt_linear_im_on_strip`
(`‖ζ z‖ < 8 + 2|im z|`) already does this.  This module reflects that bound through
the functional equation `riemannZeta_one_sub` to cover the left half of the strip.

## The reflection

For `s = σ + it` with `σ ≤ 1/2`, set `w = 1 - s`; then `re w = 1 - σ ≥ 1/2`,
`im w = -t`, and the functional equation reads
`ζ(s) = 2·(2π)^(-w)·Γ(w)·cos(πw/2)·ζ(w)`.
The three "easy" factors are bounded directly:

* `‖(2π)^(-w)‖ ≤ 1` for `re w ≥ 0` (`Complex.Gammaℝ.Stirling.norm_cpow_two_mul_pi_neg_le_one`);
* `‖ζ(w)‖ < 8 + 2|t|` from the sharp strip bound, when `re w ∈ [1/2, 3)` and `|t| ≥ 1`.

The remaining factor is the *χ-factor magnitude* `‖Γ(w)·cos(πw/2)‖`.  On a vertical
line this is polynomial in `|t|` of degree `1/2 - σ`: the `e^{-π|t|/2}` decay of
`Γ` on the line cancels the `e^{π|t|/2}` growth of `cos(πw/2)`.  This module keeps
that cancellation as the named contract `KadiriChiFactorPolyBound`; the later
sidecar `KadiriGammaDecayUncond` discharges the contract and supplies an
unconditional fixed-strip variant for the `FinalBound` assembly.
-/

namespace Kadiri

open Complex Real

/-! ## The sharp right-strip piece (proved) -/

/-- On the closed-left, half-open-right strip `re ∈ [1/2, 3)` with `|im| ≥ 1`, the
sharp linear bound packaged as a polynomial: `‖ζ z‖ ≤ 8 + 2·(|im z| + 2)`. -/
theorem norm_riemannZeta_le_poly_on_right_strip (z : ℂ)
    (hz_lo : (1 / 2 : ℝ) ≤ z.re) (hz_hi : z.re < 3) (hz_im : (1 : ℝ) ≤ |z.im|) :
    ‖riemannZeta z‖ ≤ 8 + 2 * (|z.im| + 2) := by
  have h := norm_riemannZeta_lt_linear_im_on_strip z ⟨hz_lo, hz_hi⟩ hz_im
  calc ‖riemannZeta z‖ ≤ 8 + 2 * |z.im| := h.le
    _ ≤ 8 + 2 * (|z.im| + 2) := by linarith [abs_nonneg z.im]

/-- On any bounded right half-strip `1/2 ≤ σ ≤ B`, `ζ(σ+it)` is linear in
`|t|+2`, with a constant depending on `B`. -/
theorem norm_riemannZeta_le_linear_on_right_half {B : ℝ} (hB : (1 / 2 : ℝ) ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ t : ℝ, (1 / 2 : ℝ) ≤ σ → σ ≤ B → (1 : ℝ) ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) := by
  refine ⟨2 * B + 4, by linarith, fun σ t hσlo hσhi ht => ?_⟩
  set z : ℂ := (σ : ℂ) + (t : ℂ) * I with hz
  have hzre : z.re = σ := by simp [hz, Complex.add_re, Complex.mul_re]
  have hzim : z.im = t := by simp [hz, Complex.add_im, Complex.mul_im]
  have hz_ne_one : z ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    rw [hzim] at hi
    simp at hi
    have : |t| = 0 := by rw [show t = 0 by linarith]; simp
    linarith
  have hz_dom : z ∈ zetaAbelContinuationDomain := by
    refine mem_zetaAbelContinuationDomain_of_re hz_ne_one ?_
    rw [hzre]
    have hhalf : zetaAbelContinuationReLower < (1 / 2 : ℝ) := by
      simpa using zetaAbelContinuationReLower_lt_half
    exact hhalf.trans_le hσlo
  have hζ := norm_riemannZeta_le z hz_dom
  have hone_div : ‖1 / (z - 1)‖ ≤ (1 : ℝ) := by
    rw [norm_div]
    have hden : (1 : ℝ) ≤ ‖z - 1‖ := by
      have : |(z - 1).im| ≤ ‖z - 1‖ := Complex.abs_im_le_norm (z - 1)
      have him : (z - 1).im = t := by simp [hzim]
      rw [him] at this
      exact ht.trans this
    calc ‖(1 : ℂ)‖ / ‖z - 1‖ = 1 / ‖z - 1‖ := by simp
      _ ≤ 1 / (1 : ℝ) := one_div_le_one_div_of_le zero_lt_one hden
      _ = 1 := by norm_num
  have hnormz : ‖z‖ ≤ B + |t| := by
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ = |σ| + |t| := by rw [hzre, hzim]
      _ = σ + |t| := by
          rw [abs_of_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hσlo)]
      _ ≤ B + |t| := by linarith
  have hdiv : ‖z‖ / z.re ≤ 2 * (B + |t|) := by
    rw [hzre]
    have hinv : 1 / σ ≤ (2 : ℝ) := by
      calc 1 / σ ≤ 1 / (1 / 2 : ℝ) :=
            one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hσlo
        _ = 2 := by norm_num
    calc ‖z‖ / σ = ‖z‖ * (1 / σ) := by ring
      _ ≤ (B + |t|) * 2 := by
          exact mul_le_mul hnormz hinv (by positivity) (by linarith [hB, abs_nonneg t])
      _ = 2 * (B + |t|) := by ring
  calc ‖riemannZeta z‖ ≤ 1 + ‖1 / (z - 1)‖ + ‖z‖ / z.re := hζ
    _ ≤ 1 + 1 + 2 * (B + |t|) := by gcongr
    _ ≤ (2 * B + 4) * (|t| + 2) := by nlinarith [abs_nonneg t, hB]

/-! ## The χ-factor contract (the one missing analytic input)

For a point `s = σ + it` on the strip with `σ ≤ 1/2`, write `w = 1 - s`.  The
χ-factor magnitude `‖Γ(w)·cos(πw/2)‖` is polynomial in `|t|` of degree `1/2 - σ`.
This is the only piece not already in-tree: it needs the cancellation between the
`e^{-π|t|/2}` decay of `‖Γ(σ'+it)‖` on a vertical line and the `e^{π|t|/2}` growth
of `‖cos(πw/2)‖`.  The Stirling bounds in `StripBounds.lean` are one-sided and lose
this cancellation, so we record the cancelled estimate as a named contract. -/

/-- **Vertical Gamma decay input.**  This is the precise Stirling-on-vertical-lines
estimate needed to discharge the χ-factor contract on the bounded strip
`1/2 ≤ u ≤ A + 1`. -/
def KadiriVerticalGammaDecay (A : ℝ) : Prop :=
  ∃ CΓ : ℝ, 0 ≤ CΓ ∧
    ∀ u t : ℝ, u ∈ Set.Icc (1 / 2 : ℝ) (A + 1) → (1 : ℝ) ≤ |t| →
      ‖Complex.Gamma ((u : ℂ) - (t : ℂ) * I)‖ ≤
        CΓ * (|t| + 2) ^ (u - 1 / 2) * Real.exp (-(Real.pi * |t| / 2))

/-- **χ-factor polynomial contract.**  On the strip `σ ∈ [-A, 1/2]`, for `|t| ≥ 1`,
the functional-equation χ-factor `Γ(1-s)·cos(π(1-s)/2)` evaluated at `s = σ + it`
is polynomial in `|t|`:
`‖Γ(1-s)·cos(π(1-s)/2)‖ ≤ Cχ·(|t| + 2)^(A + 1/2)`.
The degree is taken uniformly as `A + 1/2`, the sharp worst case of
`1/2 - σ` on the strip. -/
def KadiriChiFactorPolyBound (A : ℝ) : Prop :=
  ∃ Cχ : ℝ, 0 ≤ Cχ ∧
    ∀ σ t : ℝ, σ ∈ Set.Icc (-A) (1 / 2 : ℝ) → (1 : ℝ) ≤ |t| →
      ‖Complex.Gamma (1 - ((σ : ℂ) + (t : ℂ) * I)) *
          Complex.cos ((Real.pi : ℂ) * (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2)‖
        ≤ Cχ * (|t| + 2) ^ (A + 1 / 2)

private lemma kadiri_cos_reflection_bound (σ t : ℝ) :
    ‖Complex.cos ((Real.pi : ℂ) * (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2)‖ ≤
      Real.exp (Real.pi * |t| / 2) := by
  have hcos := Complex.norm_cos_le_exp_abs_im
    ((Real.pi : ℂ) * (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2)
  refine hcos.trans ?_
  refine Real.exp_le_exp.mpr ?_
  have him :
      (((Real.pi : ℂ) * (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2).im)
        = -Real.pi * t / 2 := by
    simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
  rw [him]
  have habs : |(-Real.pi * t) / 2| = Real.pi * |t| / 2 := by
    rw [abs_div, abs_mul, abs_neg, abs_of_pos Real.pi_pos,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact le_of_eq habs

/-- The named χ-factor contract follows from the precise vertical Gamma decay estimate. -/
theorem kadiriChiFactorPolyBound_of_verticalGammaDecay {A : ℝ} (_hA0 : 0 ≤ A)
    (hΓ : KadiriVerticalGammaDecay A) : KadiriChiFactorPolyBound A := by
  obtain ⟨CΓ, hCΓ, hΓbd⟩ := hΓ
  refine ⟨CΓ, hCΓ, fun σ t hσ ht => ?_⟩
  set u : ℝ := 1 - σ with hu_def
  have hu : u ∈ Set.Icc (1 / 2 : ℝ) (A + 1) := by
    obtain ⟨hσlo, hσhi⟩ := hσ
    constructor <;> linarith
  have hbase0 : (0 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hbase1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hΓline :
      ‖Complex.Gamma (1 - ((σ : ℂ) + (t : ℂ) * I))‖ ≤
        CΓ * (|t| + 2) ^ (u - 1 / 2) * Real.exp (-(Real.pi * |t| / 2)) := by
    have h := hΓbd u t hu ht
    simpa [hu_def, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hcos := kadiri_cos_reflection_bound σ t
  have hΓrhs_nonneg :
      0 ≤ CΓ * (|t| + 2) ^ (u - 1 / 2) * Real.exp (-(Real.pi * |t| / 2)) := by
    positivity
  have hprod :
      ‖Complex.Gamma (1 - ((σ : ℂ) + (t : ℂ) * I)) *
          Complex.cos ((Real.pi : ℂ) * (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2)‖
        ≤ CΓ * (|t| + 2) ^ (u - 1 / 2) := by
    calc
      ‖Complex.Gamma (1 - ((σ : ℂ) + (t : ℂ) * I)) *
          Complex.cos ((Real.pi : ℂ) * (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2)‖
          = ‖Complex.Gamma (1 - ((σ : ℂ) + (t : ℂ) * I))‖ *
              ‖Complex.cos ((Real.pi : ℂ) * (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2)‖ := by
            rw [norm_mul]
      _ ≤ (CΓ * (|t| + 2) ^ (u - 1 / 2) * Real.exp (-(Real.pi * |t| / 2))) *
            Real.exp (Real.pi * |t| / 2) := by
          exact mul_le_mul hΓline hcos (norm_nonneg _) hΓrhs_nonneg
      _ = CΓ * (|t| + 2) ^ (u - 1 / 2) := by
          have hexp :
              Real.exp (-(Real.pi * |t| / 2)) * Real.exp (Real.pi * |t| / 2) = 1 := by
            rw [← Real.exp_add]
            ring_nf
            simp
          calc
            CΓ * (|t| + 2) ^ (u - 1 / 2) * Real.exp (-(Real.pi * |t| / 2)) *
                Real.exp (Real.pi * |t| / 2)
                = CΓ * (|t| + 2) ^ (u - 1 / 2) *
                    (Real.exp (-(Real.pi * |t| / 2)) * Real.exp (Real.pi * |t| / 2)) := by
                  ring
            _ = CΓ * (|t| + 2) ^ (u - 1 / 2) := by
                  rw [hexp]
                  ring
  have hexp :
      (|t| + 2) ^ (u - 1 / 2) ≤ (|t| + 2) ^ (A + 1 / 2) := by
    exact Real.rpow_le_rpow_of_exponent_le hbase1 (by linarith [hu.2])
  exact hprod.trans (mul_le_mul_of_nonneg_left hexp hCΓ)

/-! ## The wide-strip bound (proved, conditional on the χ-factor contract) -/

/-- The reflected real part lands in the sharp right strip.  For `σ ∈ [-A, 1/2]`
with `A < 2`, the point `w = 1 - (σ + it)` has `re w ∈ [1/2, 3)` and `|im w| = |t|`. -/
private lemma reflect_mem_right_strip {A σ t : ℝ} (hA : A < 2)
    (hσ : σ ∈ Set.Icc (-A) (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ (1 - ((σ : ℂ) + (t : ℂ) * I)).re ∧
      (1 - ((σ : ℂ) + (t : ℂ) * I)).re < 3 ∧
      |(1 - ((σ : ℂ) + (t : ℂ) * I)).im| = |t| := by
  obtain ⟨hσ_lo, hσ_hi⟩ := hσ
  have hre : (1 - ((σ : ℂ) + (t : ℂ) * I)).re = 1 - σ := by
    simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
  have him : (1 - ((σ : ℂ) + (t : ℂ) * I)).im = -t := by
    simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
  refine ⟨?_, ?_, ?_⟩
  · rw [hre]; linarith
  · rw [hre]; linarith
  · rw [him, abs_neg]

/-- **Wide-strip polynomial-in-`t` bound for `riemannZeta` (conditional).**
Given the χ-factor contract `KadiriChiFactorPolyBound A` with `0 ≤ A < 2`, there is
a constant `C` and degree `d = A + 3/2` such that on the vertical strip
`σ ∈ [-A, 1/2]`, for every `|t| ≥ 1`,
`‖ζ(σ + it)‖ ≤ C·(|t| + 2)^d`.
The right half `re ∈ [1/2, 3)` uses the sharp linear bound directly; the left half
is reflected through the functional equation, where the χ-factor is controlled by
the contract and `‖ζ(1-s)‖ < 8 + 2|t|` by the sharp bound. -/
theorem riemannZeta_wideStrip_poly_bound {A : ℝ} (_hA0 : 0 ≤ A) (hA2 : A < 2)
    (hχ : KadiriChiFactorPolyBound A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (-A) (1 / 2 : ℝ) → (1 : ℝ) ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ (A + 3 / 2) := by
  obtain ⟨Cχ, hCχ, hχbd⟩ := hχ
  -- the working constant: 2 · Cχ · 12 absorbs the `8 + 2|t| ≤ 12·(|t|+2)` slack.
  refine ⟨2 * Cχ * 12, by positivity, fun σ t hσ ht => ?_⟩
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  set w : ℂ := 1 - s with hw
  obtain ⟨hw_lo, hw_hi, hw_im⟩ := reflect_mem_right_strip (A := A) (σ := σ) (t := t) hA2 hσ
  -- |im w| = |t| ≥ 1.
  have hw_im_ge : (1 : ℝ) ≤ |w.im| := by rw [hw, hw_im]; exact ht
  -- functional equation: `ζ(s) = 2·(2π)^(-w)·Γ(w)·cos(πw/2)·ζ(w)`.
  have hwn : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n hn
    have h' := congrArg Complex.re hn
    simp only [Complex.neg_re, Complex.natCast_re] at h'
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [hw] at h'
    have hwre : w.re = (1 - s).re := by rw [hw]
    rw [← hwre] at hw_lo
    linarith [hw_lo, h']
  have hw1 : w ≠ 1 := by
    intro h
    have h' := congrArg Complex.im h
    rw [hw] at h'
    have : (1 - s).im = (1 : ℂ).im := h'
    simp only [Complex.one_im] at this
    have hsim : s.im = t := by simp [hs, Complex.add_im, Complex.mul_im]
    have : -t = 0 := by
      have hh : (1 - s).im = -s.im := by simp [Complex.sub_im, Complex.one_im]
      rw [hh, hsim] at this; linarith [this]
    have htabs : |t| = 0 := by rw [show t = 0 by linarith [this]]; simp
    rw [htabs] at ht; linarith
  have hfe := riemannZeta_one_sub hwn hw1
  -- `1 - w = s`.
  have h1w : (1 : ℂ) - w = s := by rw [hw]; ring
  rw [h1w] at hfe
  -- bound the three "easy" factors.
  have hw_re_nonneg : (0 : ℝ) ≤ w.re := by
    have hwre : w.re = (1 - s).re := by rw [hw]
    rw [hwre]; linarith [hw_lo]
  have hpow : ‖((2 : ℂ) * (Real.pi : ℂ)) ^ (-w)‖ ≤ 1 :=
    Complex.Gammaℝ.Stirling.norm_cpow_two_mul_pi_neg_le_one hw_re_nonneg
  have hζw : ‖riemannZeta w‖ ≤ 8 + 2 * (|t| + 2) := by
    have hwre : w.re = (1 - s).re := by rw [hw]
    have hb := norm_riemannZeta_le_poly_on_right_strip w (by rw [hwre]; exact hw_lo)
      (by rw [hwre]; exact hw_hi) hw_im_ge
    rw [hw_im] at hb; exact hb
  -- χ-factor contract.
  have hχval :
      ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ ≤
        Cχ * (|t| + 2) ^ (A + 1 / 2) := by
    have := hχbd σ t hσ ht
    rwa [show (1 - ((σ : ℂ) + (t : ℂ) * I)) = w by rw [hw, hs]] at this
  -- assemble: ‖ζ(s)‖ = 2 · ‖(2π)^(-w)‖ · ‖Γ(w)cos(πw/2)‖ · ‖ζ(w)‖.
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
  -- nonnegativity scaffolding.
  have hAnn : (0 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hbasege1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hpowA_nonneg : (0 : ℝ) ≤ (|t| + 2) ^ (A + 1 / 2) :=
    Real.rpow_nonneg hAnn (A + 1 / 2)
  have hpow1_nonneg : (0 : ℝ) ≤ (|t| + 2) ^ (A + 3 / 2) :=
    Real.rpow_nonneg hAnn (A + 3 / 2)
  have hχ_nonneg : (0 : ℝ) ≤ ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ := norm_nonneg _
  have hζw_nonneg : (0 : ℝ) ≤ ‖riemannZeta w‖ := norm_nonneg _
  -- `8 + 2(|t|+2) ≤ 12·(|t|+2)` since `|t|+2 ≥ 1`.
  have hζw_lin : ‖riemannZeta w‖ ≤ 12 * (|t| + 2) := by
    refine hζw.trans ?_
    nlinarith [hbasege1]
  -- `(|t|+2)^(A+1/2) · (|t|+2) = (|t|+2)^(A+3/2)`.
  have hrpow_add :
      (|t| + 2) ^ (A + 1 / 2) * (|t| + 2) = (|t| + 2) ^ (A + 3 / 2) := by
    rw [← Real.rpow_add_one (by linarith [hbasege1] : (|t| + 2) ≠ 0) (A + 1 / 2)]
    ring_nf
  calc ‖riemannZeta s‖
      = 2 * ‖((2 : ℂ) * (Real.pi : ℂ)) ^ (-w)‖
          * ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ * ‖riemannZeta w‖ := hsplit
    _ ≤ 2 * 1 * (Cχ * (|t| + 2) ^ (A + 1 / 2)) * (12 * (|t| + 2)) := by
        have h12 : (0 : ℝ) ≤ 12 * (|t| + 2) := by positivity
        have hCχt : (0 : ℝ) ≤ Cχ * (|t| + 2) ^ (A + 1 / 2) :=
          mul_nonneg hCχ hpowA_nonneg
        have hpow_nonneg : (0 : ℝ) ≤ ‖((2 : ℂ) * (Real.pi : ℂ)) ^ (-w)‖ := norm_nonneg _
        have step12 : 2 * ‖((2 : ℂ) * (Real.pi : ℂ)) ^ (-w)‖
            * ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖
            ≤ 2 * 1 * (Cχ * (|t| + 2) ^ (A + 1 / 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num)) hχval hχ_nonneg (by positivity)
        exact mul_le_mul step12 hζw_lin hζw_nonneg (by positivity)
    _ = 2 * Cχ * 12 * ((|t| + 2) ^ (A + 1 / 2) * (|t| + 2)) := by ring
    _ = 2 * Cχ * 12 * (|t| + 2) ^ (A + 3 / 2) := by rw [hrpow_add]

/-- Wide-strip polynomial bound on the left half-strip, with no `A < 2` cutoff.
The reflected zeta factor is controlled by the bounded right-half Abel estimate;
the only non-in-tree analytic input remains `KadiriChiFactorPolyBound A`. -/
theorem riemannZeta_leftStrip_poly_bound {A : ℝ} (hA0 : 0 ≤ A)
    (hχ : KadiriChiFactorPolyBound A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (-A) (1 / 2 : ℝ) → (1 : ℝ) ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ (A + 3 / 2) := by
  obtain ⟨Cχ, hCχ, hχbd⟩ := hχ
  obtain ⟨Cr, hCr, hright⟩ := norm_riemannZeta_le_linear_on_right_half
    (B := A + 1) (by linarith)
  refine ⟨2 * Cχ * Cr, by positivity, fun σ t hσ ht => ?_⟩
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  set w : ℂ := 1 - s with hw
  obtain ⟨hσlo, hσhi⟩ := hσ
  have hw_re : w.re = 1 - σ := by
    rw [hw, hs]
    simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
  have hw_im : w.im = -t := by
    rw [hw, hs]
    simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
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
      ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ ≤
        Cχ * (|t| + 2) ^ (A + 1 / 2) := by
    have := hχbd σ t ⟨hσlo, hσhi⟩ ht
    rwa [show (1 - ((σ : ℂ) + (t : ℂ) * I)) = w by rw [hw, hs]] at this
  have hsplit : ‖riemannZeta s‖
      = 2 * ‖((2 : ℂ) * (Real.pi : ℂ)) ^ (-w)‖
          * ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ *
            ‖riemannZeta w‖ := by
    rw [hfe]
    rw [show (2 : ℂ) * ((2 : ℂ) * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w
          * Complex.cos ((Real.pi : ℂ) * w / 2) * riemannZeta w
        = (2 : ℂ) * (((2 : ℂ) * (Real.pi : ℂ)) ^ (-w)
            * (Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)) *
              riemannZeta w) by ring]
    rw [norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat]
    ring
  have hbase : (0 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hbase1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hrpow_add :
      (|t| + 2) ^ (A + 1 / 2) * (|t| + 2) = (|t| + 2) ^ (A + 3 / 2) := by
    rw [← Real.rpow_add_one (by linarith [hbase1] : (|t| + 2) ≠ 0) (A + 1 / 2)]
    ring_nf
  calc ‖riemannZeta s‖
      = 2 * ‖((2 : ℂ) * (Real.pi : ℂ)) ^ (-w)‖
          * ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ *
            ‖riemannZeta w‖ := hsplit
    _ ≤ 2 * 1 * (Cχ * (|t| + 2) ^ (A + 1 / 2)) * (Cr * (|t| + 2)) := by
        have hχ_nonneg :
            (0 : ℝ) ≤ ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖ :=
          norm_nonneg _
        have hζ_nonneg : (0 : ℝ) ≤ ‖riemannZeta w‖ := norm_nonneg _
        have step :
            2 * ‖((2 : ℂ) * (Real.pi : ℂ)) ^ (-w)‖ *
                ‖Complex.Gamma w * Complex.cos ((Real.pi : ℂ) * w / 2)‖
              ≤ 2 * 1 * (Cχ * (|t| + 2) ^ (A + 1 / 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num)) hχval hχ_nonneg
            (by positivity)
        exact mul_le_mul step hζw hζ_nonneg (by positivity)
    _ = 2 * Cχ * Cr * ((|t| + 2) ^ (A + 1 / 2) * (|t| + 2)) := by ring
    _ = 2 * Cχ * Cr * (|t| + 2) ^ (A + 3 / 2) := by rw [hrpow_add]

/-- Fixed-strip polynomial bound from a left edge `-A` to any bounded right edge
`B`, conditional only on `KadiriChiFactorPolyBound A`. -/
theorem riemannZeta_fixedStrip_poly_bound {A B : ℝ} (hA0 : 0 ≤ A)
    (hB : (1 / 2 : ℝ) ≤ B) (hχ : KadiriChiFactorPolyBound A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ t : ℝ, σ ∈ Set.Icc (-A) B → (1 : ℝ) ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (|t| + 2) ^ (A + 3 / 2) := by
  obtain ⟨Cl, hCl, hleft⟩ := riemannZeta_leftStrip_poly_bound hA0 hχ
  obtain ⟨Cr, hCr, hright⟩ := norm_riemannZeta_le_linear_on_right_half hB
  refine ⟨max Cl Cr, by positivity, fun σ t hσ ht => ?_⟩
  have hbase1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hpow_nonneg : (0 : ℝ) ≤ (|t| + 2) ^ (A + 3 / 2) :=
    Real.rpow_nonneg (by linarith [abs_nonneg t]) _
  by_cases hleftcase : σ ≤ (1 / 2 : ℝ)
  · have hbound := hleft σ t ⟨hσ.1, hleftcase⟩ ht
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow_nonneg)
  · have hσlo : (1 / 2 : ℝ) ≤ σ := by linarith
    have hb := hright σ t hσlo hσ.2 ht
    have hpow : |t| + 2 ≤ (|t| + 2) ^ (A + 3 / 2) := by
      nth_rw 1 [← Real.rpow_one (|t| + 2)]
      exact Real.rpow_le_rpow_of_exponent_le hbase1 (by linarith)
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cr * (|t| + 2) := hb
      _ ≤ Cr * (|t| + 2) ^ (A + 3 / 2) := mul_le_mul_of_nonneg_left hpow hCr
      _ ≤ max Cl Cr * (|t| + 2) ^ (A + 3 / 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpow_nonneg

end Kadiri
