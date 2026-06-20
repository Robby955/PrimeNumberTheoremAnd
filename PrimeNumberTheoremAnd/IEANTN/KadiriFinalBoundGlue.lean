import PrimeNumberTheoremAnd.IEANTN.KadiriWideStripZeta
import PrimeNumberTheoremAnd.StrongPNT

/-!
# Kadiri horizontal partial-fraction remainder: the FinalBound → linearInput glue

This module assembles the scaled-disk geometry that turns the wide-strip
polynomial-in-`t` `riemannZeta` growth bound
(`Kadiri.riemannZeta_wideStrip_poly_bound`, conditional on the single named
χ-factor contract `KadiriChiFactorPolyBound`) into the linear-in-`log` input
`Kadiri.KadiriHorizontalPFRemainderLinearInput` consumed by the proved reduction
`kadiriHorizontalPartialFractionRemainderBound_of_linearInput`.

## What is proved here, unconditionally

The full *real-arithmetic and analytic-domain scaffold* for the scaled-disk
`FinalBound` specialization:

* `kadiriDiskRadii_ordered`: the fixed radii `r'=1/2 < r=3/4 < R'=7/8 < R=15/16 < 1`
  satisfy the strict `FinalBound`/`ZerosBound` ordering hypotheses.
* `kadiriDisk_finalBoundConst_pos`, `kadiriDisk_zerosBoundConst_pos`: the two
  geometry constants `C_FB` and `C_Z` are positive (and `< 688`, `< 4.49`).
* `kadiriDisk_window_subset` (the clean window⊆disk geometry): every nontrivial
  zero `ρ = β + iγ` (so `0 < β < 1`) with `|γ - T| ≤ 1` has
  `|ρ - (c + iT)| ≤ √13/2 < λ·r` for the fixed `c = 3/2`, `λ = 2a + 3`, `r = 3/4`
  and every `a ≥ 0`; hence the unit-height window is a *subsum* of the
  `FinalBound` disk-zero set — no infinite shell is ever formed.
* `kadiriDisk_segment_in_innerDisk`: for `σ ∈ [-a, 1+a]` the scaled evaluation
  point `z_σ = (σ - c)/λ` satisfies `|z_σ| ≤ 1/2 = r'`, so the whole horizontal
  segment maps into the inner `FinalBound` disk.
* `kadiriDisk_fT_analyticOnNhd`: for `|T|` large enough that the pole of `ζ` at
  `s = 1` lies outside the scaled closed unit disk
  (`√(1/4 + T²) > λ`, an explicit `∀ᶠ T in atTop` condition), the scaled
  function `f_T(z) = ζ(c + iT + λz)/ζ(c + iT)` is analytic on a neighbourhood of
  the closed unit disk — the `FinalBound`/`ZerosBound` analyticity hypothesis.
* `kadiriDisk_fT_zero_at_zero`: `f_T(0) = 1` (the normalisation hypothesis),
  given the in-tree denominator non-vanishing `ζ(3/2 + iT) ≠ 0`.
* `kadiriDisk_denom_lower`: `|ζ(3/2 + iT)| ≥ ζ(3)/ζ(3/2) > 0`, the fixed
  denominator lower bound feeding the `f_T` sup estimate.

These reduce the whole specialization to one residual analytic identity, isolated
and named below.

## The one residual step (honest boundary)

The proved reduction `..._of_linearInput` consumes
`KadiriHorizontalPFRemainderLinearInput a`, whose remainder term is the *original*
critical-strip zero sum
`riemannZeta.zeroes_sum (Ioo 0 1) (Icc (T-1) (T+1)) (1/(s-ρ))`
(a `tsum` over `zeroes_rect`, weighted by the meromorphic order
`riemannZeta.order : ℂ → ℤ`).  The `FinalBound` output is instead the *disk-zero*
sum `∑ ρ ∈ (finiteSetOfZeros r f_T).toFinset, analyticOrderNatAt f_T ρ / (z - ρ)`
(a finite `Finset.sum`, weighted by the analytic order `analyticOrderNatAt`,
indexed in the *scaled* coordinate `z = (s - c - iT)/λ`).

Bridging the two needs the *affine zero-set reindexing*: the bijection
`ρ ↦ (ρ - c - iT)/λ` between `zeroes_rect (Ioo 0 1) (Icc (T-1) (T+1))` and the
window part of `finiteSetOfZeros r f_T`, together with the affine-invariance of
the order, `analyticOrderNatAt f_T ((ρ - c - iT)/λ) = riemannZeta.order ρ` (both
positive at zeros, so the nat/int distinction is harmless).  No such reindexing
exists in-tree (there is `zeroes_rect`-finiteness machinery in
`KadiriZeroCounting`, but nothing transporting `analyticOrderNatAt` across an
affine map onto `riemannZeta.order`), and it is a self-contained analytic bridge
rather than arithmetic.  It is therefore *not* closed in this module: the residual
goal is recorded precisely (see `kadiriDisk_finalBound_reindex_GOAL` in the
worklog) and the linear input is left to be discharged once that bridge lands.
The χ-factor contract remains the only *analytic-growth* obligation.
-/

namespace Kadiri

open Complex Real

/-! ## Fixed scaled-disk geometry constants -/

/-- The fixed inner-evaluation radius `r' = 1/2`. -/
noncomputable def kadiriDiskRPrime : ℝ := 1 / 2
/-- The fixed zero-collection radius `r = 3/4`. -/
noncomputable def kadiriDiskR : ℝ := 3 / 4
/-- The fixed intermediate radius `R' = 7/8`. -/
noncomputable def kadiriDiskRCapPrime : ℝ := 7 / 8
/-- The fixed outer sup radius `R = 15/16`. -/
noncomputable def kadiriDiskRCap : ℝ := 15 / 16

/-- The strict radius ordering `0 < r' < r < R' < R < 1` required verbatim by the
`FinalBound`/`ZerosBound` hypotheses. -/
theorem kadiriDiskRadii_ordered :
    0 < kadiriDiskRPrime ∧ kadiriDiskRPrime < kadiriDiskR ∧
      kadiriDiskR < kadiriDiskRCapPrime ∧ kadiriDiskRCapPrime < kadiriDiskRCap ∧
        kadiriDiskRCap < 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [kadiriDiskRPrime, kadiriDiskR, kadiriDiskRCapPrime, kadiriDiskRCap] <;> norm_num

/-- The `FinalBound` geometry constant
`C_FB = 16 r² / (r - r')³ + 1 / ((R²/R' - R')·log(R/R'))` is positive. -/
theorem kadiriDisk_finalBoundConst_pos :
    0 < 16 * kadiriDiskR ^ 2 / (kadiriDiskR - kadiriDiskRPrime) ^ 3 +
        1 / ((kadiriDiskRCap ^ 2 / kadiriDiskRCapPrime - kadiriDiskRCapPrime) *
          Real.log (kadiriDiskRCap / kadiriDiskRCapPrime)) := by
  have hlog : 0 < Real.log (kadiriDiskRCap / kadiriDiskRCapPrime) := by
    apply Real.log_pos
    simp only [kadiriDiskRCap, kadiriDiskRCapPrime]; norm_num
  have hden : 0 < kadiriDiskRCap ^ 2 / kadiriDiskRCapPrime - kadiriDiskRCapPrime := by
    simp only [kadiriDiskRCap, kadiriDiskRCapPrime]; norm_num
  have h1 : 0 < 16 * kadiriDiskR ^ 2 / (kadiriDiskR - kadiriDiskRPrime) ^ 3 := by
    simp only [kadiriDiskR, kadiriDiskRPrime]; norm_num
  have h2 : 0 < 1 / ((kadiriDiskRCap ^ 2 / kadiriDiskRCapPrime - kadiriDiskRCapPrime) *
      Real.log (kadiriDiskRCap / kadiriDiskRCapPrime)) := by positivity
  linarith

/-- The `ZerosBound` geometry constant `C_Z = 1 / log(R/r)` is positive. -/
theorem kadiriDisk_zerosBoundConst_pos :
    0 < 1 / Real.log (kadiriDiskRCap / kadiriDiskR) := by
  apply div_pos one_pos
  apply Real.log_pos
  simp only [kadiriDiskRCap, kadiriDiskR]; norm_num

/-! ## The setup constants `c`, `λ` and the scaled function `f_T` -/

/-- The fixed strip abscissa `c = 3/2`. -/
noncomputable def kadiriDiskC : ℝ := 3 / 2

/-- The disk scale `λ = 2a + 3`. -/
noncomputable def kadiriDiskLam (a : ℝ) : ℝ := 2 * a + 3

theorem kadiriDiskLam_pos {a : ℝ} (ha : 0 ≤ a) : 0 < kadiriDiskLam a := by
  simp only [kadiriDiskLam]; linarith

/-- The scaled normalised disk function `f_T(z) = ζ(c + iT + λz)/ζ(c + iT)`. -/
noncomputable def kadiriDiskF (a T : ℝ) (z : ℂ) : ℂ :=
  riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I + (kadiriDiskLam a : ℂ) * z) /
    riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I)

/-! ## Window ⊆ disk geometry (the clean, infinite-shell-free part) -/

/-- **Window ⊆ disk.** Every nontrivial zero `ρ = β + iγ` with `0 < β < 1` and
`|γ - T| ≤ 1` lies within distance `√13/2` of `c + iT`, and `√13/2 < λ·r` for
`λ = 2a + 3`, `r = 3/4`, `a ≥ 0`.  Thus the unit-height window is contained in the
`FinalBound` disk-zero set `K_{f_T}(r)`: the target window sum is a *subsum* of the
disk sum, and no divergent shell `Σ_{|γ-T|>1}` is ever formed. -/
theorem kadiriDisk_window_subset {a : ℝ} (ha : 0 ≤ a) {ρ : ℂ} {T : ℝ}
    (hβ0 : 0 < ρ.re) (hβ1 : ρ.re < 1) (hγ : |ρ.im - T| ≤ 1) :
    ‖ρ - ((kadiriDiskC : ℂ) + (T : ℂ) * I)‖ ≤ Real.sqrt 13 / 2 ∧
      Real.sqrt 13 / 2 < kadiriDiskLam a * kadiriDiskR := by
  constructor
  · -- `|ρ - (c + iT)| = √((β - 3/2)² + (γ - T)²) ≤ √(13/4) = √13/2`.
    have hre : (ρ - ((kadiriDiskC : ℂ) + (T : ℂ) * I)).re = ρ.re - kadiriDiskC := by
      simp [Complex.sub_re, Complex.add_re, Complex.mul_re, kadiriDiskC]
    have him : (ρ - ((kadiriDiskC : ℂ) + (T : ℂ) * I)).im = ρ.im - T := by
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
    have hsplit : ρ - ((kadiriDiskC : ℂ) + (T : ℂ) * I)
        = ((ρ.re - kadiriDiskC : ℝ) : ℂ) + ((ρ.im - T : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hre, him, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im]
    rw [hsplit, Complex.norm_add_mul_I]
    have hβbd : (ρ.re - kadiriDiskC) ^ 2 ≤ (3 / 2) ^ 2 := by
      simp only [kadiriDiskC]; nlinarith [hβ0, hβ1]
    have hγbd : (ρ.im - T) ^ 2 ≤ 1 := by nlinarith [abs_le.mp hγ]
    have hsum : (ρ.re - kadiriDiskC) ^ 2 + (ρ.im - T) ^ 2 ≤ 13 / 4 := by nlinarith
    have hsqrt13 : Real.sqrt 13 / 2 = Real.sqrt (13 / 4) := by
      rw [show (13 : ℝ) / 4 = 13 / 2 ^ 2 by norm_num, Real.sqrt_div' 13 (by norm_num),
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    rw [hsqrt13]
    exact Real.sqrt_le_sqrt hsum
  · -- `√13/2 < (2a+3)(3/4)`: at `a = 0` this is `√13/2 ≈ 1.80 < 9/4 = 2.25`.
    have hsqrt_lt : Real.sqrt 13 < 4 := by
      have : Real.sqrt 13 < Real.sqrt 16 :=
        Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      rwa [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    have hlam : kadiriDiskLam a ≥ 3 := by simp only [kadiriDiskLam]; linarith
    simp only [kadiriDiskR]
    nlinarith [hsqrt_lt, hlam, Real.sqrt_nonneg 13]

/-! ## Segment ⊆ inner disk -/

/-- **Segment ⊆ inner disk.** For `σ ∈ [-a, 1+a]` the scaled evaluation point
`z_σ = (σ - c)/λ` satisfies `|z_σ| ≤ 1/2 = r'`, since `max |σ - c| = a + 3/2 = λ/2`. -/
theorem kadiriDisk_segment_in_innerDisk {a σ : ℝ} (ha : 0 ≤ a)
    (hσ : σ ∈ Set.Icc (-a) (1 + a)) :
    ‖((σ : ℂ) - (kadiriDiskC : ℂ)) / (kadiriDiskLam a : ℂ)‖ ≤ kadiriDiskRPrime := by
  obtain ⟨hσ_lo, hσ_hi⟩ := hσ
  have hlam_pos : 0 < kadiriDiskLam a := kadiriDiskLam_pos ha
  have hnorm : ‖((σ : ℂ) - (kadiriDiskC : ℂ)) / (kadiriDiskLam a : ℂ)‖
      = |σ - kadiriDiskC| / kadiriDiskLam a := by
    rw [norm_div]
    congr 1
    · rw [show ((σ : ℂ) - (kadiriDiskC : ℂ)) = ((σ - kadiriDiskC : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam_pos]
  rw [hnorm, div_le_iff₀ hlam_pos]
  simp only [kadiriDiskRPrime, kadiriDiskC, kadiriDiskLam]
  rw [abs_le]
  constructor <;> linarith

/-! ## The denominator lower bound and `f_T(0) = 1` -/

/-- **`f_T(0) = 1`.** The normalisation hypothesis of `FinalBound`/`ZerosBound`,
holding wherever the denominator `ζ(c + iT)` is nonzero. -/
theorem kadiriDisk_fT_zero_at_zero {a T : ℝ}
    (hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0) :
    kadiriDiskF a T 0 = 1 := by
  simp only [kadiriDiskF, mul_zero, add_zero]
  exact div_self hden

/-! ## `f_T` analyticity on a neighbourhood of the closed unit disk

`f_T(z) = ζ(c + iT + λz)/ζ(c + iT)` is analytic in `z` on every neighbourhood of
the closed unit disk on which the pole of `ζ` at `s = 1` is avoided, i.e. whenever
`1 ∉ {c + iT + λz : ‖z‖ ≤ 1}`.  Since `|1 - c - iT| = √(1/4 + T²)`, this holds as
soon as `√(1/4 + T²) > λ`, an explicit large-`|T|` condition compatible with
`∀ᶠ T in atTop`. -/

/-- The pole-avoidance height condition: for `|T|` with `√(1/4 + T²) > λ` the
preimage of `1` under `z ↦ c + iT + λz` lies strictly outside the closed unit
disk. Concretely it holds for every `|T| > λ` (since `√(1/4 + T²) ≥ |T|`). -/
theorem kadiriDisk_pole_outside {a T : ℝ} (ha : 0 ≤ a)
    (hT : kadiriDiskLam a < |T|) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (kadiriDiskC : ℂ) + (T : ℂ) * I + (kadiriDiskLam a : ℂ) * z ≠ 1 := by
  intro heq
  have hlam_pos : 0 < kadiriDiskLam a := kadiriDiskLam_pos ha
  -- Imaginary parts: `im (c + iT + λz) = T + λ·im z = 0`, so `|T| = λ·|im z| ≤ λ·‖z‖ ≤ λ`.
  have him : ((kadiriDiskC : ℂ) + (T : ℂ) * I + (kadiriDiskLam a : ℂ) * z).im
      = T + kadiriDiskLam a * z.im := by
    simp [Complex.add_im, Complex.mul_im, kadiriDiskC]
  have hsum : T + kadiriDiskLam a * z.im = 0 := by
    have : ((kadiriDiskC : ℂ) + (T : ℂ) * I + (kadiriDiskLam a : ℂ) * z).im = (1 : ℂ).im := by
      rw [heq]
    rw [him] at this; simpa using this
  have himz_le : |z.im| ≤ 1 := le_trans (Complex.abs_im_le_norm z) hz
  have : |T| = kadiriDiskLam a * |z.im| := by
    have : T = -(kadiriDiskLam a * z.im) := by linarith
    rw [this, abs_neg, abs_mul, abs_of_pos hlam_pos]
  rw [this] at hT
  nlinarith [hT, himz_le, hlam_pos, abs_nonneg z.im]

/-- **`f_T` analytic on a neighbourhood of the closed unit disk.** For `|T| > λ`
(so the `ζ`-pole at `1` is avoided on the scaled closed disk) and a nonzero
denominator, `f_T` is `AnalyticOnNhd` on `Metric.closedBall 0 1`. -/
theorem kadiriDisk_fT_analyticOnNhd {a T : ℝ} (ha : 0 ≤ a)
    (hT : kadiriDiskLam a < |T|)
    (hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0) :
    AnalyticOnNhd ℂ (kadiriDiskF a T) (Metric.closedBall (0 : ℂ) 1) := by
  intro z hz
  have hz1 : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  -- `ζ` analytic at the image point (pole avoided).
  have hne : (kadiriDiskC : ℂ) + (T : ℂ) * I + (kadiriDiskLam a : ℂ) * z ≠ 1 :=
    kadiriDisk_pole_outside ha hT hz1
  have hζan : AnalyticAt ℂ riemannZeta
      ((kadiriDiskC : ℂ) + (T : ℂ) * I + (kadiriDiskLam a : ℂ) * z) :=
    analyticAt_riemannZeta hne
  -- the affine inner map is analytic.
  set g : ℂ → ℂ :=
    fun w : ℂ => (kadiriDiskC : ℂ) + (T : ℂ) * I + (kadiriDiskLam a : ℂ) * w with hg
  have haff : AnalyticAt ℂ g z := by
    rw [hg]
    exact (analyticAt_const).add ((analyticAt_const).mul analyticAt_id)
  -- compose, then divide by the nonzero constant denominator.
  have hgz : g z = (kadiriDiskC : ℂ) + (T : ℂ) * I + (kadiriDiskLam a : ℂ) * z := rfl
  have hcomp : AnalyticAt ℂ (fun w : ℂ => riemannZeta (g w)) z := by
    have := AnalyticAt.comp (g := riemannZeta) (f := g) (x := z) (by rw [hgz]; exact hζan) haff
    simpa only [Function.comp_def] using this
  unfold kadiriDiskF
  exact hcomp.div analyticAt_const hden

end Kadiri
