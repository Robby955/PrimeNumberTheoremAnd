import PrimeNumberTheoremAnd.IEANTN.KadiriFinalBoundGlue
import PrimeNumberTheoremAnd.IEANTN.KadiriEq12Helpers
import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting

/-!
# Kadiri horizontal zero-set reindexing: the order-transport bridge

The scaled-disk `FinalBound` specialization (`KadiriFinalBoundGlue`) outputs a
finite zero sum weighted by the *analytic* order `analyticOrderNatAt f_T ρ`
(`ℕ`), indexed in the scaled disk coordinate.  The target Kadiri horizontal sum
`riemannZeta.zeroes_sum` is weighted by the *meromorphic* order
`riemannZeta.order ρ` (`ℤ`), indexed in the original coordinate.  Bridging the
two needs the affine zero-set reindexing together with the *order transport*.

This module proves the order-transport facts, axiom-clean, from the mathlib
meromorphic-order composition and constant-multiple API:

* `kadiriDiskAffine`, the affine map `e : z ↦ c + iT + λz`, is an analytic
  bijection (`λ ≠ 0`) whose inverse is `ρ ↦ (ρ - c - iT)/λ`.
* `meromorphicOrderAt (kadiriDiskF a T) ((ρ - c - iT)/λ) = meromorphicOrderAt riemannZeta ρ`
  (`kadiriDiskF_meromorphicOrderAt_eq`): the affine reparametrization is a local
  biholomorphism (`deriv e = λ ≠ 0`, mathlib `meromorphicOrderAt_comp_of_deriv_ne_zero`),
  and dividing by the nonzero constant `ζ(c + iT)` preserves order
  (`meromorphicOrderAt_smul_of_ne_zero`).
* `kadiriDiskF_order_transport`: at a nontrivial zero `ρ` (so `ρ ≠ 1`, hence `ζ`
  is analytic at `ρ`), the integer `riemannZeta.order ρ` equals the natural
  `analyticOrderNatAt (kadiriDiskF a T) ((ρ - c - iT)/λ)` (both nonnegative at the
  zero, so the `ℕ`/`ℤ` distinction is harmless), via the analytic-to-meromorphic
  order identity `AnalyticAt.meromorphicOrderAt_eq`.

No new analytic contract is introduced: the only inputs are the nonvanishing of
the fixed denominator `ζ(c + iT)` and the pole-avoidance giving analyticity of
`ζ` at `ρ` (automatic for nontrivial zeros, since `ρ ≠ 1`).
-/

namespace Kadiri

open Complex
open scoped BigOperators

/-- The disk zero-collection radius is strictly inside the unit disk. -/
theorem kadiriDiskR_lt_one : kadiriDiskR < 1 := by
  norm_num [kadiriDiskR]

/-! ## The affine reparametrization `e : z ↦ c + iT + λz` -/

/-- The affine map `e : z ↦ c + iT + λz` underlying the scaled disk. -/
noncomputable def kadiriDiskAffine (a T : ℝ) (z : ℂ) : ℂ :=
  (kadiriDiskC : ℂ) + (T : ℂ) * I + (kadiriDiskLam a : ℂ) * z

/-- The inverse coordinate `ρ ↦ (ρ - c - iT)/λ`. -/
noncomputable def kadiriDiskCoord (a T : ℝ) (ρ : ℂ) : ℂ :=
  (ρ - (kadiriDiskC : ℂ) - (T : ℂ) * I) / (kadiriDiskLam a : ℂ)

theorem kadiriDiskLam_ne_zero {a : ℝ} (ha : 0 ≤ a) : (kadiriDiskLam a : ℂ) ≠ 0 := by
  have : (0 : ℝ) < kadiriDiskLam a := kadiriDiskLam_pos ha
  exact_mod_cast ne_of_gt this

/-- `e (coord ρ) = ρ`: the inverse coordinate sends `ρ` back to `ρ`. -/
theorem kadiriDiskAffine_coord {a : ℝ} (ha : 0 ≤ a) (T : ℝ) (ρ : ℂ) :
    kadiriDiskAffine a T (kadiriDiskCoord a T ρ) = ρ := by
  unfold kadiriDiskAffine kadiriDiskCoord
  rw [mul_div_cancel₀ _ (kadiriDiskLam_ne_zero ha)]
  ring

/-- `coord (e z) = z`: the affine coordinate is a two-sided inverse. -/
theorem kadiriDiskCoord_affine {a : ℝ} (ha : 0 ≤ a) (T : ℝ) (z : ℂ) :
    kadiriDiskCoord a T (kadiriDiskAffine a T z) = z := by
  unfold kadiriDiskCoord kadiriDiskAffine
  field_simp [kadiriDiskLam_ne_zero ha]
  ring

/-- The inverse coordinate map is injective. -/
theorem kadiriDiskCoord_injective {a : ℝ} (ha : 0 ≤ a) (T : ℝ) :
    Function.Injective (kadiriDiskCoord a T) := by
  intro ρ ρ' hρρ'
  have h := congrArg (kadiriDiskAffine a T) hρρ'
  simpa [kadiriDiskAffine_coord ha T ρ, kadiriDiskAffine_coord ha T ρ'] using h

/-- The affine map is analytic everywhere. -/
theorem kadiriDiskAffine_analyticAt (a T : ℝ) (z : ℂ) :
    AnalyticAt ℂ (kadiriDiskAffine a T) z := by
  unfold kadiriDiskAffine
  exact (analyticAt_const).add ((analyticAt_const).mul analyticAt_id)

/-- The derivative of the affine map is the nonzero scale `λ`. -/
theorem kadiriDiskAffine_deriv (a T : ℝ) (z : ℂ) :
    deriv (kadiriDiskAffine a T) z = (kadiriDiskLam a : ℂ) := by
  unfold kadiriDiskAffine
  have h1 : deriv (fun w : ℂ => (kadiriDiskC : ℂ) + (T : ℂ) * I + (kadiriDiskLam a : ℂ) * w) z
      = deriv (fun w : ℂ => (kadiriDiskLam a : ℂ) * w) z := by
    rw [show (fun w : ℂ => (kadiriDiskC : ℂ) + (T : ℂ) * I + (kadiriDiskLam a : ℂ) * w)
          = (fun w : ℂ => ((kadiriDiskC : ℂ) + (T : ℂ) * I) + (kadiriDiskLam a : ℂ) * w) by
        funext w; ring]
    exact deriv_const_add _
  rw [h1, deriv_const_mul_field, deriv_id'', mul_one]

/-! ## `kadiriDiskF` as constant-multiple of `ζ ∘ e` -/

/-- `kadiriDiskF a T = (fun w => (ζ(c + iT))⁻¹) • (riemannZeta ∘ e)`. -/
theorem kadiriDiskF_eq_const_smul_comp (a T : ℝ) :
    kadiriDiskF a T
      = (fun _ : ℂ => (riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I))⁻¹)
          • (riemannZeta ∘ kadiriDiskAffine a T) := by
  funext z
  change riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I + (kadiriDiskLam a : ℂ) * z) /
        riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I)
      = (riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I))⁻¹ •
          riemannZeta (kadiriDiskAffine a T z)
  rw [smul_eq_mul, div_eq_inv_mul]
  rfl

/-! ## The order transport (meromorphic level) -/

/-- **Order transport (meromorphic).** With the denominator `ζ(c + iT) ≠ 0`, the
meromorphic order of the scaled disk function `f_T` at the inverse coordinate of
`ρ` equals the meromorphic order of `ζ` at `ρ`.  The affine reparametrization
`e` is a local biholomorphism (`deriv e = λ ≠ 0`), and the nonzero constant
`(ζ(c + iT))⁻¹` does not change the order. -/
theorem kadiriDiskF_meromorphicOrderAt_eq {a : ℝ} (ha : 0 ≤ a) {T : ℝ}
    (hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0) (ρ : ℂ) :
    meromorphicOrderAt (kadiriDiskF a T) (kadiriDiskCoord a T ρ)
      = meromorphicOrderAt riemannZeta ρ := by
  set z₀ : ℂ := kadiriDiskCoord a T ρ with hz₀
  have hgz₀ : kadiriDiskAffine a T z₀ = ρ := kadiriDiskAffine_coord ha T ρ
  -- Rewrite `f_T` as `const • (ζ ∘ e)`.
  rw [kadiriDiskF_eq_const_smul_comp a T]
  -- Step 1: dividing by the nonzero constant preserves order.
  rw [meromorphicOrderAt_smul_of_ne_zero (analyticAt_const) (by simpa using inv_ne_zero hden)]
  -- Step 2: the affine reparametrization preserves order (`deriv e = λ ≠ 0`).
  rw [meromorphicOrderAt_comp_of_deriv_ne_zero (kadiriDiskAffine_analyticAt a T z₀)
    (by rw [kadiriDiskAffine_deriv a T z₀]; exact kadiriDiskLam_ne_zero ha)]
  rw [hgz₀]

/-! ## The order transport (ℤ/ℕ level) -/

/-- `ζ` is analytic at every nontrivial zero `ρ` (so `ρ ≠ 1`), hence so is the
scaled function `f_T` at the inverse coordinate of `ρ`. -/
theorem kadiriDiskF_analyticAt_of_ne_one {a : ℝ} (ha : 0 ≤ a) (T : ℝ)
    {ρ : ℂ} (hρ : ρ ≠ 1) :
    AnalyticAt ℂ (kadiriDiskF a T) (kadiriDiskCoord a T ρ) := by
  set z₀ : ℂ := kadiriDiskCoord a T ρ with hz₀
  have hgz₀ : kadiriDiskAffine a T z₀ = ρ := kadiriDiskAffine_coord ha T ρ
  have hζ : AnalyticAt ℂ riemannZeta ρ := analyticAt_riemannZeta hρ
  have hcomp : AnalyticAt ℂ (riemannZeta ∘ kadiriDiskAffine a T) z₀ :=
    (hgz₀ ▸ hζ).comp (kadiriDiskAffine_analyticAt a T z₀)
  rw [kadiriDiskF_eq_const_smul_comp a T]
  exact (analyticAt_const).smul hcomp

/-- **Order transport (`ℤ` = `ℕ`).** At a nontrivial zero `ρ` (so `ρ ≠ 1`), the
integer meromorphic order `riemannZeta.order ρ` equals the natural analytic order
`analyticOrderNatAt (kadiriDiskF a T) ((ρ - c - iT)/λ)`.  Both are nonnegative at
the zero (analyticity), so the `ℕ`/`ℤ` distinction is harmless. -/
theorem kadiriDiskF_order_transport {a : ℝ} (ha : 0 ≤ a) {T : ℝ}
    (hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0) {ρ : ℂ} (hρ : ρ ≠ 1) :
    (riemannZeta.order ρ : ℤ)
      = (analyticOrderNatAt (kadiriDiskF a T) (kadiriDiskCoord a T ρ) : ℤ) := by
  have hfa : AnalyticAt ℂ (kadiriDiskF a T) (kadiriDiskCoord a T ρ) :=
    kadiriDiskF_analyticAt_of_ne_one ha T hρ
  -- `riemannZeta.order ρ = (meromorphicOrderAt ζ ρ).untopD 0`.
  unfold riemannZeta.order
  -- transport the meromorphic order across the affine reparametrization.
  rw [← kadiriDiskF_meromorphicOrderAt_eq ha hden ρ]
  -- since `f_T` is analytic at the disk point, the meromorphic order is the
  -- image of the analytic order under `↑ : ℕ∞ → ℤ`-with-top.
  rw [hfa.meromorphicOrderAt_eq]
  -- now `((analyticOrderAt f_T z₀).map (↑)).untopD 0 = analyticOrderNatAt f_T z₀`.
  cases h : analyticOrderAt (kadiriDiskF a T) (kadiriDiskCoord a T ρ) with
  | top =>
    simp [analyticOrderNatAt, h]
  | coe n =>
    simp only [analyticOrderNatAt, h, ENat.map_coe, ENat.toNat_coe]
    rw [WithTop.untopD_coe]

/-! ## Zero-set membership equivalence and the summand chain

These two facts complete the per-zero data for the affine reindex: a zero of `ζ`
at `ρ` is exactly a zero of `f_T` at the inverse coordinate (the constant
denominator is nonzero), and the disk summand `1/(z_σ - coord ρ)` rescales to the
target summand `λ/(s - ρ)`. -/

/-- **Zero ↔ zero.** With `ζ(c + iT) ≠ 0`, `ζ(ρ) = 0` iff `f_T(coord ρ) = 0`. -/
theorem kadiriDiskF_zero_iff {a : ℝ} (ha : 0 ≤ a) {T : ℝ}
    (hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0) (ρ : ℂ) :
    kadiriDiskF a T (kadiriDiskCoord a T ρ) = 0 ↔ riemannZeta ρ = 0 := by
  have hgz₀ : kadiriDiskAffine a T (kadiriDiskCoord a T ρ) = ρ :=
    kadiriDiskAffine_coord ha T ρ
  unfold kadiriDiskF
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rw [show (kadiriDiskC : ℂ) + (T : ℂ) * I
            + (kadiriDiskLam a : ℂ) * kadiriDiskCoord a T ρ
          = kadiriDiskAffine a T (kadiriDiskCoord a T ρ) from rfl, hgz₀] at h
      exact h
    · exact absurd h hden
  · intro h
    left
    rw [show (kadiriDiskC : ℂ) + (T : ℂ) * I
          + (kadiriDiskLam a : ℂ) * kadiriDiskCoord a T ρ
        = kadiriDiskAffine a T (kadiriDiskCoord a T ρ) from rfl, hgz₀]
    exact h

/-- **Summand chain.** For the horizontal evaluation point `s = σ + iT` with
disk coordinate `z_σ = coord s`, the disk summand `1/(z_σ - coord ρ)` equals the
rescaled target summand `λ/(s - ρ)`.  (Here `coord s - coord ρ = (s - ρ)/λ`.) -/
theorem kadiriDiskCoord_sub (a T : ℝ) (s ρ : ℂ) :
    kadiriDiskCoord a T s - kadiriDiskCoord a T ρ = (s - ρ) / (kadiriDiskLam a : ℂ) := by
  unfold kadiriDiskCoord
  rw [div_sub_div_same]
  ring_nf

/-- The disk summand `1/(coord s - coord ρ)` is `λ·(1/(s - ρ))`. -/
theorem kadiriDisk_summand_chain (a T : ℝ) (s ρ : ℂ) :
    (1 : ℂ) / (kadiriDiskCoord a T s - kadiriDiskCoord a T ρ)
      = (kadiriDiskLam a : ℂ) * (1 / (s - ρ)) := by
  rw [kadiriDiskCoord_sub a T s ρ, one_div_div, mul_one_div]

/-- The same summand chain when the zero is already given in disk coordinates. -/
theorem kadiriDisk_summand_chain_affine {a : ℝ} (ha : 0 ≤ a) (T : ℝ) (s z : ℂ) :
    (1 : ℂ) / (kadiriDiskCoord a T s - z)
      = (kadiriDiskLam a : ℂ) * (1 / (s - kadiriDiskAffine a T z)) := by
  calc
    (1 : ℂ) / (kadiriDiskCoord a T s - z)
        = (1 : ℂ) /
            (kadiriDiskCoord a T s - kadiriDiskCoord a T (kadiriDiskAffine a T z)) := by
          rw [kadiriDiskCoord_affine ha T z]
    _ = (kadiriDiskLam a : ℂ) * (1 / (s - kadiriDiskAffine a T z)) :=
          kadiriDisk_summand_chain a T s (kadiriDiskAffine a T z)

/-- After dividing the disk sum by the scale `λ`, a disk-coordinate summand becomes
the original-coordinate summand. -/
theorem kadiriDisk_scaled_order_summand_chain_affine {a : ℝ} (ha : 0 ≤ a)
    (T : ℝ) (s z : ℂ) (n : ℕ) :
    ((kadiriDiskLam a : ℂ)⁻¹) *
        ((n : ℂ) / (kadiriDiskCoord a T s - z))
      = (n : ℂ) / (s - kadiriDiskAffine a T z) := by
  rw [show (n : ℂ) / (kadiriDiskCoord a T s - z)
      = (n : ℂ) * ((1 : ℂ) / (kadiriDiskCoord a T s - z)) by
        rw [div_eq_mul_inv, one_div]]
  rw [kadiriDisk_summand_chain_affine ha T s z]
  field_simp [kadiriDiskLam_ne_zero ha]

/-! ## Finite window reindexing -/

/-- The unit-height nontrivial-zero window is finite. -/
theorem zeroes_rect_Ioo_Icc_window_finite (T : ℝ) :
    (riemannZeta.zeroes_rect (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1))).Finite := by
  let S : Set ℂ := Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (T - 1) (T + 1)
  refine (riemannZeta.zeroes_on_Compact_finite' (S := S) ?_).subset ?_
  · exact IsCompact.reProdIm isCompact_Icc isCompact_Icc
  · intro z hz
    simp only [riemannZeta.zeroes_rect, Set.mem_setOf_eq] at hz
    simp only [S, Complex.mem_reProdIm, Set.mem_inter_iff]
    exact ⟨⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1⟩, hz.2.2⟩

/-- A zero in the open critical strip is not the pole point `1`. -/
theorem zeroes_rect_Ioo_ne_one {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ riemannZeta.zeroes_rect (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1))) :
    ρ ≠ 1 := by
  intro h
  have hre : ρ.re < 1 := hρ.1.2
  rw [h] at hre
  norm_num at hre

/-- A member of the finite unit-height window has real part in the open
critical strip. -/
theorem zeroes_rect_Ioo_Icc_window_toFinset_re_mem {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset) :
    ρ.re ∈ Set.Ioo (0 : ℝ) 1 :=
  ((zeroes_rect_Ioo_Icc_window_finite T).mem_toFinset.mp hρ).1

/-- A member of the finite unit-height window has imaginary part in that
window. -/
theorem zeroes_rect_Ioo_Icc_window_toFinset_im_mem {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset) :
    ρ.im ∈ Set.Icc (T - 1) (T + 1) :=
  ((zeroes_rect_Ioo_Icc_window_finite T).mem_toFinset.mp hρ).2.1

/-- A member of the finite unit-height window is a zero of `ζ`. -/
theorem zeroes_rect_Ioo_Icc_window_toFinset_zeta_zero {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset) :
    riemannZeta ρ = 0 := by
  have hzero := ((zeroes_rect_Ioo_Icc_window_finite T).mem_toFinset.mp hρ).2.2
  simpa [riemannZeta.zeroes] using hzero

/-- A non-real zero of `ζ` lies in the open critical strip. -/
theorem riemannZeta_zero_re_mem_Ioo_of_im_ne_zero {ρ : ℂ}
    (hζ : riemannZeta ρ = 0) (him : ρ.im ≠ 0) :
    ρ.re ∈ Set.Ioo (0 : ℝ) 1 := by
  have hnot_left : ¬ρ.re ≤ 0 := by
    intro hle
    exact (riemannZeta_ne_zero_of_re_nonpos_im_ne_zero hle him) hζ
  have hnot_right : ¬(1 : ℝ) ≤ ρ.re := by
    intro hle
    exact (riemannZeta_ne_zero_of_one_le_re hle) hζ
  exact ⟨lt_of_not_ge hnot_left, lt_of_not_ge hnot_right⟩

/-- A zero in the unit-height window maps to a disk zero of `kadiriDiskF`. -/
theorem kadiriDisk_window_coord_mem_setOfZeros {a T : ℝ} (ha : 0 ≤ a)
    (hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0) {ρ : ℂ}
    (hρ : ρ ∈ riemannZeta.zeroes_rect (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1))) :
    kadiriDiskCoord a T ρ ∈ SetOfZeros kadiriDiskR (kadiriDiskF a T) := by
  have hγ : |ρ.im - T| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [hρ.2.1.1], by linarith [hρ.2.1.2]⟩
  obtain ⟨hdist, hlt⟩ := kadiriDisk_window_subset ha hρ.1.1 hρ.1.2 hγ
  have hlam_pos : 0 < kadiriDiskLam a := kadiriDiskLam_pos ha
  have hnorm :
      ‖kadiriDiskCoord a T ρ‖ =
        ‖ρ - ((kadiriDiskC : ℂ) + (T : ℂ) * I)‖ / kadiriDiskLam a := by
    have hcoord :
        kadiriDiskCoord a T ρ =
          (ρ - ((kadiriDiskC : ℂ) + (T : ℂ) * I)) / (kadiriDiskLam a : ℂ) := by
      unfold kadiriDiskCoord
      ring
    rw [hcoord, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam_pos]
  constructor
  · rw [hnorm]
    exact (div_le_iff₀ hlam_pos).2
      (le_of_lt (lt_of_le_of_lt hdist (by simpa [mul_comm] using hlt)))
  · exact (kadiriDiskF_zero_iff ha hden ρ).2 hρ.2.2

/-- The coordinate image of the unit-height zero window lies in the disk-zero set. -/
theorem kadiriDisk_window_image_subset_setOfZeros {a T : ℝ} (ha : 0 ≤ a)
    (hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0) :
    (kadiriDiskCoord a T) ''
        riemannZeta.zeroes_rect (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1))
      ⊆ SetOfZeros kadiriDiskR (kadiriDiskF a T) := by
  rintro ω ⟨ρ, hρ, rfl⟩
  exact kadiriDisk_window_coord_mem_setOfZeros ha hden hρ

/-- The coordinate-image window finset is a subfinset of the `FinalBound` disk-zero finset. -/
theorem kadiriDisk_window_image_subset_diskFinset {a T : ℝ} (ha : 0 ≤ a)
    (hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0)
      {finiteZeros : (SetOfZeros 1 (kadiriDiskF a T)).Finite} :
      (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T)
        ⊆ (finiteSetOfZeros_mono (r := kadiriDiskR) (f := kadiriDiskF a T)
          kadiriDiskR_lt_one finiteZeros).toFinset := by
    intro ω hω
    obtain ⟨ρ, hρfin, rfl⟩ := Finset.mem_image.mp hω
    exact (finiteSetOfZeros_mono (r := kadiriDiskR) (f := kadiriDiskF a T)
      kadiriDiskR_lt_one finiteZeros).mem_toFinset.mpr
      (kadiriDisk_window_coord_mem_setOfZeros ha hden
        ((zeroes_rect_Ioo_Icc_window_finite T).mem_toFinset.mp hρfin))

/-- The finite window `zeroes_sum` rewritten as the disk-coordinate sum over the same zeros. -/
theorem kadiriWindow_zeroes_sum_eq_disk_coord_sum {a T : ℝ} (ha : 0 ≤ a)
    (hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0) (s : ℂ) :
    (∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
        (analyticOrderNatAt (kadiriDiskF a T) (kadiriDiskCoord a T ρ) : ℂ) /
          (kadiriDiskCoord a T s - kadiriDiskCoord a T ρ))
      =
        (kadiriDiskLam a : ℂ) *
          riemannZeta.zeroes_sum (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1))
            (fun ρ ↦ (1 : ℂ) / (s - ρ)) := by
  rw [_root_.zeroes_sum_eq_toFinset_sum (fun ρ ↦ (1 : ℂ) / (s - ρ))
    (zeroes_rect_Ioo_Icc_window_finite T), Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro ρ hρ
  have hρmem :
      ρ ∈ riemannZeta.zeroes_rect (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1)) :=
    (zeroes_rect_Ioo_Icc_window_finite T).mem_toFinset.mp hρ
  have horderZ := kadiriDiskF_order_transport ha hden (zeroes_rect_Ioo_ne_one hρmem)
  have horderC :
      (analyticOrderNatAt (kadiriDiskF a T) (kadiriDiskCoord a T ρ) : ℂ)
        = (riemannZeta.order ρ : ℂ) := by
    exact_mod_cast horderZ.symm
  calc
    (analyticOrderNatAt (kadiriDiskF a T) (kadiriDiskCoord a T ρ) : ℂ) /
        (kadiriDiskCoord a T s - kadiriDiskCoord a T ρ)
        = (riemannZeta.order ρ : ℂ) *
            ((1 : ℂ) / (kadiriDiskCoord a T s - kadiriDiskCoord a T ρ)) := by
          rw [horderC, div_eq_mul_inv, one_div]
    _ = (riemannZeta.order ρ : ℂ) *
          ((kadiriDiskLam a : ℂ) * (1 / (s - ρ))) := by
          rw [kadiriDisk_summand_chain a T s ρ]
    _ = (kadiriDiskLam a : ℂ) *
          ((1 : ℂ) / (s - ρ) * (riemannZeta.order ρ : ℂ)) := by
          ring_nf

/-- The finite window `zeroes_sum` rewritten as the disk-coordinate sum over the
image finset indexed by `ω = (ρ - c - iT)/λ`. -/
theorem kadiriWindow_zeroes_sum_eq_disk_coord_image_sum {a T : ℝ} (ha : 0 ≤ a)
    (hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0) (s : ℂ) :
    (∑ ω ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T),
        (analyticOrderNatAt (kadiriDiskF a T) ω : ℂ) /
          (kadiriDiskCoord a T s - ω))
      =
        (kadiriDiskLam a : ℂ) *
          riemannZeta.zeroes_sum (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1))
            (fun ρ ↦ (1 : ℂ) / (s - ρ)) := by
  rw [Finset.sum_image]
  · exact kadiriWindow_zeroes_sum_eq_disk_coord_sum ha hden s
  · intro ρ hρ ρ' hρ' hcoord
    exact kadiriDiskCoord_injective ha T hcoord

/-- Split the finite disk-zero sum into the window-image part plus the finite complement. -/
theorem kadiriDisk_sum_eq_window_add_correction {a T : ℝ}
      (hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0)
      {finiteZeros : (SetOfZeros 1 (kadiriDiskF a T)).Finite} (ha : 0 ≤ a) (F : ℂ → ℂ) :
      (∑ z ∈ (finiteSetOfZeros_mono (r := kadiriDiskR) (f := kadiriDiskF a T)
        kadiriDiskR_lt_one finiteZeros).toFinset,
        F z)
        =
          (∑ z ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T),
            F z) +
          ∑ z ∈ (finiteSetOfZeros_mono (r := kadiriDiskR) (f := kadiriDiskF a T)
              kadiriDiskR_lt_one finiteZeros).toFinset \
              (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T),
            F z := by
    have hsub := kadiriDisk_window_image_subset_diskFinset ha hden (finiteZeros := finiteZeros)
    calc
      (∑ z ∈ (finiteSetOfZeros_mono (r := kadiriDiskR) (f := kadiriDiskF a T)
        kadiriDiskR_lt_one finiteZeros).toFinset,
        F z)
          =
            (∑ z ∈ (finiteSetOfZeros_mono (r := kadiriDiskR) (f := kadiriDiskF a T)
                kadiriDiskR_lt_one finiteZeros).toFinset \
                (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T),
              F z) +
            ∑ z ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T),
              F z := (Finset.sum_sdiff hsub).symm
    _ =
          (∑ z ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T),
            F z) +
          ∑ z ∈ (finiteSetOfZeros_mono (r := kadiriDiskR) (f := kadiriDiskF a T)
              kadiriDiskR_lt_one finiteZeros).toFinset \
              (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T),
            F z := by rw [add_comm]

/-- The full finite disk sum, divided by the affine scale, is the target window
`zeroes_sum` plus the finite disk-minus-window correction in original coordinates. -/
theorem kadiriDisk_scaled_disk_sum_eq_window_plus_correction {a T : ℝ} (ha : 0 ≤ a)
    (hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0) (s : ℂ)
      {finiteZeros : (SetOfZeros 1 (kadiriDiskF a T)).Finite} :
      ((kadiriDiskLam a : ℂ)⁻¹) *
          (∑ z ∈ (finiteSetOfZeros_mono (r := kadiriDiskR) (f := kadiriDiskF a T)
              kadiriDiskR_lt_one finiteZeros).toFinset,
            (analyticOrderNatAt (kadiriDiskF a T) z : ℂ) /
              (kadiriDiskCoord a T s - z))
        =
          riemannZeta.zeroes_sum (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1))
            (fun ρ ↦ (1 : ℂ) / (s - ρ)) +
          ∑ z ∈ (finiteSetOfZeros_mono (r := kadiriDiskR) (f := kadiriDiskF a T)
              kadiriDiskR_lt_one finiteZeros).toFinset \
              (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T),
            (analyticOrderNatAt (kadiriDiskF a T) z : ℂ) /
            (s - kadiriDiskAffine a T z) := by
  rw [kadiriDisk_sum_eq_window_add_correction hden (finiteZeros := finiteZeros) ha
    (fun z ↦ (analyticOrderNatAt (kadiriDiskF a T) z : ℂ) /
      (kadiriDiskCoord a T s - z))]
  rw [mul_add]
  congr 1
  · rw [kadiriWindow_zeroes_sum_eq_disk_coord_image_sum ha hden s]
    field_simp [kadiriDiskLam_ne_zero ha]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro z hz
    exact kadiriDisk_scaled_order_summand_chain_affine ha T s z
      (analyticOrderNatAt (kadiriDiskF a T) z)

/-- A disk zero of `f_T` maps back to an original zero of `ζ`. -/
theorem kadiriDiskF_zero_at_affine_of_setOfZeros {a T : ℝ} (ha : 0 ≤ a)
    (hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0) {z : ℂ}
    (hz : z ∈ SetOfZeros kadiriDiskR (kadiriDiskF a T)) :
    riemannZeta (kadiriDiskAffine a T z) = 0 := by
  exact (kadiriDiskF_zero_iff ha hden (kadiriDiskAffine a T z)).1
    (by simpa [kadiriDiskCoord_affine ha T z] using hz.2)

/-- A disk point of radius `r` maps to original height within `λr` of the center height. -/
theorem kadiriDiskAffine_im_sub_center_abs_le {a T : ℝ} (ha : 0 ≤ a) {z : ℂ}
    (hz_norm : ‖z‖ ≤ kadiriDiskR) :
    |(kadiriDiskAffine a T z).im - T| ≤ kadiriDiskLam a * kadiriDiskR := by
  have hlam_pos : 0 < kadiriDiskLam a := kadiriDiskLam_pos ha
  have him : (kadiriDiskAffine a T z).im - T = kadiriDiskLam a * z.im := by
    simp [kadiriDiskAffine]
  rw [him, abs_mul, abs_of_pos hlam_pos]
  exact mul_le_mul_of_nonneg_left (le_trans (Complex.abs_im_le_norm z) hz_norm) hlam_pos.le

/-- At sufficiently large center height, every disk zero maps to a non-real original zero. -/
theorem kadiriDiskAffine_im_ne_zero_of_large {a T : ℝ} (ha : 0 ≤ a)
    (hlarge : kadiriDiskLam a * kadiriDiskR + 1 < |T|) {z : ℂ}
    (hz_norm : ‖z‖ ≤ kadiriDiskR) :
    (kadiriDiskAffine a T z).im ≠ 0 := by
  intro him0
  have hdiff := kadiriDiskAffine_im_sub_center_abs_le (T := T) ha hz_norm
  have hTle : |T| ≤ kadiriDiskLam a * kadiriDiskR := by
    calc
      |T| = |(kadiriDiskAffine a T z).im - T| := by rw [him0, zero_sub, abs_neg]
      _ ≤ kadiriDiskLam a * kadiriDiskR := hdiff
  linarith

/-- A disk zero outside the unit-height window is at original-coordinate distance at least
`1` from any point with the same imaginary part as the disk center. -/
theorem kadiriDisk_diskZero_not_window_original_sep {a T : ℝ} {s z : ℂ}
    (ha : 0 ≤ a)
    (hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0)
    (hlarge : kadiriDiskLam a * kadiriDiskR + 1 < |T|)
    (hz : z ∈ SetOfZeros kadiriDiskR (kadiriDiskF a T))
    (hz_not_window :
      z ∉ (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T))
    (hs_im : s.im = T) :
    1 ≤ ‖s - kadiriDiskAffine a T z‖ := by
  let ρ : ℂ := kadiriDiskAffine a T z
  have hζ : riemannZeta ρ = 0 := by
    simpa [ρ] using kadiriDiskF_zero_at_affine_of_setOfZeros ha hden hz
  have him_ne : ρ.im ≠ 0 := by
    simpa [ρ] using kadiriDiskAffine_im_ne_zero_of_large ha hlarge hz.1
  have hre : ρ.re ∈ Set.Ioo (0 : ℝ) 1 :=
    riemannZeta_zero_re_mem_Ioo_of_im_ne_zero hζ him_ne
  have hnot_le : ¬ |ρ.im - T| ≤ 1 := by
    intro hle
    have him_window : ρ.im ∈ Set.Icc (T - 1) (T + 1) := by
      rw [abs_le] at hle
      exact ⟨by linarith, by linarith⟩
    have hρ_window :
        ρ ∈ riemannZeta.zeroes_rect (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1)) :=
      ⟨hre, him_window, hζ⟩
    have hcoord_mem :
        kadiriDiskCoord a T ρ ∈
          (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T) := by
      exact Finset.mem_image.mpr
        ⟨ρ, (zeroes_rect_Ioo_Icc_window_finite T).mem_toFinset.mpr hρ_window, rfl⟩
    have hcoord : kadiriDiskCoord a T ρ = z := by
      simpa [ρ] using kadiriDiskCoord_affine ha T z
    exact hz_not_window (by simpa [hcoord] using hcoord_mem)
  have him_gt : 1 < |ρ.im - T| := lt_of_not_ge hnot_le
  calc
    1 ≤ |ρ.im - T| := le_of_lt him_gt
    _ = |(s - ρ).im| := by
      rw [Complex.sub_im, hs_im, abs_sub_comm]
    _ ≤ ‖s - ρ‖ := Complex.abs_im_le_norm (s - ρ)

/-- The large-height separation specialized to the finite disk-minus-window complement. -/
theorem kadiriDisk_diskMinusWindow_original_sep {a T : ℝ} (ha : 0 ≤ a)
    (hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0)
    (hlarge : kadiriDiskLam a * kadiriDiskR + 1 < |T|) (s : ℂ) (hs_im : s.im = T)
    {finiteZeros : (SetOfZeros 1 (kadiriDiskF a T)).Finite} :
    ∀ z ∈ (finiteSetOfZeros_mono kadiriDiskR_lt_one finiteZeros).toFinset \
        (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T),
      1 ≤ ‖s - kadiriDiskAffine a T z‖ := by
  intro z hz
  have hzK :
      z ∈ (finiteSetOfZeros_mono kadiriDiskR_lt_one finiteZeros).toFinset :=
    (Finset.mem_sdiff.mp hz).1
  have hz_not_window :
      z ∉ (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T) :=
    (Finset.mem_sdiff.mp hz).2
  exact kadiriDisk_diskZero_not_window_original_sep ha hden hlarge
    ((finiteSetOfZeros_mono kadiriDiskR_lt_one finiteZeros).mem_toFinset.mp hzK)
    hz_not_window hs_im

/-! ## Finite correction estimate -/

/-- A finite original-coordinate correction sum is bounded by the sum of disk zero orders
when every corrected zero is at distance at least `1` from the evaluation point. -/
theorem kadiriDisk_original_correction_norm_le_order_sum (a T : ℝ) (s : ℂ) (E : Finset ℂ)
    (hsep : ∀ z ∈ E, 1 ≤ ‖s - kadiriDiskAffine a T z‖) :
    ‖∑ z ∈ E,
        (analyticOrderNatAt (kadiriDiskF a T) z : ℂ) / (s - kadiriDiskAffine a T z)‖
      ≤ ((∑ z ∈ E, analyticOrderNatAt (kadiriDiskF a T) z : ℕ) : ℝ) := by
  calc
    ‖∑ z ∈ E,
        (analyticOrderNatAt (kadiriDiskF a T) z : ℂ) / (s - kadiriDiskAffine a T z)‖
        ≤ ∑ z ∈ E,
            ‖(analyticOrderNatAt (kadiriDiskF a T) z : ℂ) /
              (s - kadiriDiskAffine a T z)‖ := norm_sum_le _ _
    _ ≤ ∑ z ∈ E, (analyticOrderNatAt (kadiriDiskF a T) z : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro z hz
          have hsepz := hsep z hz
          have hden_pos : 0 < ‖s - kadiriDiskAffine a T z‖ :=
            lt_of_lt_of_le zero_lt_one hsepz
          rw [norm_div, RCLike.norm_natCast]
          calc
            (analyticOrderNatAt (kadiriDiskF a T) z : ℝ) /
                ‖s - kadiriDiskAffine a T z‖
                ≤ (analyticOrderNatAt (kadiriDiskF a T) z : ℝ) / 1 := by
                  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) zero_lt_one hsepz
            _ = (analyticOrderNatAt (kadiriDiskF a T) z : ℝ) := by simp
    _ = ((∑ z ∈ E, analyticOrderNatAt (kadiriDiskF a T) z : ℕ) : ℝ) := by simp

/-- The finite disk-minus-window correction is bounded by its total disk order at large height. -/
theorem kadiriDisk_diskMinusWindow_correction_norm_le_order_sum {a T : ℝ} (ha : 0 ≤ a)
    (hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0)
    (hlarge : kadiriDiskLam a * kadiriDiskR + 1 < |T|) (s : ℂ) (hs_im : s.im = T)
    {finiteZeros : (SetOfZeros 1 (kadiriDiskF a T)).Finite} :
    ‖∑ z ∈ (finiteSetOfZeros_mono kadiriDiskR_lt_one finiteZeros).toFinset \
        (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T),
        (analyticOrderNatAt (kadiriDiskF a T) z : ℂ) /
          (s - kadiriDiskAffine a T z)‖
      ≤ ((∑ z ∈ (finiteSetOfZeros_mono kadiriDiskR_lt_one finiteZeros).toFinset \
          (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T),
          analyticOrderNatAt (kadiriDiskF a T) z : ℕ) : ℝ) :=
  kadiriDisk_original_correction_norm_le_order_sum a T s
    ((finiteSetOfZeros_mono kadiriDiskR_lt_one finiteZeros).toFinset \
      (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T))
    (kadiriDisk_diskMinusWindow_original_sep (finiteZeros := finiteZeros) ha hden hlarge s hs_im)

end Kadiri
