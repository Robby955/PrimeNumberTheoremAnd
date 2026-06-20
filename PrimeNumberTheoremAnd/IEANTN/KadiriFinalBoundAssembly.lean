import PrimeNumberTheoremAnd.IEANTN.KadiriZeroReindex
import PrimeNumberTheoremAnd.IEANTN.KadiriGammaDecayUncond
import PrimeNumberTheoremAnd.IEANTN.KadiriHorizontalPVPackageConstruction
import PrimeNumberTheoremAnd.IEANTN.KadiriZetaLowerBound

/-!
# Kadiri horizontal `FinalBound` assembly: the unconditional partial-fraction remainder

This module performs the mechanical assembly that turns the already-proved,
unconditional scaffold into the genuine remaining analytic obligation
`Kadiri.KadiriHorizontalPFRemainderLinearInput`, which the proved reduction
`kadiriHorizontalPartialFractionRemainderBound_of_linearInput` consumes.

The three inputs are assembled from in-tree facts only:

* **Denominator lower bound (piece 1).**  `‖ζ(3/2 + iT)‖ ≥ c₀ > 0` uniform in `T`
  comes directly from the in-tree Euler-product lower bound `zeta_lower_bound`
  (`StrongPNTPort/PNT3_RiemannZeta.lean`) with `c₀ = ‖ζ(3)/ζ(3/2)‖`
  (`zeta332pos`).  No Euler product is rebuilt here.
* **Scaled-disk sup bound (piece 2).**  `‖f_T z‖ ≤ B_T` for `‖z‖ ≤ R` is
  numerator (`riemannZeta_fixedStrip_poly_bound_uncond` on the fixed strip the
  disk image lands in) over denominator (piece 1).  The resulting `log B_T` is
  `O(log U)` with `U = |T| + 2`.
* **Log-derivative transport (piece 3a).**  `logDeriv f_T (coord s) = λ·logDeriv ζ s`
  via `kadiriDiskF_eq_const_smul_comp` and the affine derivative `λ`.
-/

namespace Kadiri

open Complex Real

/-! ## Piece 1: the fixed denominator lower bound `‖ζ(3/2 + iT)‖ ≥ c₀ > 0` -/

/-- The fixed positive denominator constant `c₀ = ‖ζ(3)/ζ(3/2)‖`. -/
noncomputable def kadiriDiskDenomConst : ℝ :=
  ‖riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)‖

theorem kadiriDiskDenomConst_pos : 0 < kadiriDiskDenomConst :=
  StrongPNTPort.zeta332pos

/-- The disk denominator point `3/2 + iT` agrees with the lower-bound point. -/
theorem kadiriDisk_denom_point_eq (T : ℝ) :
    (kadiriDiskC : ℂ) + (T : ℂ) * I = (((3 : ℝ) / 2 : ℝ) : ℂ) + (T : ℝ) * Complex.I := by
  simp [kadiriDiskC]

/-- **Piece 1.** Uniform lower bound `‖ζ(3/2 + iT)‖ ≥ c₀ > 0` for every `T`. -/
theorem kadiriDisk_denom_lower (T : ℝ) :
    kadiriDiskDenomConst ≤ ‖riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I)‖ := by
  simpa [kadiriDiskDenomConst, kadiriDiskC] using StrongPNTPort.zeta_lower_bound T

/-- The fixed denominator never vanishes. -/
theorem kadiriDisk_denom_ne_zero (T : ℝ) :
    riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0 := by
  have h := lt_of_lt_of_le kadiriDiskDenomConst_pos (kadiriDisk_denom_lower T)
  exact norm_pos_iff.mp h

/-! ## Piece 3a: the log-derivative transport `logDeriv f_T (coord s) = λ·logDeriv ζ s` -/

/-- The affine image `e (coord s) = s`. -/
theorem kadiriDiskAffine_coord' {a : ℝ} (ha : 0 ≤ a) (T : ℝ) (s : ℂ) :
    (kadiriDiskC : ℂ) + (T : ℂ) * I + (kadiriDiskLam a : ℂ) * kadiriDiskCoord a T s = s := by
  have h := kadiriDiskAffine_coord ha T s
  simpa [kadiriDiskAffine] using h

/-- **Piece 3a (log-derivative transport).**  At a point `s ≠ 1`, the log-derivative
of `f_T` at the inverse coordinate of `s` equals `λ·logDeriv ζ s`, i.e.
`deriv f_T (coord s) / f_T (coord s) = λ·(ζ' / ζ)(s)`.  Holds even at zeros of `ζ`
(both sides are then junk-equal), but is used where `ζ(s) ≠ 0`. -/
theorem kadiriDiskF_logDeriv_transport {a : ℝ} (ha : 0 ≤ a) {T : ℝ}
    {s : ℂ} (hs : s ≠ 1) :
    logDeriv (kadiriDiskF a T) (kadiriDiskCoord a T s)
      = (kadiriDiskLam a : ℂ) * logDeriv riemannZeta s := by
  set z₀ : ℂ := kadiriDiskCoord a T s with hz₀
  have hgz : kadiriDiskAffine a T z₀ = s := kadiriDiskAffine_coord ha T s
  -- f_T = const • (ζ ∘ e); the constant is the (nonzero) reciprocal denominator.
  have hconst_ne : (riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I))⁻¹ ≠ 0 :=
    inv_ne_zero (kadiriDisk_denom_ne_zero T)
  rw [kadiriDiskF_eq_const_smul_comp a T]
  -- rewrite `const • g` pointwise as `fun w => const * g w`.
  have hfun :
      ((fun _ : ℂ => (riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I))⁻¹)
          • (riemannZeta ∘ kadiriDiskAffine a T))
        = fun w : ℂ =>
            (riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I))⁻¹ *
              (riemannZeta ∘ kadiriDiskAffine a T) w := by
    funext w
    simp [smul_eq_mul]
  rw [hfun, logDeriv_const_mul z₀ _ hconst_ne]
  -- logDeriv (ζ ∘ e) z₀ = logDeriv ζ (e z₀) · deriv e z₀ = logDeriv ζ s · λ.
  have hζdiff : DifferentiableAt ℂ riemannZeta (kadiriDiskAffine a T z₀) := by
    rw [hgz]; exact (analyticAt_riemannZeta hs).differentiableAt
  have hediff : DifferentiableAt ℂ (kadiriDiskAffine a T) z₀ :=
    (kadiriDiskAffine_analyticAt a T z₀).differentiableAt
  rw [logDeriv_comp hζdiff hediff, kadiriDiskAffine_deriv a T z₀, hgz]
  ring

/-! ## Piece 2: the scaled-disk sup bound `‖f_T z‖ ≤ B_T` for `‖z‖ ≤ R`

The disk image point `e z = c + iT + λz` for `‖z‖ ≤ R = 15/16` has real part in the
fixed strip `[c - λR, c + λR]` and imaginary part `T + λ·im z`, with
`|im(e z)| ≥ |T| - λR`.  Once `|T| ≥ λR + 1` the imaginary part has modulus `≥ 1`,
so the unconditional fixed-strip polynomial bound applies, and dividing by the fixed
denominator lower bound gives the `f_T`-sup. -/

/-- The disk image point, as a `re + im·I` rectangle, for the fixed-strip bound. -/
private theorem kadiriDisk_image_rect (a T : ℝ) (z : ℂ) :
    (kadiriDiskC : ℂ) + (T : ℂ) * I + (kadiriDiskLam a : ℂ) * z
      = (((kadiriDiskC + kadiriDiskLam a * z.re : ℝ)) : ℂ)
        + (((T + kadiriDiskLam a * z.im : ℝ)) : ℂ) * I := by
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, kadiriDiskC]

/-- The disk-image real part lies in the fixed strip `[-(λR - c), λR + c]`. -/
private theorem kadiriDisk_image_re_mem {a : ℝ} (ha : 0 ≤ a) {z : ℂ}
    (hz : ‖z‖ ≤ kadiriDiskRCap) :
    kadiriDiskC + kadiriDiskLam a * z.re
      ∈ Set.Icc (-(kadiriDiskLam a * kadiriDiskRCap - kadiriDiskC))
          (kadiriDiskLam a * kadiriDiskRCap + kadiriDiskC) := by
  have hlam_pos : 0 < kadiriDiskLam a := kadiriDiskLam_pos ha
  have hre : |z.re| ≤ kadiriDiskRCap := le_trans (Complex.abs_re_le_norm z) hz
  rw [abs_le] at hre
  constructor
  · nlinarith [hre.1, hlam_pos]
  · nlinarith [hre.2, hlam_pos]

/-- `λR - c ≥ 0`, so the left strip edge `-(λR - c)` is `≤ 0` (a genuine strip). -/
private theorem kadiriDisk_strip_A_nonneg {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ kadiriDiskLam a * kadiriDiskRCap - kadiriDiskC := by
  have hlam : (3 : ℝ) ≤ kadiriDiskLam a := by simp only [kadiriDiskLam]; linarith
  simp only [kadiriDiskRCap, kadiriDiskC]
  nlinarith [hlam]

/-- The right strip edge `λR + c ≥ 1/2`. -/
private theorem kadiriDisk_strip_B_ge {a : ℝ} (ha : 0 ≤ a) :
    (1 / 2 : ℝ) ≤ kadiriDiskLam a * kadiriDiskRCap + kadiriDiskC := by
  have hlam : (3 : ℝ) ≤ kadiriDiskLam a := by simp only [kadiriDiskLam]; linarith
  simp only [kadiriDiskRCap, kadiriDiskC]
  nlinarith [hlam]

/-- **Piece 2 (scaled-disk sup bound).**  There are `Cζ ≥ 0` and a fixed power
`e ≥ 0` so that, once `|T| ≥ λR + 1`, every `z` with `‖z‖ ≤ R` satisfies
`‖f_T z‖ ≤ (Cζ / c₀) · (|T| + λR + 2)^e`.  (The numerator is the unconditional
fixed-strip `ζ` growth, the denominator the fixed lower bound `c₀`.) -/
theorem kadiriDisk_fT_sup_bound {a : ℝ} (ha : 0 ≤ a) :
    ∃ Cζ e : ℝ, 0 ≤ Cζ ∧ 0 ≤ e ∧
      ∀ T : ℝ, kadiriDiskLam a * kadiriDiskRCap + 1 ≤ |T| →
        ∀ z : ℂ, ‖z‖ ≤ kadiriDiskRCap →
          ‖kadiriDiskF a T z‖
            ≤ (Cζ / kadiriDiskDenomConst) *
                (|T| + kadiriDiskLam a * kadiriDiskRCap + 2) ^ e := by
  have hlam_pos : 0 < kadiriDiskLam a := kadiriDiskLam_pos ha
  obtain ⟨Cζ, e, hCζ, he0, hbd⟩ :=
    riemannZeta_fixedStrip_poly_bound_uncond
      (A := kadiriDiskLam a * kadiriDiskRCap - kadiriDiskC)
      (B := kadiriDiskLam a * kadiriDiskRCap + kadiriDiskC)
      (kadiriDisk_strip_A_nonneg ha) (kadiriDisk_strip_B_ge ha)
  refine ⟨Cζ, e, hCζ, he0, fun T hT z hz => ?_⟩
  set σ : ℝ := kadiriDiskC + kadiriDiskLam a * z.re with hσ
  set τ : ℝ := T + kadiriDiskLam a * z.im with hτ
  -- bounds on the strip membership and the imaginary modulus.
  have hσmem : σ ∈ Set.Icc (-(kadiriDiskLam a * kadiriDiskRCap - kadiriDiskC))
      (kadiriDiskLam a * kadiriDiskRCap + kadiriDiskC) := kadiriDisk_image_re_mem ha hz
  have himz : |z.im| ≤ kadiriDiskRCap := le_trans (Complex.abs_im_le_norm z) hz
  have h1 : |kadiriDiskLam a * z.im| ≤ kadiriDiskLam a * kadiriDiskRCap := by
    rw [abs_mul, abs_of_pos hlam_pos]
    exact mul_le_mul_of_nonneg_left himz hlam_pos.le
  have hτ_ge : (1 : ℝ) ≤ |τ| := by
    -- T = τ - λ·z.im, so |T| ≤ |τ| + |λ·z.im|, hence |τ| ≥ |T| - λR ≥ 1.
    have htri : |T| ≤ |τ| + |kadiriDiskLam a * z.im| := by
      have : T = τ + (-(kadiriDiskLam a * z.im)) := by rw [hτ]; ring
      calc |T| = |τ + (-(kadiriDiskLam a * z.im))| := by rw [this]
        _ ≤ |τ| + |(-(kadiriDiskLam a * z.im))| := abs_add_le _ _
        _ = |τ| + |kadiriDiskLam a * z.im| := by rw [abs_neg]
    linarith [htri, h1, hT]
  -- numerator bound.
  have hnum :
      ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * I)‖ ≤ Cζ * (|τ| + 2) ^ e := hbd σ τ hσmem hτ_ge
  -- rewrite f_T z and split the norm.
  have hf : kadiriDiskF a T z
      = riemannZeta ((σ : ℂ) + (τ : ℂ) * I) / riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) := by
    rw [kadiriDiskF, kadiriDisk_image_rect a T z]
  have hden_pos : 0 < ‖riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I)‖ :=
    lt_of_lt_of_le kadiriDiskDenomConst_pos (kadiriDisk_denom_lower T)
  have hdenom : kadiriDiskDenomConst ≤ ‖riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I)‖ :=
    kadiriDisk_denom_lower T
  -- |τ| + 2 ≤ |T| + λR + 2 since |τ| ≤ |T| + λR.
  have hτ_le : |τ| ≤ |T| + kadiriDiskLam a * kadiriDiskRCap := by
    have h1 : |kadiriDiskLam a * z.im| ≤ kadiriDiskLam a * kadiriDiskRCap := by
      rw [abs_mul, abs_of_pos hlam_pos]
      exact mul_le_mul_of_nonneg_left himz hlam_pos.le
    calc |τ| = |T + kadiriDiskLam a * z.im| := by rw [hτ]
      _ ≤ |T| + |kadiriDiskLam a * z.im| := abs_add_le _ _
      _ ≤ |T| + kadiriDiskLam a * kadiriDiskRCap := by linarith
  have hbase_le : |τ| + 2 ≤ |T| + kadiriDiskLam a * kadiriDiskRCap + 2 := by linarith
  have hbase_pos : (0 : ℝ) ≤ |τ| + 2 := by linarith [abs_nonneg τ]
  have hPbase_nonneg : (0 : ℝ) ≤ |T| + kadiriDiskLam a * kadiriDiskRCap + 2 := by
    linarith [hbase_pos, hbase_le]
  have hpow_mono : (|τ| + 2) ^ e ≤ (|T| + kadiriDiskLam a * kadiriDiskRCap + 2) ^ e :=
    Real.rpow_le_rpow hbase_pos hbase_le he0
  have hP_nonneg : (0 : ℝ) ≤ (|T| + kadiriDiskLam a * kadiriDiskRCap + 2) ^ e :=
    Real.rpow_nonneg hPbase_nonneg e
  -- assemble: ‖f_T z‖ = ‖num‖/‖den‖ ≤ (Cζ/c₀)·P  via ‖num‖ ≤ Cζ·P and c₀ ≤ ‖den‖.
  have hnumP : ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * I)‖
      ≤ Cζ * (|T| + kadiriDiskLam a * kadiriDiskRCap + 2) ^ e :=
    hnum.trans (mul_le_mul_of_nonneg_left hpow_mono hCζ)
  rw [hf, norm_div, div_le_iff₀ hden_pos]
  calc ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * I)‖
      ≤ Cζ * (|T| + kadiriDiskLam a * kadiriDiskRCap + 2) ^ e := hnumP
    _ = (Cζ / kadiriDiskDenomConst) *
          (|T| + kadiriDiskLam a * kadiriDiskRCap + 2) ^ e * kadiriDiskDenomConst := by
        field_simp [kadiriDiskDenomConst_pos.ne']
    _ ≤ (Cζ / kadiriDiskDenomConst) *
          (|T| + kadiriDiskLam a * kadiriDiskRCap + 2) ^ e *
            ‖riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I)‖ :=
        mul_le_mul_of_nonneg_left hdenom
          (mul_nonneg (div_nonneg hCζ kadiriDiskDenomConst_pos.le) hP_nonneg)

/-- The scaled disk zero set of `f_T` in the unit disk is finite.  It injects
through the affine map into the zeta zeros on the compact affine image of the
closed unit disk, which avoids the pole at `1` when `λ < |T|`. -/
theorem kadiriDisk_finiteZeros {a T : ℝ} (ha : 0 ≤ a)
    (hT : kadiriDiskLam a < |T|) :
    (SetOfZeros 1 (kadiriDiskF a T)).Finite := by
  let S : Set ℂ := kadiriDiskAffine a T '' Metric.closedBall (0 : ℂ) 1
  have hball : IsCompact (Metric.closedBall (0 : ℂ) 1) :=
    ProperSpace.isCompact_closedBall (0 : ℂ) 1
  have haff_cont : Continuous (kadiriDiskAffine a T) :=
    continuous_iff_continuousAt.mpr fun z => (kadiriDiskAffine_analyticAt a T z).continuousAt
  have hScompact : IsCompact S := hball.image haff_cont
  have hS_no_one : (1 : ℂ) ∉ S := by
    rintro ⟨z, hz, hz1⟩
    have hz_norm : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    exact (kadiriDisk_pole_outside ha hT hz_norm) hz1
  have hZfin : (S ∩ riemannZeta.zeroes).Finite :=
    riemannZeta.zeroes_on_Compact_finite hScompact hS_no_one
  have haff_inj :
      Set.InjOn (kadiriDiskAffine a T)
        ((kadiriDiskAffine a T) ⁻¹' (S ∩ riemannZeta.zeroes)) := by
    intro z _ w _ hzw
    have := congrArg (kadiriDiskCoord a T) hzw
    simpa [kadiriDiskCoord_affine ha T z, kadiriDiskCoord_affine ha T w] using this
  have hpre : ((kadiriDiskAffine a T) ⁻¹' (S ∩ riemannZeta.zeroes)).Finite :=
    hZfin.preimage haff_inj
  refine hpre.subset ?_
  intro z hz
  rcases hz with ⟨hz_norm, hfz⟩
  have hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0 :=
    kadiriDisk_denom_ne_zero T
  constructor
  · exact ⟨z, by simpa [Metric.mem_closedBall, dist_zero_right] using hz_norm, rfl⟩
  · have hζzero : riemannZeta (kadiriDiskAffine a T z) = 0 :=
      (kadiriDiskF_zero_iff ha hden (kadiriDiskAffine a T z)).mp
        (by simpa [kadiriDiskCoord_affine ha T z] using hfz)
    simpa [riemannZeta.zeroes] using hζzero

/-! ## Piece 3b: `FinalBound` translated to the original window plus correction -/

/-- The scaled coordinate of the horizontal point `σ + iT`. -/
theorem kadiriDiskCoord_horizontalPoint (a T σ : ℝ) :
    kadiriDiskCoord a T ((σ : ℂ) + (T : ℂ) * I)
      = ((σ : ℂ) - (kadiriDiskC : ℂ)) / (kadiriDiskLam a : ℂ) := by
  unfold kadiriDiskCoord
  ring

/-- **Piece 3b.** `FinalBound`, translated through the affine coordinate and the
finite window/correction split.  This is the z-variable estimate before the
eventual `log(|T|+2)` sup-bound constants are inserted. -/
theorem kadiriDisk_finalBound_window_correction {a T B σ : ℝ} (ha : 0 ≤ a)
    (hT : kadiriDiskLam a < |T|) (hB : 1 < B)
    {finiteZeros : (SetOfZeros 1 (kadiriDiskF a T)).Finite}
    (fz_bound : ∀ z : ℂ, ‖z‖ ≤ kadiriDiskRCap → ‖kadiriDiskF a T z‖ ≤ B)
    (hσ : σ ∈ Set.Icc (-a) (1 + a))
    (hζ : riemannZeta ((σ : ℂ) + (T : ℂ) * I) ≠ 0) :
    let s : ℂ := (σ : ℂ) + (T : ℂ) * I
    ‖logDeriv riemannZeta s -
        (riemannZeta.zeroes_sum (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1))
            (fun ρ ↦ (1 : ℂ) / (s - ρ)) +
          ∑ z ∈ (finiteSetOfZeros_mono (r := kadiriDiskR) kadiriDiskR_lt_one finiteZeros).toFinset \
              (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T),
            (analyticOrderNatAt (kadiriDiskF a T) z : ℂ) /
              (s - kadiriDiskAffine a T z))‖
      ≤ (kadiriDiskLam a)⁻¹ *
        (16 * kadiriDiskR ^ 2 / (kadiriDiskR - kadiriDiskRPrime) ^ 3 +
          1 / ((kadiriDiskRCap ^ 2 / kadiriDiskRCapPrime - kadiriDiskRCapPrime) *
            Real.log (kadiriDiskRCap / kadiriDiskRCapPrime))) * Real.log B := by
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  let D : ℂ :=
    ∑ z ∈ (finiteSetOfZeros_mono (r := kadiriDiskR) kadiriDiskR_lt_one finiteZeros).toFinset,
      (analyticOrderNatAt (kadiriDiskF a T) z : ℂ) / (kadiriDiskCoord a T s - z)
  have hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0 :=
    kadiriDisk_denom_ne_zero T
  obtain ⟨hrp_pos, hrp_lt_r, hr_lt_Rp, hRp_lt_R, hR_lt_one⟩ := kadiriDiskRadii_ordered
  have hz_norm : ‖kadiriDiskCoord a T s‖ ≤ kadiriDiskRPrime := by
    change ‖kadiriDiskCoord a T ((σ : ℂ) + (T : ℂ) * I)‖ ≤ kadiriDiskRPrime
    rw [kadiriDiskCoord_horizontalPoint]
    exact kadiriDisk_segment_in_innerDisk ha hσ
  have hz_closed : kadiriDiskCoord a T s ∈ Metric.closedBall (0 : ℂ) kadiriDiskRPrime := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz_norm
  have hz_not_zero : kadiriDiskCoord a T s ∉ SetOfZeros kadiriDiskRCapPrime (kadiriDiskF a T) := by
    intro hz
    exact hζ (by simpa [s] using (kadiriDiskF_zero_iff ha hden s).mp hz.2)
  have hs_ne_one : s ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    have hTzero : T = 0 := by
      simpa [s, Complex.add_im, Complex.mul_im] using him
    have hLam_pos : 0 < kadiriDiskLam a := kadiriDiskLam_pos ha
    have hTpos : 0 < |T| := lt_trans hLam_pos hT
    have hzero_not_pos : ¬ (0 : ℝ) < |(0 : ℝ)| := by norm_num
    rw [hTzero] at hTpos
    exact hzero_not_pos hTpos
  have hFBraw := FinalBound (B := B) (r' := kadiriDiskRPrime) (r := kadiriDiskR)
    (R' := kadiriDiskRCapPrime) (R := kadiriDiskRCap) (f := kadiriDiskF a T)
    (z := kadiriDiskCoord a T s) hB hrp_pos hrp_lt_r kadiriDiskR_lt_one
    hr_lt_Rp hRp_lt_R hR_lt_one (kadiriDisk_fT_analyticOnNhd ha hT hden)
    (kadiriDisk_fT_zero_at_zero hden) finiteZeros fz_bound ⟨hz_closed, hz_not_zero⟩
  have hFB :
      ‖logDeriv (kadiriDiskF a T) (kadiriDiskCoord a T s) - D‖ ≤
        (16 * kadiriDiskR ^ 2 / (kadiriDiskR - kadiriDiskRPrime) ^ 3 +
          1 / ((kadiriDiskRCap ^ 2 / kadiriDiskRCapPrime - kadiriDiskRCapPrime) *
            Real.log (kadiriDiskRCap / kadiriDiskRCapPrime))) * Real.log B := by
    simpa [D, logDeriv_apply] using hFBraw
  rw [kadiriDiskF_logDeriv_transport ha hs_ne_one] at hFB
  have hscale :
      ‖logDeriv riemannZeta s - (kadiriDiskLam a : ℂ)⁻¹ * D‖ =
        (kadiriDiskLam a)⁻¹ *
          ‖(kadiriDiskLam a : ℂ) * logDeriv riemannZeta s - D‖ := by
    have hLam_pos : 0 < kadiriDiskLam a := kadiriDiskLam_pos ha
    have hLam_ne : (kadiriDiskLam a : ℂ) ≠ 0 := kadiriDiskLam_ne_zero ha
    have hmul :
        logDeriv riemannZeta s - (kadiriDiskLam a : ℂ)⁻¹ * D
          = (kadiriDiskLam a : ℂ)⁻¹ *
              ((kadiriDiskLam a : ℂ) * logDeriv riemannZeta s - D) := by
      calc
        logDeriv riemannZeta s - (kadiriDiskLam a : ℂ)⁻¹ * D
            = (kadiriDiskLam a : ℂ)⁻¹ *
                ((kadiriDiskLam a : ℂ) * logDeriv riemannZeta s) -
                  (kadiriDiskLam a : ℂ)⁻¹ * D := by
              rw [inv_mul_cancel_left₀ hLam_ne]
        _ = (kadiriDiskLam a : ℂ)⁻¹ *
              ((kadiriDiskLam a : ℂ) * logDeriv riemannZeta s - D) := by
              ring
    calc
      ‖logDeriv riemannZeta s - (kadiriDiskLam a : ℂ)⁻¹ * D‖
          = ‖(kadiriDiskLam a : ℂ)⁻¹ *
              ((kadiriDiskLam a : ℂ) * logDeriv riemannZeta s - D)‖ := by
            rw [hmul]
      _ = ‖((kadiriDiskLam a : ℂ)⁻¹)‖ *
            ‖(kadiriDiskLam a : ℂ) * logDeriv riemannZeta s - D‖ := by
            rw [norm_mul]
      _ = (kadiriDiskLam a)⁻¹ *
            ‖(kadiriDiskLam a : ℂ) * logDeriv riemannZeta s - D‖ := by
            rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLam_pos]
  have hscaled :
      ‖logDeriv riemannZeta s - (kadiriDiskLam a : ℂ)⁻¹ * D‖ ≤
        (kadiriDiskLam a)⁻¹ *
          ((16 * kadiriDiskR ^ 2 / (kadiriDiskR - kadiriDiskRPrime) ^ 3 +
            1 / ((kadiriDiskRCap ^ 2 / kadiriDiskRCapPrime - kadiriDiskRCapPrime) *
              Real.log (kadiriDiskRCap / kadiriDiskRCapPrime))) * Real.log B) := by
    rw [hscale]
    exact mul_le_mul_of_nonneg_left hFB (inv_nonneg.mpr (kadiriDiskLam_pos ha).le)
  have hsplit := kadiriDisk_scaled_disk_sum_eq_window_plus_correction
    (a := a) (T := T) (finiteZeros := finiteZeros) ha hden s
  change
    ‖logDeriv riemannZeta s -
        (riemannZeta.zeroes_sum (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1))
            (fun ρ ↦ (1 : ℂ) / (s - ρ)) +
          ∑ z ∈ (finiteSetOfZeros_mono (r := kadiriDiskR) kadiriDiskR_lt_one finiteZeros).toFinset \
              (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T),
            (analyticOrderNatAt (kadiriDiskF a T) z : ℂ) /
              (s - kadiriDiskAffine a T z))‖
      ≤ (kadiriDiskLam a)⁻¹ *
        (16 * kadiriDiskR ^ 2 / (kadiriDiskR - kadiriDiskRPrime) ^ 3 +
          1 / ((kadiriDiskRCap ^ 2 / kadiriDiskRCapPrime - kadiriDiskRCapPrime) *
            Real.log (kadiriDiskRCap / kadiriDiskRCapPrime))) * Real.log B
  rw [← hsplit]
  simpa [mul_assoc] using hscaled

/-- The finite disk-minus-window correction is bounded by the `ZerosBound`
order budget.  This is the correction half of the scaled `FinalBound` assembly:
the separation lemma turns each original-coordinate denominator into a harmless
`≤ 1`, and `ZerosBound` bounds the resulting order sum by `C_Z log B`. -/
theorem kadiriDisk_correction_norm_le_zerosBound {a T B σ : ℝ} (ha : 0 ≤ a)
    (hT : kadiriDiskLam a < |T|)
    (hlarge : kadiriDiskLam a * kadiriDiskR + 1 < |T|)
    {finiteZeros : (SetOfZeros 1 (kadiriDiskF a T)).Finite}
    (fz_bound : ∀ z : ℂ, ‖z‖ ≤ kadiriDiskRCap → ‖kadiriDiskF a T z‖ ≤ B) :
    let s : ℂ := (σ : ℂ) + (T : ℂ) * I
    ‖∑ z ∈ (finiteSetOfZeros_mono (r := kadiriDiskR) kadiriDiskR_lt_one finiteZeros).toFinset \
        (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T),
        (analyticOrderNatAt (kadiriDiskF a T) z : ℂ) /
          (s - kadiriDiskAffine a T z)‖
      ≤ (1 / Real.log (kadiriDiskRCap / kadiriDiskR)) * Real.log B := by
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  let K :=
    (finiteSetOfZeros_mono (r := kadiriDiskR) (f := kadiriDiskF a T)
      kadiriDiskR_lt_one finiteZeros).toFinset
  let W := (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T)
  have hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0 :=
    kadiriDisk_denom_ne_zero T
  have hs_im : s.im = T := by
    simp [s, Complex.add_im, Complex.mul_im]
  have hcorr :
      ‖∑ z ∈ K \ W,
          (analyticOrderNatAt (kadiriDiskF a T) z : ℂ) /
            (s - kadiriDiskAffine a T z)‖
        ≤ ((∑ z ∈ K \ W, analyticOrderNatAt (kadiriDiskF a T) z : ℕ) : ℝ) := by
    simpa [K, W, s] using
      (kadiriDisk_diskMinusWindow_correction_norm_le_order_sum
        (a := a) (T := T) ha hden hlarge s hs_im (finiteZeros := finiteZeros))
  have hsubset_nat :
      (∑ z ∈ K \ W, analyticOrderNatAt (kadiriDiskF a T) z : ℕ)
        ≤ ∑ z ∈ K, analyticOrderNatAt (kadiriDiskF a T) z := by
    refine Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_
    intro z _ _
    exact Nat.zero_le _
  have hsubset :
      ((∑ z ∈ K \ W, analyticOrderNatAt (kadiriDiskF a T) z : ℕ) : ℝ)
        ≤ ((∑ z ∈ K, analyticOrderNatAt (kadiriDiskF a T) z : ℕ) : ℝ) := by
    exact_mod_cast hsubset_nat
  obtain ⟨hrp_pos, hrp_lt_r, hr_lt_Rp, hRp_lt_R, hR_lt_one⟩ := kadiriDiskRadii_ordered
  have hr_pos : 0 < kadiriDiskR := lt_trans hrp_pos hrp_lt_r
  have hr_lt_R : kadiriDiskR < kadiriDiskRCap := lt_trans hr_lt_Rp hRp_lt_R
  have hzeros :
      ((∑ z ∈ K, analyticOrderNatAt (kadiriDiskF a T) z : ℕ) : ℝ)
        ≤ (1 / Real.log (kadiriDiskRCap / kadiriDiskR)) * Real.log B := by
    simpa [K] using
      (ZerosBound (B := B) (r := kadiriDiskR) (R := kadiriDiskRCap)
        (f := kadiriDiskF a T) hr_pos kadiriDiskR_lt_one hr_lt_R hR_lt_one
        (kadiriDisk_fT_analyticOnNhd ha hT hden) (kadiriDisk_fT_zero_at_zero hden)
        finiteZeros fz_bound)
  change
    ‖∑ z ∈ K \ W,
        (analyticOrderNatAt (kadiriDiskF a T) z : ℂ) /
          (s - kadiriDiskAffine a T z)‖
      ≤ (1 / Real.log (kadiriDiskRCap / kadiriDiskR)) * Real.log B
  exact hcorr.trans (hsubset.trans hzeros)

/-- The scaled `FinalBound` estimate with the disk-minus-window correction absorbed
by `ZerosBound`, in the original horizontal window coordinates. -/
theorem kadiriDisk_finalBound_window_logDeriv {a T B σ : ℝ} (ha : 0 ≤ a)
    (hT : kadiriDiskLam a < |T|)
    (hlarge : kadiriDiskLam a * kadiriDiskR + 1 < |T|) (hB : 1 < B)
    {finiteZeros : (SetOfZeros 1 (kadiriDiskF a T)).Finite}
    (fz_bound : ∀ z : ℂ, ‖z‖ ≤ kadiriDiskRCap → ‖kadiriDiskF a T z‖ ≤ B)
    (hσ : σ ∈ Set.Icc (-a) (1 + a))
    (hζ : riemannZeta ((σ : ℂ) + (T : ℂ) * I) ≠ 0) :
    let s : ℂ := (σ : ℂ) + (T : ℂ) * I
    ‖-logDeriv riemannZeta s +
        riemannZeta.zeroes_sum (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1))
          (fun ρ ↦ (1 : ℂ) / (s - ρ))‖
      ≤
        (((kadiriDiskLam a)⁻¹ *
            (16 * kadiriDiskR ^ 2 / (kadiriDiskR - kadiriDiskRPrime) ^ 3 +
              1 / ((kadiriDiskRCap ^ 2 / kadiriDiskRCapPrime - kadiriDiskRCapPrime) *
                Real.log (kadiriDiskRCap / kadiriDiskRCapPrime)))) +
          (1 / Real.log (kadiriDiskRCap / kadiriDiskR))) * Real.log B := by
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  let W : ℂ :=
    riemannZeta.zeroes_sum (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1))
      (fun ρ ↦ (1 : ℂ) / (s - ρ))
  let E : ℂ :=
    ∑ z ∈ (finiteSetOfZeros_mono (r := kadiriDiskR) (f := kadiriDiskF a T)
        kadiriDiskR_lt_one finiteZeros).toFinset \
        (zeroes_rect_Ioo_Icc_window_finite T).toFinset.image (kadiriDiskCoord a T),
      (analyticOrderNatAt (kadiriDiskF a T) z : ℂ) /
        (s - kadiriDiskAffine a T z)
  let CFB : ℝ :=
    16 * kadiriDiskR ^ 2 / (kadiriDiskR - kadiriDiskRPrime) ^ 3 +
      1 / ((kadiriDiskRCap ^ 2 / kadiriDiskRCapPrime - kadiriDiskRCapPrime) *
        Real.log (kadiriDiskRCap / kadiriDiskRCapPrime))
  let CZ : ℝ := 1 / Real.log (kadiriDiskRCap / kadiriDiskR)
  have hfb :
      ‖logDeriv riemannZeta s - (W + E)‖ ≤
        (kadiriDiskLam a)⁻¹ * CFB * Real.log B := by
    simpa [s, W, E, CFB, mul_assoc] using
      (kadiriDisk_finalBound_window_correction
        (a := a) (T := T) (B := B) (σ := σ) ha hT hB
        (finiteZeros := finiteZeros) fz_bound hσ hζ)
  have hcorr : ‖E‖ ≤ CZ * Real.log B := by
    simpa [s, E, CZ] using
      (kadiriDisk_correction_norm_le_zerosBound
        (a := a) (T := T) (B := B) (σ := σ) ha hT hlarge
        (finiteZeros := finiteZeros) fz_bound)
  have hdecomp :
      -logDeriv riemannZeta s + W =
        -(logDeriv riemannZeta s - (W + E)) - E := by
    ring
  change ‖-logDeriv riemannZeta s + W‖ ≤
    ((kadiriDiskLam a)⁻¹ * CFB + CZ) * Real.log B
  calc
    ‖-logDeriv riemannZeta s + W‖
        = ‖-(logDeriv riemannZeta s - (W + E)) - E‖ := by rw [hdecomp]
    _ ≤ ‖-(logDeriv riemannZeta s - (W + E))‖ + ‖E‖ := norm_sub_le _ _
    _ = ‖logDeriv riemannZeta s - (W + E)‖ + ‖E‖ := by rw [norm_neg]
    _ ≤ (kadiriDiskLam a)⁻¹ * CFB * Real.log B + CZ * Real.log B :=
      add_le_add hfb hcorr
    _ = ((kadiriDiskLam a)⁻¹ * CFB + CZ) * Real.log B := by ring

/-- The combined horizontal-window estimate in the exact derivative-over-zeta
form used by `KadiriHorizontalPFRemainderLinearInput`; the disk finite-zero
hypothesis is discharged by `kadiriDisk_finiteZeros`. -/
theorem kadiriDisk_finalBound_window_deriv {a T B σ : ℝ} (ha : 0 ≤ a)
    (hT : kadiriDiskLam a < |T|)
    (hlarge : kadiriDiskLam a * kadiriDiskR + 1 < |T|) (hB : 1 < B)
    (fz_bound : ∀ z : ℂ, ‖z‖ ≤ kadiriDiskRCap → ‖kadiriDiskF a T z‖ ≤ B)
    (hσ : σ ∈ Set.Icc (-a) (1 + a))
    (hζ : riemannZeta ((σ : ℂ) + (T : ℂ) * I) ≠ 0) :
    let s : ℂ := (σ : ℂ) + (T : ℂ) * I
    ‖(-deriv riemannZeta s / riemannZeta s) +
        riemannZeta.zeroes_sum (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1))
          (fun ρ ↦ (1 : ℂ) / (s - ρ))‖
      ≤
        (((kadiriDiskLam a)⁻¹ *
            (16 * kadiriDiskR ^ 2 / (kadiriDiskR - kadiriDiskRPrime) ^ 3 +
              1 / ((kadiriDiskRCap ^ 2 / kadiriDiskRCapPrime - kadiriDiskRCapPrime) *
                Real.log (kadiriDiskRCap / kadiriDiskRCapPrime)))) +
          (1 / Real.log (kadiriDiskRCap / kadiriDiskR))) * Real.log B := by
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  have hfin := kadiriDisk_finiteZeros ha hT
  have hneg : (-deriv riemannZeta s / riemannZeta s) =
      -(deriv riemannZeta s / riemannZeta s) := by
    rw [neg_div]
  change ‖(-deriv riemannZeta s / riemannZeta s) +
      riemannZeta.zeroes_sum (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1))
        (fun ρ ↦ (1 : ℂ) / (s - ρ))‖ ≤ _
  rw [hneg]
  simpa [s, logDeriv_apply] using
    (kadiriDisk_finalBound_window_logDeriv
      (a := a) (T := T) (B := B) (σ := σ) ha hT hlarge hB
      (finiteZeros := hfin) fz_bound hσ hζ)

/-- The scaled-disk `FinalBound` assembly supplies the linear-in-log horizontal
partial-fraction input.  The local sup parameter is chosen as
`B_T = (|T|+2)^(e+1)` eventually: the polynomial sup bound is absorbed into this
power, and `log B_T = (e+1) log(|T|+2)`. -/
theorem kadiriHorizontalPFRemainderLinearInput_of_finalBound {a : ℝ} (ha : 0 ≤ a) :
    KadiriHorizontalPFRemainderLinearInput a := by
  obtain ⟨Cζ, e, hCζ, he0, hsup⟩ := kadiriDisk_fT_sup_bound ha
  let lamR : ℝ := kadiriDiskLam a * kadiriDiskRCap
  let K : ℝ := Cζ / kadiriDiskDenomConst
  let A : ℝ := max 1 (K * (1 + lamR) ^ e)
  let M : ℝ := e + 1
  let CFB : ℝ :=
    16 * kadiriDiskR ^ 2 / (kadiriDiskR - kadiriDiskRPrime) ^ 3 +
      1 / ((kadiriDiskRCap ^ 2 / kadiriDiskRCapPrime - kadiriDiskRCapPrime) *
        Real.log (kadiriDiskRCap / kadiriDiskRCapPrime))
  let CZ : ℝ := 1 / Real.log (kadiriDiskRCap / kadiriDiskR)
  let Ctot : ℝ := (kadiriDiskLam a)⁻¹ * CFB + CZ
  refine ⟨ha, Ctot * M, ?_, ?_⟩
  · have hCFB_nonneg : 0 ≤ CFB := by
      simpa [CFB] using kadiriDisk_finalBoundConst_pos.le
    have hCZ_nonneg : 0 ≤ CZ := by
      simpa [CZ] using kadiriDisk_zerosBoundConst_pos.le
    have hCtot_nonneg : 0 ≤ Ctot := by
      exact add_nonneg
        (mul_nonneg (inv_nonneg.mpr (kadiriDiskLam_pos ha).le) hCFB_nonneg)
        hCZ_nonneg
    have hM_nonneg : 0 ≤ M := by
      dsimp [M]
      linarith
    exact mul_nonneg hCtot_nonneg hM_nonneg
  · let N : ℝ :=
      max (Real.exp 1)
        (max (kadiriDiskLam a + 1) (max (lamR + 2) A))
    filter_upwards [Filter.eventually_ge_atTop N] with T hTge
    have hN_exp : Real.exp 1 ≤ N := by
      dsimp [N]
      exact le_max_left _ _
    have hN_lam : kadiriDiskLam a + 1 ≤ N := by
      dsimp [N]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hN_lamR : lamR + 2 ≤ N := by
      dsimp [N]
      exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    have hN_A : A ≤ N := by
      dsimp [N]
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
    have hT_nonneg : 0 ≤ T := by
      have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
      linarith
    have hAbsT : |T| = T := abs_of_nonneg hT_nonneg
    have hTe : Real.exp 1 ≤ |T| := by
      rw [hAbsT]
      exact le_trans hN_exp hTge
    have hcenter_pos : kadiriDiskLam a < |T| := by
      rw [hAbsT]
      linarith
    have hcenter_neg : kadiriDiskLam a < |-T| := by
      simpa [abs_neg] using hcenter_pos
    have hsup_height_pos : lamR + 1 ≤ |T| := by
      rw [hAbsT]
      linarith
    have hsup_height_neg : lamR + 1 ≤ |-T| := by
      simpa [abs_neg] using hsup_height_pos
    obtain ⟨hrp_pos, hrp_lt_r, hr_lt_Rp, hRp_lt_R, _hR_lt_one⟩ := kadiriDiskRadii_ordered
    have hR_lt_RCap : kadiriDiskR < kadiriDiskRCap := lt_trans hr_lt_Rp hRp_lt_R
    have hlamR_nonneg : 0 ≤ lamR := by
      dsimp [lamR]
      exact mul_nonneg (kadiriDiskLam_pos ha).le (by norm_num [kadiriDiskRCap])
    have hlarge_pos : kadiriDiskLam a * kadiriDiskR + 1 < |T| := by
      have hlt : kadiriDiskLam a * kadiriDiskR < lamR := by
        dsimp [lamR]
        exact mul_lt_mul_of_pos_left hR_lt_RCap (kadiriDiskLam_pos ha)
      rw [hAbsT]
      linarith
    have hlarge_neg : kadiriDiskLam a * kadiriDiskR + 1 < |-T| := by
      simpa [abs_neg] using hlarge_pos
    have hK_nonneg : 0 ≤ K := by
      exact div_nonneg hCζ kadiriDiskDenomConst_pos.le
    have hM_pos : 0 < M := by
      dsimp [M]
      linarith
    have hU_pos : 0 < |T| + 2 := by positivity
    have hU_gt_one : 1 < |T| + 2 := by
      have := abs_nonneg T
      linarith
    have hBT_gt : 1 < (|T| + 2) ^ M := Real.one_lt_rpow hU_gt_one hM_pos
    have hU_ge_A : A ≤ |T| + 2 := by
      rw [hAbsT]
      linarith
    have hpoly :
        K * (|T| + lamR + 2) ^ e ≤ (|T| + 2) ^ M := by
      let U : ℝ := |T| + 2
      have hU_pos' : 0 < U := by simpa [U] using hU_pos
      have hU_nonneg : 0 ≤ U := hU_pos'.le
      have hbase_const_nonneg : 0 ≤ 1 + lamR := by linarith
      have hP_nonneg : 0 ≤ |T| + lamR + 2 := by
        linarith [abs_nonneg T, hlamR_nonneg]
      have hP_le : |T| + lamR + 2 ≤ (1 + lamR) * U := by
        dsimp [U]
        nlinarith [hlamR_nonneg, abs_nonneg T]
      have hpow_le :
          (|T| + lamR + 2) ^ e ≤ ((1 + lamR) * U) ^ e :=
        Real.rpow_le_rpow hP_nonneg hP_le he0
      have hconst_le_A : K * (1 + lamR) ^ e ≤ A := by
        dsimp [A]
        exact le_max_right _ _
      have hUe_nonneg : 0 ≤ U ^ e := Real.rpow_nonneg hU_nonneg e
      calc
        K * (|T| + lamR + 2) ^ e
            ≤ K * ((1 + lamR) * U) ^ e :=
              mul_le_mul_of_nonneg_left hpow_le hK_nonneg
        _ = K * ((1 + lamR) ^ e * U ^ e) := by
              rw [Real.mul_rpow hbase_const_nonneg hU_nonneg]
        _ = (K * (1 + lamR) ^ e) * U ^ e := by ring
        _ ≤ A * U ^ e := mul_le_mul_of_nonneg_right hconst_le_A hUe_nonneg
        _ ≤ U * U ^ e := mul_le_mul_of_nonneg_right (by simpa [U] using hU_ge_A) hUe_nonneg
        _ = U ^ M := by
              dsimp [M]
              rw [Real.rpow_add hU_pos' e 1, Real.rpow_one]
              ring
        _ = (|T| + 2) ^ M := by rfl
    have hfz_bound_center :
        ∀ Tc : ℝ, |Tc| = |T| → lamR + 1 ≤ |Tc| →
          ∀ z : ℂ, ‖z‖ ≤ kadiriDiskRCap →
            ‖kadiriDiskF a Tc z‖ ≤ (|T| + 2) ^ M := by
      intro Tc hTc_abs hheight z hz
      have hsupz := hsup Tc (by simpa [lamR] using hheight) z hz
      have hsupz' :
          ‖kadiriDiskF a Tc z‖ ≤ K * (|T| + lamR + 2) ^ e := by
        simpa [K, lamR, hTc_abs] using hsupz
      exact hsupz'.trans hpoly
    have hfz_top :
        ∀ z : ℂ, ‖z‖ ≤ kadiriDiskRCap →
          ‖kadiriDiskF a T z‖ ≤ (|T| + 2) ^ M :=
      hfz_bound_center T rfl hsup_height_pos
    have hfz_bot :
        ∀ z : ℂ, ‖z‖ ≤ kadiriDiskRCap →
          ‖kadiriDiskF a (-T) z‖ ≤ (|T| + 2) ^ M :=
      hfz_bound_center (-T) (by rw [abs_neg]) hsup_height_neg
    refine ⟨hTe, ?_, ?_⟩
    · intro σ hσ hζ
      have hderiv :=
        kadiriDisk_finalBound_window_deriv (a := a) (T := T)
          (B := (|T| + 2) ^ M) (σ := σ) ha hcenter_pos hlarge_pos
          hBT_gt hfz_top hσ (by simpa [kadiriTopHorizontalPoint] using hζ)
      calc
        ‖(-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
              riemannZeta (kadiriTopHorizontalPoint T σ)) +
            riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
              (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))‖
            ≤ Ctot * Real.log ((|T| + 2) ^ M) := by
              simpa [kadiriTopHorizontalPoint, Ctot, CFB, CZ] using hderiv
        _ = (Ctot * M) * Real.log (|T| + 2) := by
              rw [Real.log_rpow hU_pos M]
              ring
    · intro σ hσ hζ
      have hderiv :=
        kadiriDisk_finalBound_window_deriv (a := a) (T := -T)
          (B := (|T| + 2) ^ M) (σ := σ) ha hcenter_neg hlarge_neg
          hBT_gt hfz_bot hσ (by simpa [kadiriBotHorizontalPoint] using hζ)
      calc
        ‖(-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
              riemannZeta (kadiriBotHorizontalPoint T σ)) +
            riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc ((-T) - 1) ((-T) + 1))
              (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))‖
            ≤ Ctot * Real.log ((|T| + 2) ^ M) := by
              simpa [kadiriBotHorizontalPoint, Ctot, CFB, CZ] using hderiv
        _ = (Ctot * M) * Real.log (|T| + 2) := by
              rw [Real.log_rpow hU_pos M]
              ring

/-- The squared-log partial-fraction remainder follows from the discharged
linear input. -/
theorem kadiriHorizontalPartialFractionRemainderBound_of_finalBound {a : ℝ} (ha : 0 ≤ a) :
    KadiriHorizontalPartialFractionRemainderBound a :=
  kadiriHorizontalPartialFractionRemainderBound_of_linearInput
    (kadiriHorizontalPFRemainderLinearInput_of_finalBound ha)

end Kadiri
