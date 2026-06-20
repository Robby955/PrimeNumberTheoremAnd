import PrimeNumberTheoremAnd.IEANTN.KadiriFinalBoundAssembly

/-!
# Canonical horizontal PV package surface

This sidecar supplies canonical total horizontal PV values that agree with the
ordinary horizontal integrals at non-zero ordinates. At zero ordinates the value
is set to zero; the package only requires the no-zero bridge plus an atTop bound,
so the remaining analytic work is exactly the bound for these canonical values.
-/

namespace Kadiri

open MeasureTheory Complex Filter
open scoped Topology

noncomputable section

/-- Canonical top horizontal PV value: ordinary integral at non-zero ordinates,
zero at zero ordinates. -/
noncomputable def kadiriTopHorizontalPVCanonical (φ : ℝ → ℂ) (a : ℝ) (T : ℝ) : ℂ :=
  by
    classical
    exact
      if KadiriNoZeroOrdinate T then
        kadiriTopHorizontalIntegral φ a T
      else
        0

/-- Canonical bottom horizontal PV value: ordinary integral at non-zero ordinates
for the bottom ordinate `-T`, zero otherwise. -/
noncomputable def kadiriBotHorizontalPVCanonical (φ : ℝ → ℂ) (a : ℝ) (T : ℝ) : ℂ :=
  by
    classical
    exact
      if KadiriNoZeroOrdinate (-T) then
        kadiriBotHorizontalIntegral φ a T
      else
        0

/-- The canonical PV values satisfy the no-zero ordinary-integral bridge by
definition. -/
theorem kadiriHorizontalPVCanonical_noZeroBridge {φ : ℝ → ℂ} {a : ℝ} :
    KadiriZetaHorizontalPVNoZeroBridge φ a
      (kadiriTopHorizontalPVCanonical φ a)
      (kadiriBotHorizontalPVCanonical φ a) := by
  classical
  constructor
  · intro T hT
    simp [kadiriTopHorizontalPVCanonical, hT]
  · intro T hT
    simp [kadiriBotHorizontalPVCanonical, hT]

/-- The legacy quantitative all-height horizontal bound gives the corresponding
bare `KadiriHorizontalPVBound` for the ordinary horizontal integrals. This is
only an adapter for an already-quantitative input; it does not derive the
corrected PV estimate from the partial-fraction remainder route. -/
theorem kadiriHorizontalIntegralPVBound_of_atTopBound {φ : ℝ → ℂ} {a : ℝ}
    (hB : KadiriHorizontalAtTopBound φ a) :
    KadiriHorizontalPVBound
      (fun T : ℝ => kadiriTopHorizontalIntegral φ a T)
      (fun T : ℝ => kadiriBotHorizontalIntegral φ a T) := by
  rcases hB with ⟨C, hC, k, hB⟩
  let prefactor : ℂ := 1 / (2 * (Real.pi : ℂ) * I)
  let segment : Set ℝ := Set.Ioo (-a) (1 + a)
  let D : ℝ := ‖prefactor‖ * volume.real segment
  have hD : 0 ≤ D := by
    positivity
  have hmeasure : volume segment < ⊤ := by
    simp [segment, Real.volume_Ioo]
  refine ⟨D * C, mul_nonneg hD hC, k, ?_⟩
  filter_upwards [hB] with T hT
  rcases hT with ⟨hT_abs, htop, hbot⟩
  refine ⟨hT_abs, ?_, ?_⟩
  · have hset :
        ‖∫ σ in segment,
            (-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
                riemannZeta (kadiriTopHorizontalPoint T σ)) *
              kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))‖
          ≤ (C * (Real.log |T|) ^ k / |T|) * volume.real segment := by
      refine MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (μ := volume) (s := segment)
        (f := fun σ : ℝ =>
          (-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
              riemannZeta (kadiriTopHorizontalPoint T σ)) *
            kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)))
        hmeasure ?_
      intro σ hσ
      exact htop σ (Set.Ioo_subset_Icc_self hσ)
    calc
      ‖kadiriTopHorizontalIntegral φ a T‖
          = ‖prefactor *
              ∫ σ in segment,
                (-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
                    riemannZeta (kadiriTopHorizontalPoint T σ)) *
                  kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))‖ := by
              simp [kadiriTopHorizontalIntegral, prefactor, segment]
      _ = ‖prefactor‖ *
            ‖∫ σ in segment,
              (-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
                  riemannZeta (kadiriTopHorizontalPoint T σ)) *
                kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))‖ := by
              rw [norm_mul]
      _ ≤ ‖prefactor‖ * ((C * (Real.log |T|) ^ k / |T|) * volume.real segment) :=
              mul_le_mul_of_nonneg_left hset (norm_nonneg _)
      _ = (D * C) * (Real.log |T|) ^ k / |T| := by
              simp [D]
              ring
  · have hset :
        ‖∫ σ in segment,
            (-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
                riemannZeta (kadiriBotHorizontalPoint T σ)) *
              kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))‖
          ≤ (C * (Real.log |T|) ^ k / |T|) * volume.real segment := by
      refine MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (μ := volume) (s := segment)
        (f := fun σ : ℝ =>
          (-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
              riemannZeta (kadiriBotHorizontalPoint T σ)) *
            kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)))
        hmeasure ?_
      intro σ hσ
      exact hbot σ (Set.Ioo_subset_Icc_self hσ)
    calc
      ‖kadiriBotHorizontalIntegral φ a T‖
          = ‖prefactor *
              ∫ σ in segment,
                (-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
                    riemannZeta (kadiriBotHorizontalPoint T σ)) *
                  kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))‖ := by
              simp [kadiriBotHorizontalIntegral, prefactor, segment]
      _ = ‖prefactor‖ *
            ‖∫ σ in segment,
              (-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
                  riemannZeta (kadiriBotHorizontalPoint T σ)) *
                kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))‖ := by
              rw [norm_mul]
      _ ≤ ‖prefactor‖ * ((C * (Real.log |T|) ^ k / |T|) * volume.real segment) :=
              mul_le_mul_of_nonneg_left hset (norm_nonneg _)
      _ = (D * C) * (Real.log |T|) ^ k / |T| := by
              simp [D]
              ring

/-- Passing from ordinary horizontal-integral bounds to canonical PV bounds is
lossless: at zero ordinates the canonical value is `0`, and elsewhere it is the
ordinary integral. -/
theorem kadiriHorizontalPVCanonical_bound_of_integral_bound {φ : ℝ → ℂ} {a : ℝ}
    (hbound : KadiriHorizontalPVBound
      (fun T : ℝ => kadiriTopHorizontalIntegral φ a T)
      (fun T : ℝ => kadiriBotHorizontalIntegral φ a T)) :
    KadiriHorizontalPVBound
      (kadiriTopHorizontalPVCanonical φ a)
      (kadiriBotHorizontalPVCanonical φ a) := by
  rcases hbound with ⟨C, hC, k, hbound⟩
  refine ⟨C, hC, k, ?_⟩
  filter_upwards [hbound] with T hT
  rcases hT with ⟨hT_abs, htop, hbot⟩
  have htop_nonneg : 0 ≤ C * (Real.log |T|) ^ k / |T| :=
    le_trans (norm_nonneg _) htop
  have hbot_nonneg : 0 ≤ C * (Real.log |T|) ^ k / |T| :=
    le_trans (norm_nonneg _) hbot
  refine ⟨hT_abs, ?_, ?_⟩
  · by_cases hNo : KadiriNoZeroOrdinate T
    · simpa [kadiriTopHorizontalPVCanonical, hNo] using htop
    · simpa [kadiriTopHorizontalPVCanonical, hNo] using htop_nonneg
  · by_cases hNo : KadiriNoZeroOrdinate (-T)
    · simpa [kadiriBotHorizontalPVCanonical, hNo] using hbot
    · simpa [kadiriBotHorizontalPVCanonical, hNo] using hbot_nonneg

/-- A legacy all-height bound supplies the canonical PV bound. The corrected
PF/PV route should eventually replace the `KadiriHorizontalAtTopBound`
hypothesis with the partial-fraction remainder plus `φ` decay inputs. -/
theorem kadiriHorizontalPVCanonical_bound_of_atTopBound {φ : ℝ → ℂ} {a : ℝ}
    (hB : KadiriHorizontalAtTopBound φ a) :
    KadiriHorizontalPVBound
      (kadiriTopHorizontalPVCanonical φ a)
      (kadiriBotHorizontalPVCanonical φ a) :=
  kadiriHorizontalPVCanonical_bound_of_integral_bound
    (kadiriHorizontalIntegralPVBound_of_atTopBound hB)

/-- The pole-subtracted PF residual integral on the top horizontal segment. -/
noncomputable def kadiriTopHorizontalPFResidualIntegral
    (φ : ℝ → ℂ) (a T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    ∫ σ in Set.Ioo (-a) (1 + a),
      (((-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
            riemannZeta (kadiriTopHorizontalPoint T σ)) +
          riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
            (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))) *
        kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)))

/-- The pole-subtracted PF residual integral on the bottom horizontal segment. -/
noncomputable def kadiriBotHorizontalPFResidualIntegral
    (φ : ℝ → ℂ) (a T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    ∫ σ in Set.Ioo (-a) (1 + a),
      (((-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
            riemannZeta (kadiriBotHorizontalPoint T σ)) +
          riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc ((-T) - 1) ((-T) + 1))
            (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))) *
        kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)))

/-- The finite zero-window pole contribution on the top horizontal segment. -/
noncomputable def kadiriTopHorizontalZeroWindowPVIntegral
    (φ : ℝ → ℂ) (a T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    ∫ σ in Set.Ioo (-a) (1 + a),
      (riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
        (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))) *
        kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))

/-- The finite zero-window pole contribution on the bottom horizontal segment. -/
noncomputable def kadiriBotHorizontalZeroWindowPVIntegral
    (φ : ℝ → ℂ) (a T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    ∫ σ in Set.Ioo (-a) (1 + a),
      (riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc ((-T) - 1) ((-T) + 1))
        (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))) *
        kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))

/-- The top single-zero finite-window PV contribution, without the zero order
weight. -/
noncomputable def kadiriTopHorizontalSingleZeroWindowPVIntegral
    (φ : ℝ → ℂ) (a T : ℝ) (ρ : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    ∫ σ in Set.Ioo (-a) (1 + a),
      ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
        kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))

/-- The bottom single-zero finite-window PV contribution, without the zero order
weight. -/
noncomputable def kadiriBotHorizontalSingleZeroWindowPVIntegral
    (φ : ℝ → ℂ) (a T : ℝ) (ρ : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    ∫ σ in Set.Ioo (-a) (1 + a),
      ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
        kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))

/-- The scalar Cauchy integral underlying one top projected-constant
single-zero contribution. -/
noncomputable def kadiriTopHorizontalSingleZeroWindowPVScalarIntegral
    (a T : ℝ) (ρ : ℂ) : ℂ :=
  ∫ σ in Set.Ioo (-a) (1 + a),
    (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)

/-- The scalar Cauchy integral underlying one bottom projected-constant
single-zero contribution. -/
noncomputable def kadiriBotHorizontalSingleZeroWindowPVScalarIntegral
    (a T : ℝ) (ρ : ℂ) : ℂ :=
  ∫ σ in Set.Ioo (-a) (1 + a),
    (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)

private theorem kadiriHorizontalScalarResolventIntegral_eq_log_sub
    {u v β δ : ℝ} (huv : u ≤ v) (hδ : δ ≠ 0) :
    ∫ σ in Set.Ioo u v,
        (1 : ℂ) / (((σ - β : ℝ) : ℂ) + (δ : ℂ) * I) =
      Complex.log (((v - β : ℝ) : ℂ) + (δ : ℂ) * I) -
        Complex.log (((u - β : ℝ) : ℂ) + (δ : ℂ) * I) := by
  let F : ℝ → ℂ := fun x =>
    Complex.log (((x - β : ℝ) : ℂ) + (δ : ℂ) * I)
  let f : ℝ → ℂ := fun x =>
    (1 : ℂ) / (((x - β : ℝ) : ℂ) + (δ : ℂ) * I)
  have hslit : ∀ x : ℝ,
      (((x - β : ℝ) : ℂ) + (δ : ℂ) * I) ∈ Complex.slitPlane := by
    intro x
    rw [Complex.mem_slitPlane_iff]
    right
    simpa using hδ
  have hden_ne : ∀ x : ℝ,
      (((x - β : ℝ) : ℂ) + (δ : ℂ) * I) ≠ 0 := by
    intro x
    exact Complex.slitPlane_ne_zero (hslit x)
  have hderiv : ∀ x ∈ Set.uIcc u v, HasDerivAt F (f x) x := by
    intro x _hx
    have hinner :
        HasDerivAt
          (fun y : ℝ => (((y - β : ℝ) : ℂ) + (δ : ℂ) * I))
          (1 : ℂ) x := by
      have hbase :
          HasDerivAt (fun y : ℝ => (y : ℂ) - (β : ℂ)) (1 : ℂ) x :=
        (Complex.ofRealCLM.hasDerivAt (x := x)).sub_const (β : ℂ)
      simpa [sub_eq_add_neg] using hbase.add_const ((δ : ℂ) * I)
    have hlog := Complex.hasDerivAt_log (hslit x)
    have hcomp := hlog.comp x hinner
    simp only [F, f, div_eq_mul_inv]
    convert hcomp using 1 <;>
      first
        | rfl
        | (funext w; rfl)
        | (push_cast; ring)
  have hcont : ContinuousOn f (Set.uIcc u v) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact continuousOn_const
    · fun_prop
    · intro x _hx
      exact hden_ne x
  have hint : IntervalIntegrable f volume u v :=
    hcont.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le huv]
  simpa [F, f] using hftc

theorem kadiriTopHorizontalSingleZeroWindowPVScalarIntegral_eq_log_sub
    {a T : ℝ} {ρ : ℂ} (ha : 0 ≤ a) (hδ : T - ρ.im ≠ 0) :
    kadiriTopHorizontalSingleZeroWindowPVScalarIntegral a T ρ =
      Complex.log ((((1 + a) - ρ.re : ℝ) : ℂ) + ((T - ρ.im : ℝ) : ℂ) * I) -
        Complex.log ((((-a) - ρ.re : ℝ) : ℂ) + ((T - ρ.im : ℝ) : ℂ) * I) := by
  have hle : -a ≤ 1 + a := by linarith
  calc
    kadiriTopHorizontalSingleZeroWindowPVScalarIntegral a T ρ
        = ∫ σ in Set.Ioo (-a) (1 + a),
            (1 : ℂ) / (((σ - ρ.re : ℝ) : ℂ) + ((T - ρ.im : ℝ) : ℂ) * I) := by
          unfold kadiriTopHorizontalSingleZeroWindowPVScalarIntegral
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with σ
          congr 1
          apply Complex.ext <;> simp [kadiriTopHorizontalPoint]
    _ = Complex.log ((((1 + a) - ρ.re : ℝ) : ℂ) + ((T - ρ.im : ℝ) : ℂ) * I) -
          Complex.log ((((-a) - ρ.re : ℝ) : ℂ) + ((T - ρ.im : ℝ) : ℂ) * I) :=
          kadiriHorizontalScalarResolventIntegral_eq_log_sub hle hδ

theorem kadiriBotHorizontalSingleZeroWindowPVScalarIntegral_eq_log_sub
    {a T : ℝ} {ρ : ℂ} (ha : 0 ≤ a) (hδ : -T - ρ.im ≠ 0) :
    kadiriBotHorizontalSingleZeroWindowPVScalarIntegral a T ρ =
      Complex.log ((((1 + a) - ρ.re : ℝ) : ℂ) + ((-T - ρ.im : ℝ) : ℂ) * I) -
        Complex.log ((((-a) - ρ.re : ℝ) : ℂ) + ((-T - ρ.im : ℝ) : ℂ) * I) := by
  have hle : -a ≤ 1 + a := by linarith
  calc
    kadiriBotHorizontalSingleZeroWindowPVScalarIntegral a T ρ
        = ∫ σ in Set.Ioo (-a) (1 + a),
            (1 : ℂ) / (((σ - ρ.re : ℝ) : ℂ) + ((-T - ρ.im : ℝ) : ℂ) * I) := by
          unfold kadiriBotHorizontalSingleZeroWindowPVScalarIntegral
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with σ
          congr 1
          apply Complex.ext <;> simp [kadiriBotHorizontalPoint]
    _ = Complex.log ((((1 + a) - ρ.re : ℝ) : ℂ) + ((-T - ρ.im : ℝ) : ℂ) * I) -
          Complex.log ((((-a) - ρ.re : ℝ) : ℂ) + ((-T - ρ.im : ℝ) : ℂ) * I) :=
          kadiriHorizontalScalarResolventIntegral_eq_log_sub hle hδ

private theorem kadiriScalarLogSub_re_eq {p q δ : ℝ}
    (hp : 0 < p) (hq : 0 < q) :
    (Complex.log ((q : ℂ) + (δ : ℂ) * I) -
        Complex.log ((-p : ℝ) + (δ : ℂ) * I)).re =
      (1 / 2) * Real.log ((q ^ 2 + δ ^ 2) / (p ^ 2 + δ ^ 2)) := by
  let zq : ℂ := (q : ℂ) + (δ : ℂ) * I
  let zp : ℂ := (-p : ℝ) + (δ : ℂ) * I
  have hq_nonneg : 0 ≤ q ^ 2 + δ ^ 2 := add_nonneg (sq_nonneg q) (sq_nonneg δ)
  have hp_nonneg : 0 ≤ p ^ 2 + δ ^ 2 := add_nonneg (sq_nonneg p) (sq_nonneg δ)
  have hq_pos : 0 < q ^ 2 + δ ^ 2 := by nlinarith [sq_pos_of_pos hq, sq_nonneg δ]
  have hp_pos : 0 < p ^ 2 + δ ^ 2 := by nlinarith [sq_pos_of_pos hp, sq_nonneg δ]
  have hzq_norm : ‖zq‖ = Real.sqrt (q ^ 2 + δ ^ 2) := by
    rw [← sq_eq_sq₀ (norm_nonneg zq) (Real.sqrt_nonneg _)]
    rw [Complex.sq_norm, Real.sq_sqrt hq_nonneg]
    simp [zq, Complex.normSq_add_mul_I]
  have hzp_norm : ‖zp‖ = Real.sqrt (p ^ 2 + δ ^ 2) := by
    rw [← sq_eq_sq₀ (norm_nonneg zp) (Real.sqrt_nonneg _)]
    rw [Complex.sq_norm, Real.sq_sqrt hp_nonneg]
    change Complex.normSq (((-p : ℝ) : ℂ) + (δ : ℂ) * I) = p ^ 2 + δ ^ 2
    rw [Complex.normSq_add_mul_I]
    ring
  calc
    (Complex.log ((q : ℂ) + (δ : ℂ) * I) -
        Complex.log ((-p : ℝ) + (δ : ℂ) * I)).re
        = Real.log ‖zq‖ - Real.log ‖zp‖ := by
            simp [zq, zp, Complex.log_re]
    _ = Real.log (q ^ 2 + δ ^ 2) / 2 -
          Real.log (p ^ 2 + δ ^ 2) / 2 := by
            rw [hzq_norm, hzp_norm, Real.log_sqrt hq_nonneg,
              Real.log_sqrt hp_nonneg]
    _ = (1 / 2) * Real.log ((q ^ 2 + δ ^ 2) / (p ^ 2 + δ ^ 2)) := by
            rw [Real.log_div hq_pos.ne' hp_pos.ne']
            ring

private theorem kadiriScalarLogSub_norm_le {a p q δ : ℝ} (ha : 0 < a)
    (hp_lo : a ≤ p) (hp_hi : p ≤ 1 + a) (hq_lo : a ≤ q) (hq_hi : q ≤ 1 + a) :
    ‖Complex.log ((q : ℂ) + (δ : ℂ) * I) -
        Complex.log ((-p : ℝ) + (δ : ℂ) * I)‖
      ≤ 2 * Real.pi + Real.log ((1 + a) / a) := by
  let zq : ℂ := (q : ℂ) + (δ : ℂ) * I
  let zp : ℂ := (-p : ℝ) + (δ : ℂ) * I
  let z : ℂ := Complex.log zq - Complex.log zp
  have hp : 0 < p := lt_of_lt_of_le ha hp_lo
  have hq : 0 < q := lt_of_lt_of_le ha hq_lo
  have hre : |z.re| ≤ Real.log ((1 + a) / a) := by
    have hreal := kadiriKernelReAbsLe ha hp_lo hp_hi hq_lo hq_hi (δ := δ)
    have hz_re :
        z.re = (1 / 2) * Real.log ((q ^ 2 + δ ^ 2) / (p ^ 2 + δ ^ 2)) := by
      simpa [z, zq, zp] using
        kadiriScalarLogSub_re_eq (p := p) (q := q) (δ := δ) hp hq
    rw [hz_re]
    exact hreal
  have him : |z.im| ≤ 2 * Real.pi := by
    have harg := (Complex.abs_arg_sub_arg_lt zq zp).le
    have him_eq : |z.im| = |Complex.arg zq - Complex.arg zp| := by
      simp [z, zq, zp, Complex.log_im]
    simpa [him_eq] using harg
  calc
    ‖Complex.log ((q : ℂ) + (δ : ℂ) * I) -
        Complex.log ((-p : ℝ) + (δ : ℂ) * I)‖
        = ‖z‖ := by simp [z, zq, zp]
    _ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ Real.log ((1 + a) / a) + 2 * Real.pi := add_le_add hre him
    _ = 2 * Real.pi + Real.log ((1 + a) / a) := by ring

/-- The horizontal-projection constant part of a top single-zero PV contribution.
The remaining variation term is where the `Φ'` bound is used. -/
noncomputable def kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral
    (φ : ℝ → ℂ) (a T : ℝ) (ρ : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    ∫ σ in Set.Ioo (-a) (1 + a),
      ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
        kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re))

/-- The `Φ`-variation part of a top single-zero PV contribution. -/
noncomputable def kadiriTopHorizontalSingleZeroWindowPVVariationIntegral
    (φ : ℝ → ℂ) (a T : ℝ) (ρ : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    ∫ σ in Set.Ioo (-a) (1 + a),
      ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
        (kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)) -
          kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re)))

/-- The horizontal-projection constant part of a bottom single-zero PV contribution. -/
noncomputable def kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral
    (φ : ℝ → ℂ) (a T : ℝ) (ρ : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    ∫ σ in Set.Ioo (-a) (1 + a),
      ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
        kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re))

/-- The `Φ`-variation part of a bottom single-zero PV contribution. -/
noncomputable def kadiriBotHorizontalSingleZeroWindowPVVariationIntegral
    (φ : ℝ → ℂ) (a T : ℝ) (ρ : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    ∫ σ in Set.Ioo (-a) (1 + a),
      ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
        (kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)) -
          kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re)))

/-- The top projected-constant term factors as the scalar Cauchy integral times
the projected `Φ` value. -/
theorem kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral_eq_scalar
    {φ : ℝ → ℂ} {a T : ℝ} {ρ : ℂ} :
    kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ =
      (1 / (2 * (Real.pi : ℂ) * I)) *
        kadiriTopHorizontalSingleZeroWindowPVScalarIntegral a T ρ *
        kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re)) := by
  unfold kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral
  unfold kadiriTopHorizontalSingleZeroWindowPVScalarIntegral
  rw [MeasureTheory.integral_mul_const]
  ring

/-- The bottom projected-constant term factors as the scalar Cauchy integral
times the projected `Φ` value. -/
theorem kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral_eq_scalar
    {φ : ℝ → ℂ} {a T : ℝ} {ρ : ℂ} :
    kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ =
      (1 / (2 * (Real.pi : ℂ) * I)) *
        kadiriBotHorizontalSingleZeroWindowPVScalarIntegral a T ρ *
        kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re)) := by
  unfold kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral
  unfold kadiriBotHorizontalSingleZeroWindowPVScalarIntegral
  rw [MeasureTheory.integral_mul_const]
  ring

/-- A scalar Cauchy-integral norm bound plus a projected `Φ` bound controls the
top projected-constant term. -/
theorem kadiriTopHorizontalSingleZeroWindowPVProjectedConstant_norm_le_of_scalar
    {φ : ℝ → ℂ} {a T : ℝ} {ρ : ℂ} {K A : ℝ}
    (hscalar : ‖kadiriTopHorizontalSingleZeroWindowPVScalarIntegral a T ρ‖ ≤ K)
    (hPhi :
      ‖kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re))‖ ≤ A / |T|) :
    ‖kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ‖
      ≤ (‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ * K * A) / |T| := by
  let prefactor : ℂ := 1 / (2 * (Real.pi : ℂ) * I)
  have hpref_nonneg : 0 ≤ ‖prefactor‖ := norm_nonneg _
  have hK : 0 ≤ K := le_trans (norm_nonneg _) hscalar
  have hscalar_step :
      ‖prefactor‖ * ‖kadiriTopHorizontalSingleZeroWindowPVScalarIntegral a T ρ‖
        ≤ ‖prefactor‖ * K :=
    mul_le_mul_of_nonneg_left hscalar hpref_nonneg
  have hcoeff_nonneg : 0 ≤ ‖prefactor‖ * K := mul_nonneg hpref_nonneg hK
  calc
    ‖kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ‖
        = ‖prefactor * kadiriTopHorizontalSingleZeroWindowPVScalarIntegral a T ρ *
            kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re))‖ := by
          rw [kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral_eq_scalar]
    _ = ‖prefactor‖ *
          ‖kadiriTopHorizontalSingleZeroWindowPVScalarIntegral a T ρ‖ *
          ‖kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re))‖ := by
          rw [norm_mul, norm_mul]
    _ ≤ (‖prefactor‖ * K) *
          ‖kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re))‖ := by
          exact mul_le_mul_of_nonneg_right hscalar_step (norm_nonneg _)
    _ ≤ (‖prefactor‖ * K) * (A / |T|) := by
          exact mul_le_mul_of_nonneg_left hPhi hcoeff_nonneg
    _ = (‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ * K * A) / |T| := by
          dsimp [prefactor]
          ring

/-- A scalar Cauchy-integral norm bound plus a projected `Φ` bound controls the
bottom projected-constant term. -/
theorem kadiriBotHorizontalSingleZeroWindowPVProjectedConstant_norm_le_of_scalar
    {φ : ℝ → ℂ} {a T : ℝ} {ρ : ℂ} {K A : ℝ}
    (hscalar : ‖kadiriBotHorizontalSingleZeroWindowPVScalarIntegral a T ρ‖ ≤ K)
    (hPhi :
      ‖kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re))‖ ≤ A / |T|) :
    ‖kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ‖
      ≤ (‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ * K * A) / |T| := by
  let prefactor : ℂ := 1 / (2 * (Real.pi : ℂ) * I)
  have hpref_nonneg : 0 ≤ ‖prefactor‖ := norm_nonneg _
  have hK : 0 ≤ K := le_trans (norm_nonneg _) hscalar
  have hscalar_step :
      ‖prefactor‖ * ‖kadiriBotHorizontalSingleZeroWindowPVScalarIntegral a T ρ‖
        ≤ ‖prefactor‖ * K :=
    mul_le_mul_of_nonneg_left hscalar hpref_nonneg
  have hcoeff_nonneg : 0 ≤ ‖prefactor‖ * K := mul_nonneg hpref_nonneg hK
  calc
    ‖kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ‖
        = ‖prefactor * kadiriBotHorizontalSingleZeroWindowPVScalarIntegral a T ρ *
            kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re))‖ := by
          rw [kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral_eq_scalar]
    _ = ‖prefactor‖ *
          ‖kadiriBotHorizontalSingleZeroWindowPVScalarIntegral a T ρ‖ *
          ‖kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re))‖ := by
          rw [norm_mul, norm_mul]
    _ ≤ (‖prefactor‖ * K) *
          ‖kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re))‖ := by
          exact mul_le_mul_of_nonneg_right hscalar_step (norm_nonneg _)
    _ ≤ (‖prefactor‖ * K) * (A / |T|) := by
          exact mul_le_mul_of_nonneg_left hPhi hcoeff_nonneg
    _ = (‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ * K * A) / |T| := by
          dsimp [prefactor]
          ring

/-- Algebraic split of one top weighted single-pole integral into the scalar
kernel part and the `Φ`-variation part. -/
theorem kadiriTopHorizontalSingleZeroWindowPVIntegral_eq_projectedConst_add_variation
    {φ : ℝ → ℂ} {a T : ℝ} {ρ : ℂ}
    (hconst : Integrable (fun σ : ℝ =>
      ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
        kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re)))
      (volume.restrict (Set.Ioo (-a) (1 + a))))
    (hvariation : Integrable (fun σ : ℝ =>
      ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
        (kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)) -
          kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re))))
      (volume.restrict (Set.Ioo (-a) (1 + a)))) :
    kadiriTopHorizontalSingleZeroWindowPVIntegral φ a T ρ =
      kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ +
        kadiriTopHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ := by
  have hsplit :
      (∫ σ in Set.Ioo (-a) (1 + a),
        ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
          kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))) =
        (∫ σ in Set.Ioo (-a) (1 + a),
          ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
            kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re))) +
        (∫ σ in Set.Ioo (-a) (1 + a),
          ((1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ)) *
            (kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)) -
              kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T ρ.re)))) := by
    rw [← MeasureTheory.integral_add hconst hvariation]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with σ
    ring
  unfold kadiriTopHorizontalSingleZeroWindowPVIntegral
  unfold kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral
  unfold kadiriTopHorizontalSingleZeroWindowPVVariationIntegral
  rw [hsplit]
  ring

/-- Algebraic split of one bottom weighted single-pole integral into the scalar
kernel part and the `Φ`-variation part. -/
theorem kadiriBotHorizontalSingleZeroWindowPVIntegral_eq_projectedConst_add_variation
    {φ : ℝ → ℂ} {a T : ℝ} {ρ : ℂ}
    (hconst : Integrable (fun σ : ℝ =>
      ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
        kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re)))
      (volume.restrict (Set.Ioo (-a) (1 + a))))
    (hvariation : Integrable (fun σ : ℝ =>
      ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
        (kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)) -
          kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re))))
      (volume.restrict (Set.Ioo (-a) (1 + a)))) :
    kadiriBotHorizontalSingleZeroWindowPVIntegral φ a T ρ =
      kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ +
        kadiriBotHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ := by
  have hsplit :
      (∫ σ in Set.Ioo (-a) (1 + a),
        ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
          kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))) =
        (∫ σ in Set.Ioo (-a) (1 + a),
          ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
            kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re))) +
        (∫ σ in Set.Ioo (-a) (1 + a),
          ((1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ)) *
            (kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)) -
              kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T ρ.re)))) := by
    rw [← MeasureTheory.integral_add hconst hvariation]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with σ
    ring
  unfold kadiriBotHorizontalSingleZeroWindowPVIntegral
  unfold kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral
  unfold kadiriBotHorizontalSingleZeroWindowPVVariationIntegral
  rw [hsplit]
  ring

/-- Integrability needed to split the pole-subtracted residual integral into its
log-derivative and finite zero-window pieces. This is the ordinary-integral
bridge side of the finite zero-window PV estimate. -/
def KadiriHorizontalZeroWindowPVIntegrability (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  ∀ᶠ T : ℝ in Filter.atTop,
    (KadiriNoZeroOrdinate T →
      IntegrableOn (fun σ : ℝ =>
        (-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
            riemannZeta (kadiriTopHorizontalPoint T σ)) *
          kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)))
        (Set.Ioo (-a) (1 + a)) ∧
      IntegrableOn (fun σ : ℝ =>
        (riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
          (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))) *
          kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)))
        (Set.Ioo (-a) (1 + a))) ∧
    (KadiriNoZeroOrdinate (-T) →
      IntegrableOn (fun σ : ℝ =>
        (-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
            riemannZeta (kadiriBotHorizontalPoint T σ)) *
          kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)))
        (Set.Ioo (-a) (1 + a)) ∧
      IntegrableOn (fun σ : ℝ =>
        (riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc ((-T) - 1) ((-T) + 1))
          (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))) *
          kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)))
        (Set.Ioo (-a) (1 + a)))

/-- Order-counting input for the finite unit-height zero windows used on the
two horizontal segments.  It is independent of `φ`; the bottom window is indexed
by the ordinate `-T`. -/
def KadiriHorizontalZeroWindowOrderSumBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ,
    ∀ᶠ T : ℝ in Filter.atTop,
      Real.exp 1 ≤ |T| ∧
        (∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
          ((riemannZeta.order ρ : ℤ) : ℝ)) ≤ C * (Real.log |T|) ^ k ∧
        (∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset,
          ((riemannZeta.order ρ : ℤ) : ℝ)) ≤ C * (Real.log |T|) ^ k

private theorem kadiri_log_abs_add_two_le_two_log_abs {T : ℝ} (hT : 2 ≤ |T|) :
    Real.log (|T| + 2) ≤ 2 * Real.log |T| := by
  have h_abs_pos : 0 < |T| := by linarith
  have h_add_pos : 0 < |T| + 2 := by linarith
  have h_sq : |T| + 2 ≤ |T| ^ (2 : ℕ) := by
    nlinarith [hT]
  calc
    Real.log (|T| + 2) ≤ Real.log (|T| ^ (2 : ℕ)) :=
      Real.log_le_log h_add_pos h_sq
    _ = 2 * Real.log |T| := by
      rw [Real.log_pow]
      norm_num

private theorem kadiriWindow_order_sum_le_zerosBound {a T B : ℝ} (ha : 0 ≤ a)
    (hT : kadiriDiskLam a < |T|)
    (fz_bound : ∀ z : ℂ, ‖z‖ ≤ kadiriDiskRCap → ‖kadiriDiskF a T z‖ ≤ B) :
    (∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
        ((riemannZeta.order ρ : ℤ) : ℝ))
      ≤ (1 / Real.log (kadiriDiskRCap / kadiriDiskR)) * Real.log B := by
  classical
  let W := (zeroes_rect_Ioo_Icc_window_finite T).toFinset
  let finiteZeros := kadiriDisk_finiteZeros ha hT
  let K :=
    (finiteSetOfZeros_mono (r := kadiriDiskR) (f := kadiriDiskF a T)
      kadiriDiskR_lt_one finiteZeros).toFinset
  let coord := kadiriDiskCoord a T
  have hden : riemannZeta ((kadiriDiskC : ℂ) + (T : ℂ) * I) ≠ 0 :=
    kadiriDisk_denom_ne_zero T
  have hsum_eq :
      (∑ ρ ∈ W, ((riemannZeta.order ρ : ℤ) : ℝ)) =
        ∑ ω ∈ W.image coord,
          ((analyticOrderNatAt (kadiriDiskF a T) ω : ℕ) : ℝ) := by
    have himage :
        (∑ ω ∈ W.image coord,
            ((analyticOrderNatAt (kadiriDiskF a T) ω : ℕ) : ℝ)) =
          ∑ ρ ∈ W,
            ((analyticOrderNatAt (kadiriDiskF a T) (coord ρ) : ℕ) : ℝ) := by
      rw [Finset.sum_image]
      intro ρ hρ η hη hcoord
      exact kadiriDiskCoord_injective ha T hcoord
    rw [himage]
    refine Finset.sum_congr rfl ?_
    intro ρ hρ
    have hρmem :
        ρ ∈ riemannZeta.zeroes_rect (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1)) :=
      (zeroes_rect_Ioo_Icc_window_finite T).mem_toFinset.mp (by simpa [W] using hρ)
    have horderZ := kadiriDiskF_order_transport ha hden (zeroes_rect_Ioo_ne_one hρmem)
    exact_mod_cast horderZ
  have hsubset :
      W.image coord ⊆ K := by
    simpa [W, K, coord] using
      (kadiriDisk_window_image_subset_diskFinset (a := a) (T := T) ha hden
        (finiteZeros := finiteZeros))
  have hsubset_nat :
      (∑ ω ∈ W.image coord, analyticOrderNatAt (kadiriDiskF a T) ω) ≤
        ∑ z ∈ K, analyticOrderNatAt (kadiriDiskF a T) z := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro z _ _
    exact Nat.zero_le _
  have hsubset_real :
      (∑ ω ∈ W.image coord,
          ((analyticOrderNatAt (kadiriDiskF a T) ω : ℕ) : ℝ)) ≤
        ((∑ z ∈ K, analyticOrderNatAt (kadiriDiskF a T) z : ℕ) : ℝ) := by
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
  calc
    (∑ ρ ∈ W, ((riemannZeta.order ρ : ℤ) : ℝ))
        = ∑ ω ∈ W.image coord,
            ((analyticOrderNatAt (kadiriDiskF a T) ω : ℕ) : ℝ) := hsum_eq
    _ ≤ ((∑ z ∈ K, analyticOrderNatAt (kadiriDiskF a T) z : ℕ) : ℝ) :=
        hsubset_real
    _ ≤ (1 / Real.log (kadiriDiskRCap / kadiriDiskR)) * Real.log B := hzeros

/-- FinalBound and the local disk zero order budget give the polylogarithmic
order sum bound for the finite unit-height windows. -/
theorem kadiriHorizontalZeroWindowOrderSumBound_of_finalBound :
    KadiriHorizontalZeroWindowOrderSumBound := by
  let a : ℝ := 0
  have ha : 0 ≤ a := by norm_num [a]
  obtain ⟨Cζ, e, hCζ, he0, hsup⟩ := kadiriDisk_fT_sup_bound ha
  let lamR : ℝ := kadiriDiskLam a * kadiriDiskRCap
  let Ksup : ℝ := Cζ / kadiriDiskDenomConst
  let A : ℝ := max 1 (Ksup * (1 + lamR) ^ e)
  let M : ℝ := e + 1
  let CZ : ℝ := 1 / Real.log (kadiriDiskRCap / kadiriDiskR)
  let C : ℝ := 2 * CZ * M
  refine ⟨C, ?_, 1, ?_⟩
  · have hCZ_nonneg : 0 ≤ CZ := by
      simpa [CZ] using kadiriDisk_zerosBoundConst_pos.le
    have hM_nonneg : 0 ≤ M := by
      dsimp [M]
      linarith
    dsimp [C]
    positivity
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
    have hT_two : 2 ≤ |T| := by
      have he : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      exact le_trans he hTe
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
    have hKsup_nonneg : 0 ≤ Ksup := by
      exact div_nonneg hCζ kadiriDiskDenomConst_pos.le
    have hM_pos : 0 < M := by
      dsimp [M]
      linarith
    have hM_nonneg : 0 ≤ M := hM_pos.le
    have hU_pos : 0 < |T| + 2 := by positivity
    have hU_ge_A : A ≤ |T| + 2 := by
      rw [hAbsT]
      linarith
    have hpoly :
        Ksup * (|T| + lamR + 2) ^ e ≤ (|T| + 2) ^ M := by
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
      have hconst_le_A : Ksup * (1 + lamR) ^ e ≤ A := by
        dsimp [A]
        exact le_max_right _ _
      have hUe_nonneg : 0 ≤ U ^ e := Real.rpow_nonneg hU_nonneg e
      calc
        Ksup * (|T| + lamR + 2) ^ e
            ≤ Ksup * ((1 + lamR) * U) ^ e :=
              mul_le_mul_of_nonneg_left hpow_le hKsup_nonneg
        _ = Ksup * ((1 + lamR) ^ e * U ^ e) := by
              rw [Real.mul_rpow hbase_const_nonneg hU_nonneg]
        _ = (Ksup * (1 + lamR) ^ e) * U ^ e := by ring
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
          ‖kadiriDiskF a Tc z‖ ≤ Ksup * (|T| + lamR + 2) ^ e := by
        simpa [Ksup, lamR, hTc_abs] using hsupz
      exact hsupz'.trans hpoly
    have hfz_top :
        ∀ z : ℂ, ‖z‖ ≤ kadiriDiskRCap →
          ‖kadiriDiskF a T z‖ ≤ (|T| + 2) ^ M :=
      hfz_bound_center T rfl hsup_height_pos
    have hfz_bot :
        ∀ z : ℂ, ‖z‖ ≤ kadiriDiskRCap →
          ‖kadiriDiskF a (-T) z‖ ≤ (|T| + 2) ^ M :=
      hfz_bound_center (-T) (by rw [abs_neg]) hsup_height_neg
    have hCZ_nonneg : 0 ≤ CZ := by
      simpa [CZ] using kadiriDisk_zerosBoundConst_pos.le
    have hCZM_nonneg : 0 ≤ CZ * M := mul_nonneg hCZ_nonneg hM_nonneg
    have hlog_le := kadiri_log_abs_add_two_le_two_log_abs hT_two
    have htop_raw :
        (∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
            ((riemannZeta.order ρ : ℤ) : ℝ))
          ≤ CZ * Real.log ((|T| + 2) ^ M) := by
      simpa [CZ] using
        (kadiriWindow_order_sum_le_zerosBound (a := a) (T := T)
          (B := (|T| + 2) ^ M) ha hcenter_pos hfz_top)
    have hbot_raw :
        (∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset,
            ((riemannZeta.order ρ : ℤ) : ℝ))
          ≤ CZ * Real.log ((|T| + 2) ^ M) := by
      simpa [CZ, abs_neg] using
        (kadiriWindow_order_sum_le_zerosBound (a := a) (T := -T)
          (B := (|T| + 2) ^ M) ha hcenter_neg hfz_bot)
    refine ⟨hTe, ?_, ?_⟩
    · calc
        (∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
            ((riemannZeta.order ρ : ℤ) : ℝ))
            ≤ CZ * Real.log ((|T| + 2) ^ M) := htop_raw
        _ = (CZ * M) * Real.log (|T| + 2) := by
              rw [Real.log_rpow hU_pos M]
              ring
        _ ≤ (CZ * M) * (2 * Real.log |T|) :=
              mul_le_mul_of_nonneg_left hlog_le hCZM_nonneg
        _ = C * (Real.log |T|) ^ (1 : ℕ) := by
              dsimp [C]
              ring
    · calc
        (∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset,
            ((riemannZeta.order ρ : ℤ) : ℝ))
            ≤ CZ * Real.log ((|T| + 2) ^ M) := hbot_raw
        _ = (CZ * M) * Real.log (|T| + 2) := by
              rw [Real.log_rpow hU_pos M]
              ring
        _ ≤ (CZ * M) * (2 * Real.log |T|) :=
              mul_le_mul_of_nonneg_left hlog_le hCZM_nonneg
        _ = C * (Real.log |T|) ^ (1 : ℕ) := by
              dsimp [C]
              ring

/-- The finite zero-window kernel bound before applying zero-counting: each
unit-height window contributes at most its order mass times `A / |T|`.  This is
the `φ`-dependent estimate supplied by the scalar PV kernel bound together with
`Φ`/`Φ'` decay. -/
def KadiriHorizontalZeroWindowPVKernelOrderEstimate (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ᶠ T : ℝ in Filter.atTop,
      Real.exp 1 ≤ |T| ∧
        (KadiriNoZeroOrdinate T →
          ‖kadiriTopHorizontalZeroWindowPVIntegral φ a T‖
            ≤ (A / |T|) *
              ∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
                ((riemannZeta.order ρ : ℤ) : ℝ)) ∧
        (KadiriNoZeroOrdinate (-T) →
          ‖kadiriBotHorizontalZeroWindowPVIntegral φ a T‖
            ≤ (A / |T|) *
              ∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset,
                ((riemannZeta.order ρ : ℤ) : ℝ))

/-- Finite-pole expansion of the zero-window PV contribution into single-zero
PV integrals. This is the algebraic bridge between `zeroes_sum` under the
integral and the per-zero scalar kernel estimates. -/
def KadiriHorizontalZeroWindowFinitePoleExpansion (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  ∀ᶠ T : ℝ in Filter.atTop,
    (KadiriNoZeroOrdinate T →
      kadiriTopHorizontalZeroWindowPVIntegral φ a T =
        ∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
          ((riemannZeta.order ρ : ℤ) : ℂ) *
            kadiriTopHorizontalSingleZeroWindowPVIntegral φ a T ρ) ∧
    (KadiriNoZeroOrdinate (-T) →
      kadiriBotHorizontalZeroWindowPVIntegral φ a T =
        ∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset,
          ((riemannZeta.order ρ : ℤ) : ℂ) *
            kadiriBotHorizontalSingleZeroWindowPVIntegral φ a T ρ)

/-- Per-zero weighted Φ-kernel estimate for the finite zero windows. Together
with the finite-pole expansion, this implies the order-mass kernel estimate. -/
def KadiriHorizontalZeroWindowSinglePoleWeightedEstimate
    (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ᶠ T : ℝ in Filter.atTop,
      Real.exp 1 ≤ |T| ∧
        (KadiriNoZeroOrdinate T →
          ∀ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
            ‖((riemannZeta.order ρ : ℤ) : ℂ) *
                kadiriTopHorizontalSingleZeroWindowPVIntegral φ a T ρ‖
              ≤ (A / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ)) ∧
        (KadiriNoZeroOrdinate (-T) →
          ∀ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset,
            ‖((riemannZeta.order ρ : ℤ) : ℂ) *
                kadiriBotHorizontalSingleZeroWindowPVIntegral φ a T ρ‖
              ≤ (A / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ))

/-- Uniform scalar Cauchy-integral bound for the top and bottom finite zero
windows. This is the precise remaining scalar-kernel obligation for the
projected-constant term. -/
def KadiriHorizontalZeroWindowPVScalarIntegralBound (a : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ᶠ T : ℝ in Filter.atTop,
      Real.exp 1 ≤ |T| ∧
        (KadiriNoZeroOrdinate T →
          ∀ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
            ‖kadiriTopHorizontalSingleZeroWindowPVScalarIntegral a T ρ‖ ≤ K) ∧
        (KadiriNoZeroOrdinate (-T) →
          ∀ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset,
            ‖kadiriBotHorizontalSingleZeroWindowPVScalarIntegral a T ρ‖ ≤ K)

theorem kadiriTopHorizontalSingleZeroWindowPVScalarIntegral_norm_le
    {a T : ℝ} {ρ : ℂ} (ha : 0 < a)
    (hNo : KadiriNoZeroOrdinate T)
    (hρ : ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset) :
    ‖kadiriTopHorizontalSingleZeroWindowPVScalarIntegral a T ρ‖
      ≤ 2 * Real.pi + Real.log ((1 + a) / a) := by
  have hρre := zeroes_rect_Ioo_Icc_window_toFinset_re_mem hρ
  have hρzero := zeroes_rect_Ioo_Icc_window_toFinset_zeta_zero hρ
  have him_ne : ρ.im ≠ T := hNo ρ hρzero
  have hδ : T - ρ.im ≠ 0 := by
    intro hδ
    have : ρ.im = T := by linarith
    exact him_ne this
  have hp_lo : a ≤ ρ.re + a := by linarith [hρre.1]
  have hp_hi : ρ.re + a ≤ 1 + a := by linarith [hρre.2]
  have hq_lo : a ≤ 1 + a - ρ.re := by linarith [hρre.2]
  have hq_hi : 1 + a - ρ.re ≤ 1 + a := by linarith [hρre.1]
  have hbound :=
    kadiriScalarLogSub_norm_le (a := a) (p := ρ.re + a)
      (q := 1 + a - ρ.re) (δ := T - ρ.im)
      ha hp_lo hp_hi hq_lo hq_hi
  rw [kadiriTopHorizontalSingleZeroWindowPVScalarIntegral_eq_log_sub
    (le_of_lt ha) hδ]
  convert hbound using 2
  ring_nf

theorem kadiriBotHorizontalSingleZeroWindowPVScalarIntegral_norm_le
    {a T : ℝ} {ρ : ℂ} (ha : 0 < a)
    (hNo : KadiriNoZeroOrdinate (-T))
    (hρ : ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset) :
    ‖kadiriBotHorizontalSingleZeroWindowPVScalarIntegral a T ρ‖
      ≤ 2 * Real.pi + Real.log ((1 + a) / a) := by
  have hρre := zeroes_rect_Ioo_Icc_window_toFinset_re_mem hρ
  have hρzero := zeroes_rect_Ioo_Icc_window_toFinset_zeta_zero hρ
  have him_ne : ρ.im ≠ -T := hNo ρ hρzero
  have hδ : -T - ρ.im ≠ 0 := by
    intro hδ
    have : ρ.im = -T := by linarith
    exact him_ne this
  have hp_lo : a ≤ ρ.re + a := by linarith [hρre.1]
  have hp_hi : ρ.re + a ≤ 1 + a := by linarith [hρre.2]
  have hq_lo : a ≤ 1 + a - ρ.re := by linarith [hρre.2]
  have hq_hi : 1 + a - ρ.re ≤ 1 + a := by linarith [hρre.1]
  have hbound :=
    kadiriScalarLogSub_norm_le (a := a) (p := ρ.re + a)
      (q := 1 + a - ρ.re) (δ := -T - ρ.im)
      ha hp_lo hp_hi hq_lo hq_hi
  rw [kadiriBotHorizontalSingleZeroWindowPVScalarIntegral_eq_log_sub
    (le_of_lt ha) hδ]
  convert hbound using 2
  ring_nf

theorem kadiriHorizontalZeroWindowPVScalarIntegralBound_of_logPrimitive
    {a : ℝ} (ha : 0 < a) :
    KadiriHorizontalZeroWindowPVScalarIntegralBound a := by
  let K : ℝ := 2 * Real.pi + Real.log ((1 + a) / a)
  have hlog_nonneg : 0 ≤ Real.log ((1 + a) / a) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ ha]
    linarith
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    positivity
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with T hT
    have hT_nonneg : 0 ≤ T := le_trans (Real.exp_pos 1).le hT
    have hT_abs : Real.exp 1 ≤ |T| := by
      simpa [abs_of_nonneg hT_nonneg] using hT
    refine ⟨hT_abs, ?_, ?_⟩
    · intro hNo ρ hρ
      exact kadiriTopHorizontalSingleZeroWindowPVScalarIntegral_norm_le ha hNo hρ
    · intro hNo ρ hρ
      exact kadiriBotHorizontalSingleZeroWindowPVScalarIntegral_norm_le ha hNo hρ

theorem kadiriHorizontalZeroWindowPVScalarIntegralBound_of_singlePoleKernelBound
    {a : ℝ} (ha : 0 < a) (_hkernel : KadiriSinglePolePVKernelBound a) :
    KadiriHorizontalZeroWindowPVScalarIntegralBound a :=
  kadiriHorizontalZeroWindowPVScalarIntegralBound_of_logPrimitive ha

/-- Order-weighted estimate for the projected-constant half of each single-zero
weighted PV contribution. The variation half is tracked separately because it
uses the `Φ'` bound. -/
def KadiriHorizontalZeroWindowProjectedConstantEstimate
    (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ᶠ T : ℝ in Filter.atTop,
      Real.exp 1 ≤ |T| ∧
        (KadiriNoZeroOrdinate T →
          ∀ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
            ‖((riemannZeta.order ρ : ℤ) : ℂ) *
                kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ‖
              ≤ (A / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ)) ∧
        (KadiriNoZeroOrdinate (-T) →
          ∀ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset,
            ‖((riemannZeta.order ρ : ℤ) : ℂ) *
                kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ‖
              ≤ (A / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ))

/-- Order-weighted estimate for the `Φ`-variation half of each single-zero
weighted PV contribution. This is the part controlled by the `Φ'` decay. -/
def KadiriHorizontalZeroWindowVariationEstimate
    (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ᶠ T : ℝ in Filter.atTop,
      Real.exp 1 ≤ |T| ∧
        (KadiriNoZeroOrdinate T →
          ∀ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
            ‖((riemannZeta.order ρ : ℤ) : ℂ) *
                kadiriTopHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ‖
              ≤ (A / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ)) ∧
        (KadiriNoZeroOrdinate (-T) →
          ∀ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset,
            ‖((riemannZeta.order ρ : ℤ) : ℂ) *
                kadiriBotHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ‖
              ≤ (A / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ))

/-- Algebraic projected split of every zero-window single-pole integral into a
constant term at the horizontal projection plus a `Φ`-variation term. -/
def KadiriHorizontalZeroWindowProjectedSplit
    (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  ∀ᶠ T : ℝ in Filter.atTop,
    (KadiriNoZeroOrdinate T →
      ∀ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
        kadiriTopHorizontalSingleZeroWindowPVIntegral φ a T ρ =
          kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ +
            kadiriTopHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ) ∧
    (KadiriNoZeroOrdinate (-T) →
      ∀ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset,
        kadiriBotHorizontalSingleZeroWindowPVIntegral φ a T ρ =
          kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ +
            kadiriBotHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ)

private theorem riemannZeta_order_cast_real_nonneg_of_window {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset) :
    0 ≤ ((riemannZeta.order ρ : ℤ) : ℝ) := by
  have hρmem :
      ρ ∈ riemannZeta.zeroes_rect (Set.Ioo (0 : ℝ) 1) (Set.Icc (T - 1) (T + 1)) :=
    (zeroes_rect_Ioo_Icc_window_finite T).mem_toFinset.mp hρ
  exact_mod_cast riemannZeta_order_nonneg (zeroes_rect_Ioo_ne_one hρmem)

private theorem riemannZeta_order_complex_norm_eq_real_of_window {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset) :
    ‖((riemannZeta.order ρ : ℤ) : ℂ)‖ =
      ((riemannZeta.order ρ : ℤ) : ℝ) := by
  have horder_nonneg := riemannZeta_order_cast_real_nonneg_of_window hρ
  change ‖(((riemannZeta.order ρ : ℤ) : ℝ) : ℂ)‖ =
    ((riemannZeta.order ρ : ℤ) : ℝ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg horder_nonneg]

/-- `Φ` decay plus the scalar Cauchy-integral bound gives the order-weighted
projected-constant estimate. -/
theorem kadiriHorizontalZeroWindowProjectedConstantEstimate_of_phiPrime_scalarIntegral
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hΦ : KadiriHorizontalPhiPrimeDecayBound φ a)
    (hscalar : KadiriHorizontalZeroWindowPVScalarIntegralBound a) :
    KadiriHorizontalZeroWindowProjectedConstantEstimate φ a := by
  rcases hΦ with ⟨A0, _A1, hA0, _hA1, hΦ⟩
  rcases hscalar with ⟨K, hK, hscalar⟩
  let prefactor : ℂ := 1 / (2 * (Real.pi : ℂ) * I)
  let A : ℝ := ‖prefactor‖ * K * A0
  refine ⟨A, ?_, ?_⟩
  · dsimp [A]
    positivity
  · filter_upwards [hΦ, hscalar] with T hΦT hscalarT
    rcases hΦT with ⟨_hT_two, hΦtop, hΦbot⟩
    rcases hscalarT with ⟨hT_exp, hscalar_top, hscalar_bot⟩
    refine ⟨hT_exp, ?_, ?_⟩
    · intro hNo ρ hρ
      have hρre_Ioo := zeroes_rect_Ioo_Icc_window_toFinset_re_mem hρ
      have hρre_Icc : ρ.re ∈ Set.Icc (-a) (1 + a) := by
        constructor
        · linarith [ha, hρre_Ioo.1]
        · linarith [ha, hρre_Ioo.2]
      have hφ := (hΦtop ρ.re hρre_Icc).1
      have hconst :=
        kadiriTopHorizontalSingleZeroWindowPVProjectedConstant_norm_le_of_scalar
          (hscalar := hscalar_top hNo ρ hρ) (hPhi := hφ)
      have horder_nonneg := riemannZeta_order_cast_real_nonneg_of_window hρ
      have horder_norm := riemannZeta_order_complex_norm_eq_real_of_window hρ
      calc
        ‖((riemannZeta.order ρ : ℤ) : ℂ) *
            kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ‖
            = ‖((riemannZeta.order ρ : ℤ) : ℂ)‖ *
                ‖kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ‖ := by
              rw [norm_mul]
        _ = ((riemannZeta.order ρ : ℤ) : ℝ) *
                ‖kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ‖ := by
              rw [horder_norm]
        _ ≤ ((riemannZeta.order ρ : ℤ) : ℝ) *
              ((‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ * K * A0) / |T|) :=
              mul_le_mul_of_nonneg_left hconst horder_nonneg
        _ = (A / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ) := by
              dsimp [A, prefactor]
              ring
    · intro hNo ρ hρ
      have hρre_Ioo := zeroes_rect_Ioo_Icc_window_toFinset_re_mem hρ
      have hρre_Icc : ρ.re ∈ Set.Icc (-a) (1 + a) := by
        constructor
        · linarith [ha, hρre_Ioo.1]
        · linarith [ha, hρre_Ioo.2]
      have hφ := (hΦbot ρ.re hρre_Icc).1
      have hconst :=
        kadiriBotHorizontalSingleZeroWindowPVProjectedConstant_norm_le_of_scalar
          (hscalar := hscalar_bot hNo ρ hρ) (hPhi := hφ)
      have horder_nonneg := riemannZeta_order_cast_real_nonneg_of_window hρ
      have horder_norm := riemannZeta_order_complex_norm_eq_real_of_window hρ
      calc
        ‖((riemannZeta.order ρ : ℤ) : ℂ) *
            kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ‖
            = ‖((riemannZeta.order ρ : ℤ) : ℂ)‖ *
                ‖kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ‖ := by
              rw [norm_mul]
        _ = ((riemannZeta.order ρ : ℤ) : ℝ) *
                ‖kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ‖ := by
              rw [horder_norm]
        _ ≤ ((riemannZeta.order ρ : ℤ) : ℝ) *
              ((‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ * K * A0) / |T|) :=
              mul_le_mul_of_nonneg_left hconst horder_nonneg
        _ = (A / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ) := by
              dsimp [A, prefactor]
              ring

/-- The projected-constant and variation estimates assemble the per-zero
single-pole weighted estimate once the algebraic projected split is available. -/
theorem kadiriHorizontalZeroWindowSinglePoleWeightedEstimate_of_projectedConstant_variation
    {φ : ℝ → ℂ} {a : ℝ}
    (hsplit : KadiriHorizontalZeroWindowProjectedSplit φ a)
    (hconst : KadiriHorizontalZeroWindowProjectedConstantEstimate φ a)
    (hvariation : KadiriHorizontalZeroWindowVariationEstimate φ a) :
    KadiriHorizontalZeroWindowSinglePoleWeightedEstimate φ a := by
  rcases hconst with ⟨Aconst, hAconst, hconst⟩
  rcases hvariation with ⟨Avar, hAvar, hvariation⟩
  refine ⟨Aconst + Avar, add_nonneg hAconst hAvar, ?_⟩
  filter_upwards [hsplit, hconst, hvariation] with T hsplitT hconstT hvariationT
  rcases hconstT with ⟨hT_exp, hconst_top, hconst_bot⟩
  rcases hvariationT with ⟨_hT_exp_var, hvariation_top, hvariation_bot⟩
  rcases hsplitT with ⟨hsplit_top, hsplit_bot⟩
  refine ⟨hT_exp, ?_, ?_⟩
  · intro hNo ρ hρ
    have hsingle := hsplit_top hNo ρ hρ
    have hconst_bound := hconst_top hNo ρ hρ
    have hvariation_bound := hvariation_top hNo ρ hρ
    calc
      ‖((riemannZeta.order ρ : ℤ) : ℂ) *
          kadiriTopHorizontalSingleZeroWindowPVIntegral φ a T ρ‖
          = ‖((riemannZeta.order ρ : ℤ) : ℂ) *
              (kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ +
                kadiriTopHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ)‖ := by
            rw [hsingle]
      _ = ‖((riemannZeta.order ρ : ℤ) : ℂ) *
              kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ +
            ((riemannZeta.order ρ : ℤ) : ℂ) *
              kadiriTopHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ‖ := by
            ring_nf
      _ ≤ ‖((riemannZeta.order ρ : ℤ) : ℂ) *
              kadiriTopHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ‖ +
            ‖((riemannZeta.order ρ : ℤ) : ℂ) *
              kadiriTopHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ‖ :=
            norm_add_le _ _
      _ ≤ (Aconst / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ) +
            (Avar / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ) :=
            add_le_add hconst_bound hvariation_bound
      _ = ((Aconst + Avar) / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ) := by
            ring
  · intro hNo ρ hρ
    have hsingle := hsplit_bot hNo ρ hρ
    have hconst_bound := hconst_bot hNo ρ hρ
    have hvariation_bound := hvariation_bot hNo ρ hρ
    calc
      ‖((riemannZeta.order ρ : ℤ) : ℂ) *
          kadiriBotHorizontalSingleZeroWindowPVIntegral φ a T ρ‖
          = ‖((riemannZeta.order ρ : ℤ) : ℂ) *
              (kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ +
                kadiriBotHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ)‖ := by
            rw [hsingle]
      _ = ‖((riemannZeta.order ρ : ℤ) : ℂ) *
              kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ +
            ((riemannZeta.order ρ : ℤ) : ℂ) *
              kadiriBotHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ‖ := by
            ring_nf
      _ ≤ ‖((riemannZeta.order ρ : ℤ) : ℂ) *
              kadiriBotHorizontalSingleZeroWindowPVProjectedConstantIntegral φ a T ρ‖ +
            ‖((riemannZeta.order ρ : ℤ) : ℂ) *
              kadiriBotHorizontalSingleZeroWindowPVVariationIntegral φ a T ρ‖ :=
            norm_add_le _ _
      _ ≤ (Aconst / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ) +
            (Avar / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ) :=
            add_le_add hconst_bound hvariation_bound
      _ = ((Aconst + Avar) / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ) := by
            ring

/-- The finite-pole expansion plus the per-zero weighted Φ-kernel estimate gives
the order-mass zero-window PV kernel estimate. -/
theorem kadiriHorizontalZeroWindowPVKernelOrderEstimate_of_finitePoleExpansion
    {φ : ℝ → ℂ} {a : ℝ}
    (hexpand : KadiriHorizontalZeroWindowFinitePoleExpansion φ a)
    (hsingle : KadiriHorizontalZeroWindowSinglePoleWeightedEstimate φ a) :
    KadiriHorizontalZeroWindowPVKernelOrderEstimate φ a := by
  rcases hsingle with ⟨A, hA, hsingle⟩
  refine ⟨A, hA, ?_⟩
  filter_upwards [hexpand, hsingle] with T hexpandT hsingleT
  rcases hsingleT with ⟨hT, htop_single, hbot_single⟩
  refine ⟨hT, ?_, ?_⟩
  · intro hNo
    rw [hexpandT.1 hNo]
    calc
      ‖∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
          ((riemannZeta.order ρ : ℤ) : ℂ) *
            kadiriTopHorizontalSingleZeroWindowPVIntegral φ a T ρ‖
          ≤ ∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
              ‖((riemannZeta.order ρ : ℤ) : ℂ) *
                kadiriTopHorizontalSingleZeroWindowPVIntegral φ a T ρ‖ :=
            norm_sum_le _ _
      _ ≤ ∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
            (A / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ) :=
            Finset.sum_le_sum (fun ρ hρ => htop_single hNo ρ hρ)
      _ = (A / |T|) *
            ∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
              ((riemannZeta.order ρ : ℤ) : ℝ) := by
            rw [Finset.mul_sum]
  · intro hNo
    rw [hexpandT.2 hNo]
    calc
      ‖∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset,
          ((riemannZeta.order ρ : ℤ) : ℂ) *
            kadiriBotHorizontalSingleZeroWindowPVIntegral φ a T ρ‖
          ≤ ∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset,
              ‖((riemannZeta.order ρ : ℤ) : ℂ) *
                kadiriBotHorizontalSingleZeroWindowPVIntegral φ a T ρ‖ :=
            norm_sum_le _ _
      _ ≤ ∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset,
            (A / |T|) * ((riemannZeta.order ρ : ℤ) : ℝ) :=
            Finset.sum_le_sum (fun ρ hρ => hbot_single hNo ρ hρ)
      _ = (A / |T|) *
            ∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset,
              ((riemannZeta.order ρ : ℤ) : ℝ) := by
            rw [Finset.mul_sum]

/-- `Φ`/`Φ'` decay supplies the zero-window integrability needed to split the
ordinary horizontal integral from the pole-subtracted residual. -/
def KadiriHorizontalZeroWindowPVIntegrability_of_phiPrime
    (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  KadiriHorizontalPhiPrimeDecayBound φ a →
    KadiriHorizontalZeroWindowPVIntegrability φ a

/-- `Φ`/`Φ'` decay supplies the order-mass kernel estimate for the finite
zero-window PV contribution. -/
def KadiriHorizontalZeroWindowPVKernelOrderEstimate_of_phiPrime
    (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  KadiriHorizontalPhiPrimeDecayBound φ a →
    KadiriHorizontalZeroWindowPVKernelOrderEstimate φ a

/-- The finite-kernel/count/`Φ` estimate package that supplies the two analytic
inputs needed by the zero-window PV correction route.  The package is still
`φ`-dependent: it contains the `Φ`/`Φ'` decay estimate and the two precise
places where that decay is consumed, plus the independent zero-window order
counting input. -/
structure KadiriHorizontalZeroWindowFiniteKernelCountPhiEstimates
    (φ : ℝ → ℂ) (a : ℝ) : Prop where
  phiPrime : KadiriHorizontalPhiPrimeDecayBound φ a
  integrability :
    KadiriHorizontalZeroWindowPVIntegrability_of_phiPrime φ a
  kernelOrder :
    KadiriHorizontalZeroWindowPVKernelOrderEstimate_of_phiPrime φ a
  orderSum : KadiriHorizontalZeroWindowOrderSumBound

/-- Finite zero-window PV kernel estimate. This is the input supplied by the
single-pole kernel bound, zero order counting, and `Φ`/`Φ'` decay. -/
def KadiriHorizontalFiniteZeroWindowPVKernelEstimate (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ,
    ∀ᶠ T : ℝ in Filter.atTop,
      Real.exp 1 ≤ |T| ∧
        (KadiriNoZeroOrdinate T →
          ‖kadiriTopHorizontalZeroWindowPVIntegral φ a T‖
            ≤ C * (Real.log |T|) ^ k / |T|) ∧
        (KadiriNoZeroOrdinate (-T) →
          ‖kadiriBotHorizontalZeroWindowPVIntegral φ a T‖
            ≤ C * (Real.log |T|) ^ k / |T|)

/-- The order-mass kernel estimate plus zero-window order counting gives the
logarithmic finite zero-window PV kernel estimate. -/
theorem kadiriHorizontalFiniteZeroWindowPVKernelEstimate_of_kernelOrderEstimate
    {φ : ℝ → ℂ} {a : ℝ}
    (hkernel : KadiriHorizontalZeroWindowPVKernelOrderEstimate φ a)
    (horders : KadiriHorizontalZeroWindowOrderSumBound) :
    KadiriHorizontalFiniteZeroWindowPVKernelEstimate φ a := by
  rcases hkernel with ⟨A, hA, hkernel⟩
  rcases horders with ⟨C, hC, k, horders⟩
  refine ⟨A * C, mul_nonneg hA hC, k, ?_⟩
  filter_upwards [hkernel, horders] with T hkernelT hordersT
  rcases hkernelT with ⟨hT, htop_kernel, hbot_kernel⟩
  rcases hordersT with ⟨_hT_order, htop_orders, hbot_orders⟩
  have hT_pos : 0 < |T| := lt_of_lt_of_le (Real.exp_pos 1) hT
  have hA_div_nonneg : 0 ≤ A / |T| := div_nonneg hA hT_pos.le
  refine ⟨hT, ?_, ?_⟩
  · intro hNo
    calc
      ‖kadiriTopHorizontalZeroWindowPVIntegral φ a T‖
          ≤ (A / |T|) *
              ∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite T).toFinset,
                ((riemannZeta.order ρ : ℤ) : ℝ) := htop_kernel hNo
      _ ≤ (A / |T|) * (C * (Real.log |T|) ^ k) :=
          mul_le_mul_of_nonneg_left htop_orders hA_div_nonneg
      _ = (A * C) * (Real.log |T|) ^ k / |T| := by
          ring
  · intro hNo
    calc
      ‖kadiriBotHorizontalZeroWindowPVIntegral φ a T‖
          ≤ (A / |T|) *
              ∑ ρ ∈ (zeroes_rect_Ioo_Icc_window_finite (-T)).toFinset,
                ((riemannZeta.order ρ : ℤ) : ℝ) := hbot_kernel hNo
      _ ≤ (A / |T|) * (C * (Real.log |T|) ^ k) :=
          mul_le_mul_of_nonneg_left hbot_orders hA_div_nonneg
      _ = (A * C) * (Real.log |T|) ^ k / |T| := by
          ring

/-- The finite-pole expansion, per-zero weighted `Φ` kernel estimate, and
zero-window order counting give the logarithmic finite zero-window PV kernel
estimate. -/
theorem kadiriHorizontalFiniteZeroWindowPVKernelEstimate_of_finitePoleExpansion_count
    {φ : ℝ → ℂ} {a : ℝ}
    (hexpand : KadiriHorizontalZeroWindowFinitePoleExpansion φ a)
    (hsingle : KadiriHorizontalZeroWindowSinglePoleWeightedEstimate φ a)
    (horders : KadiriHorizontalZeroWindowOrderSumBound) :
    KadiriHorizontalFiniteZeroWindowPVKernelEstimate φ a :=
  kadiriHorizontalFiniteZeroWindowPVKernelEstimate_of_kernelOrderEstimate
    (kadiriHorizontalZeroWindowPVKernelOrderEstimate_of_finitePoleExpansion
      hexpand hsingle)
    horders

/-- FinalBound supplies the zero-window order counting input, so the
finite-pole expansion and per-zero weighted `Φ` kernel estimate give the target
finite zero-window PV kernel estimate. -/
theorem kadiriHorizontalFiniteZeroWindowPVKernelEstimate_of_finitePoleExpansion_finalBound
    {φ : ℝ → ℂ} {a : ℝ}
    (hexpand : KadiriHorizontalZeroWindowFinitePoleExpansion φ a)
    (hsingle : KadiriHorizontalZeroWindowSinglePoleWeightedEstimate φ a) :
    KadiriHorizontalFiniteZeroWindowPVKernelEstimate φ a :=
  kadiriHorizontalFiniteZeroWindowPVKernelEstimate_of_finitePoleExpansion_count
    hexpand hsingle kadiriHorizontalZeroWindowOrderSumBound_of_finalBound

/-- The `Φ`/`Φ'` decay estimate and its finite zero-window kernel-order
consequence, combined with zero-window order counting, give the target finite
zero-window PV kernel estimate. -/
theorem kadiriHorizontalFiniteZeroWindowPVKernelEstimate_of_phiPrime_kernelOrder_count
    {φ : ℝ → ℂ} {a : ℝ}
    (hΦ : KadiriHorizontalPhiPrimeDecayBound φ a)
    (hkernel :
      KadiriHorizontalZeroWindowPVKernelOrderEstimate_of_phiPrime φ a)
    (horders : KadiriHorizontalZeroWindowOrderSumBound) :
    KadiriHorizontalFiniteZeroWindowPVKernelEstimate φ a :=
  kadiriHorizontalFiniteZeroWindowPVKernelEstimate_of_kernelOrderEstimate
    (hkernel hΦ) horders

/-- The `Φ`/`Φ'` integrability estimate gives the target zero-window
integrability input. -/
theorem kadiriHorizontalZeroWindowPVIntegrability_of_phiPrime
    {φ : ℝ → ℂ} {a : ℝ}
    (hΦ : KadiriHorizontalPhiPrimeDecayBound φ a)
    (hint : KadiriHorizontalZeroWindowPVIntegrability_of_phiPrime φ a) :
    KadiriHorizontalZeroWindowPVIntegrability φ a :=
  hint hΦ

/-- The finite-kernel/count/`Φ` package supplies exactly the two analytic
inputs consumed by the zero-window PV correction theorem. -/
theorem kadiriHorizontalZeroWindowPVInputs_of_finiteKernelCountPhiEstimates
    {φ : ℝ → ℂ} {a : ℝ}
    (h : KadiriHorizontalZeroWindowFiniteKernelCountPhiEstimates φ a) :
    KadiriHorizontalFiniteZeroWindowPVKernelEstimate φ a ∧
      KadiriHorizontalZeroWindowPVIntegrability φ a :=
  ⟨kadiriHorizontalFiniteZeroWindowPVKernelEstimate_of_phiPrime_kernelOrder_count
      h.phiPrime h.kernelOrder h.orderSum,
    kadiriHorizontalZeroWindowPVIntegrability_of_phiPrime
      h.phiPrime h.integrability⟩

/-- The finite zero-window PV correction still needed after the PF residual is
bounded. It is exactly the gap between the ordinary horizontal integral and the
pole-subtracted residual integral at non-zero ordinates. -/
def KadiriHorizontalZeroWindowPVCorrectionBound (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ,
    ∀ᶠ T : ℝ in Filter.atTop,
      Real.exp 1 ≤ |T| ∧
        (KadiriNoZeroOrdinate T →
          ‖kadiriTopHorizontalIntegral φ a T -
              kadiriTopHorizontalPFResidualIntegral φ a T‖
            ≤ C * (Real.log |T|) ^ k / |T|) ∧
        (KadiriNoZeroOrdinate (-T) →
          ‖kadiriBotHorizontalIntegral φ a T -
              kadiriBotHorizontalPFResidualIntegral φ a T‖
            ≤ C * (Real.log |T|) ^ k / |T|)

/-- On a no-zero top ordinate, every point of the horizontal segment is a
non-zero point of `ζ`. -/
theorem kadiriTopHorizontalPoint_zeta_ne_zero_of_noZero {T σ : ℝ}
    (hNo : KadiriNoZeroOrdinate T) :
    riemannZeta (kadiriTopHorizontalPoint T σ) ≠ 0 := by
  intro hζ
  exact (hNo (kadiriTopHorizontalPoint T σ) hζ) (by simp [kadiriTopHorizontalPoint])

/-- On a no-zero bottom ordinate, every point of the horizontal segment is a
non-zero point of `ζ`. -/
theorem kadiriBotHorizontalPoint_zeta_ne_zero_of_noZero {T σ : ℝ}
    (hNo : KadiriNoZeroOrdinate (-T)) :
    riemannZeta (kadiriBotHorizontalPoint T σ) ≠ 0 := by
  intro hζ
  exact (hNo (kadiriBotHorizontalPoint T σ) hζ) (by simp [kadiriBotHorizontalPoint])

/-- At top no-zero ordinates, the ordinary horizontal integral differs from the
PF residual by the negative finite zero-window pole contribution. -/
theorem kadiriTopHorizontalIntegral_sub_pfResidualIntegral_eq_neg_zeroWindow
    {φ : ℝ → ℂ} {a T : ℝ}
    (hlog : IntegrableOn (fun σ : ℝ =>
      (-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
          riemannZeta (kadiriTopHorizontalPoint T σ)) *
        kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)))
      (Set.Ioo (-a) (1 + a)))
    (hzero : IntegrableOn (fun σ : ℝ =>
      (riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
        (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))) *
        kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)))
      (Set.Ioo (-a) (1 + a))) :
    kadiriTopHorizontalIntegral φ a T - kadiriTopHorizontalPFResidualIntegral φ a T =
      -kadiriTopHorizontalZeroWindowPVIntegral φ a T := by
  simp [kadiriTopHorizontalIntegral, kadiriTopHorizontalPFResidualIntegral,
    kadiriTopHorizontalZeroWindowPVIntegral]
  have hzero' : IntegrableOn (fun σ : ℝ =>
      (riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
        (fun ρ ↦ (kadiriTopHorizontalPoint T σ - ρ)⁻¹)) *
        kadiriHorizontalPhi φ (-kadiriTopHorizontalPoint T σ))
      (Set.Ioo (-a) (1 + a)) := by
    simpa [one_div] using hzero
  have hcong :
      (∫ σ in Set.Ioo (-a) (1 + a),
          (-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
              riemannZeta (kadiriTopHorizontalPoint T σ) +
            riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
              (fun ρ ↦ (kadiriTopHorizontalPoint T σ - ρ)⁻¹)) *
            kadiriHorizontalPhi φ (-kadiriTopHorizontalPoint T σ)) =
        ∫ σ in Set.Ioo (-a) (1 + a),
          (-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
              riemannZeta (kadiriTopHorizontalPoint T σ)) *
            kadiriHorizontalPhi φ (-kadiriTopHorizontalPoint T σ) +
          (riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
              (fun ρ ↦ (kadiriTopHorizontalPoint T σ - ρ)⁻¹)) *
            kadiriHorizontalPhi φ (-kadiriTopHorizontalPoint T σ) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with σ
    ring
  rw [hcong, MeasureTheory.integral_add hlog hzero']
  ring

/-- At bottom no-zero ordinates, the ordinary horizontal integral differs from
the PF residual by the negative finite zero-window pole contribution. -/
theorem kadiriBotHorizontalIntegral_sub_pfResidualIntegral_eq_neg_zeroWindow
    {φ : ℝ → ℂ} {a T : ℝ}
    (hlog : IntegrableOn (fun σ : ℝ =>
      (-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
          riemannZeta (kadiriBotHorizontalPoint T σ)) *
        kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)))
      (Set.Ioo (-a) (1 + a)))
    (hzero : IntegrableOn (fun σ : ℝ =>
      (riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc ((-T) - 1) ((-T) + 1))
        (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))) *
        kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)))
      (Set.Ioo (-a) (1 + a))) :
    kadiriBotHorizontalIntegral φ a T - kadiriBotHorizontalPFResidualIntegral φ a T =
      -kadiriBotHorizontalZeroWindowPVIntegral φ a T := by
  simp [kadiriBotHorizontalIntegral, kadiriBotHorizontalPFResidualIntegral,
    kadiriBotHorizontalZeroWindowPVIntegral]
  have hzero' : IntegrableOn (fun σ : ℝ =>
      (riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc ((-T) - 1) ((-T) + 1))
        (fun ρ ↦ (kadiriBotHorizontalPoint T σ - ρ)⁻¹)) *
        kadiriHorizontalPhi φ (-kadiriBotHorizontalPoint T σ))
      (Set.Ioo (-a) (1 + a)) := by
    simpa [one_div] using hzero
  have hcong :
      (∫ σ in Set.Ioo (-a) (1 + a),
          (-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
              riemannZeta (kadiriBotHorizontalPoint T σ) +
            riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc ((-T) - 1) ((-T) + 1))
              (fun ρ ↦ (kadiriBotHorizontalPoint T σ - ρ)⁻¹)) *
            kadiriHorizontalPhi φ (-kadiriBotHorizontalPoint T σ)) =
        ∫ σ in Set.Ioo (-a) (1 + a),
          (-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
              riemannZeta (kadiriBotHorizontalPoint T σ)) *
            kadiriHorizontalPhi φ (-kadiriBotHorizontalPoint T σ) +
          (riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc ((-T) - 1) ((-T) + 1))
              (fun ρ ↦ (kadiriBotHorizontalPoint T σ - ρ)⁻¹)) *
            kadiriHorizontalPhi φ (-kadiriBotHorizontalPoint T σ) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with σ
    ring
  rw [hcong, MeasureTheory.integral_add hlog hzero']
  ring

/-- The finite zero-window kernel estimate and the set-integral bridge give the
correction bound consumed by the corrected horizontal PV route. -/
theorem kadiriHorizontalZeroWindowPVCorrectionBound_of_kernelEstimate
    {φ : ℝ → ℂ} {a : ℝ}
    (hint : KadiriHorizontalZeroWindowPVIntegrability φ a)
    (hkernel : KadiriHorizontalFiniteZeroWindowPVKernelEstimate φ a) :
    KadiriHorizontalZeroWindowPVCorrectionBound φ a := by
  rcases hkernel with ⟨C, hC, k, hkernel⟩
  refine ⟨C, hC, k, ?_⟩
  filter_upwards [hint, hkernel] with T hintT hkernelT
  rcases hkernelT with ⟨hT, htop, hbot⟩
  refine ⟨hT, ?_, ?_⟩
  · intro hNo
    rcases hintT.1 hNo with ⟨hlog, hzero⟩
    rw [kadiriTopHorizontalIntegral_sub_pfResidualIntegral_eq_neg_zeroWindow
      (φ := φ) (a := a) (T := T) hlog hzero, norm_neg]
    exact htop hNo
  · intro hNo
    rcases hintT.2 hNo with ⟨hlog, hzero⟩
    rw [kadiriBotHorizontalIntegral_sub_pfResidualIntegral_eq_neg_zeroWindow
      (φ := φ) (a := a) (T := T) hlog hzero, norm_neg]
    exact hbot hNo

/-- Zero-window integrability, the order-mass kernel estimate, and zero-window
order counting give the PV correction bound consumed by the corrected
horizontal route. -/
theorem kadiriHorizontalZeroWindowPVCorrectionBound_of_kernelOrderEstimate
    {φ : ℝ → ℂ} {a : ℝ}
    (hint : KadiriHorizontalZeroWindowPVIntegrability φ a)
    (hkernel : KadiriHorizontalZeroWindowPVKernelOrderEstimate φ a)
    (horders : KadiriHorizontalZeroWindowOrderSumBound) :
    KadiriHorizontalZeroWindowPVCorrectionBound φ a :=
  kadiriHorizontalZeroWindowPVCorrectionBound_of_kernelEstimate hint
    (kadiriHorizontalFiniteZeroWindowPVKernelEstimate_of_kernelOrderEstimate
      hkernel horders)

/-- Zero-window integrability, the finite-pole expansion, the per-zero weighted
kernel estimate, and zero-window order counting give the PV correction bound. -/
theorem kadiriHorizontalZeroWindowPVCorrectionBound_of_finitePoleExpansion_count
    {φ : ℝ → ℂ} {a : ℝ}
    (hint : KadiriHorizontalZeroWindowPVIntegrability φ a)
    (hexpand : KadiriHorizontalZeroWindowFinitePoleExpansion φ a)
    (hsingle : KadiriHorizontalZeroWindowSinglePoleWeightedEstimate φ a)
    (horders : KadiriHorizontalZeroWindowOrderSumBound) :
    KadiriHorizontalZeroWindowPVCorrectionBound φ a :=
  kadiriHorizontalZeroWindowPVCorrectionBound_of_kernelEstimate hint
    (kadiriHorizontalFiniteZeroWindowPVKernelEstimate_of_finitePoleExpansion_count
      hexpand hsingle horders)

/-- FinalBound supplies zero-window order counting, so zero-window integrability,
the finite-pole expansion, and the per-zero weighted kernel estimate give the
PV correction bound. -/
theorem kadiriHorizontalZeroWindowPVCorrectionBound_of_finitePoleExpansion_finalBound
    {φ : ℝ → ℂ} {a : ℝ}
    (hint : KadiriHorizontalZeroWindowPVIntegrability φ a)
    (hexpand : KadiriHorizontalZeroWindowFinitePoleExpansion φ a)
    (hsingle : KadiriHorizontalZeroWindowSinglePoleWeightedEstimate φ a) :
    KadiriHorizontalZeroWindowPVCorrectionBound φ a :=
  kadiriHorizontalZeroWindowPVCorrectionBound_of_finitePoleExpansion_count
    hint hexpand hsingle kadiriHorizontalZeroWindowOrderSumBound_of_finalBound

/-- `Φ`/`Φ'` decay, routed through the zero-window integrability and kernel-order
inputs, plus zero-window order counting, gives the PV correction bound. -/
theorem kadiriHorizontalZeroWindowPVCorrectionBound_of_phiPrime_kernelOrder_count
    {φ : ℝ → ℂ} {a : ℝ}
    (hΦ : KadiriHorizontalPhiPrimeDecayBound φ a)
    (hint : KadiriHorizontalZeroWindowPVIntegrability_of_phiPrime φ a)
    (hkernel : KadiriHorizontalZeroWindowPVKernelOrderEstimate_of_phiPrime φ a)
    (horders : KadiriHorizontalZeroWindowOrderSumBound) :
    KadiriHorizontalZeroWindowPVCorrectionBound φ a :=
  kadiriHorizontalZeroWindowPVCorrectionBound_of_kernelOrderEstimate
    (hint hΦ) (hkernel hΦ) horders

/-- The finite-kernel/count/`Φ` package gives the zero-window PV correction
bound consumed by the corrected horizontal route. -/
theorem kadiriHorizontalZeroWindowPVCorrectionBound_of_finiteKernelCountPhiEstimates
    {φ : ℝ → ℂ} {a : ℝ}
    (h : KadiriHorizontalZeroWindowFiniteKernelCountPhiEstimates φ a) :
    KadiriHorizontalZeroWindowPVCorrectionBound φ a :=
  kadiriHorizontalZeroWindowPVCorrectionBound_of_phiPrime_kernelOrder_count
    h.phiPrime h.integrability h.kernelOrder h.orderSum

private theorem kadiri_log_abs_add_two_sq_le_four_log_abs_sq {T : ℝ}
    (hT : 2 ≤ |T|) :
    (Real.log (|T| + 2)) ^ (2 : ℕ) ≤
      4 * (Real.log |T|) ^ (2 : ℕ) := by
  have h_abs_pos : 0 < |T| := by linarith
  have h_add_pos : 0 < |T| + 2 := by linarith
  have h_sq : |T| + 2 ≤ |T| ^ (2 : ℕ) := by
    nlinarith [hT]
  have hlog_le :
      Real.log (|T| + 2) ≤ 2 * Real.log |T| := by
    calc
      Real.log (|T| + 2) ≤ Real.log (|T| ^ (2 : ℕ)) :=
        Real.log_le_log h_add_pos h_sq
      _ = 2 * Real.log |T| := by
        rw [Real.log_pow]
        norm_num
  have hlog_nonneg : 0 ≤ Real.log (|T| + 2) :=
    Real.log_nonneg (by linarith)
  calc
    (Real.log (|T| + 2)) ^ (2 : ℕ)
        ≤ (2 * Real.log |T|) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hlog_nonneg hlog_le 2
    _ = 4 * (Real.log |T|) ^ (2 : ℕ) := by ring

/-- The `φ`-dependent PV integration estimate needed after the local
partial-fraction decomposition. It bounds the ordinary horizontal integrals at
the non-zero ordinates where the canonical PV values agree with them. -/
def KadiriHorizontalPVIntegrationBound (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ,
    ∀ᶠ T : ℝ in Filter.atTop,
      1 ≤ |T| ∧
        (KadiriNoZeroOrdinate T →
          ‖kadiriTopHorizontalIntegral φ a T‖
            ≤ C * (Real.log |T|) ^ k / |T|) ∧
        (KadiriNoZeroOrdinate (-T) →
          ‖kadiriBotHorizontalIntegral φ a T‖
            ≤ C * (Real.log |T|) ^ k / |T|)

/-- Condition-B level input for the corrected PV route: C1 decay of the
Laplace transform on the horizontal strips, plus the PV integration estimate
that turns the pole-subtracted horizontal integrals into an atTop bound. -/
def KadiriHorizontalPhiC1DecayBound (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  KadiriHorizontalPhiPrimeDecayBound φ a ∧
    KadiriHorizontalPVIntegrationBound φ a

/-- Package the condition-B C1 decay and the PV integration estimate into the
single `PhiC1Decay` input consumed by the final horizontal route. -/
theorem kadiriHorizontalPhiC1DecayBound_of_conditionB {φ : ℝ → ℂ} {a : ℝ}
    (hΦ : KadiriHorizontalPhiPrimeDecayBound φ a)
    (hPV : KadiriHorizontalPVIntegrationBound φ a) :
    KadiriHorizontalPhiC1DecayBound φ a :=
  ⟨hΦ, hPV⟩

/-- A PV integration bound gives the canonical PV bound, because the canonical
values are the ordinary integrals off zero ordinates and are zero on zero
ordinates. -/
theorem kadiriHorizontalPVCanonical_bound_of_pvIntegrationBound
    {φ : ℝ → ℂ} {a : ℝ}
    (hPV : KadiriHorizontalPVIntegrationBound φ a) :
    KadiriHorizontalPVBound
      (kadiriTopHorizontalPVCanonical φ a)
      (kadiriBotHorizontalPVCanonical φ a) := by
  rcases hPV with ⟨C, hC, k, hPV⟩
  refine ⟨C, hC, k, ?_⟩
  filter_upwards [hPV] with T hT
  rcases hT with ⟨hT_abs, htop, hbot⟩
  have hT_pos : 0 < |T| := lt_of_lt_of_le zero_lt_one hT_abs
  have hlog_nonneg : 0 ≤ (Real.log |T|) ^ k :=
    pow_nonneg (Real.log_nonneg hT_abs) k
  have hrhs_nonneg : 0 ≤ C * (Real.log |T|) ^ k / |T| :=
    div_nonneg (mul_nonneg hC hlog_nonneg) hT_pos.le
  refine ⟨hT_abs, ?_, ?_⟩
  · by_cases hNo : KadiriNoZeroOrdinate T
    · simpa [kadiriTopHorizontalPVCanonical, hNo] using htop hNo
    · simpa [kadiriTopHorizontalPVCanonical, hNo] using hrhs_nonneg
  · by_cases hNo : KadiriNoZeroOrdinate (-T)
    · simpa [kadiriBotHorizontalPVCanonical, hNo] using hbot hNo
    · simpa [kadiriBotHorizontalPVCanonical, hNo] using hrhs_nonneg

/-- The `PhiC1Decay` route input supplies the canonical PV bound. -/
theorem kadiriHorizontalPVCanonical_bound_of_phiC1Decay
    {φ : ℝ → ℂ} {a : ℝ}
    (hΦ : KadiriHorizontalPhiC1DecayBound φ a) :
    KadiriHorizontalPVBound
      (kadiriTopHorizontalPVCanonical φ a)
      (kadiriBotHorizontalPVCanonical φ a) :=
  kadiriHorizontalPVCanonical_bound_of_pvIntegrationBound hΦ.2

/-- PF residual plus `Φ` decay and the finite zero-window PV correction gives
the ordinary-integral PV estimate. This is the assembly step after FinalBound:
the PF remainder controls the pole-subtracted residual, and the correction input
accounts for the finite zero-window pole terms. -/
theorem kadiriHorizontalPVIntegrationBound_of_pf_phiPrime_and_zeroWindowCorrection
    {φ : ℝ → ℂ} {a : ℝ}
    (hpf : KadiriHorizontalPartialFractionRemainderBound a)
    (hΦ : KadiriHorizontalPhiPrimeDecayBound φ a)
    (hcorr : KadiriHorizontalZeroWindowPVCorrectionBound φ a) :
    KadiriHorizontalPVIntegrationBound φ a := by
  rcases hpf with ⟨B, hB, hpf⟩
  rcases hΦ with ⟨A0, _A1, hA0, _hA1, hΦ⟩
  rcases hcorr with ⟨Ccorr, hCcorr, kcorr, hcorr⟩
  let prefactor : ℂ := 1 / (2 * (Real.pi : ℂ) * I)
  let segment : Set ℝ := Set.Ioo (-a) (1 + a)
  let D : ℝ := ‖prefactor‖ * volume.real segment
  let Cres : ℝ := D * (B * A0) * 4
  have hD : 0 ≤ D := by
    positivity
  have hBA0 : 0 ≤ B * A0 := mul_nonneg hB hA0
  have hCres : 0 ≤ Cres := by
    dsimp [Cres]
    positivity
  refine ⟨Ccorr + Cres, add_nonneg hCcorr hCres, max kcorr 2, ?_⟩
  have hmeasure : volume segment < ⊤ := by
    simp [segment, Real.volume_Ioo]
  filter_upwards [hpf, hΦ, hcorr] with T hpfT hΦT hcorrT
  rcases hpfT with ⟨hT_one, hpf_top, hpf_bot⟩
  rcases hΦT with ⟨hT_two, hΦ_top, hΦ_bot⟩
  rcases hcorrT with ⟨hT_exp, hcorr_top, hcorr_bot⟩
  have hT_pos : 0 < |T| := lt_of_lt_of_le zero_lt_one hT_one
  have hL1 : 1 ≤ Real.log |T| := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log |T| := Real.log_le_log (Real.exp_pos 1) hT_exp
  have hpow_corr :
      (Real.log |T|) ^ kcorr ≤
        (Real.log |T|) ^ max kcorr 2 :=
    pow_le_pow_right₀ hL1 (Nat.le_max_left kcorr 2)
  have hpow_res :
      (Real.log |T|) ^ (2 : ℕ) ≤
        (Real.log |T|) ^ max kcorr 2 :=
    pow_le_pow_right₀ hL1 (Nat.le_max_right kcorr 2)
  have hcorr_lift :
      Ccorr * (Real.log |T|) ^ kcorr / |T| ≤
        Ccorr * (Real.log |T|) ^ max kcorr 2 / |T| :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow_corr hCcorr) hT_pos.le
  have hres_lift :
      Cres * (Real.log |T|) ^ (2 : ℕ) / |T| ≤
        Cres * (Real.log |T|) ^ max kcorr 2 / |T| :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow_res hCres) hT_pos.le
  have hlog_add_sq :
      (Real.log (|T| + 2)) ^ (2 : ℕ) ≤
        4 * (Real.log |T|) ^ (2 : ℕ) :=
    kadiri_log_abs_add_two_sq_le_four_log_abs_sq hT_two
  have hres_top :
      ∀ hNo : KadiriNoZeroOrdinate T,
        ‖kadiriTopHorizontalPFResidualIntegral φ a T‖
          ≤ Cres * (Real.log |T|) ^ (2 : ℕ) / |T| := by
    intro hNo
    have hset :
        ‖∫ σ in segment,
            (((-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
                  riemannZeta (kadiriTopHorizontalPoint T σ)) +
                riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
                  (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))) *
              kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)))‖
          ≤ ((B * (Real.log (|T| + 2)) ^ (2 : ℕ)) * (A0 / |T|)) *
              volume.real segment := by
      refine MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (μ := volume) (s := segment)
        (f := fun σ : ℝ =>
          (((-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
                riemannZeta (kadiriTopHorizontalPoint T σ)) +
              riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
                (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))) *
            kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))))
        hmeasure ?_
      intro σ hσ
      have hσIcc : σ ∈ Set.Icc (-a) (1 + a) :=
        Set.Ioo_subset_Icc_self hσ
      have hζ : riemannZeta (kadiriTopHorizontalPoint T σ) ≠ 0 :=
        kadiriTopHorizontalPoint_zeta_ne_zero_of_noZero hNo
      have hrem := hpf_top σ hσIcc hζ
      have hphi := (hΦ_top σ hσIcc).1
      have hrem_rhs_nonneg :
          0 ≤ B * (Real.log (|T| + 2)) ^ (2 : ℕ) :=
        mul_nonneg hB (sq_nonneg _)
      calc
        ‖(((-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
              riemannZeta (kadiriTopHorizontalPoint T σ)) +
            riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
              (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))) *
          kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)))‖
            = ‖(-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
                  riemannZeta (kadiriTopHorizontalPoint T σ)) +
                riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
                  (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))‖ *
              ‖kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))‖ := by
                rw [norm_mul]
        _ ≤ (B * (Real.log (|T| + 2)) ^ (2 : ℕ)) * (A0 / |T|) :=
            mul_le_mul hrem hphi (norm_nonneg _) hrem_rhs_nonneg
    calc
      ‖kadiriTopHorizontalPFResidualIntegral φ a T‖
          = ‖prefactor *
              ∫ σ in segment,
                (((-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
                      riemannZeta (kadiriTopHorizontalPoint T σ)) +
                    riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
                      (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))) *
                  kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)))‖ := by
              simp [kadiriTopHorizontalPFResidualIntegral, prefactor, segment]
      _ = ‖prefactor‖ *
            ‖∫ σ in segment,
                (((-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
                      riemannZeta (kadiriTopHorizontalPoint T σ)) +
                    riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
                      (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))) *
                  kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ)))‖ := by
              rw [norm_mul]
      _ ≤ ‖prefactor‖ *
            (((B * (Real.log (|T| + 2)) ^ (2 : ℕ)) * (A0 / |T|)) *
              volume.real segment) :=
              mul_le_mul_of_nonneg_left hset (norm_nonneg _)
      _ = D * (B * A0 * (Real.log (|T| + 2)) ^ (2 : ℕ) / |T|) := by
              simp [D]
              field_simp [hT_pos.ne']
      _ ≤ Cres * (Real.log |T|) ^ (2 : ℕ) / |T| := by
              have hcoef : 0 ≤ D * (B * A0) := mul_nonneg hD hBA0
              calc
                D * (B * A0 * (Real.log (|T| + 2)) ^ (2 : ℕ) / |T|)
                    = (D * (B * A0)) *
                        (Real.log (|T| + 2)) ^ (2 : ℕ) / |T| := by ring
                _ ≤ (D * (B * A0)) *
                        (4 * (Real.log |T|) ^ (2 : ℕ)) / |T| :=
                    div_le_div_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hlog_add_sq hcoef) hT_pos.le
                _ = Cres * (Real.log |T|) ^ (2 : ℕ) / |T| := by
                    simp [Cres]
                    ring
  have hres_bot :
      ∀ hNo : KadiriNoZeroOrdinate (-T),
        ‖kadiriBotHorizontalPFResidualIntegral φ a T‖
          ≤ Cres * (Real.log |T|) ^ (2 : ℕ) / |T| := by
    intro hNo
    have hset :
        ‖∫ σ in segment,
            (((-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
                  riemannZeta (kadiriBotHorizontalPoint T σ)) +
                riemannZeta.zeroes_sum (Set.Ioo 0 1)
                  (Set.Icc ((-T) - 1) ((-T) + 1))
                  (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))) *
              kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)))‖
          ≤ ((B * (Real.log (|T| + 2)) ^ (2 : ℕ)) * (A0 / |T|)) *
              volume.real segment := by
      refine MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (μ := volume) (s := segment)
        (f := fun σ : ℝ =>
          (((-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
                riemannZeta (kadiriBotHorizontalPoint T σ)) +
              riemannZeta.zeroes_sum (Set.Ioo 0 1)
                (Set.Icc ((-T) - 1) ((-T) + 1))
                (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))) *
            kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))))
        hmeasure ?_
      intro σ hσ
      have hσIcc : σ ∈ Set.Icc (-a) (1 + a) :=
        Set.Ioo_subset_Icc_self hσ
      have hζ : riemannZeta (kadiriBotHorizontalPoint T σ) ≠ 0 :=
        kadiriBotHorizontalPoint_zeta_ne_zero_of_noZero hNo
      have hrem := hpf_bot σ hσIcc hζ
      have hphi := (hΦ_bot σ hσIcc).1
      have hrem_rhs_nonneg :
          0 ≤ B * (Real.log (|T| + 2)) ^ (2 : ℕ) :=
        mul_nonneg hB (sq_nonneg _)
      calc
        ‖(((-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
              riemannZeta (kadiriBotHorizontalPoint T σ)) +
            riemannZeta.zeroes_sum (Set.Ioo 0 1)
              (Set.Icc ((-T) - 1) ((-T) + 1))
              (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))) *
          kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)))‖
            = ‖(-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
                  riemannZeta (kadiriBotHorizontalPoint T σ)) +
                riemannZeta.zeroes_sum (Set.Ioo 0 1)
                  (Set.Icc ((-T) - 1) ((-T) + 1))
                  (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))‖ *
              ‖kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))‖ := by
                rw [norm_mul]
        _ ≤ (B * (Real.log (|T| + 2)) ^ (2 : ℕ)) * (A0 / |T|) :=
            mul_le_mul hrem hphi (norm_nonneg _) hrem_rhs_nonneg
    calc
      ‖kadiriBotHorizontalPFResidualIntegral φ a T‖
          = ‖prefactor *
              ∫ σ in segment,
                (((-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
                      riemannZeta (kadiriBotHorizontalPoint T σ)) +
                    riemannZeta.zeroes_sum (Set.Ioo 0 1)
                      (Set.Icc ((-T) - 1) ((-T) + 1))
                      (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))) *
                  kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)))‖ := by
              simp [kadiriBotHorizontalPFResidualIntegral, prefactor, segment]
      _ = ‖prefactor‖ *
            ‖∫ σ in segment,
                (((-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
                      riemannZeta (kadiriBotHorizontalPoint T σ)) +
                    riemannZeta.zeroes_sum (Set.Ioo 0 1)
                      (Set.Icc ((-T) - 1) ((-T) + 1))
                      (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))) *
                  kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ)))‖ := by
              rw [norm_mul]
      _ ≤ ‖prefactor‖ *
            (((B * (Real.log (|T| + 2)) ^ (2 : ℕ)) * (A0 / |T|)) *
              volume.real segment) :=
              mul_le_mul_of_nonneg_left hset (norm_nonneg _)
      _ = D * (B * A0 * (Real.log (|T| + 2)) ^ (2 : ℕ) / |T|) := by
              simp [D]
              field_simp [hT_pos.ne']
      _ ≤ Cres * (Real.log |T|) ^ (2 : ℕ) / |T| := by
              have hcoef : 0 ≤ D * (B * A0) := mul_nonneg hD hBA0
              calc
                D * (B * A0 * (Real.log (|T| + 2)) ^ (2 : ℕ) / |T|)
                    = (D * (B * A0)) *
                        (Real.log (|T| + 2)) ^ (2 : ℕ) / |T| := by ring
                _ ≤ (D * (B * A0)) *
                        (4 * (Real.log |T|) ^ (2 : ℕ)) / |T| :=
                    div_le_div_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hlog_add_sq hcoef) hT_pos.le
                _ = Cres * (Real.log |T|) ^ (2 : ℕ) / |T| := by
                    simp [Cres]
                    ring
  refine ⟨hT_one, ?_, ?_⟩
  · intro hNo
    have hsplit :
        kadiriTopHorizontalIntegral φ a T =
          (kadiriTopHorizontalIntegral φ a T -
              kadiriTopHorizontalPFResidualIntegral φ a T) +
            kadiriTopHorizontalPFResidualIntegral φ a T := by
      abel
    calc
      ‖kadiriTopHorizontalIntegral φ a T‖
          = ‖(kadiriTopHorizontalIntegral φ a T -
                kadiriTopHorizontalPFResidualIntegral φ a T) +
              kadiriTopHorizontalPFResidualIntegral φ a T‖ := by
              exact congrArg norm hsplit
      _ ≤ ‖kadiriTopHorizontalIntegral φ a T -
              kadiriTopHorizontalPFResidualIntegral φ a T‖ +
            ‖kadiriTopHorizontalPFResidualIntegral φ a T‖ := norm_add_le _ _
      _ ≤ Ccorr * (Real.log |T|) ^ kcorr / |T| +
            Cres * (Real.log |T|) ^ (2 : ℕ) / |T| :=
          add_le_add (hcorr_top hNo) (hres_top hNo)
      _ ≤ Ccorr * (Real.log |T|) ^ max kcorr 2 / |T| +
            Cres * (Real.log |T|) ^ max kcorr 2 / |T| :=
          add_le_add hcorr_lift hres_lift
      _ = (Ccorr + Cres) * (Real.log |T|) ^ max kcorr 2 / |T| := by
          ring
  · intro hNo
    have hsplit :
        kadiriBotHorizontalIntegral φ a T =
          (kadiriBotHorizontalIntegral φ a T -
              kadiriBotHorizontalPFResidualIntegral φ a T) +
            kadiriBotHorizontalPFResidualIntegral φ a T := by
      abel
    calc
      ‖kadiriBotHorizontalIntegral φ a T‖
          = ‖(kadiriBotHorizontalIntegral φ a T -
                kadiriBotHorizontalPFResidualIntegral φ a T) +
              kadiriBotHorizontalPFResidualIntegral φ a T‖ := by
              exact congrArg norm hsplit
      _ ≤ ‖kadiriBotHorizontalIntegral φ a T -
              kadiriBotHorizontalPFResidualIntegral φ a T‖ +
            ‖kadiriBotHorizontalPFResidualIntegral φ a T‖ := norm_add_le _ _
      _ ≤ Ccorr * (Real.log |T|) ^ kcorr / |T| +
            Cres * (Real.log |T|) ^ (2 : ℕ) / |T| :=
          add_le_add (hcorr_bot hNo) (hres_bot hNo)
      _ ≤ Ccorr * (Real.log |T|) ^ max kcorr 2 / |T| +
            Cres * (Real.log |T|) ^ max kcorr 2 / |T| :=
          add_le_add hcorr_lift hres_lift
      _ = (Ccorr + Cres) * (Real.log |T|) ^ max kcorr 2 / |T| := by
          ring

/-- FinalBound plus the `φ`-dependent C1/PV input gives the canonical PV bound.
The FinalBound side contributes the proved local partial-fraction remainder; the
PV bound itself comes from the explicit `PhiC1Decay` input. -/
theorem kadiriHorizontalPVCanonical_bound_of_finalBound_and_phiC1Decay
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hΦ : KadiriHorizontalPhiC1DecayBound φ a) :
    KadiriHorizontalPVBound
      (kadiriTopHorizontalPVCanonical φ a)
      (kadiriBotHorizontalPVCanonical φ a) :=
  by
    have _hpf : KadiriHorizontalPartialFractionRemainderBound a :=
      kadiriHorizontalPartialFractionRemainderBound_of_finalBound ha
    exact kadiriHorizontalPVCanonical_bound_of_phiC1Decay hΦ

/-- Route-level outputs from the FinalBound linear PF input plus the
`φ`-dependent integrated horizontal estimate. The first projection records the
proved linear-to-squared PF reduction; the second projection is the canonical PV
bound needed by the package. -/
theorem kadiriHorizontalPVRoute_outputs_of_linearInput_and_atTopBound
    {φ : ℝ → ℂ} {a : ℝ}
    (hlin : KadiriHorizontalPFRemainderLinearInput a)
    (hB : KadiriHorizontalAtTopBound φ a) :
    KadiriHorizontalPartialFractionRemainderBound a ∧
      KadiriHorizontalPVBound
        (kadiriTopHorizontalPVCanonical φ a)
        (kadiriBotHorizontalPVCanonical φ a) := by
  exact ⟨
    kadiriHorizontalPartialFractionRemainderBound_of_linearInput hlin,
    kadiriHorizontalPVCanonical_bound_of_atTopBound hB⟩

/-- Canonical PV bound from the FinalBound linear PF input plus the
`φ`-dependent integrated horizontal estimate. -/
theorem kadiriHorizontalPVCanonical_bound_of_linearInput_and_atTopBound
    {φ : ℝ → ℂ} {a : ℝ}
    (hlin : KadiriHorizontalPFRemainderLinearInput a)
    (hB : KadiriHorizontalAtTopBound φ a) :
    KadiriHorizontalPVBound
      (kadiriTopHorizontalPVCanonical φ a)
      (kadiriBotHorizontalPVCanonical φ a) :=
  (kadiriHorizontalPVRoute_outputs_of_linearInput_and_atTopBound hlin hB).2

/-- Route-level outputs from the linear PF input plus the `PhiC1Decay` input. -/
theorem kadiriHorizontalPVRoute_outputs_of_linearInput_and_phiC1Decay
    {φ : ℝ → ℂ} {a : ℝ}
    (hlin : KadiriHorizontalPFRemainderLinearInput a)
    (hΦ : KadiriHorizontalPhiC1DecayBound φ a) :
    KadiriHorizontalPartialFractionRemainderBound a ∧
      KadiriHorizontalPVBound
        (kadiriTopHorizontalPVCanonical φ a)
        (kadiriBotHorizontalPVCanonical φ a) := by
  exact ⟨
    kadiriHorizontalPartialFractionRemainderBound_of_linearInput hlin,
    kadiriHorizontalPVCanonical_bound_of_phiC1Decay hΦ⟩

/-- Once the canonical PV values have the required atTop decay, they assemble
the corrected PV package. This reduces package construction to the single
remaining analytic estimate `KadiriHorizontalPVBound`. -/
def kadiriHorizontalPVPackage_of_canonical_bound {φ : ℝ → ℂ} {a : ℝ}
    (hbound : KadiriHorizontalPVBound
      (kadiriTopHorizontalPVCanonical φ a)
      (kadiriBotHorizontalPVCanonical φ a)) :
    KadiriHorizontalPVPackage φ a :=
  kadiriHorizontalPVPackage_of_inputs
    (kadiriTopHorizontalPVCanonical φ a)
    (kadiriBotHorizontalPVCanonical φ a)
    hbound
    kadiriHorizontalPVCanonical_noZeroBridge

/-- Top horizontal PV vanishing from the canonical PV bound. -/
theorem kadiriTopHorizontalPVCanonical_vanishes_of_bound {φ : ℝ → ℂ} {a : ℝ}
    (hbound : KadiriHorizontalPVBound
      (kadiriTopHorizontalPVCanonical φ a)
      (kadiriBotHorizontalPVCanonical φ a)) :
    Filter.Tendsto (kadiriTopHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_top_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_canonical_bound (φ := φ) (a := a) hbound)

/-- Bottom horizontal PV vanishing from the canonical PV bound. -/
theorem kadiriBotHorizontalPVCanonical_vanishes_of_bound {φ : ℝ → ℂ} {a : ℝ}
    (hbound : KadiriHorizontalPVBound
      (kadiriTopHorizontalPVCanonical φ a)
      (kadiriBotHorizontalPVCanonical φ a)) :
    Filter.Tendsto (kadiriBotHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_canonical_bound (φ := φ) (a := a) hbound)

/-- Legacy all-height package constructor for canonical PV values. -/
def kadiriHorizontalPVPackage_of_atTopBound {φ : ℝ → ℂ} {a : ℝ}
    (hB : KadiriHorizontalAtTopBound φ a) :
    KadiriHorizontalPVPackage φ a :=
  kadiriHorizontalPVPackage_of_canonical_bound
    (kadiriHorizontalPVCanonical_bound_of_atTopBound hB)

/-- Package constructor from the FinalBound linear PF input plus the
`φ`-dependent integrated horizontal estimate. -/
def kadiriHorizontalPVPackage_of_linearInput_and_atTopBound
    {φ : ℝ → ℂ} {a : ℝ}
    (hlin : KadiriHorizontalPFRemainderLinearInput a)
    (hB : KadiriHorizontalAtTopBound φ a) :
    KadiriHorizontalPVPackage φ a :=
  kadiriHorizontalPVPackage_of_canonical_bound
    (kadiriHorizontalPVCanonical_bound_of_linearInput_and_atTopBound hlin hB)

/-- Package constructor from FinalBound plus the `PhiC1Decay` input. -/
def kadiriHorizontalPVPackage_of_finalBound_and_phiC1Decay
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hΦ : KadiriHorizontalPhiC1DecayBound φ a) :
    KadiriHorizontalPVPackage φ a :=
  kadiriHorizontalPVPackage_of_canonical_bound
    (kadiriHorizontalPVCanonical_bound_of_finalBound_and_phiC1Decay ha hΦ)

/-- Package constructor from FinalBound, condition-B C1 decay, and the
PV-integration estimate. -/
def kadiriHorizontalPVPackage_of_finalBound_and_conditionB
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hΦ : KadiriHorizontalPhiPrimeDecayBound φ a)
    (hPV : KadiriHorizontalPVIntegrationBound φ a) :
    KadiriHorizontalPVPackage φ a :=
  kadiriHorizontalPVPackage_of_finalBound_and_phiC1Decay ha
    (kadiriHorizontalPhiC1DecayBound_of_conditionB hΦ hPV)

/-- Package constructor from FinalBound, condition-B C1 decay, and the
zero-window PV correction. -/
def kadiriHorizontalPVPackage_of_finalBound_conditionB_and_zeroWindowCorrection
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hΦ : KadiriHorizontalPhiPrimeDecayBound φ a)
    (hcorr : KadiriHorizontalZeroWindowPVCorrectionBound φ a) :
    KadiriHorizontalPVPackage φ a :=
  kadiriHorizontalPVPackage_of_finalBound_and_conditionB ha hΦ
    (kadiriHorizontalPVIntegrationBound_of_pf_phiPrime_and_zeroWindowCorrection
      (kadiriHorizontalPartialFractionRemainderBound_of_finalBound ha) hΦ hcorr)

/-- Package constructor from FinalBound, condition-B C1 decay, and the finite
zero-window PV kernel estimate. -/
def kadiriHorizontalPVPackage_of_finalBound_conditionB_and_zeroWindowKernelEstimate
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hΦ : KadiriHorizontalPhiPrimeDecayBound φ a)
    (hint : KadiriHorizontalZeroWindowPVIntegrability φ a)
    (hkernel : KadiriHorizontalFiniteZeroWindowPVKernelEstimate φ a) :
    KadiriHorizontalPVPackage φ a :=
  kadiriHorizontalPVPackage_of_finalBound_conditionB_and_zeroWindowCorrection ha hΦ
    (kadiriHorizontalZeroWindowPVCorrectionBound_of_kernelEstimate hint hkernel)

/-- Package constructor from FinalBound and the finite-kernel/count/`Φ`
zero-window estimate package. -/
def kadiriHorizontalPVPackage_of_finalBound_and_finiteKernelCountPhiEstimates
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (h : KadiriHorizontalZeroWindowFiniteKernelCountPhiEstimates φ a) :
    KadiriHorizontalPVPackage φ a :=
  kadiriHorizontalPVPackage_of_finalBound_conditionB_and_zeroWindowCorrection ha
    h.phiPrime
    (kadiriHorizontalZeroWindowPVCorrectionBound_of_finiteKernelCountPhiEstimates h)

/-- Top canonical horizontal PV vanishing from the legacy all-height bound. -/
theorem kadiriTopHorizontalPVCanonical_vanishes_of_atTopBound {φ : ℝ → ℂ} {a : ℝ}
    (hB : KadiriHorizontalAtTopBound φ a) :
    Filter.Tendsto (kadiriTopHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiriTopHorizontalPVCanonical_vanishes_of_bound
    (kadiriHorizontalPVCanonical_bound_of_atTopBound hB)

/-- Bottom canonical horizontal PV vanishing from the legacy all-height bound. -/
theorem kadiriBotHorizontalPVCanonical_vanishes_of_atTopBound {φ : ℝ → ℂ} {a : ℝ}
    (hB : KadiriHorizontalAtTopBound φ a) :
    Filter.Tendsto (kadiriBotHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiriBotHorizontalPVCanonical_vanishes_of_bound
    (kadiriHorizontalPVCanonical_bound_of_atTopBound hB)

/-- Top q1 horizontal PV vanishing with the package constructed from route
inputs, not supplied as a hypothesis. -/
theorem kadiri_thm_3_1_q1_top_horizontal_pv_vanishes_of_linearInput_and_atTopBound
    {φ : ℝ → ℂ} {a : ℝ}
    (hlin : KadiriHorizontalPFRemainderLinearInput a)
    (hB : KadiriHorizontalAtTopBound φ a) :
    Filter.Tendsto (kadiriTopHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_top_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_linearInput_and_atTopBound hlin hB)

/-- Bottom q1 horizontal PV vanishing with the package constructed from route
inputs, not supplied as a hypothesis. -/
theorem kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes_of_linearInput_and_atTopBound
    {φ : ℝ → ℂ} {a : ℝ}
    (hlin : KadiriHorizontalPFRemainderLinearInput a)
    (hB : KadiriHorizontalAtTopBound φ a) :
    Filter.Tendsto (kadiriBotHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_linearInput_and_atTopBound hlin hB)

/-- Top q1 horizontal PV vanishing from FinalBound, condition-B C1 decay, and
the PV-integration estimate. -/
theorem kadiri_thm_3_1_q1_top_horizontal_pv_vanishes_of_finalBound_and_conditionB
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hΦ : KadiriHorizontalPhiPrimeDecayBound φ a)
    (hPV : KadiriHorizontalPVIntegrationBound φ a) :
    Filter.Tendsto (kadiriTopHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_top_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_finalBound_and_conditionB ha hΦ hPV)

/-- Bottom q1 horizontal PV vanishing from FinalBound, condition-B C1 decay, and
the PV-integration estimate. -/
theorem kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes_of_finalBound_and_conditionB
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hΦ : KadiriHorizontalPhiPrimeDecayBound φ a)
    (hPV : KadiriHorizontalPVIntegrationBound φ a) :
    Filter.Tendsto (kadiriBotHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_finalBound_and_conditionB ha hΦ hPV)

/-- Top q1 horizontal PV vanishing from FinalBound, condition-B C1 decay, and
the finite zero-window PV correction. -/
theorem kadiri_thm_3_1_q1_top_horizontal_pv_vanishes_of_finalBound_conditionB_and_zeroWindowCorrection
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hΦ : KadiriHorizontalPhiPrimeDecayBound φ a)
    (hcorr : KadiriHorizontalZeroWindowPVCorrectionBound φ a) :
    Filter.Tendsto (kadiriTopHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_top_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_finalBound_conditionB_and_zeroWindowCorrection ha hΦ hcorr)

/-- Bottom q1 horizontal PV vanishing from FinalBound, condition-B C1 decay, and
the finite zero-window PV correction. -/
theorem kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes_of_finalBound_conditionB_and_zeroWindowCorrection
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hΦ : KadiriHorizontalPhiPrimeDecayBound φ a)
    (hcorr : KadiriHorizontalZeroWindowPVCorrectionBound φ a) :
    Filter.Tendsto (kadiriBotHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_finalBound_conditionB_and_zeroWindowCorrection ha hΦ hcorr)

/-- Top q1 horizontal PV vanishing from FinalBound, condition-B C1 decay, and
the finite zero-window PV kernel estimate. -/
theorem kadiri_thm_3_1_q1_top_horizontal_pv_vanishes_of_finalBound_conditionB_and_zeroWindowKernelEstimate
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hΦ : KadiriHorizontalPhiPrimeDecayBound φ a)
    (hint : KadiriHorizontalZeroWindowPVIntegrability φ a)
    (hkernel : KadiriHorizontalFiniteZeroWindowPVKernelEstimate φ a) :
    Filter.Tendsto (kadiriTopHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_top_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_finalBound_conditionB_and_zeroWindowKernelEstimate
      ha hΦ hint hkernel)

/-- Bottom q1 horizontal PV vanishing from FinalBound, condition-B C1 decay, and
the finite zero-window PV kernel estimate. -/
theorem kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes_of_finalBound_conditionB_and_zeroWindowKernelEstimate
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hΦ : KadiriHorizontalPhiPrimeDecayBound φ a)
    (hint : KadiriHorizontalZeroWindowPVIntegrability φ a)
    (hkernel : KadiriHorizontalFiniteZeroWindowPVKernelEstimate φ a) :
    Filter.Tendsto (kadiriBotHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_finalBound_conditionB_and_zeroWindowKernelEstimate
      ha hΦ hint hkernel)

/-- Top q1 horizontal PV vanishing from FinalBound and the finite-kernel/count/
`Φ` zero-window estimate package. -/
theorem kadiri_thm_3_1_q1_top_horizontal_pv_vanishes_of_finalBound_and_finiteKernelCountPhiEstimates
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (h : KadiriHorizontalZeroWindowFiniteKernelCountPhiEstimates φ a) :
    Filter.Tendsto (kadiriTopHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_top_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_finalBound_and_finiteKernelCountPhiEstimates
      ha h)

/-- Bottom q1 horizontal PV vanishing from FinalBound and the finite-kernel/
count/`Φ` zero-window estimate package. -/
theorem kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes_of_finalBound_and_finiteKernelCountPhiEstimates
    {φ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (h : KadiriHorizontalZeroWindowFiniteKernelCountPhiEstimates φ a) :
    Filter.Tendsto (kadiriBotHorizontalPVCanonical φ a) Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_finalBound_and_finiteKernelCountPhiEstimates
      ha h)

end

end Kadiri
