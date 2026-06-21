import PrimeNumberTheoremAnd.Defs
import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Kadiri horizontal PV surface

This sidecar keeps the upstream `Filter.atTop` targets unchanged, records the
older pointwise contract as a legacy adapter, and names the corrected PV route.
-/

namespace Kadiri

open MeasureTheory Complex
open ArithmeticFunction hiding log
open Filter
open scoped Topology

noncomputable def kadiriHorizontalPhi (φ : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume

noncomputable def kadiriTopHorizontalPoint (T σ : ℝ) : ℂ :=
  (σ : ℂ) + (T : ℂ) * I

noncomputable def kadiriBotHorizontalPoint (T σ : ℝ) : ℂ :=
  (σ : ℂ) + ((-T : ℝ) : ℂ) * I

noncomputable def kadiriTopHorizontalIntegral (φ : ℝ → ℂ) (a T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    ∫ σ in Set.Ioo (-a) (1 + a),
      (-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
          riemannZeta (kadiriTopHorizontalPoint T σ)) *
        kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))

noncomputable def kadiriBotHorizontalIntegral (φ : ℝ → ℂ) (a T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    ∫ σ in Set.Ioo (-a) (1 + a),
      (-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
          riemannZeta (kadiriBotHorizontalPoint T σ)) *
        kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))

/-- Legacy pointwise horizontal bound for Kadiri's direct all-height argument.

This contract is too strong at zero ordinates of `ζ`, where `ζ'/ζ` has poles.
It is retained only to keep the old adapters available while the corrected PV
route is formalized below.
-/
def KadiriHorizontalAtTopBound (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ,
    ∀ᶠ T : ℝ in Filter.atTop,
      1 ≤ |T| ∧
        (∀ σ ∈ Set.Icc (-a) (1 + a),
          ‖(-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
              riemannZeta (kadiriTopHorizontalPoint T σ)) *
            kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))‖
            ≤ C * (Real.log |T|) ^ k / |T|) ∧
        (∀ σ ∈ Set.Icc (-a) (1 + a),
          ‖(-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
              riemannZeta (kadiriBotHorizontalPoint T σ)) *
            kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))‖
            ≤ C * (Real.log |T|) ^ k / |T|)

/-- Legacy all-height horizontal log-derivative estimate.

The corrected route below replaces this false pointwise premise by a PV
operator plus a bridge to the ordinary integral at non-zero ordinates.
-/
def KadiriAllHeightZetaLogDerivBound (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ,
    ∀ᶠ T : ℝ in Filter.atTop,
      1 ≤ |T| ∧
        (∀ σ ∈ Set.Icc (-a) (1 + a),
          ‖-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
              riemannZeta (kadiriTopHorizontalPoint T σ)‖
            ≤ C * (Real.log |T|) ^ k) ∧
        (∀ σ ∈ Set.Icc (-a) (1 + a),
          ‖-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
              riemannZeta (kadiriBotHorizontalPoint T σ)‖
            ≤ C * (Real.log |T|) ^ k)

/-- Uniform condition-(B) decay surface for the bilateral Laplace transform on
Kadiri's two horizontal segments. -/
def KadiriHorizontalPhiDecayBound (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ T : ℝ in Filter.atTop,
      1 ≤ |T| ∧
        (∀ σ ∈ Set.Icc (-a) (1 + a),
          ‖kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))‖ ≤ C / |T|) ∧
        (∀ σ ∈ Set.Icc (-a) (1 + a),
          ‖kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))‖ ≤ C / |T|)

theorem kadiriHorizontalAtTopBound_of_zetaLogDeriv_and_phiDecay
    {φ : ℝ → ℂ} {a : ℝ}
    (hζ : KadiriAllHeightZetaLogDerivBound a)
    (hΦ : KadiriHorizontalPhiDecayBound φ a) :
    KadiriHorizontalAtTopBound φ a := by
  rcases hζ with ⟨Cζ, hCζ, kζ, hζ⟩
  rcases hΦ with ⟨CΦ, hCΦ, hΦ⟩
  refine ⟨Cζ * CΦ, mul_nonneg hCζ hCΦ, kζ, ?_⟩
  filter_upwards [hζ, hΦ] with T hζT hΦT
  rcases hζT with ⟨hT, hζ_top, hζ_bot⟩
  rcases hΦT with ⟨_hTΦ, hΦ_top, hΦ_bot⟩
  have hT_pos : 0 < |T| := lt_of_lt_of_le zero_lt_one hT
  have hlog_nonneg : 0 ≤ (Real.log |T|) ^ kζ :=
    pow_nonneg (Real.log_nonneg hT) kζ
  have hζ_rhs_nonneg : 0 ≤ Cζ * (Real.log |T|) ^ kζ :=
    mul_nonneg hCζ hlog_nonneg
  refine ⟨hT, ?_, ?_⟩
  · intro σ hσ
    have hz := hζ_top σ hσ
    have hphi := hΦ_top σ hσ
    calc
      ‖(-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
            riemannZeta (kadiriTopHorizontalPoint T σ)) *
          kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))‖
          = ‖-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
                riemannZeta (kadiriTopHorizontalPoint T σ)‖ *
              ‖kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))‖ := by
              rw [norm_mul]
      _ ≤ (Cζ * (Real.log |T|) ^ kζ) * (CΦ / |T|) :=
          mul_le_mul hz hphi (norm_nonneg _) hζ_rhs_nonneg
      _ = Cζ * CΦ * (Real.log |T|) ^ kζ / |T| := by
          field_simp [hT_pos.ne']
  · intro σ hσ
    have hz := hζ_bot σ hσ
    have hphi := hΦ_bot σ hσ
    calc
      ‖(-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
            riemannZeta (kadiriBotHorizontalPoint T σ)) *
          kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))‖
          = ‖-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
                riemannZeta (kadiriBotHorizontalPoint T σ)‖ *
              ‖kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))‖ := by
              rw [norm_mul]
      _ ≤ (Cζ * (Real.log |T|) ^ kζ) * (CΦ / |T|) :=
          mul_le_mul hz hphi (norm_nonneg _) hζ_rhs_nonneg
      _ = Cζ * CΦ * (Real.log |T|) ^ kζ / |T| := by
          field_simp [hT_pos.ne']

private lemma tendsto_const_mul_log_pow_div_abs_atTop (D C : ℝ) (k : ℕ) :
    Filter.Tendsto (fun T : ℝ => D * (C * (Real.log |T|) ^ k / |T|))
      Filter.atTop (nhds 0) := by
  have hbase : Filter.Tendsto (fun T : ℝ => (Real.log T) ^ k / T)
      Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_pow_atTop 1 k (by norm_num : (0 : ℝ) < 1)
  have hC : Filter.Tendsto (fun T : ℝ => C * (Real.log T) ^ k / T)
      Filter.atTop (nhds 0) := by
    simpa [mul_div_assoc] using hbase.const_mul C
  have hD : Filter.Tendsto (fun T : ℝ => D * (C * (Real.log T) ^ k / T))
      Filter.atTop (nhds 0) := by
    simpa using hC.const_mul D
  refine Filter.Tendsto.congr' ?_ hD
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  rw [abs_of_nonneg hT]

/-- No zero of `ζ` has ordinate `T`. This is the ordinary-integral bridge
condition for the top horizontal segment. -/
def KadiriNoZeroOrdinate (T : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.im ≠ T

/-- The scalar Cauchy-PV kernel for one zero on the horizontal segment.

For `p = β + a`, `q = 1 + a - β`, and `δ = T - γ`, this is the corrected
single-pole contribution. At `δ = 0` the PV value is `log (q / p)`.
-/
noncomputable def kadiriPoleKernelPV (p q δ : ℝ) : ℂ :=
  if δ = 0 then
    (Real.log (q / p) : ℂ)
  else
    ((((1 : ℝ) / 2) * Real.log ((q ^ 2 + δ ^ 2) / (p ^ 2 + δ ^ 2))) : ℂ)
      - ((Real.arctan (q / δ) + Real.arctan (p / δ) : ℝ) : ℂ) * I

/-- A zero-weighted single-pole PV contribution on the top horizontal segment. -/
noncomputable def kadiriWeightedPolePV (a T : ℝ) (Φ : ℂ → ℂ) (ρ : ℂ) : ℂ :=
  ((riemannZeta.order ρ : ℤ) : ℂ) * Φ (-ρ) *
    kadiriPoleKernelPV (ρ.re + a) (1 + a - ρ.re) (T - ρ.im)

/-- Uniform single-pole PV kernel bound in the shape needed for the horizontal
argument. The bound is `π + log ((1+a)/a)`, not zero. -/
def KadiriSinglePolePVKernelBound (a : ℝ) : Prop :=
  0 < a →
    ∀ β δ : ℝ, 0 < β → β < 1 →
      ‖kadiriPoleKernelPV (β + a) (1 + a - β) δ‖ ≤
        Real.pi + Real.log ((1 + a) / a)

/-- Condition-(B) horizontal decay surface for `Φ` and its complex derivative.
The route uses these estimates directly, with constants allowed to be crude. -/
def KadiriHorizontalPhiPrimeDecayBound (φ : ℝ → ℂ) (a : ℝ) : Prop :=
  ∃ A0 A1 : ℝ, 0 ≤ A0 ∧ 0 ≤ A1 ∧
    ∀ᶠ T : ℝ in Filter.atTop,
      2 ≤ |T| ∧
        (∀ σ ∈ Set.Icc (-a) (1 + a),
          ‖kadiriHorizontalPhi φ (-(kadiriTopHorizontalPoint T σ))‖ ≤ A0 / |T| ∧
          ‖deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
              (-(kadiriTopHorizontalPoint T σ))‖ ≤ A1 / |T|) ∧
        (∀ σ ∈ Set.Icc (-a) (1 + a),
          ‖kadiriHorizontalPhi φ (-(kadiriBotHorizontalPoint T σ))‖ ≤ A0 / |T| ∧
          ‖deriv (fun z : ℂ => kadiriHorizontalPhi φ z)
              (-(kadiriBotHorizontalPoint T σ))‖ ≤ A1 / |T|)

/-- The new analytic lemma still needed for the PV route: after removing the
nearby zero poles, the log-derivative remainder is `O(log(|T|+2)^2)` on the
horizontal segment, away from the poles. -/
def KadiriHorizontalPartialFractionRemainderBound (a : ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧
    ∀ᶠ T : ℝ in Filter.atTop,
      1 ≤ |T| ∧
        (∀ σ ∈ Set.Icc (-a) (1 + a),
          riemannZeta (kadiriTopHorizontalPoint T σ) ≠ 0 →
            ‖(-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
                riemannZeta (kadiriTopHorizontalPoint T σ)) +
              riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
                (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))‖
              ≤ B * (Real.log (|T| + 2)) ^ (2 : ℕ)) ∧
        (∀ σ ∈ Set.Icc (-a) (1 + a),
          riemannZeta (kadiriBotHorizontalPoint T σ) ≠ 0 →
            ‖(-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
                riemannZeta (kadiriBotHorizontalPoint T σ)) +
              riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc ((-T) - 1) ((-T) + 1))
                (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))‖
              ≤ B * (Real.log (|T| + 2)) ^ (2 : ℕ))

/-- A PV bound for the top and bottom horizontal PV values. This is the
downstream estimate assembled from `Φ` decay, the single-pole kernel bound,
zero counting, and the partial-fraction remainder bound. -/
def KadiriHorizontalPVBound (topPV botPV : ℝ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ,
    ∀ᶠ T : ℝ in Filter.atTop,
      1 ≤ |T| ∧
        ‖topPV T‖ ≤ C * (Real.log |T|) ^ k / |T| ∧
        ‖botPV T‖ ≤ C * (Real.log |T|) ^ k / |T|

/-- The ordinary-integral bridge for non-zero ordinates. The bottom segment uses
ordinate `-T`. -/
def KadiriZetaHorizontalPVNoZeroBridge
    (φ : ℝ → ℂ) (a : ℝ) (topPV botPV : ℝ → ℂ) : Prop :=
  (∀ T : ℝ, KadiriNoZeroOrdinate T →
      topPV T = kadiriTopHorizontalIntegral φ a T) ∧
    (∀ T : ℝ, KadiriNoZeroOrdinate (-T) →
      botPV T = kadiriBotHorizontalIntegral φ a T)

/-- The corrected horizontal PV package. Constructing this package is the
remaining analytic task; the `bound` field gives the `Filter.atTop` vanishing
proved below. -/
structure KadiriHorizontalPVPackage (φ : ℝ → ℂ) (a : ℝ) where
  topPV : ℝ → ℂ
  botPV : ℝ → ℂ
  bound : KadiriHorizontalPVBound topPV botPV
  bridge : KadiriZetaHorizontalPVNoZeroBridge φ a topPV botPV

theorem kadiriTopHorizontalPV_tendsto_zero_of_pvBound
    {topPV botPV : ℝ → ℂ}
    (hB : KadiriHorizontalPVBound topPV botPV) :
    Filter.Tendsto topPV Filter.atTop (nhds 0) := by
  rcases hB with ⟨C, _hC, k, hB⟩
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ : ℝ => 0)
    (h := fun T : ℝ => (1 : ℝ) * (C * (Real.log |T|) ^ k / |T|))
    tendsto_const_nhds
    (tendsto_const_mul_log_pow_div_abs_atTop 1 C k)
    ?_ ?_
  · filter_upwards with T
    exact norm_nonneg _
  · filter_upwards [hB] with T hT
    simpa using hT.2.1

theorem kadiriBotHorizontalPV_tendsto_zero_of_pvBound
    {topPV botPV : ℝ → ℂ}
    (hB : KadiriHorizontalPVBound topPV botPV) :
    Filter.Tendsto botPV Filter.atTop (nhds 0) := by
  rcases hB with ⟨C, _hC, k, hB⟩
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ : ℝ => 0)
    (h := fun T : ℝ => (1 : ℝ) * (C * (Real.log |T|) ^ k / |T|))
    tendsto_const_nhds
    (tendsto_const_mul_log_pow_div_abs_atTop 1 C k)
    ?_ ?_
  · filter_upwards with T
    exact norm_nonneg _
  · filter_upwards [hB] with T hT
    simpa using hT.2.2

theorem kadiri_thm_3_1_q1_top_horizontal_pv_vanishes
    {φ : ℝ → ℂ} {a : ℝ} (P : KadiriHorizontalPVPackage φ a) :
    Filter.Tendsto P.topPV Filter.atTop (nhds 0) :=
  kadiriTopHorizontalPV_tendsto_zero_of_pvBound P.bound

theorem kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes
    {φ : ℝ → ℂ} {a : ℝ} (P : KadiriHorizontalPVPackage φ a) :
    Filter.Tendsto P.botPV Filter.atTop (nhds 0) :=
  kadiriBotHorizontalPV_tendsto_zero_of_pvBound P.bound

theorem kadiriTopHorizontalIntegral_tendsto_zero_of_atTopBound
    {φ : ℝ → ℂ} {a : ℝ}
    (hB : KadiriHorizontalAtTopBound φ a) :
    Filter.Tendsto (fun T : ℝ => kadiriTopHorizontalIntegral φ a T)
      Filter.atTop (nhds 0) := by
  rcases hB with ⟨C, _hC, k, hB⟩
  let prefactor : ℂ := 1 / (2 * (Real.pi : ℂ) * I)
  let segment : Set ℝ := Set.Ioo (-a) (1 + a)
  let D : ℝ := ‖prefactor‖ * volume.real segment
  have hmeasure : volume segment < ⊤ := by
    simp [segment, Real.volume_Ioo]
  have h_upper :
      ∀ᶠ T : ℝ in Filter.atTop,
        ‖kadiriTopHorizontalIntegral φ a T‖
          ≤ D * (C * (Real.log |T|) ^ k / |T|) := by
    filter_upwards [hB] with T hT
    rcases hT with ⟨_hT_abs, htop, _hbot⟩
    have hset :
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
      _ = D * (C * (Real.log |T|) ^ k / |T|) := by
              simp [D]
              ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ : ℝ => 0)
    (h := fun T : ℝ => D * (C * (Real.log |T|) ^ k / |T|))
    tendsto_const_nhds
    (tendsto_const_mul_log_pow_div_abs_atTop D C k)
    ?_ ?_
  · filter_upwards with T
    exact norm_nonneg _
  · exact h_upper

theorem kadiriBotHorizontalIntegral_tendsto_zero_of_atTopBound
    {φ : ℝ → ℂ} {a : ℝ}
    (hB : KadiriHorizontalAtTopBound φ a) :
    Filter.Tendsto (fun T : ℝ => kadiriBotHorizontalIntegral φ a T)
      Filter.atTop (nhds 0) := by
  rcases hB with ⟨C, _hC, k, hB⟩
  let prefactor : ℂ := 1 / (2 * (Real.pi : ℂ) * I)
  let segment : Set ℝ := Set.Ioo (-a) (1 + a)
  let D : ℝ := ‖prefactor‖ * volume.real segment
  have hmeasure : volume segment < ⊤ := by
    simp [segment, Real.volume_Ioo]
  have h_upper :
      ∀ᶠ T : ℝ in Filter.atTop,
        ‖kadiriBotHorizontalIntegral φ a T‖
          ≤ D * (C * (Real.log |T|) ^ k / |T|) := by
    filter_upwards [hB] with T hT
    rcases hT with ⟨_hT_abs, _htop, hbot⟩
    have hset :
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
      _ = D * (C * (Real.log |T|) ^ k / |T|) := by
              simp [D]
              ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ : ℝ => 0)
    (h := fun T : ℝ => D * (C * (Real.log |T|) ^ k / |T|))
    tendsto_const_nhds
    (tendsto_const_mul_log_pow_div_abs_atTop D C k)
    ?_ ?_
  · filter_upwards with T
    exact norm_nonneg _
  · exact h_upper

theorem kadiri_top_horizontal_vanishes_of_named_tendsto
    {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (_ha : 0 < a) (_hab : a < b) (_ha1 : a < 1)
    (h : Filter.Tendsto (fun T : ℝ => kadiriTopHorizontalIntegral φ a T)
        Filter.atTop (nhds 0)) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Filter.Tendsto
      (fun T : ℝ ↦
        (1 / (2 * (Real.pi : ℂ) * I)) *
          ∫ σ in Set.Ioo (-a) (1 + a),
            (-deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
                riemannZeta ((σ : ℂ) + (T : ℂ) * I)) *
              Φ (-((σ : ℂ) + (T : ℂ) * I)))
      Filter.atTop (nhds 0) := by
  simpa [kadiriTopHorizontalIntegral, kadiriHorizontalPhi, kadiriTopHorizontalPoint] using h

theorem kadiri_bot_horizontal_vanishes_of_named_tendsto
    {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (_ha : 0 < a) (_hab : a < b) (_ha1 : a < 1)
    (h : Filter.Tendsto (fun T : ℝ => kadiriBotHorizontalIntegral φ a T)
        Filter.atTop (nhds 0)) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Filter.Tendsto
      (fun T : ℝ ↦
        (1 / (2 * (Real.pi : ℂ) * I)) *
          ∫ σ in Set.Ioo (-a) (1 + a),
            (-deriv riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) /
                riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) *
              Φ (-((σ : ℂ) + ((-T : ℝ) : ℂ) * I)))
      Filter.atTop (nhds 0) := by
  simpa [kadiriBotHorizontalIntegral, kadiriHorizontalPhi, kadiriBotHorizontalPoint] using h

theorem kadiri_top_horizontal_vanishes_of_atTopBound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (hB : KadiriHorizontalAtTopBound φ a) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Filter.Tendsto
      (fun T : ℝ ↦
        (1 / (2 * (Real.pi : ℂ) * I)) *
          ∫ σ in Set.Ioo (-a) (1 + a),
            (-deriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) /
                riemannZeta ((σ : ℂ) + (T : ℂ) * I)) *
              Φ (-((σ : ℂ) + (T : ℂ) * I)))
      Filter.atTop (nhds 0) := by
  exact kadiri_top_horizontal_vanishes_of_named_tendsto
    hφ hb hφ_decay hφ'_decay ha hab ha1
    (kadiriTopHorizontalIntegral_tendsto_zero_of_atTopBound hB)

theorem kadiri_bot_horizontal_vanishes_of_atTopBound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (hB : KadiriHorizontalAtTopBound φ a) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Filter.Tendsto
      (fun T : ℝ ↦
        (1 / (2 * (Real.pi : ℂ) * I)) *
          ∫ σ in Set.Ioo (-a) (1 + a),
            (-deriv riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) /
                riemannZeta ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) *
              Φ (-((σ : ℂ) + ((-T : ℝ) : ℂ) * I)))
      Filter.atTop (nhds 0) := by
  exact kadiri_bot_horizontal_vanishes_of_named_tendsto
    hφ hb hφ_decay hφ'_decay ha hab ha1
    (kadiriBotHorizontalIntegral_tendsto_zero_of_atTopBound hB)

end Kadiri
