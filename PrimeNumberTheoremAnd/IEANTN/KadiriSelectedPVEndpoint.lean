import PrimeNumberTheoremAnd.IEANTN.KadiriHadamardPVBridge

/-!
# Selected good-height Hadamard/PV endpoint handoffs

This module specializes the existing dyadic Hadamard/PV endpoint handoffs to the
selected good-height filter.  The analytic remainder estimate is still a real input:
these wrappers remove only the generic off-pole-filter plumbing.
-/

noncomputable section

namespace Kadiri

open Complex Filter MeasureTheory
open scoped Topology Interval

/--
Endpoint-facing form of the quantitative selected-height budget.

The concrete dyadic zero-count source gives a constant `c > 0` such that the endpoint may
choose the radius `η = c / log(2^k)` for all large dyadic levels.  This packages both the
cardinality-radius smallness certificate and the selected height, so downstream endpoint
code does not carry `hsmall` as a separate hypothesis.
-/
theorem exists_kadiriDyadicGoodHeightSelector_logRadius_with_budget
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      let η : ℝ := c / Real.log ((2 : ℝ) ^ k)
      0 ≤ η ∧
      ((kadiriDyadicZeroWindow ((2 : ℝ) ^ k)).ncard : ℝ) *
          (2 * η) < (2 : ℝ) ^ k ∧
      ∃ T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)),
        ∀ rho : NontrivialZeros, rho ∈ kadiriDyadicZeroWindow ((2 : ℝ) ^ k) →
          η < |T - (rho : ℂ).im| := by
  obtain ⟨c, hc, hbudget⟩ :=
    exists_kadiriDyadicGoodHeightSelector_logRadius_budget hsrc
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbudget, Filter.eventually_ge_atTop (1 : ℕ)] with k hbudget_k hk
  let η : ℝ := c / Real.log ((2 : ℝ) ^ k)
  have hX_pos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
  have hk_ne : k ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hX_gt_one : 1 < (2 : ℝ) ^ k :=
    one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) hk_ne
  have hlog_pos : 0 < Real.log ((2 : ℝ) ^ k) := Real.log_pos hX_gt_one
  have hη_nonneg : 0 ≤ η := by
    dsimp [η]
    positivity
  have hsmall :
      ((kadiriDyadicZeroWindow ((2 : ℝ) ^ k)).ncard : ℝ) * (2 * η) <
        (2 : ℝ) ^ k :=
    hbudget_k η hη_nonneg le_rfl
  obtain ⟨T, hT, hgap⟩ :=
    exists_kadiriDyadicGoodHeight_of_card_mul_radius_lt
      (X := (2 : ℝ) ^ k) (η := η) hX_pos hη_nonneg hsmall
  exact ⟨hη_nonneg, hsmall, T, hT, hgap⟩

/-- The concrete dyadic Hadamard/PV remainder is integrable on selected good heights. -/
theorem eventually_kadiriDyadicHadamardPVRemainder_intervalIntegrable_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
      IntervalIntegrable (fun σ : ℝ => kadiriDyadicHadamardPVRemainder k T σ)
        volume (-a) (1 + a) := by
  filter_upwards [eventually_kadiriDyadicGoodHeightFilter_offPole hsrc] with T hT
  exact kadiriDyadicHadamardPVRemainder_intervalIntegrable_of_offPole a T ha k hT

/--
Pointwise control of the concrete dyadic Hadamard/PV remainder on selected good heights
supplies the selected-filter integral budget.
-/
theorem
    eventually_kadiriDyadicHadamardPVRemainder_integral_bound_of_pointwise_bound_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (B : ℝ)
    (hpoint : ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
      ∀ σ ∈ Ι (-a) (1 + a),
        ‖kadiriDyadicHadamardPVRemainder k T σ‖ ≤ B) :
    ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
      ‖∫ σ in (-a)..(1 + a), kadiriDyadicHadamardPVRemainder k T σ‖ ≤
        B * (1 + 2 * a) := by
  filter_upwards [hpoint] with T hT_point
  exact kadiriDyadicHadamardPVRemainder_integral_bound_of_pointwise_bound
    a T ha k B hT_point

/--
Selected-good-height endpoint bound from a concrete Hadamard/PV remainder integral budget.

This is the selected-filter specialization of the existing concrete dyadic endpoint
assembly; it discharges the off-pole and integrability obligations from the selector.
-/
theorem
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_concrete_remainder_budget_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (a e : ℝ) (ha : 0 ≤ a) (he : 0 < e) (hea : e ≤ a) (k : ℕ) (B : ℝ)
    (hrem_bound : ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
      ‖∫ σ in (-a)..(1 + a), kadiriDyadicHadamardPVRemainder k T σ‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
              weightedZeroHeightBucket) * C + B := by
  exact
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_concrete_remainder_budget_on_filter
      a e he hea k B (kadiriDyadicGoodHeightFilter hsrc)
      (kadiriDyadicGoodHeightFilter_le_cofinite hsrc)
      (eventually_kadiriDyadicHadamardPVRemainder_intervalIntegrable_on_dyadicGoodHeightFilter
        hsrc a ha k)
      hrem_bound

/--
Selected-good-height endpoint bound from pointwise control of the concrete
Hadamard/PV remainder.
-/
theorem
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_concrete_remainder_pointwise_bound_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (a e : ℝ) (ha : 0 ≤ a) (he : 0 < e) (hea : e ≤ a) (k : ℕ) (B : ℝ)
    (hpoint : ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
      ∀ σ ∈ Ι (-a) (1 + a),
        ‖kadiriDyadicHadamardPVRemainder k T σ‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
              weightedZeroHeightBucket) * C + B * (1 + 2 * a) := by
  exact
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_concrete_remainder_budget_on_dyadicGoodHeightFilter
      hsrc a e ha he hea k (B * (1 + 2 * a))
      (eventually_kadiriDyadicHadamardPVRemainder_integral_bound_of_pointwise_bound_on_dyadicGoodHeightFilter
        hsrc a ha k B hpoint)

/--
Selected-good-height endpoint bound from an integral budget for the sign-correct zeta
Hadamard/PV remainder.
-/
theorem
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_zeta_remainder_bound_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (a e : ℝ) (ha : 0 ≤ a) (he : 0 < e) (hea : e ≤ a) (k : ℕ) (B : ℝ)
    (hzeta_rem_bound : ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
      ‖∫ σ in (-a)..(1 + a), kadiriDyadicZetaLogDerivPVRemainder k T σ‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (2 * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
              weightedZeroHeightBucket) * C + B := by
  exact
    kadiri_logDeriv_zeta_full_segment_dyadic_offpole_eventually_bound_of_zeta_remainder_bound_on_filter
      a e ha he hea k B (kadiriDyadicGoodHeightFilter hsrc)
      (kadiriDyadicGoodHeightFilter_le_cofinite hsrc)
      (eventually_kadiriDyadicGoodHeightFilter_offPole hsrc)
      hzeta_rem_bound

/--
A local Hadamard/PV remainder bound proved directly for the selected good-height sequence
is the same bound on the selected good-height filter.
-/
theorem eventually_kadiriDyadicGoodHeightFilter_localPVRemainder_logSq_of_sequence
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ k : ℕ in atTop,
      ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
        ‖kadiriLocalZetaLogDerivPVRemainder (kadiriDyadicGoodHeightSequence hsrc k) σ‖ ≤
          R * Real.log |kadiriDyadicGoodHeightSequence hsrc k| ^ (2 : ℕ)) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
          ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
            R * Real.log |T| ^ (2 : ℕ) := by
  obtain ⟨R, hR, hrem_event⟩ := hrem
  refine ⟨R, hR, ?_⟩
  rw [kadiriDyadicGoodHeightFilter]
  change ∀ᶠ k : ℕ in atTop,
    ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
      ‖kadiriLocalZetaLogDerivPVRemainder (kadiriDyadicGoodHeightSequence hsrc k) σ‖ ≤
        R * Real.log |kadiriDyadicGoodHeightSequence hsrc k| ^ (2 : ℕ)
  exact hrem_event

theorem eventually_kadiriDyadicGoodHeightSequence_localPVRemainder_logSq_of_candidate
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ k : ℕ in atTop,
      ∀ T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)),
        kadiriHorizontalZetaOffPoleHeight T →
          ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
            ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
              R * Real.log |T| ^ (2 : ℕ)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ k : ℕ in atTop,
      ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
        ‖kadiriLocalZetaLogDerivPVRemainder (kadiriDyadicGoodHeightSequence hsrc k) σ‖ ≤
          R * Real.log |kadiriDyadicGoodHeightSequence hsrc k| ^ (2 : ℕ) := by
  obtain ⟨R, hR, hrem_event⟩ := hrem
  refine ⟨R, hR, ?_⟩
  filter_upwards [eventually_kadiriDyadicGoodHeightSequence_spec hsrc, hrem_event]
    with k hspec hrem_k
  intro σ hσ
  exact hrem_k (kadiriDyadicGoodHeightSequence hsrc k) hspec.1 hspec.2.1 σ hσ

/--
A selected signed horizontal `log^2` bound is equivalent, up to the already-proved local
principal `log^2` budget, to selected local Hadamard/PV remainder control.
-/
theorem
    eventually_kadiriDyadicGoodHeightFilter_localPVRemainder_logSq_of_positiveHorizontalSegmentLogDerivBound
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hseg : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        kadiriPositiveHorizontalSegmentLogDerivBound (-1) 2 T C) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
          ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
            R * Real.log |T| ^ (2 : ℕ) := by
  obtain ⟨P, hP, hprincipal⟩ :=
    eventually_kadiriDyadicGoodHeightFilter_localPrincipal_logSq hsrc
  obtain ⟨C, hC, hseg_event⟩ := hseg
  refine ⟨C + P, add_nonneg hC hP, ?_⟩
  filter_upwards [hseg_event, hprincipal] with T hseg_T hprincipal_T
  intro σ hσ
  let logDerivTerm : ℂ :=
    deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
      riemannZeta (((σ : ℂ) + (T : ℂ) * I))
  let principal : ℂ :=
    ∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
      ((riemannZeta.order (rho : ℂ) : ℂ) /
        (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))
  have hrem_eq :
      kadiriLocalZetaLogDerivPVRemainder T σ = logDerivTerm - principal := by
    rfl
  have hlog :
      ‖logDerivTerm‖ ≤ C * Real.log |T| ^ (2 : ℕ) := by
    simpa [logDerivTerm] using hseg_T σ hσ
  have hprincipal_bound :
      ‖principal‖ ≤ P * Real.log |T| ^ (2 : ℕ) := by
    simpa [principal] using hprincipal_T σ
  calc
    ‖kadiriLocalZetaLogDerivPVRemainder T σ‖
        = ‖logDerivTerm - principal‖ := by rw [hrem_eq]
    _ ≤ ‖logDerivTerm‖ + ‖principal‖ := norm_sub_le logDerivTerm principal
    _ ≤ C * Real.log |T| ^ (2 : ℕ) + P * Real.log |T| ^ (2 : ℕ) :=
        add_le_add hlog hprincipal_bound
    _ = (C + P) * Real.log |T| ^ (2 : ℕ) := by ring

/--
Absolute-height horizontal `log^2` control on the selected filter is the same remaining
analytic input as selected local Hadamard/PV remainder control.
-/
theorem
    eventually_kadiriDyadicGoodHeightFilter_localPVRemainder_logSq_of_horizontalSegmentLogDerivBound
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hseg : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        kadiriHorizontalSegmentLogDerivBound (-1) 2 |T| C) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
          ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
            R * Real.log |T| ^ (2 : ℕ) := by
  obtain ⟨P, hP, hprincipal⟩ :=
    eventually_kadiriDyadicGoodHeightFilter_localPrincipal_logSq hsrc
  obtain ⟨C, hC, hseg_event⟩ := hseg
  refine ⟨C + P, add_nonneg hC hP, ?_⟩
  filter_upwards [hseg_event, hprincipal] with T hseg_T hprincipal_T
  intro σ hσ
  let logDerivTerm : ℂ :=
    deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
      riemannZeta (((σ : ℂ) + (T : ℂ) * I))
  let principal : ℂ :=
    ∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
      ((riemannZeta.order (rho : ℂ) : ℂ) /
        (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))
  have hrem_eq :
      kadiriLocalZetaLogDerivPVRemainder T σ = logDerivTerm - principal := by
    rfl
  have hlog :
      ‖logDerivTerm‖ ≤ C * Real.log |T| ^ (2 : ℕ) := by
    simpa [logDerivTerm] using hseg_T σ hσ T rfl
  have hprincipal_bound :
      ‖principal‖ ≤ P * Real.log |T| ^ (2 : ℕ) := by
    simpa [principal] using hprincipal_T σ
  calc
    ‖kadiriLocalZetaLogDerivPVRemainder T σ‖
        = ‖logDerivTerm - principal‖ := by rw [hrem_eq]
    _ ≤ ‖logDerivTerm‖ + ‖principal‖ := norm_sub_le logDerivTerm principal
    _ ≤ C * Real.log |T| ^ (2 : ℕ) + P * Real.log |T| ^ (2 : ℕ) :=
        add_le_add hlog hprincipal_bound
    _ = (C + P) * Real.log |T| ^ (2 : ℕ) := by ring

/--
Selected local Hadamard/PV `log^2` control combines with the selector's distance gap and
local zero-count bound to give the two-sided horizontal segment `log^2` bound.
-/
theorem
    eventually_kadiriDyadicGoodHeightFilter_horizontalSegmentLogDerivBound_of_sequence_localPVRemainder
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ k : ℕ in atTop,
      ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
        ‖kadiriLocalZetaLogDerivPVRemainder (kadiriDyadicGoodHeightSequence hsrc k) σ‖ ≤
          R * Real.log |kadiriDyadicGoodHeightSequence hsrc k| ^ (2 : ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        kadiriHorizontalSegmentLogDerivBound (-1) 2 T C :=
  eventually_kadiriDyadicGoodHeightFilter_horizontalSegmentLogDerivBound_of_localPVRemainder
    hsrc (eventually_kadiriDyadicGoodHeightFilter_localPVRemainder_logSq_of_sequence
      hsrc hrem)

/--
Absolute-height form of
`eventually_kadiriDyadicGoodHeightFilter_horizontalSegmentLogDerivBound_of_sequence_localPVRemainder`,
matching the endpoint consumer.
-/
theorem
    eventually_kadiriDyadicGoodHeightFilter_abs_horizontalSegmentLogDerivBound_of_sequence_localPVRemainder
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ k : ℕ in atTop,
      ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
        ‖kadiriLocalZetaLogDerivPVRemainder (kadiriDyadicGoodHeightSequence hsrc k) σ‖ ≤
          R * Real.log |kadiriDyadicGoodHeightSequence hsrc k| ^ (2 : ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        kadiriHorizontalSegmentLogDerivBound (-1) 2 |T| C :=
  eventually_kadiriDyadicGoodHeightFilter_abs_horizontalSegmentLogDerivBound_of_horizontalSegmentLogDerivBound
    hsrc
    (eventually_kadiriDyadicGoodHeightFilter_horizontalSegmentLogDerivBound_of_sequence_localPVRemainder
      hsrc hrem)

/--
Selected-filter budget package and horizontal `log^2` bound in one eventual statement.

This is the endpoint-facing selected-height handoff: the concrete radius budget and
zero-gap facts travel with the horizontal segment bound obtained from the local
Hadamard/PV remainder estimate.
-/
theorem
    eventually_kadiriDyadicGoodHeightFilter_budget_and_abs_horizontalSegmentLogDerivBound_of_sequence_localPVRemainder
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ k : ℕ in atTop,
      ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
        ‖kadiriLocalZetaLogDerivPVRemainder (kadiriDyadicGoodHeightSequence hsrc k) σ‖ ≤
          R * Real.log |kadiriDyadicGoodHeightSequence hsrc k| ^ (2 : ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        (∃ k : ℕ,
          T = kadiriDyadicGoodHeightSequence hsrc k ∧
          let η : ℝ := kadiriDyadicGoodHeightRadius hsrc / Real.log ((2 : ℝ) ^ k)
          0 ≤ η ∧
          ((kadiriDyadicZeroWindow ((2 : ℝ) ^ k)).ncard : ℝ) *
              (2 * η) < (2 : ℝ) ^ k ∧
          T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)) ∧
          kadiriHorizontalZetaOffPoleHeight T ∧
          (∀ rho : NontrivialZeros, rho ∈ kadiriDyadicZeroWindow ((2 : ℝ) ^ k) →
            η < |T - (rho : ℂ).im|) ∧
          (∀ rho : NontrivialZeros, rho ∈ kadiriLocalZeroWindow T →
            η < |T - (rho : ℂ).im|)) ∧
        kadiriHorizontalSegmentLogDerivBound (-1) 2 |T| C := by
  obtain ⟨C, hC, hseg⟩ :=
    eventually_kadiriDyadicGoodHeightFilter_abs_horizontalSegmentLogDerivBound_of_sequence_localPVRemainder
      hsrc hrem
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_kadiriDyadicGoodHeightFilter_spec_with_budget hsrc, hseg]
    with T hbudget hseg_T
  exact ⟨hbudget, hseg_T⟩

theorem
    eventually_kadiriDyadicGoodHeightFilter_budget_and_positiveLogDeriv_logSq_of_sequence_localPVRemainder
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ k : ℕ in atTop,
      ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
        ‖kadiriLocalZetaLogDerivPVRemainder (kadiriDyadicGoodHeightSequence hsrc k) σ‖ ≤
          R * Real.log |kadiriDyadicGoodHeightSequence hsrc k| ^ (2 : ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        (∃ k : ℕ,
          T = kadiriDyadicGoodHeightSequence hsrc k ∧
          let η : ℝ := kadiriDyadicGoodHeightRadius hsrc / Real.log ((2 : ℝ) ^ k)
          0 ≤ η ∧
          ((kadiriDyadicZeroWindow ((2 : ℝ) ^ k)).ncard : ℝ) *
              (2 * η) < (2 : ℝ) ^ k ∧
          T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)) ∧
          kadiriHorizontalZetaOffPoleHeight T ∧
          (∀ rho : NontrivialZeros, rho ∈ kadiriDyadicZeroWindow ((2 : ℝ) ^ k) →
            η < |T - (rho : ℂ).im|) ∧
          (∀ rho : NontrivialZeros, rho ∈ kadiriLocalZeroWindow T →
            η < |T - (rho : ℂ).im|)) ∧
        kadiriPositiveHorizontalSegmentLogDerivBound (-1) 2 T C :=
  eventually_kadiriDyadicGoodHeightFilter_budget_and_positiveLogDeriv_logSq_of_localPVRemainder
    hsrc (eventually_kadiriDyadicGoodHeightFilter_localPVRemainder_logSq_of_sequence
      hsrc hrem)

theorem
    eventually_kadiriDyadicGoodHeightFilter_budget_and_abs_horizontalSegmentLogDerivBound_of_candidate_localPVRemainder
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ k : ℕ in atTop,
      ∀ T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)),
        kadiriHorizontalZetaOffPoleHeight T →
          ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
            ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
              R * Real.log |T| ^ (2 : ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        (∃ k : ℕ,
          T = kadiriDyadicGoodHeightSequence hsrc k ∧
          let η : ℝ := kadiriDyadicGoodHeightRadius hsrc / Real.log ((2 : ℝ) ^ k)
          0 ≤ η ∧
          ((kadiriDyadicZeroWindow ((2 : ℝ) ^ k)).ncard : ℝ) *
              (2 * η) < (2 : ℝ) ^ k ∧
          T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)) ∧
          kadiriHorizontalZetaOffPoleHeight T ∧
          (∀ rho : NontrivialZeros, rho ∈ kadiriDyadicZeroWindow ((2 : ℝ) ^ k) →
            η < |T - (rho : ℂ).im|) ∧
          (∀ rho : NontrivialZeros, rho ∈ kadiriLocalZeroWindow T →
            η < |T - (rho : ℂ).im|)) ∧
        kadiriHorizontalSegmentLogDerivBound (-1) 2 |T| C :=
  eventually_kadiriDyadicGoodHeightFilter_budget_and_abs_horizontalSegmentLogDerivBound_of_sequence_localPVRemainder
    hsrc
    (eventually_kadiriDyadicGoodHeightSequence_localPVRemainder_logSq_of_candidate hsrc hrem)

theorem
    eventually_kadiriDyadicGoodHeightFilter_budget_and_positiveLogDeriv_logSq_of_candidate_localPVRemainder
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ k : ℕ in atTop,
      ∀ T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)),
        kadiriHorizontalZetaOffPoleHeight T →
          ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
            ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
              R * Real.log |T| ^ (2 : ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        (∃ k : ℕ,
          T = kadiriDyadicGoodHeightSequence hsrc k ∧
          let η : ℝ := kadiriDyadicGoodHeightRadius hsrc / Real.log ((2 : ℝ) ^ k)
          0 ≤ η ∧
          ((kadiriDyadicZeroWindow ((2 : ℝ) ^ k)).ncard : ℝ) *
              (2 * η) < (2 : ℝ) ^ k ∧
          T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)) ∧
          kadiriHorizontalZetaOffPoleHeight T ∧
          (∀ rho : NontrivialZeros, rho ∈ kadiriDyadicZeroWindow ((2 : ℝ) ^ k) →
            η < |T - (rho : ℂ).im|) ∧
          (∀ rho : NontrivialZeros, rho ∈ kadiriLocalZeroWindow T →
            η < |T - (rho : ℂ).im|)) ∧
        kadiriPositiveHorizontalSegmentLogDerivBound (-1) 2 T C :=
  eventually_kadiriDyadicGoodHeightFilter_budget_and_positiveLogDeriv_logSq_of_sequence_localPVRemainder
    hsrc
    (eventually_kadiriDyadicGoodHeightSequence_localPVRemainder_logSq_of_candidate hsrc hrem)

/--
Endpoint handoff from a selected-sequence local Hadamard/PV remainder bound.

This is the narrow selected-height route: the selector provides the off-pole/gap data and
local principal `log^2` control, while the only remaining input is the analytic local
Hadamard/PV remainder estimate along the selected sequence.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_sequence_localPVRemainder_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ n : ℕ in atTop,
      ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
        ‖kadiriLocalZetaLogDerivPVRemainder (kadiriDyadicGoodHeightSequence hsrc n) σ‖ ≤
          R * Real.log |kadiriDyadicGoodHeightSequence hsrc n| ^ (2 : ℕ)) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp :=
  eventually_kadiri_logDeriv_zeta_full_segment_bound_of_localPVRemainder_on_dyadicGoodHeightFilter
    hsrc a ha k
    (eventually_kadiriDyadicGoodHeightFilter_localPVRemainder_logSq_of_sequence
      hsrc hrem)

/--
Endpoint handoff retaining the selected-filter budget certificate alongside the
full-segment estimate.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_with_budget_of_sequence_localPVRemainder_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ n : ℕ in atTop,
      ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
        ‖kadiriLocalZetaLogDerivPVRemainder (kadiriDyadicGoodHeightSequence hsrc n) σ‖ ≤
          R * Real.log |kadiriDyadicGoodHeightSequence hsrc n| ^ (2 : ℕ)) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        (∃ n : ℕ,
          T = kadiriDyadicGoodHeightSequence hsrc n ∧
          let η : ℝ := kadiriDyadicGoodHeightRadius hsrc / Real.log ((2 : ℝ) ^ n)
          0 ≤ η ∧
          ((kadiriDyadicZeroWindow ((2 : ℝ) ^ n)).ncard : ℝ) *
              (2 * η) < (2 : ℝ) ^ n ∧
          T ∈ Set.Ioc ((2 : ℝ) ^ n) (2 * ((2 : ℝ) ^ n)) ∧
          kadiriHorizontalZetaOffPoleHeight T ∧
          (∀ rho : NontrivialZeros, rho ∈ kadiriDyadicZeroWindow ((2 : ℝ) ^ n) →
            η < |T - (rho : ℂ).im|) ∧
          (∀ rho : NontrivialZeros, rho ∈ kadiriLocalZeroWindow T →
            η < |T - (rho : ℂ).im|)) ∧
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp := by
  obtain ⟨e, M, C, Cp, he, hM, hC, hCp, hendpoint⟩ :=
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_sequence_localPVRemainder_on_dyadicGoodHeightFilter
      hsrc a ha k hrem
  refine ⟨e, M, C, Cp, he, hM, hC, hCp, ?_⟩
  filter_upwards [eventually_kadiriDyadicGoodHeightFilter_spec_with_budget hsrc, hendpoint]
    with T hbudget hendpoint_T
  exact ⟨hbudget, hendpoint_T⟩

theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_with_budget_of_candidate_localPVRemainder_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hrem : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ n : ℕ in atTop,
      ∀ T ∈ Set.Ioc ((2 : ℝ) ^ n) (2 * ((2 : ℝ) ^ n)),
        kadiriHorizontalZetaOffPoleHeight T →
          ∀ σ ∈ Set.uIcc (-1 : ℝ) 2,
            ‖kadiriLocalZetaLogDerivPVRemainder T σ‖ ≤
              R * Real.log |T| ^ (2 : ℕ)) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        (∃ n : ℕ,
          T = kadiriDyadicGoodHeightSequence hsrc n ∧
          let η : ℝ := kadiriDyadicGoodHeightRadius hsrc / Real.log ((2 : ℝ) ^ n)
          0 ≤ η ∧
          ((kadiriDyadicZeroWindow ((2 : ℝ) ^ n)).ncard : ℝ) *
              (2 * η) < (2 : ℝ) ^ n ∧
          T ∈ Set.Ioc ((2 : ℝ) ^ n) (2 * ((2 : ℝ) ^ n)) ∧
          kadiriHorizontalZetaOffPoleHeight T ∧
          (∀ rho : NontrivialZeros, rho ∈ kadiriDyadicZeroWindow ((2 : ℝ) ^ n) →
            η < |T - (rho : ℂ).im|) ∧
          (∀ rho : NontrivialZeros, rho ∈ kadiriLocalZeroWindow T →
            η < |T - (rho : ℂ).im|)) ∧
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp :=
  eventually_kadiri_logDeriv_zeta_full_segment_bound_with_budget_of_sequence_localPVRemainder_on_dyadicGoodHeightFilter
    hsrc a ha k
    (eventually_kadiriDyadicGoodHeightSequence_localPVRemainder_logSq_of_candidate hsrc hrem)

theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_titchmarshPartialFraction_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hpartial :
      kadiriTitchmarshLocalPartialFractionLogBoundOnFilter
        (kadiriDyadicGoodHeightFilter hsrc)) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp :=
  eventually_kadiri_logDeriv_zeta_full_segment_bound_of_localPVRemainder_on_dyadicGoodHeightFilter
    hsrc a ha k
    (eventually_kadiriDyadicGoodHeightFilter_localPVRemainder_logSq_of_titchmarshPartialFraction
      hsrc hpartial)

/--
Closed selected-height endpoint: the Hadamard/PV bridge supplies the Titchmarsh
partial-fraction input, so the endpoint no longer carries `hpartial`.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_titchmarshPartialFraction_closed_on_dyadicGoodHeightFilter
    (hsrc : zeroImagDyadicCumulativeCountBoundSource)
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in kadiriDyadicGoodHeightFilter hsrc,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp :=
  eventually_kadiri_logDeriv_zeta_full_segment_bound_of_titchmarshPartialFraction_on_dyadicGoodHeightFilter
    hsrc a ha k
    (kadiriTitchmarshLocalPartialFractionLogBoundOnFilter_of_dyadicGoodHeight hsrc)

/--
Unconditional selected-height endpoint: the local-window zero-count producer
supplies the dyadic good-height source.
-/
theorem
    eventually_kadiri_logDeriv_zeta_full_segment_bound_of_titchmarshPartialFraction_unconditional_on_dyadicGoodHeightFilter
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    ∃ e M C Cp : ℝ, 0 < e ∧ 0 ≤ M ∧ 0 ≤ C ∧ 0 ≤ Cp ∧
      ∀ᶠ T : ℝ in
          kadiriDyadicGoodHeightFilter
            zeroImagDyadicCumulativeCountBoundSource_of_local_window,
        ‖∫ σ in (-a)..(1 + a),
            -deriv riemannZeta (((σ : ℂ) + (T : ℂ) * I)) /
              riemannZeta (((σ : ℂ) + (T : ℂ) * I))‖
          ≤ (C * Real.log |T| ^ 9) * (1 + 2 * a) + |Real.log Real.pi| * a +
              (((kadiriTruncatedNontrivialZeros ((2 : ℝ) ^ (k + 1))).card : ℝ) *
                M) * Cp :=
  eventually_kadiri_logDeriv_zeta_full_segment_bound_of_titchmarshPartialFraction_on_dyadicGoodHeightFilter
    zeroImagDyadicCumulativeCountBoundSource_of_local_window a ha k
    kadiriTitchmarshLocalPartialFractionLogBoundOnFilter_unconditional

end Kadiri
