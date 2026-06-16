import PrimeNumberTheoremAnd.IEANTN.KadiriLogDerivFullSegment

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

end Kadiri
