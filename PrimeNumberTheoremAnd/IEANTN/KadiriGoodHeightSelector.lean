import PrimeNumberTheoremAnd.IEANTN.KadiriLocalZeroWindowCount
import Mathlib.MeasureTheory.Measure.Real

namespace Kadiri

open Complex Filter MeasureTheory

open scoped Topology

noncomputable section

/-- Non-trivial zeros whose ordinates can influence the dyadic height interval `[X, 2X]`
through a radius-one local zero window. -/
def kadiriDyadicZeroWindow (X : ℝ) : Set NontrivialZeros :=
  {rho | (rho : ℂ).im ∈ Set.Icc (X - 1) (2 * X + 1)}

theorem kadiriDyadicZeroWindow_finite_of_nonneg {X : ℝ} (hX : 0 ≤ X) :
    (kadiriDyadicZeroWindow X).Finite := by
  apply Set.Finite.subset (nontrivialZeros_abs_im_lt_finite (2 * X + 2))
  intro rho hrho
  rw [kadiriDyadicZeroWindow, Set.mem_setOf_eq] at hrho
  rw [Set.mem_setOf_eq]
  have hlow : -(2 * X + 1) ≤ (rho : ℂ).im := by
    calc
      -(2 * X + 1) ≤ X - 1 := by linarith
      _ ≤ (rho : ℂ).im := hrho.1
  have habs : |(rho : ℂ).im| ≤ 2 * X + 1 := abs_le.mpr ⟨hlow, hrho.2⟩
  linarith

/-- The bad interval around a zero ordinate for a candidate good-height radius `η`. -/
def kadiriZeroBadInterval (η : ℝ) (rho : NontrivialZeros) : Set ℝ :=
  Set.Icc ((rho : ℂ).im - η) ((rho : ℂ).im + η)

theorem kadiri_badInterval_volume_le (S : Finset NontrivialZeros) {η : ℝ} (_hη : 0 ≤ η) :
    volume (⋃ rho ∈ S, kadiriZeroBadInterval η rho) ≤
      ENNReal.ofReal ((S.card : ℝ) * (2 * η)) := by
  calc
    volume (⋃ rho ∈ S, kadiriZeroBadInterval η rho)
        ≤ ∑ rho ∈ S, volume (kadiriZeroBadInterval η rho) :=
          MeasureTheory.measure_biUnion_finset_le S (fun rho => kadiriZeroBadInterval η rho)
    _ = ∑ rho ∈ S, ENNReal.ofReal (2 * η) := by
        refine Finset.sum_congr rfl ?_
        intro rho _hrho
        rw [kadiriZeroBadInterval, Real.volume_Icc]
        ring_nf
    _ = S.card • ENNReal.ofReal (2 * η) := by simp
    _ = ENNReal.ofReal ((S.card : ℝ) * (2 * η)) := by
        rw [← ENNReal.ofReal_nsmul]
        rw [nsmul_eq_mul]

theorem kadiriDyadicBadInterval_volume_le {X η : ℝ} (hX : 0 ≤ X) (hη : 0 ≤ η) :
    volume
        (⋃ rho ∈ (kadiriDyadicZeroWindow_finite_of_nonneg (X := X) hX).toFinset,
          kadiriZeroBadInterval η rho) ≤
      ENNReal.ofReal (((kadiriDyadicZeroWindow X).ncard : ℝ) * (2 * η)) := by
  have hcard :
      (kadiriDyadicZeroWindow_finite_of_nonneg (X := X) hX).toFinset.card =
        (kadiriDyadicZeroWindow X).ncard := by
    rw [Set.ncard_eq_toFinset_card
      (kadiriDyadicZeroWindow X) (kadiriDyadicZeroWindow_finite_of_nonneg (X := X) hX)]
  simpa [hcard] using
    kadiri_badInterval_volume_le
      ((kadiriDyadicZeroWindow_finite_of_nonneg (X := X) hX).toFinset) hη

theorem exists_kadiriDyadicGoodHeight_of_card_mul_radius_lt {X η : ℝ}
    (hX : 0 < X) (hη : 0 ≤ η)
    (hsmall : ((kadiriDyadicZeroWindow X).ncard : ℝ) * (2 * η) < X) :
    ∃ T ∈ Set.Ioc X (2 * X),
      ∀ rho : NontrivialZeros, rho ∈ kadiriDyadicZeroWindow X →
        η < |T - (rho : ℂ).im| := by
  classical
  let S := (kadiriDyadicZeroWindow_finite_of_nonneg (X := X) hX.le).toFinset
  let bad : Set ℝ := ⋃ rho ∈ S, kadiriZeroBadInterval η rho
  have hbad_le :
      volume bad ≤ ENNReal.ofReal (((kadiriDyadicZeroWindow X).ncard : ℝ) * (2 * η)) := by
    dsimp [bad, S]
    exact kadiriDyadicBadInterval_volume_le (X := X) (η := η) hX.le hη
  have hbad_lt_ioc : volume bad < volume (Set.Ioc X (2 * X)) := by
    rw [Real.volume_Ioc, show 2 * X - X = X by ring]
    exact hbad_le.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hX).2 hsmall)
  by_contra hnone
  push Not at hnone
  have hcover : Set.Ioc X (2 * X) ⊆ bad := by
    intro T hT
    obtain ⟨rho, hrho, hle⟩ := hnone T hT
    have hrhoS : rho ∈ S := by
      dsimp [S]
      exact (kadiriDyadicZeroWindow_finite_of_nonneg (X := X) hX.le).mem_toFinset.mpr hrho
    have hTbad : T ∈ kadiriZeroBadInterval η rho := by
      rw [kadiriZeroBadInterval]
      have habs := abs_le.mp hle
      exact ⟨by linarith, by linarith⟩
    dsimp [bad]
    exact Set.mem_iUnion₂.mpr ⟨rho, hrhoS, hTbad⟩
  exact not_lt_of_ge (MeasureTheory.measure_mono hcover) hbad_lt_ioc

theorem exists_kadiriDyadicGoodHeightSelector :
    ∀ᶠ X : ℝ in atTop,
      ∀ η : ℝ, 0 ≤ η →
        ((kadiriDyadicZeroWindow X).ncard : ℝ) * (2 * η) < X →
          ∃ T ∈ Set.Ioc X (2 * X),
            ∀ rho : NontrivialZeros, rho ∈ kadiriDyadicZeroWindow X →
              η < |T - (rho : ℂ).im| := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with X hX η hη hsmall
  exact exists_kadiriDyadicGoodHeight_of_card_mul_radius_lt (X := X) (η := η)
    (by linarith) hη hsmall

/-- The dyadic good-height zero window at scale `2^k` is contained in the cumulative
dyadic zero-counting window below `2^(k+2)`. -/
theorem kadiriDyadicZeroWindow_ncard_le_cumulative_dyadic_count (k : ℕ) :
    (kadiriDyadicZeroWindow ((2 : ℝ) ^ k)).ncard ≤
      Nat.card {rho : NontrivialZeros // |(rho : ℂ).im| < (2 : ℝ) ^ (k + 2)} := by
  classical
  let target : Set NontrivialZeros := {rho | |(rho : ℂ).im| < (2 : ℝ) ^ (k + 2)}
  have htarget_fin : target.Finite := by
    dsimp [target]
    exact nontrivialZeros_abs_im_lt_finite ((2 : ℝ) ^ (k + 2))
  have hsub : kadiriDyadicZeroWindow ((2 : ℝ) ^ k) ⊆ target := by
    intro rho hrho
    rw [kadiriDyadicZeroWindow, Set.mem_setOf_eq] at hrho
    dsimp [target]
    have hXpos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
    have hXge1 : 1 ≤ (2 : ℝ) ^ k :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have him_nonneg : 0 ≤ (rho : ℂ).im := by linarith [hrho.1, hXge1]
    have habs : |(rho : ℂ).im| = (rho : ℂ).im := abs_of_nonneg him_nonneg
    rw [habs]
    have hpow : (2 : ℝ) ^ (k + 2) = 4 * (2 : ℝ) ^ k := by
      rw [show k + 2 = k + 1 + 1 by omega, pow_succ, pow_succ]
      ring
    rw [hpow]
    linarith [hrho.2, hXpos, hXge1]
  have hcard := Set.ncard_le_ncard hsub htarget_fin
  rw [← Nat.card_coe_set_eq target] at hcard
  exact hcard

/-- Concrete dyadic cardinal profile for the good-height zero window, derived from the
existing cumulative dyadic zero-counting source. -/
theorem exists_kadiriDyadicZeroWindow_card_le_count_profile
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      ((kadiriDyadicZeroWindow ((2 : ℝ) ^ k)).ncard : ℝ) ≤
        C * (((k + 2 : ℕ) : ℝ)) * ((2 : ℝ) ^ (k + 1)) := by
  rcases hsrc with ⟨C, hC, hcount⟩
  refine ⟨C, hC, ?_⟩
  intro k
  have hcard_nat := kadiriDyadicZeroWindow_ncard_le_cumulative_dyadic_count k
  have hcardR :
      ((kadiriDyadicZeroWindow ((2 : ℝ) ^ k)).ncard : ℝ) ≤
        (Nat.card {rho : NontrivialZeros // |(rho : ℂ).im| < (2 : ℝ) ^ (k + 2)} :
          ℝ) := by
    exact_mod_cast hcard_nat
  have hcount_succ := hcount (k + 1)
  have hcount_succ_bound :
      (Nat.card {rho : NontrivialZeros // |(rho : ℂ).im| < (2 : ℝ) ^ (k + 2)} :
          ℝ) ≤
        C * (((k + 2 : ℕ) : ℝ)) * ((2 : ℝ) ^ (k + 1)) := by
    simpa [show k + 1 + 1 = k + 2 by omega] using hcount_succ
  exact hcardR.trans hcount_succ_bound

/--
Dyadic quantitative good-height selector with the radius chosen from the concrete
zero-count/coarse-budget profile.

The output no longer carries the earlier cardinal-radius smallness hypothesis: the
source `zeroImagDyadicCumulativeCountBoundSource` supplies a constant `C`, and the proof
chooses a universal `c > 0` so that `c / log(2^k)` is below the radius allowed by the
finite-union bad-interval measure bound for all large dyadic levels.
-/
theorem exists_kadiriDyadicGoodHeightSelector_logRadius
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      ∃ T ∈ Set.Ioc ((2 : ℝ) ^ k) (2 * ((2 : ℝ) ^ k)),
        ∀ rho : NontrivialZeros, rho ∈ kadiriDyadicZeroWindow ((2 : ℝ) ^ k) →
          c / Real.log ((2 : ℝ) ^ k) < |T - (rho : ℂ).im| := by
  obtain ⟨C, hC, hcount⟩ := exists_kadiriDyadicZeroWindow_card_le_count_profile hsrc
  let c : ℝ := Real.log 2 / (64 * (C + 1))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC1 : 0 < C + 1 := by linarith
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hc_pos, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with k hk
  let X : ℝ := (2 : ℝ) ^ k
  let K : ℝ := ((k + 2 : ℕ) : ℝ)
  let η : ℝ := (16 * (C + 1) * K)⁻¹
  have hX_pos : 0 < X := by
    dsimp [X]
    exact pow_pos (by norm_num) k
  have hK_pos : 0 < K := by
    dsimp [K]
    exact_mod_cast Nat.succ_pos (k + 1)
  have hη_nonneg : 0 ≤ η := by
    dsimp [η]
    positivity
  have hcard :
      ((kadiriDyadicZeroWindow X).ncard : ℝ) ≤ C * K * (2 * X) := by
    have hcountk := hcount k
    have hpow_succ : (2 : ℝ) ^ (k + 1) = 2 * X := by
      dsimp [X]
      rw [pow_succ]
      ring
    simpa [X, K, hpow_succ] using hcountk
  have hsmall :
      ((kadiriDyadicZeroWindow X).ncard : ℝ) * (2 * η) < X := by
    have hmul_nonneg : 0 ≤ 2 * η := by positivity
    have hle :
        ((kadiriDyadicZeroWindow X).ncard : ℝ) * (2 * η) ≤
          (C * K * (2 * X)) * (2 * η) :=
      mul_le_mul_of_nonneg_right hcard hmul_nonneg
    have hlt : (C * K * (2 * X)) * (2 * η) < X := by
      dsimp [η]
      rw [inv_eq_one_div]
      have hden : 0 < 16 * (C + 1) * K := by positivity
      field_simp [ne_of_gt hden]
      nlinarith [mul_pos hC1 hX_pos]
    exact hle.trans_lt hlt
  obtain ⟨T, hT, hgap⟩ :=
    exists_kadiriDyadicGoodHeight_of_card_mul_radius_lt (X := X) (η := η)
      hX_pos hη_nonneg hsmall
  refine ⟨T, ?_, ?_⟩
  · simpa [X] using hT
  · intro rho hrho
    have hgap_eta : η < |T - (rho : ℂ).im| := hgap rho (by simpa [X] using hrho)
    have hk_pos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
    have hk_ne : k ≠ 0 := by omega
    have hX_gt_one : 1 < X := by
      dsimp [X]
      exact one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) hk_ne
    have hlogX_pos : 0 < Real.log X := Real.log_pos hX_gt_one
    have hlogX_eq : Real.log X = (k : ℝ) * Real.log 2 := by
      dsimp [X]
      rw [Real.log_pow]
    have hK_le : K ≤ 4 * (k : ℝ) := by
      dsimp [K]
      have hk_nat : k + 2 ≤ 4 * k := by omega
      exact_mod_cast hk_nat
    have hlog_radius_le : c / Real.log X ≤ η := by
      dsimp [c, η]
      rw [hlogX_eq]
      have hden1 : 0 < 64 * (C + 1) := by positivity
      have hden2 : 0 < (k : ℝ) * Real.log 2 := mul_pos hk_pos hlog2
      have hden3 : 0 < 16 * (C + 1) * K := by positivity
      rw [inv_eq_one_div]
      field_simp [ne_of_gt hden1, ne_of_gt hden2, ne_of_gt hden3, ne_of_gt hlog2,
        ne_of_gt hk_pos, ne_of_gt hC1]
      nlinarith
    exact lt_of_le_of_lt hlog_radius_le hgap_eta

end

end Kadiri
