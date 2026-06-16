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

end

end Kadiri
