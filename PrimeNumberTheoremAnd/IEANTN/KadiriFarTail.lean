import PrimeNumberTheoremAnd.IEANTN.KadiriHadamardTruncation
import PrimeNumberTheoremAnd.IEANTN.KadiriLocalZeroWindowCount

/-!
# Unit-band far-tail bounds for Kadiri

This file isolates the finite band estimate used in the far-tail part of the
Titchmarsh local partial-fraction bound.  The infinite summation still has to
sum these unit bands, but each band now has the required multiplicity-weighted
pointwise estimate against the U6a local zero count.
-/

namespace Kadiri

open Complex
open scoped BigOperators

noncomputable section

/-- The paired Hadamard zero contribution over the upper unit band
`T + n + 1 <= Im rho <= T + n + 2`. -/
noncomputable def kadiriUpperUnitBandPairedDiffSum (T σ : ℝ) (n : ℕ) : ℝ :=
  riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1)
    (.Icc (T + ((n : ℝ) + 1)) (T + ((n : ℝ) + 2)))
    fun ρ =>
      ‖(1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - ρ) -
        (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ)‖

/-- The upper unit band is finite. -/
theorem kadiriUpperUnitBandZeroesRect_finite (T : ℝ) (n : ℕ) :
    (riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1)
      (.Icc (T + ((n : ℝ) + 1)) (T + ((n : ℝ) + 2)))).Finite := by
  let u : ℝ := T + ((n : ℝ) + 3 / 2)
  apply Set.Finite.subset (u6aFTNearbyWindow_finite u)
  intro ρ hρ
  obtain ⟨hre, him, hζ⟩ := hρ
  unfold u6aFTNearbyWindow riemannZeta.zeroes_rect
  refine ⟨?_, ?_, hζ⟩
  · rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
    exact ⟨by linarith [hre.1], by linarith [hre.2]⟩
  · dsimp [u]
    exact ⟨by linarith [him.1], by linarith [him.2]⟩

/--
Each upper unit band contributes at most `3 / (n+1)^2` times the weighted
U6a count of a containing unit window.
-/
theorem kadiriUpperUnitBandPairedDiffSum_le_u6a_count
    {T σ : ℝ} (n : ℕ) (hσ : σ ∈ Set.uIcc (-1 : ℝ) 2) :
    kadiriUpperUnitBandPairedDiffSum T σ n ≤
      (3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) *
        u6aNearbyZeroCount (-1) 2 (T + ((n : ℝ) + 3 / 2)) := by
  classical
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  let u : ℝ := T + ((n : ℝ) + 3 / 2)
  let band : Finset ℂ := (kadiriUpperUnitBandZeroesRect_finite T n).toFinset
  let wide : Finset ℂ := (u6aFTNearbyWindow_finite u).toFinset
  have hσIcc : σ ∈ Set.Icc (-1 : ℝ) 2 := by
    simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] using hσ
  have hband_sum :
      kadiriUpperUnitBandPairedDiffSum T σ n =
        ∑ ρ ∈ band,
          ‖(1 : ℂ) / (s - ρ) -
            (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ)‖ *
            ((riemannZeta.order ρ : ℤ) : ℝ) := by
    simpa [kadiriUpperUnitBandPairedDiffSum, band, s] using
      riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := .Ioo (0 : ℝ) 1)
        (J := .Icc (T + ((n : ℝ) + 1)) (T + ((n : ℝ) + 2)))
        (f := fun ρ =>
          ‖(1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - ρ) -
            (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ)‖)
        (kadiriUpperUnitBandZeroesRect_finite T n)
  have hwide_sum :
      u6aNearbyZeroCount (-1) 2 u =
        ∑ ρ ∈ wide, ((riemannZeta.order ρ : ℤ) : ℝ) := by
    simpa [u6aNearbyZeroCount, wide, u] using
      riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := Set.uIcc (-1 : ℝ) 2) (J := Set.Icc (u - 1) (u + 1))
        (f := fun _ => (1 : ℝ)) (u6aFTNearbyWindow_finite u)
  have hsubset : band ⊆ wide := by
    intro ρ hρ
    dsimp [band, wide] at hρ ⊢
    have hmem := (kadiriUpperUnitBandZeroesRect_finite T n).mem_toFinset.mp hρ
    obtain ⟨hre, him, hζ⟩ := hmem
    rw [(u6aFTNearbyWindow_finite u).mem_toFinset]
    unfold u6aFTNearbyWindow riemannZeta.zeroes_rect
    refine ⟨?_, ?_, hζ⟩
    · rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
      exact ⟨by linarith [hre.1], by linarith [hre.2]⟩
    · dsimp [u]
      exact ⟨by linarith [him.1], by linarith [him.2]⟩
  have horder_nonneg : ∀ ρ ∈ wide, 0 ≤ ((riemannZeta.order ρ : ℤ) : ℝ) := by
    intro ρ hρ
    have hmem := (u6aFTNearbyWindow_finite u).mem_toFinset.mp (by simpa [wide] using hρ)
    obtain ⟨_hre, _him, hζ⟩ := hmem
    exact_mod_cast riemannZeta_order_nonneg (by
      intro hρ1
      exact riemannZeta_one_ne_zero (by simpa [hρ1] using hζ))
  have hterm : ∀ ρ ∈ band,
      ‖(1 : ℂ) / (s - ρ) -
          (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ)‖ *
          ((riemannZeta.order ρ : ℤ) : ℝ) ≤
        (3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) *
          ((riemannZeta.order ρ : ℤ) : ℝ) := by
    intro ρ hρ
    have hmem := (kadiriUpperUnitBandZeroesRect_finite T n).mem_toFinset.mp
      (by simpa [band] using hρ)
    obtain ⟨hre, him, hζ⟩ := hmem
    let rhoNT : NontrivialZeros := ⟨ρ, ⟨hre, trivial, hζ⟩⟩
    have hfar : 1 ≤ |T - (rhoNT : ℂ).im| := by
      have hnonpos : T - (rhoNT : ℂ).im ≤ 0 := by
        dsimp [rhoNT]
        nlinarith [Nat.cast_nonneg (α := ℝ) n, him.1]
      rw [abs_of_nonpos hnonpos]
      dsimp [rhoNT]
      nlinarith [Nat.cast_nonneg (α := ℝ) n, him.1]
    have hdist : ((n : ℝ) + 1) ≤ |T - (rhoNT : ℂ).im| := by
      have hnonpos : T - (rhoNT : ℂ).im ≤ 0 := by
        dsimp [rhoNT]
        nlinarith [Nat.cast_nonneg (α := ℝ) n, him.1]
      rw [abs_of_nonpos hnonpos]
      dsimp [rhoNT]
      nlinarith [him.1]
    have hpoint :
        ‖(1 : ℂ) / (s - ρ) -
            (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ)‖ ≤
          3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ)) := by
      have hraw :=
        norm_one_div_sub_one_div_at_zero_le_far_height_sq
          (s := s) (t := T)
          (by simp [s]) (by simpa [s] using hσIcc.1)
          (by simpa [s] using hσIcc.2) rhoNT hfar
      have hpos : 0 < (n : ℝ) + 1 := by positivity
      have hinv : |T - (rhoNT : ℂ).im|⁻¹ ≤ ((n : ℝ) + 1)⁻¹ :=
        inv_anti₀ hpos hdist
      have hsquare :
          |T - (rhoNT : ℂ).im|⁻¹ ^ (2 : ℕ) ≤
            ((n : ℝ) + 1)⁻¹ ^ (2 : ℕ) :=
        pow_le_pow_left₀ (by positivity) hinv 2
      exact hraw.trans (mul_le_mul_of_nonneg_left hsquare (by norm_num))
    have hord : 0 ≤ ((riemannZeta.order ρ : ℤ) : ℝ) := by
      exact_mod_cast riemannZeta_order_nonneg (by
        intro hρ1
        exact riemannZeta_one_ne_zero (by simpa [hρ1] using hζ))
    exact mul_le_mul_of_nonneg_right hpoint hord
  calc
    kadiriUpperUnitBandPairedDiffSum T σ n
        = ∑ ρ ∈ band,
          ‖(1 : ℂ) / (s - ρ) -
            (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ)‖ *
            ((riemannZeta.order ρ : ℤ) : ℝ) := hband_sum
    _ ≤ ∑ ρ ∈ band,
          (3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) *
            ((riemannZeta.order ρ : ℤ) : ℝ) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ ρ ∈ wide,
          (3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) *
            ((riemannZeta.order ρ : ℤ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun ρ hρ _ => mul_nonneg (by positivity)
            (horder_nonneg ρ (by simpa [wide] using hρ)))
    _ = (3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) *
          u6aNearbyZeroCount (-1) 2 (T + ((n : ℝ) + 3 / 2)) := by
        rw [hwide_sum]
        rw [Finset.mul_sum]

/-- The paired Hadamard zero contribution over the lower unit band
`T - n - 2 <= Im rho <= T - n - 1`. -/
noncomputable def kadiriLowerUnitBandPairedDiffSum (T σ : ℝ) (n : ℕ) : ℝ :=
  riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1)
    (.Icc (T - ((n : ℝ) + 2)) (T - ((n : ℝ) + 1)))
    fun ρ =>
      ‖(1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - ρ) -
        (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ)‖

/-- The lower unit band is finite. -/
theorem kadiriLowerUnitBandZeroesRect_finite (T : ℝ) (n : ℕ) :
    (riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1)
      (.Icc (T - ((n : ℝ) + 2)) (T - ((n : ℝ) + 1)))).Finite := by
  let u : ℝ := T - ((n : ℝ) + 3 / 2)
  apply Set.Finite.subset (u6aFTNearbyWindow_finite u)
  intro ρ hρ
  obtain ⟨hre, him, hζ⟩ := hρ
  unfold u6aFTNearbyWindow riemannZeta.zeroes_rect
  refine ⟨?_, ?_, hζ⟩
  · rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
    exact ⟨by linarith [hre.1], by linarith [hre.2]⟩
  · dsimp [u]
    exact ⟨by linarith [him.1], by linarith [him.2]⟩

/--
Each lower unit band contributes at most `3 / (n+1)^2` times the weighted
U6a count of a containing unit window.
-/
theorem kadiriLowerUnitBandPairedDiffSum_le_u6a_count
    {T σ : ℝ} (n : ℕ) (hσ : σ ∈ Set.uIcc (-1 : ℝ) 2) :
    kadiriLowerUnitBandPairedDiffSum T σ n ≤
      (3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) *
        u6aNearbyZeroCount (-1) 2 (T - ((n : ℝ) + 3 / 2)) := by
  classical
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  let u : ℝ := T - ((n : ℝ) + 3 / 2)
  let band : Finset ℂ := (kadiriLowerUnitBandZeroesRect_finite T n).toFinset
  let wide : Finset ℂ := (u6aFTNearbyWindow_finite u).toFinset
  have hσIcc : σ ∈ Set.Icc (-1 : ℝ) 2 := by
    simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] using hσ
  have hband_sum :
      kadiriLowerUnitBandPairedDiffSum T σ n =
        ∑ ρ ∈ band,
          ‖(1 : ℂ) / (s - ρ) -
            (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ)‖ *
            ((riemannZeta.order ρ : ℤ) : ℝ) := by
    simpa [kadiriLowerUnitBandPairedDiffSum, band, s] using
      riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := .Ioo (0 : ℝ) 1)
        (J := .Icc (T - ((n : ℝ) + 2)) (T - ((n : ℝ) + 1)))
        (f := fun ρ =>
          ‖(1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - ρ) -
            (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ)‖)
        (kadiriLowerUnitBandZeroesRect_finite T n)
  have hwide_sum :
      u6aNearbyZeroCount (-1) 2 u =
        ∑ ρ ∈ wide, ((riemannZeta.order ρ : ℤ) : ℝ) := by
    simpa [u6aNearbyZeroCount, wide, u] using
      riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := Set.uIcc (-1 : ℝ) 2) (J := Set.Icc (u - 1) (u + 1))
        (f := fun _ => (1 : ℝ)) (u6aFTNearbyWindow_finite u)
  have hsubset : band ⊆ wide := by
    intro ρ hρ
    dsimp [band, wide] at hρ ⊢
    have hmem := (kadiriLowerUnitBandZeroesRect_finite T n).mem_toFinset.mp hρ
    obtain ⟨hre, him, hζ⟩ := hmem
    rw [(u6aFTNearbyWindow_finite u).mem_toFinset]
    unfold u6aFTNearbyWindow riemannZeta.zeroes_rect
    refine ⟨?_, ?_, hζ⟩
    · rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
      exact ⟨by linarith [hre.1], by linarith [hre.2]⟩
    · dsimp [u]
      exact ⟨by linarith [him.1], by linarith [him.2]⟩
  have horder_nonneg : ∀ ρ ∈ wide, 0 ≤ ((riemannZeta.order ρ : ℤ) : ℝ) := by
    intro ρ hρ
    have hmem := (u6aFTNearbyWindow_finite u).mem_toFinset.mp (by simpa [wide] using hρ)
    obtain ⟨_hre, _him, hζ⟩ := hmem
    exact_mod_cast riemannZeta_order_nonneg (by
      intro hρ1
      exact riemannZeta_one_ne_zero (by simpa [hρ1] using hζ))
  have hterm : ∀ ρ ∈ band,
      ‖(1 : ℂ) / (s - ρ) -
          (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ)‖ *
          ((riemannZeta.order ρ : ℤ) : ℝ) ≤
        (3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) *
          ((riemannZeta.order ρ : ℤ) : ℝ) := by
    intro ρ hρ
    have hmem := (kadiriLowerUnitBandZeroesRect_finite T n).mem_toFinset.mp
      (by simpa [band] using hρ)
    obtain ⟨hre, him, hζ⟩ := hmem
    let rhoNT : NontrivialZeros := ⟨ρ, ⟨hre, trivial, hζ⟩⟩
    have hfar : 1 ≤ |T - (rhoNT : ℂ).im| := by
      have hnonneg : 0 ≤ T - (rhoNT : ℂ).im := by
        dsimp [rhoNT]
        nlinarith [Nat.cast_nonneg (α := ℝ) n, him.2]
      rw [abs_of_nonneg hnonneg]
      dsimp [rhoNT]
      nlinarith [Nat.cast_nonneg (α := ℝ) n, him.2]
    have hdist : ((n : ℝ) + 1) ≤ |T - (rhoNT : ℂ).im| := by
      have hnonneg : 0 ≤ T - (rhoNT : ℂ).im := by
        dsimp [rhoNT]
        nlinarith [Nat.cast_nonneg (α := ℝ) n, him.2]
      rw [abs_of_nonneg hnonneg]
      dsimp [rhoNT]
      nlinarith [him.2]
    have hpoint :
        ‖(1 : ℂ) / (s - ρ) -
            (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ)‖ ≤
          3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ)) := by
      have hraw :=
        norm_one_div_sub_one_div_at_zero_le_far_height_sq
          (s := s) (t := T)
          (by simp [s]) (by simpa [s] using hσIcc.1)
          (by simpa [s] using hσIcc.2) rhoNT hfar
      have hpos : 0 < (n : ℝ) + 1 := by positivity
      have hinv : |T - (rhoNT : ℂ).im|⁻¹ ≤ ((n : ℝ) + 1)⁻¹ :=
        inv_anti₀ hpos hdist
      have hsquare :
          |T - (rhoNT : ℂ).im|⁻¹ ^ (2 : ℕ) ≤
            ((n : ℝ) + 1)⁻¹ ^ (2 : ℕ) :=
        pow_le_pow_left₀ (by positivity) hinv 2
      exact hraw.trans (mul_le_mul_of_nonneg_left hsquare (by norm_num))
    have hord : 0 ≤ ((riemannZeta.order ρ : ℤ) : ℝ) := by
      exact_mod_cast riemannZeta_order_nonneg (by
        intro hρ1
        exact riemannZeta_one_ne_zero (by simpa [hρ1] using hζ))
    exact mul_le_mul_of_nonneg_right hpoint hord
  calc
    kadiriLowerUnitBandPairedDiffSum T σ n
        = ∑ ρ ∈ band,
          ‖(1 : ℂ) / (s - ρ) -
            (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ)‖ *
            ((riemannZeta.order ρ : ℤ) : ℝ) := hband_sum
    _ ≤ ∑ ρ ∈ band,
          (3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) *
            ((riemannZeta.order ρ : ℤ) : ℝ) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ ρ ∈ wide,
          (3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) *
            ((riemannZeta.order ρ : ℤ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun ρ hρ _ => mul_nonneg (by positivity)
            (horder_nonneg ρ (by simpa [wide] using hρ)))
    _ = (3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) *
          u6aNearbyZeroCount (-1) 2 (T - ((n : ℝ) + 3 / 2)) := by
        rw [hwide_sum]
        rw [Finset.mul_sum]

end

end Kadiri
