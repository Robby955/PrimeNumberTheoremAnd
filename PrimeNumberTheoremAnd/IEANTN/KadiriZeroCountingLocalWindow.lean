import PrimeNumberTheoremAnd.IEANTN.KadiriUnitBandZeroCount

/-!
# Local-window producer for the Kadiri dyadic zero-count source

This file derives the dyadic cumulative zero-count source from the crude
unit-window count.  It is intentionally separate from `KadiriZeroCounting` to
avoid making the foundational zero-counting file import its local Jensen layer.
-/

noncomputable section

namespace Kadiri

open Complex Filter
open scoped BigOperators

/-- Positive-height dyadic counts are bounded by summing the local unit-window count. -/
theorem zeroImagDyadicPositiveCountBoundSource_of_local_window :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      (Nat.card {rho : NontrivialZeros //
          0 < (rho : ℂ).im ∧ (rho : ℂ).im < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
        C * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k) := by
  classical
  rcases exists_nontrivialZeros_unitBand_count_le_log with ⟨C₀, hC₀_pos, hC₀⟩
  let K₀ : ℕ := Nat.card {rho : NontrivialZeros // |(rho : ℂ).im| < 2}
  refine ⟨16 * C₀ + K₀, by positivity, ?_⟩
  intro k
  let H : ℝ := (2 : ℝ) ^ (k + 1)
  let G : ℝ := ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)
  let Pos : Type := {rho : NontrivialZeros // 0 < (rho : ℂ).im ∧ (rho : ℂ).im < H}
  let Low : Type := {rho : NontrivialZeros // |(rho : ℂ).im| < 2}
  let Centers : Type := {c : ℕ // c ∈ Finset.Icc 2 (Nat.ceil H)}
  let Window : Centers → Type :=
    fun c => {rho : NontrivialZeros // |((c : ℕ) : ℝ) - (rho : ℂ).im| ≤ 1}
  have hH_pos : 0 < H := by
    dsimp [H]
    exact pow_pos (by norm_num) _
  have hH_nonneg : 0 ≤ H := hH_pos.le
  have hH_ge_one : 1 ≤ H := by
    dsimp [H]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hH_ge_two : 2 ≤ H := by
    dsimp [H]
    have hk : (1 : ℕ) ≤ k + 1 := by omega
    have hpow : (2 : ℝ) ^ (1 : ℕ) ≤ (2 : ℝ) ^ (k + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by exact_mod_cast hk)
    simpa using hpow
  have hG_ge_one : 1 ≤ G := by
    dsimp [G]
    exact dyadicCountScale_ge_one k
  haveI : Finite Low := by
    dsimp [Low]
    exact Set.finite_coe_iff.mpr (nontrivialZeros_abs_im_lt_finite 2)
  haveI : Fintype Centers := by
    dsimp [Centers]
    infer_instance
  haveI : ∀ c : Centers, Finite (Window c) := by
    intro c
    dsimp [Window]
    exact Set.finite_coe_iff.mpr (kadiriUnitBandWindow_finite ((c : ℕ) : ℝ))
  let toTarget : Pos → Low ⊕ Sigma Window := fun rho =>
    if hlow : (rho.1 : ℂ).im ≤ 1 then
      Sum.inl
        ⟨rho.1, by
          have him_nonneg : 0 ≤ (rho.1 : ℂ).im := le_of_lt rho.2.1
          rw [abs_of_nonneg him_nonneg]
          linarith⟩
    else
      let c : ℕ := Nat.ceil ((rho.1 : ℂ).im)
      have hc_mem : c ∈ Finset.Icc 2 (Nat.ceil H) := by
        have him_gt_one : 1 < (rho.1 : ℂ).im := lt_of_not_ge hlow
        have hc_gt_one_real : (1 : ℝ) < (c : ℝ) := by
          exact him_gt_one.trans_le (Nat.le_ceil ((rho.1 : ℂ).im))
        have hc_gt_one : 1 < c := by
          exact_mod_cast hc_gt_one_real
        have hc_ge_two : 2 ≤ c := by omega
        have hc_le : c ≤ Nat.ceil H :=
          Nat.ceil_mono (le_of_lt rho.2.2)
        exact Finset.mem_Icc.mpr ⟨hc_ge_two, hc_le⟩
      Sum.inr
        ⟨⟨c, hc_mem⟩,
          ⟨rho.1, by
            have him_nonneg : 0 ≤ (rho.1 : ℂ).im := le_of_lt rho.2.1
            have hc_le_im : (rho.1 : ℂ).im ≤ (c : ℝ) :=
              Nat.le_ceil ((rho.1 : ℂ).im)
            have hc_lt_im_add_one : (c : ℝ) < (rho.1 : ℂ).im + 1 :=
              Nat.ceil_lt_add_one him_nonneg
            have hdiff_nonneg : 0 ≤ (c : ℝ) - (rho.1 : ℂ).im := by
              exact sub_nonneg.mpr hc_le_im
            have hdiff_le : (c : ℝ) - (rho.1 : ℂ).im ≤ 1 := by
              linarith
            rw [abs_of_nonneg hdiff_nonneg]
            exact hdiff_le⟩⟩
  let recover : Low ⊕ Sigma Window → NontrivialZeros
    | Sum.inl rho => rho.1
    | Sum.inr rho => rho.2.1
  have hrecover : ∀ rho : Pos, recover (toTarget rho) = rho.1 := by
    intro rho
    by_cases hlow : (rho.1 : ℂ).im ≤ 1
    · simp [toTarget, recover, hlow]
    · simp [toTarget, recover, hlow]
  have hinj : Function.Injective toTarget := by
    intro rho eta h
    apply Subtype.ext
    calc
      rho.1 = recover (toTarget rho) := (hrecover rho).symm
      _ = recover (toTarget eta) := by rw [h]
      _ = eta.1 := hrecover eta
  have hcard_nat : Nat.card Pos ≤ Nat.card (Low ⊕ Sigma Window) :=
    Nat.card_le_card_of_injective toTarget hinj
  have htarget_card_nat :
      Nat.card (Low ⊕ Sigma Window) =
        Nat.card Low + ∑ c : Centers, Nat.card (Window c) := by
    rw [Nat.card_sum, Nat.card_sigma]
  have htarget_card :
      (Nat.card (Low ⊕ Sigma Window) : ℝ) =
        (K₀ : ℝ) + ∑ c : Centers, (Nat.card (Window c) : ℝ) := by
    rw [htarget_card_nat]
    simp [K₀, Low]
  have hlog_H3_nonneg : 0 ≤ Real.log (H + 3) := by
    exact Real.log_nonneg (by linarith)
  have hband_sum :
      (∑ c : Centers, (Nat.card (Window c) : ℝ)) ≤
        (Fintype.card Centers : ℝ) * (C₀ * Real.log (H + 3)) := by
    calc
      (∑ c : Centers, (Nat.card (Window c) : ℝ))
          ≤ ∑ c : Centers, C₀ * Real.log (H + 3) := by
            refine Finset.sum_le_sum fun c _ => ?_
            have hc_ge_two : 2 ≤ (c : ℕ) := (Finset.mem_Icc.mp c.2).1
            have hc_le_ceil : (c : ℕ) ≤ Nat.ceil H := (Finset.mem_Icc.mp c.2).2
            have hc_le_ceil_real : ((c : ℕ) : ℝ) ≤ (Nat.ceil H : ℝ) := by
              exact_mod_cast hc_le_ceil
            have hceil_lt : (Nat.ceil H : ℝ) < H + 1 :=
              Nat.ceil_lt_add_one hH_nonneg
            have hlog_le :
                Real.log (((c : ℕ) : ℝ) + 2) ≤ Real.log (H + 3) := by
              exact Real.log_le_log (by positivity) (by linarith)
            have hlocal := hC₀ (((c : ℕ) : ℝ)) (by exact_mod_cast hc_ge_two)
            calc
              (Nat.card (Window c) : ℝ)
                  ≤ C₀ * Real.log (((c : ℕ) : ℝ) + 2) := by
                    simpa [Window] using hlocal
              _ ≤ C₀ * Real.log (H + 3) :=
                    mul_le_mul_of_nonneg_left hlog_le hC₀_pos.le
      _ = (Fintype.card Centers : ℝ) * (C₀ * Real.log (H + 3)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hcenters_card : (Fintype.card Centers : ℝ) ≤ 2 * H := by
    let toFin : Centers → Fin (Nat.ceil H + 1) := fun c =>
      ⟨c.1, by
        have hc_le : c.1 ≤ Nat.ceil H := (Finset.mem_Icc.mp c.2).2
        omega⟩
    have htoFin_inj : Function.Injective toFin := by
      intro c d h
      apply Subtype.ext
      exact congrArg Fin.val h
    have hcard_nat :
        Fintype.card Centers ≤ Fintype.card (Fin (Nat.ceil H + 1)) :=
      Fintype.card_le_of_injective toFin htoFin_inj
    have hcard_real :
        (Fintype.card Centers : ℝ) ≤ ((Nat.ceil H + 1 : ℕ) : ℝ) := by
      simpa using (show (Fintype.card Centers : ℝ) ≤
          (Fintype.card (Fin (Nat.ceil H + 1)) : ℝ) by exact_mod_cast hcard_nat)
    have hceil_lt : (Nat.ceil H : ℝ) < H + 1 :=
      Nat.ceil_lt_add_one hH_nonneg
    have hceil_add_lt : ((Nat.ceil H + 1 : ℕ) : ℝ) < H + 2 := by
      norm_num [Nat.cast_add]
      linarith
    have hH_absorb : H + 2 ≤ 2 * H := by
      linarith
    linarith
  have hlog_H3_le : Real.log (H + 3) ≤ 4 * ((k + 1 : ℕ) : ℝ) := by
    have hH3_pos : 0 < H + 3 := by positivity
    have hH3_le : H + 3 ≤ 4 * H := by
      nlinarith
    have h4H_pos : 0 < 4 * H := by positivity
    have hlog_le : Real.log (H + 3) ≤ Real.log (4 * H) :=
      Real.log_le_log hH3_pos hH3_le
    have hlog4H : Real.log (4 * H) = Real.log 4 + Real.log H := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hH_pos)]
    have hlogH_le : Real.log H ≤ ((k + 1 : ℕ) : ℝ) := by
      dsimp [H]
      exact log_dyadic_le_nat_succ k
    have hlog4_le_three : Real.log 4 ≤ (3 : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hk_ge_one : 1 ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos k
    calc
      Real.log (H + 3) ≤ Real.log (4 * H) := hlog_le
      _ = Real.log 4 + Real.log H := hlog4H
      _ ≤ 3 + ((k + 1 : ℕ) : ℝ) := add_le_add hlog4_le_three hlogH_le
      _ ≤ 4 * ((k + 1 : ℕ) : ℝ) := by nlinarith
  have hband_sum_final :
      (∑ c : Centers, (Nat.card (Window c) : ℝ)) ≤
        16 * C₀ * G := by
    have hB_nonneg : 0 ≤ C₀ * Real.log (H + 3) :=
      mul_nonneg hC₀_pos.le hlog_H3_nonneg
    have hscale_nonneg : 0 ≤ 2 * H := by positivity
    calc
      (∑ c : Centers, (Nat.card (Window c) : ℝ))
          ≤ (Fintype.card Centers : ℝ) * (C₀ * Real.log (H + 3)) := hband_sum
      _ ≤ (2 * H) * (C₀ * Real.log (H + 3)) :=
          mul_le_mul_of_nonneg_right hcenters_card hB_nonneg
      _ ≤ (2 * H) * (C₀ * (4 * ((k + 1 : ℕ) : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hlog_H3_le hC₀_pos.le) hscale_nonneg
      _ = 16 * C₀ * G := by
          dsimp [H, G]
          rw [pow_succ']
          ring
  have hcard_pos :
      (Nat.card Pos : ℝ) ≤ (16 * C₀ + K₀) * G := by
    have hcard_target :
        (Nat.card Pos : ℝ) ≤ (Nat.card (Low ⊕ Sigma Window) : ℝ) := by
      exact_mod_cast hcard_nat
    have hK_absorb : (K₀ : ℝ) ≤ (K₀ : ℝ) * G := by
      calc
        (K₀ : ℝ) = (K₀ : ℝ) * 1 := by ring
        _ ≤ (K₀ : ℝ) * G :=
          mul_le_mul_of_nonneg_left hG_ge_one (by positivity)
    calc
      (Nat.card Pos : ℝ) ≤ (Nat.card (Low ⊕ Sigma Window) : ℝ) := hcard_target
      _ = (K₀ : ℝ) + ∑ c : Centers, (Nat.card (Window c) : ℝ) := htarget_card
      _ ≤ (K₀ : ℝ) + 16 * C₀ * G := by linarith
      _ ≤ (K₀ : ℝ) * G + 16 * C₀ * G := by linarith
      _ = (16 * C₀ + K₀) * G := by ring
  simpa [Pos, H, G, mul_assoc] using hcard_pos

/--
The cumulative dyadic zero-count source follows unconditionally from the
local unit-window count and conjugation symmetry.
-/
theorem zeroImagDyadicCumulativeCountBoundSource_of_local_window :
    zeroImagDyadicCumulativeCountBoundSource := by
  rcases zeroImagDyadicPositiveCountBoundSource_of_local_window with
    ⟨B, hB_nonneg, hB⟩
  rcases zeroImagDyadicAbsToPositiveCountWithZeroHeightSource_of_riemannZeta_conj with
    ⟨A, D, hA_nonneg, hD_nonneg, hAbs⟩
  refine ⟨A * B + D, add_nonneg (mul_nonneg hA_nonneg hB_nonneg) hD_nonneg, ?_⟩
  intro k
  let G : ℝ := ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k)
  have hG_ge_one : 1 ≤ G := by
    dsimp [G]
    exact dyadicCountScale_ge_one k
  have hAbs_k := hAbs k
  have hB_k := hB k
  have hB_k' :
      (Nat.card {rho : NontrivialZeros //
          0 < (rho : ℂ).im ∧ (rho : ℂ).im < (2 : ℝ) ^ (k + 1)} : ℝ) ≤
        B * G := by
    calc
      (Nat.card {rho : NontrivialZeros //
          0 < (rho : ℂ).im ∧ (rho : ℂ).im < (2 : ℝ) ^ (k + 1)} : ℝ)
          ≤ B * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k) := hB_k
      _ = B * G := by
          dsimp [G]
          ring
  have hmain :
      A * (Nat.card {rho : NontrivialZeros //
          0 < (rho : ℂ).im ∧ (rho : ℂ).im < (2 : ℝ) ^ (k + 1)} : ℝ) + D ≤
        A * (B * G) + D := by
    have hmul := mul_le_mul_of_nonneg_left hB_k' hA_nonneg
    linarith
  have hD_absorb : D ≤ D * G := by
    calc
      D = D * 1 := by ring
      _ ≤ D * G := mul_le_mul_of_nonneg_left hG_ge_one hD_nonneg
  calc
    (Nat.card {rho : NontrivialZeros //
        |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ)
        ≤ A * (Nat.card {rho : NontrivialZeros //
          0 < (rho : ℂ).im ∧ (rho : ℂ).im < (2 : ℝ) ^ (k + 1)} : ℝ) + D := hAbs_k
    _ ≤ A * (B * G) + D := hmain
    _ ≤ A * (B * G) + D * G := by linarith
    _ = (A * B + D) * ((k + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ k) := by
          dsimp [G]
          ring

end Kadiri
