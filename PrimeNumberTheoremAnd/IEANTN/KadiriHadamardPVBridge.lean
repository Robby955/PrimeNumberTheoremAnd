import PrimeNumberTheoremAnd.IEANTN.KadiriFarTail
import PrimeNumberTheoremAnd.IEANTN.KadiriGammaStrip
import PrimeNumberTheoremAnd.IEANTN.KadiriLogDerivFullSegment
import PrimeNumberTheoremAnd.IEANTN.KadiriNearBand
import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCountingLocalWindow

/-!
# Hadamard/PV bridge for the Kadiri full-segment endpoint

This file isolates the bridge between the finite local zero window used by the
endpoint wrapper and the near-window `zeroes_sum` term produced by Hadamard's
partial-fraction identity.
-/

namespace Kadiri

open Complex
open Filter
open Asymptotics
open scoped BigOperators
open scoped Topology

noncomputable section

private theorem kadiriCriticalStripNearZeroes_finite (T : ℝ) :
    (riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Icc (T - 1) (T + 1))).Finite := by
  refine (u6aFTNearbyWindow_finite T).subset ?_
  intro z hz
  obtain ⟨hre, him, hzero⟩ := hz
  unfold u6aFTNearbyWindow riemannZeta.zeroes_rect
  refine ⟨?_, him, hzero⟩
  rw [Set.mem_uIcc]
  exact Or.inl ⟨by linarith [hre.1], by linarith [hre.2]⟩

/--
The finite local zero-window principal block is the same multiplicity-weighted
near-window `zeroes_sum` appearing in the Hadamard split.
-/
theorem kadiriLocalZeroWindow_principal_eq_zeroes_sum_near (T σ : ℝ) :
    (∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
        ((riemannZeta.order (rho : ℂ) : ℂ) /
          (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))) =
      riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Icc (T - 1) (T + 1))
        (fun ρ => (1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - ρ)) := by
  classical
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  let L : Finset NontrivialZeros := (kadiriLocalZeroWindow_finite T).toFinset
  let N : Finset ℂ := (kadiriCriticalStripNearZeroes_finite T).toFinset
  have hzeroes_sum :
      riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Icc (T - 1) (T + 1))
          (fun ρ => (1 : ℂ) / (s - ρ)) =
        ∑ z ∈ N,
          ((1 : ℂ) / (s - z)) * ((riemannZeta.order z : ℤ) : ℂ) := by
    simpa [N] using
      riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := .Ioo (0 : ℝ) 1) (J := .Icc (T - 1) (T + 1))
        (f := fun ρ => (1 : ℂ) / (s - ρ))
        (kadiriCriticalStripNearZeroes_finite T)
  have hsum :
      (∑ rho ∈ L,
          ((riemannZeta.order (rho : ℂ) : ℂ) / (s - (rho : ℂ)))) =
        ∑ z ∈ N,
          ((1 : ℂ) / (s - z)) * ((riemannZeta.order z : ℤ) : ℂ) := by
    refine Finset.sum_bij (fun rho _ => (rho : ℂ)) ?_ ?_ ?_ ?_
    · intro rho hrho
      dsimp [N]
      rw [(kadiriCriticalStripNearZeroes_finite T).mem_toFinset]
      dsimp [L] at hrho
      have hrho_window : rho ∈ kadiriLocalZeroWindow T :=
        (kadiriLocalZeroWindow_finite T).mem_toFinset.mp hrho
      rw [kadiriLocalZeroWindow, Set.mem_setOf_eq] at hrho_window
      have him := abs_le.mp hrho_window
      refine ⟨?_, ?_, riemannZeta_nontrivialZero_zero rho⟩
      · exact ⟨rho.property.1.1, rho.property.1.2⟩
      · exact ⟨by linarith [him.1], by linarith [him.2]⟩
    · intro rho₁ _ rho₂ _ h
      exact Subtype.ext h
    · intro z hz
      dsimp [N] at hz
      have hzmem :=
        (kadiriCriticalStripNearZeroes_finite T).mem_toFinset.mp hz
      let rho : NontrivialZeros := ⟨z, ⟨hzmem.1, trivial, hzmem.2.2⟩⟩
      refine ⟨rho, ?_, ?_⟩
      · dsimp [L]
        rw [(kadiriLocalZeroWindow_finite T).mem_toFinset]
        rw [kadiriLocalZeroWindow, Set.mem_setOf_eq]
        exact abs_le.mpr ⟨by linarith [hzmem.2.1.1], by linarith [hzmem.2.1.2]⟩
      · rfl
    · intro rho hrho
      ring
  rw [hzeroes_sum]
  simpa [s, L] using hsum

/-- The finite local zero block evaluated at the reference point `2 + iT`. -/
noncomputable def kadiriLocalZeroReferenceBlock (T : ℝ) : ℂ :=
  ∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
    ((riemannZeta.order (rho : ℂ) : ℂ) /
      (((2 : ℂ) + (T : ℂ) * I) - (rho : ℂ)))

/-- The far-complement paired zero sum after subtracting at `2 + iT`. -/
noncomputable def kadiriFarTailPairedZeroesSum (T σ : ℝ) : ℂ :=
  riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1)
    ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)})
    (fun ρ => (1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - ρ) -
      (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ))

/-- The existing far-tail logarithmic estimate applied to the named bridge component. -/
theorem exists_kadiriFarTailPairedZeroesSum_norm_le_log :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ T : ℝ in Filter.atTop,
      ∀ σ : ℝ, σ ∈ Set.uIcc (-1 : ℝ) 2 →
        ‖kadiriFarTailPairedZeroesSum T σ‖ ≤ R * Real.log T := by
  simpa [kadiriFarTailPairedZeroesSum] using
    exists_kadiri_far_tail_paired_zeroes_sum_norm_le_log

/--
At the reference point `2 + iT`, the zeta logarithmic derivative is uniformly
bounded, hence logarithmically bounded eventually.
-/
theorem exists_kadiriRightHalfplaneLogDerivAtTwo_norm_le_log :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ T : ℝ in Filter.atTop,
      ‖deriv riemannZeta (((2 : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((2 : ℂ) + (T : ℂ) * I))‖ ≤ R * Real.log T := by
  let M : ℝ := ‖deriv riemannZeta ((3 / 2 : ℝ) : ℂ) /
    riemannZeta ((3 / 2 : ℝ) : ℂ)‖
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨M / Real.log 3, div_nonneg (norm_nonneg _) hlog3.le, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with T hT
  have hright :
      ‖deriv riemannZeta (((2 : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((2 : ℂ) + (T : ℂ) * I))‖ ≤ M := by
    have h :=
      dlog_riemannZeta_bdd_on_vertical_lines_generalized
        (3 / 2) 2 T (by norm_num) (by norm_num)
    simpa [M, norm_neg] using h
  have hlog_mono : Real.log (3 : ℝ) ≤ Real.log T :=
    Real.log_le_log (by norm_num) hT
  calc
    ‖deriv riemannZeta (((2 : ℂ) + (T : ℂ) * I)) /
        riemannZeta (((2 : ℂ) + (T : ℂ) * I))‖
        ≤ M := hright
    _ = (M / Real.log 3) * Real.log 3 := by
          field_simp [ne_of_gt hlog3]
    _ ≤ (M / Real.log 3) * Real.log T :=
          mul_le_mul_of_nonneg_left hlog_mono (div_nonneg (norm_nonneg _) hlog3.le)

/--
The finite local reference block is bounded by the existing multiplicity-weighted
near-band reference sum.
-/
theorem kadiriLocalZeroReferenceBlock_norm_le_nearBandWeightedReferenceSum (T : ℝ) :
    ‖kadiriLocalZeroReferenceBlock T‖ ≤ kadiriNearBandWeightedReferenceSum T := by
  classical
  let w : ℂ := (2 : ℂ) + (T : ℂ) * I
  let N : Finset ℂ := (kadiriNearBandZeroesRect_finite T).toFinset
  have href_eq :
      kadiriLocalZeroReferenceBlock T =
        riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Icc (T - 1) (T + 1))
          (fun ρ => (1 : ℂ) / (w - ρ)) := by
    simpa [kadiriLocalZeroReferenceBlock, w] using
      (kadiriLocalZeroWindow_principal_eq_zeroes_sum_near T 2)
  rw [href_eq]
  rw [riemannZeta.zeroes_sum_eq_finset_of_finite
    (I := .Ioo (0 : ℝ) 1) (J := .Icc (T - 1) (T + 1))
    (f := fun ρ => (1 : ℂ) / (w - ρ)) (kadiriNearBandZeroesRect_finite T)]
  rw [kadiriNearBandWeightedReferenceSum,
    riemannZeta.zeroes_sum_eq_finset_of_finite
      (I := .Ioo (0 : ℝ) 1) (J := .Icc (T - 1) (T + 1))
      (f := fun ρ => ‖(1 : ℂ) / (((2 : ℝ) : ℂ) + (T : ℂ) * I - ρ)‖)
      (kadiriNearBandZeroesRect_finite T)]
  calc
    ‖∑ ρ ∈ N, (1 / (w - ρ)) * ↑(riemannZeta.order ρ)‖
        ≤ ∑ ρ ∈ N, ‖(1 / (w - ρ)) * ↑(riemannZeta.order ρ)‖ := norm_sum_le _ _
    _ = ∑ ρ ∈ N,
          ‖(1 : ℂ) / (((2 : ℝ) : ℂ) + (T : ℂ) * I - ρ)‖ *
            ((riemannZeta.order ρ : ℤ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro ρ hρ
          have hmem := (kadiriNearBandZeroesRect_finite T).mem_toFinset.mp (by
            simpa [N] using hρ)
          have horder_nonneg : 0 ≤ riemannZeta.order ρ := by
            exact_mod_cast riemannZeta_order_nonneg (by
              intro hρone
              have hre_lt := hmem.1.2
              rw [hρone] at hre_lt
              norm_num at hre_lt)
          have horder_nonneg_real : 0 ≤ ((riemannZeta.order ρ : ℤ) : ℝ) := by
            exact_mod_cast horder_nonneg
          rw [norm_mul, Complex.norm_intCast, abs_of_nonneg horder_nonneg_real]
          simp [w]

/-- The near-reference block has logarithmic growth at infinity. -/
theorem exists_kadiriLocalZeroReferenceBlock_norm_le_log :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ T : ℝ in Filter.atTop,
      ‖kadiriLocalZeroReferenceBlock T‖ ≤ R * Real.log T := by
  have hbig := kadiriNearBandWeightedReferenceSum_isBigO_log_of_u6aLocalZeroCount
  rw [Asymptotics.isBigO_iff'] at hbig
  obtain ⟨R, hR_pos, hR_eventually⟩ := hbig
  refine ⟨R, hR_pos.le, ?_⟩
  filter_upwards [hR_eventually, Filter.eventually_ge_atTop (1 : ℝ)] with T hR_T hT
  have hnear_nonneg : 0 ≤ kadiriNearBandWeightedReferenceSum T := by
    rw [kadiriNearBandWeightedReferenceSum,
      riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := .Ioo (0 : ℝ) 1) (J := .Icc (T - 1) (T + 1))
        (f := fun ρ => ‖(1 : ℂ) / (((2 : ℝ) : ℂ) + (T : ℂ) * I - ρ)‖)
        (kadiriNearBandZeroesRect_finite T)]
    exact Finset.sum_nonneg fun ρ hρ => by
      have hmem := (kadiriNearBandZeroesRect_finite T).mem_toFinset.mp hρ
      exact mul_nonneg (norm_nonneg _) (by
        exact_mod_cast riemannZeta_order_nonneg (by
          intro hρone
          have hre_lt := hmem.1.2
          rw [hρone] at hre_lt
          norm_num at hre_lt))
  have hlog_nonneg : 0 ≤ Real.log T := Real.log_nonneg hT
  calc
    ‖kadiriLocalZeroReferenceBlock T‖
        ≤ kadiriNearBandWeightedReferenceSum T :=
          kadiriLocalZeroReferenceBlock_norm_le_nearBandWeightedReferenceSum T
    _ = ‖kadiriNearBandWeightedReferenceSum T‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hnear_nonneg]
    _ ≤ R * ‖Real.log T‖ := hR_T
    _ = R * Real.log T := by rw [Real.norm_eq_abs, abs_of_nonneg hlog_nonneg]

/-- The pole plus digamma difference in the bridge has logarithmic growth. -/
theorem exists_kadiriPoleDigammaDifference_norm_le_log :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ T : ℝ in Filter.atTop,
      ∀ σ : ℝ, σ ∈ Set.uIcc (-1 : ℝ) 2 →
        ‖((1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - 1) -
            (1 : ℂ) / (1 + (T : ℂ) * I)) +
          (((1 / 2 : ℂ) * digamma ((((σ : ℂ) + (T : ℂ) * I) / 2) + 1)) -
            ((1 / 2 : ℂ) * digamma ((((2 : ℂ) + (T : ℂ) * I) / 2) + 1)))‖
          ≤ R * Real.log T := by
  obtain ⟨C, hC, hstrip⟩ := kadiri_gamma_strip_Olog
  refine ⟨4 * C, by nlinarith [hC.le], ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with T hT
  intro σ hσ
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  let w : ℂ := (2 : ℂ) + (T : ℂ) * I
  let G : ℂ → ℂ := fun z =>
    (1 : ℂ) / (z - 1) - (1 / 2 : ℂ) * (Real.log Real.pi : ℂ) +
      (1 / 2 : ℂ) * digamma (z / 2 + 1)
  have hσIcc : σ ∈ Set.Icc (-1 : ℝ) 2 := by
    simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] using hσ
  have hT_nonneg : 0 ≤ T := by linarith
  have hTabs : |T| = T := abs_of_nonneg hT_nonneg
  have him : 1 ≤ |T| := by rw [hTabs]; linarith
  have hs_bound : ‖G s‖ ≤ C * Real.log (T + 2) := by
    have h := hstrip s (by simpa [s] using hσIcc.1) (by simpa [s] using hσIcc.2)
      (by simpa [s] using him)
    simpa [G, s, hTabs] using h
  have hw_bound : ‖G w‖ ≤ C * Real.log (T + 2) := by
    have h := hstrip w (by norm_num [w]) (by norm_num [w])
      (by simpa [w] using him)
    simpa [G, w, hTabs] using h
  have hlog_plus_le : Real.log (T + 2) ≤ 2 * Real.log T := by
    have hfactor : 0 ≤ (T - 2) * (T + 1) := by
      exact mul_nonneg (by linarith) (by linarith)
    have hsq : T + 2 ≤ T ^ (2 : ℕ) := by nlinarith
    have hlog_sq : Real.log (T ^ (2 : ℕ)) = 2 * Real.log T := by
      simp
    calc
      Real.log (T + 2) ≤ Real.log (T ^ (2 : ℕ)) :=
        Real.log_le_log (by linarith) hsq
      _ = 2 * Real.log T := hlog_sq
  have hpair_eq :
      ((1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - 1) -
            (1 : ℂ) / (1 + (T : ℂ) * I)) +
          (((1 / 2 : ℂ) * digamma ((((σ : ℂ) + (T : ℂ) * I) / 2) + 1)) -
            ((1 / 2 : ℂ) * digamma ((((2 : ℂ) + (T : ℂ) * I) / 2) + 1))) =
        G s - G w := by
    simp [G, s, w]
    ring
  calc
    ‖((1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - 1) -
            (1 : ℂ) / (1 + (T : ℂ) * I)) +
          (((1 / 2 : ℂ) * digamma ((((σ : ℂ) + (T : ℂ) * I) / 2) + 1)) -
            ((1 / 2 : ℂ) * digamma ((((2 : ℂ) + (T : ℂ) * I) / 2) + 1)))‖
        = ‖G s - G w‖ := by rw [hpair_eq]
    _ ≤ ‖G s‖ + ‖G w‖ := norm_sub_le (G s) (G w)
    _ ≤ C * Real.log (T + 2) + C * Real.log (T + 2) :=
          add_le_add hs_bound hw_bound
    _ = 2 * C * Real.log (T + 2) := by ring
    _ ≤ 2 * C * (2 * Real.log T) := by
          exact mul_le_mul_of_nonneg_left hlog_plus_le (by nlinarith [hC.le])
    _ = (4 * C) * Real.log T := by ring

/--
The near-window paired Hadamard zero sum is exactly the local principal block
minus the reference block at `2 + iT`.
-/
theorem kadiri_zeroes_sum_near_paired_eq_localPrincipal_sub_reference (T σ : ℝ) :
    riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Icc (T - 1) (T + 1))
        (fun ρ => (1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - ρ) -
          (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ)) =
      (∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
          ((riemannZeta.order (rho : ℂ) : ℂ) /
            (((σ : ℂ) + (T : ℂ) * I) - (rho : ℂ)))) -
        kadiriLocalZeroReferenceBlock T := by
  classical
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  let w : ℂ := (2 : ℂ) + (T : ℂ) * I
  let L : Finset NontrivialZeros := (kadiriLocalZeroWindow_finite T).toFinset
  let N : Finset ℂ := (kadiriCriticalStripNearZeroes_finite T).toFinset
  have hzeroes_sum :
      riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Icc (T - 1) (T + 1))
          (fun ρ => (1 : ℂ) / (s - ρ) - (1 : ℂ) / (w - ρ)) =
        ∑ z ∈ N,
          (((1 : ℂ) / (s - z) - (1 : ℂ) / (w - z)) *
            ((riemannZeta.order z : ℤ) : ℂ)) := by
    simpa [N] using
      riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := .Ioo (0 : ℝ) 1) (J := .Icc (T - 1) (T + 1))
        (f := fun ρ => (1 : ℂ) / (s - ρ) - (1 : ℂ) / (w - ρ))
        (kadiriCriticalStripNearZeroes_finite T)
  have hsum :
      (∑ rho ∈ L,
          (((1 : ℂ) / (s - (rho : ℂ)) - (1 : ℂ) / (w - (rho : ℂ))) *
            ((riemannZeta.order (rho : ℂ) : ℤ) : ℂ))) =
        ∑ z ∈ N,
          (((1 : ℂ) / (s - z) - (1 : ℂ) / (w - z)) *
            ((riemannZeta.order z : ℤ) : ℂ)) := by
    refine Finset.sum_bij (fun rho _ => (rho : ℂ)) ?_ ?_ ?_ ?_
    · intro rho hrho
      dsimp [N]
      rw [(kadiriCriticalStripNearZeroes_finite T).mem_toFinset]
      dsimp [L] at hrho
      have hrho_window : rho ∈ kadiriLocalZeroWindow T :=
        (kadiriLocalZeroWindow_finite T).mem_toFinset.mp hrho
      rw [kadiriLocalZeroWindow, Set.mem_setOf_eq] at hrho_window
      have him := abs_le.mp hrho_window
      refine ⟨?_, ?_, riemannZeta_nontrivialZero_zero rho⟩
      · exact ⟨rho.property.1.1, rho.property.1.2⟩
      · exact ⟨by linarith [him.1], by linarith [him.2]⟩
    · intro rho₁ _ rho₂ _ h
      exact Subtype.ext h
    · intro z hz
      dsimp [N] at hz
      have hzmem :=
        (kadiriCriticalStripNearZeroes_finite T).mem_toFinset.mp hz
      let rho : NontrivialZeros := ⟨z, ⟨hzmem.1, trivial, hzmem.2.2⟩⟩
      refine ⟨rho, ?_, ?_⟩
      · dsimp [L]
        rw [(kadiriLocalZeroWindow_finite T).mem_toFinset]
        rw [kadiriLocalZeroWindow, Set.mem_setOf_eq]
        exact abs_le.mpr ⟨by linarith [hzmem.2.1.1], by linarith [hzmem.2.1.2]⟩
      · rfl
    · intro rho hrho
      rfl
  have hlocal :
      (∑ rho ∈ L,
          (((1 : ℂ) / (s - (rho : ℂ)) - (1 : ℂ) / (w - (rho : ℂ))) *
            ((riemannZeta.order (rho : ℂ) : ℤ) : ℂ))) =
        (∑ rho ∈ L, ((riemannZeta.order (rho : ℂ) : ℂ) / (s - (rho : ℂ)))) -
          ∑ rho ∈ L, ((riemannZeta.order (rho : ℂ) : ℂ) / (w - (rho : ℂ))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro rho hrho
    ring
  rw [hzeroes_sum, ← hsum, hlocal]
  simp [kadiriLocalZeroReferenceBlock, s, w, L]

/--
Hadamard/PV bridge for the local zeta logarithmic-derivative remainder.

This is the algebraic identity that connects the endpoint's finite local
principal subtraction to the global Hadamard split plus the far-tail term.
-/
theorem kadiriLocalZetaLogDerivPVRemainder_eq_hadamard_farTail_components
    (T σ : ℝ)
    (hs0 : ((σ : ℂ) + (T : ℂ) * I) ≠ 0)
    (hs1 : ((σ : ℂ) + (T : ℂ) * I) ≠ 1)
    (hsZ : ((σ : ℂ) + (T : ℂ) * I) ∉ riemannZeta.zeroes) :
    kadiriLocalZetaLogDerivPVRemainder T σ =
      deriv riemannZeta (((2 : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((2 : ℂ) + (T : ℂ) * I)) -
        ((1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - 1) -
          (1 : ℂ) / (1 + (T : ℂ) * I)) -
        (((1 / 2 : ℂ) * digamma ((((σ : ℂ) + (T : ℂ) * I) / 2) + 1)) -
          ((1 / 2 : ℂ) * digamma ((((2 : ℂ) + (T : ℂ) * I) / 2) + 1))) -
        kadiriLocalZeroReferenceBlock T +
        kadiriFarTailPairedZeroesSum T σ := by
  classical
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  let w : ℂ := (2 : ℂ) + (T : ℂ) * I
  let allPaired : ℂ :=
    riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.univ : Set ℝ)
      (fun ρ => (1 : ℂ) / (s - ρ) - (1 : ℂ) / (w - ρ))
  let nearPaired : ℂ :=
    riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Icc (T - 1) (T + 1))
      (fun ρ => (1 : ℂ) / (s - ρ) - (1 : ℂ) / (w - ρ))
  let farPaired : ℂ := kadiriFarTailPairedZeroesSum T σ
  let principal : ℂ :=
    ∑ rho ∈ (kadiriLocalZeroWindow_finite T).toFinset,
      ((riemannZeta.order (rho : ℂ) : ℂ) / (s - (rho : ℂ)))
  let poleDiff : ℂ := (1 : ℂ) / (s - 1) - (1 : ℂ) / (1 + (T : ℂ) * I)
  let gammaDiff : ℂ :=
    ((1 / 2 : ℂ) * digamma (s / 2 + 1)) -
      ((1 / 2 : ℂ) * digamma (w / 2 + 1))
  have hsub :
      -deriv riemannZeta s / riemannZeta s -
          (-deriv riemannZeta w / riemannZeta w) =
        poleDiff + gammaDiff - allPaired := by
    simpa [s, w, allPaired, poleDiff, gammaDiff] using
      kadiri_subtract_at_two_add_it_truncation_clean s T hs0 hs1 hsZ
  have hsplit : allPaired = nearPaired + farPaired := by
    simpa [s, w, allPaired, nearPaired, farPaired, kadiriFarTailPairedZeroesSum] using
      kadiri_zeroes_sum_split_near_far T σ
  have hnear : nearPaired = principal - kadiriLocalZeroReferenceBlock T := by
    simpa [s, w, nearPaired, principal] using
      kadiri_zeroes_sum_near_paired_eq_localPrincipal_sub_reference T σ
  have hall : allPaired = principal - kadiriLocalZeroReferenceBlock T + farPaired := by
    rw [hsplit, hnear]
  have hzeta :
      deriv riemannZeta s / riemannZeta s =
        deriv riemannZeta w / riemannZeta w -
          (poleDiff + gammaDiff - allPaired) := by
    calc
      deriv riemannZeta s / riemannZeta s
          = deriv riemannZeta w / riemannZeta w -
              (-deriv riemannZeta s / riemannZeta s -
                (-deriv riemannZeta w / riemannZeta w)) := by ring
      _ = deriv riemannZeta w / riemannZeta w -
              (poleDiff + gammaDiff - allPaired) := by rw [hsub]
  calc
    kadiriLocalZetaLogDerivPVRemainder T σ
        = deriv riemannZeta s / riemannZeta s - principal := by
            simp [kadiriLocalZetaLogDerivPVRemainder, principal, s]
    _ = (deriv riemannZeta w / riemannZeta w -
          (poleDiff + gammaDiff - allPaired)) - principal := by rw [hzeta]
    _ = deriv riemannZeta w / riemannZeta w -
          poleDiff - gammaDiff - kadiriLocalZeroReferenceBlock T + farPaired := by
            rw [hall]
            ring
    _ = deriv riemannZeta (((2 : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((2 : ℂ) + (T : ℂ) * I)) -
        ((1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - 1) -
          (1 : ℂ) / (1 + (T : ℂ) * I)) -
        (((1 / 2 : ℂ) * digamma ((((σ : ℂ) + (T : ℂ) * I) / 2) + 1)) -
          ((1 / 2 : ℂ) * digamma ((((2 : ℂ) + (T : ℂ) * I) / 2) + 1))) -
        kadiriLocalZeroReferenceBlock T +
        kadiriFarTailPairedZeroesSum T σ := by
            simp [s, w, poleDiff, gammaDiff, farPaired]

/-- Exact-name algebraic bridge for the Titchmarsh assembly. -/
theorem kadiriLocalZetaLogDerivPVRemainder_eq_bridge
    (T σ : ℝ)
    (hs0 : ((σ : ℂ) + (T : ℂ) * I) ≠ 0)
    (hs1 : ((σ : ℂ) + (T : ℂ) * I) ≠ 1)
    (hsZ : ((σ : ℂ) + (T : ℂ) * I) ∉ riemannZeta.zeroes) :
    kadiriLocalZetaLogDerivPVRemainder T σ =
      deriv riemannZeta (((2 : ℂ) + (T : ℂ) * I)) /
          riemannZeta (((2 : ℂ) + (T : ℂ) * I)) -
        ((1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - 1) -
          (1 : ℂ) / (1 + (T : ℂ) * I)) -
        (((1 / 2 : ℂ) * digamma ((((σ : ℂ) + (T : ℂ) * I) / 2) + 1)) -
          ((1 / 2 : ℂ) * digamma ((((2 : ℂ) + (T : ℂ) * I) / 2) + 1))) -
        kadiriLocalZeroReferenceBlock T +
        kadiriFarTailPairedZeroesSum T σ :=
  kadiriLocalZetaLogDerivPVRemainder_eq_hadamard_farTail_components T σ hs0 hs1 hsZ

/--
No-carry Titchmarsh local partial-fraction bound on the selected dyadic
good-height filter.
-/
theorem kadiriTitchmarshLocalPartialFractionLogBoundOnFilter_of_dyadicGoodHeight
    (hsrc : zeroImagDyadicCumulativeCountBoundSource) :
    kadiriTitchmarshLocalPartialFractionLogBoundOnFilter
      (kadiriDyadicGoodHeightFilter hsrc) := by
  obtain ⟨RA, hRA, hA⟩ := exists_kadiriRightHalfplaneLogDerivAtTwo_norm_le_log
  obtain ⟨RG, hRG, hG⟩ := exists_kadiriPoleDigammaDifference_norm_le_log
  obtain ⟨RR, hRR, hRef⟩ := exists_kadiriLocalZeroReferenceBlock_norm_le_log
  obtain ⟨RF, hRF, hFar⟩ := exists_kadiriFarTailPairedZeroesSum_norm_le_log
  refine ⟨RA + RG + RR + RF, by linarith, ?_⟩
  have hle := kadiriDyadicGoodHeightFilter_le_atTop hsrc
  have hA_good := hA.filter_mono hle
  have hG_good := hG.filter_mono hle
  have hRef_good := hRef.filter_mono hle
  have hFar_good := hFar.filter_mono hle
  have hT_good := (Filter.eventually_ge_atTop (3 : ℝ)).filter_mono hle
  filter_upwards [hA_good, hG_good, hRef_good, hFar_good, hT_good,
    eventually_kadiriDyadicGoodHeightFilter_offPole hsrc]
    with T hA_T hG_T hRef_T hFar_T hT_ge hOff
  intro σ hσ
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  let A : ℂ := deriv riemannZeta (((2 : ℂ) + (T : ℂ) * I)) /
    riemannZeta (((2 : ℂ) + (T : ℂ) * I))
  let PΓ : ℂ :=
    ((1 : ℂ) / (s - 1) - (1 : ℂ) / (1 + (T : ℂ) * I)) +
      (((1 / 2 : ℂ) * digamma ((s / 2) + 1)) -
        ((1 / 2 : ℂ) * digamma ((((2 : ℂ) + (T : ℂ) * I) / 2) + 1)))
  let Ref : ℂ := kadiriLocalZeroReferenceBlock T
  let Far : ℂ := kadiriFarTailPairedZeroesSum T σ
  have hT_nonneg : 0 ≤ T := by linarith
  have hTabs : |T| = T := abs_of_nonneg hT_nonneg
  have hs0 : s ≠ 0 := by
    intro hs
    have him := congrArg Complex.im hs
    simp [s] at him
    linarith
  have hs1 : s ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp [s] at him
    linarith
  have hsZ : s ∉ riemannZeta.zeroes := by
    have hzeta_ne := riemannZeta_ne_zero_on_horizontal_of_offPole (T := T) (σ := σ) hOff
    simpa [riemannZeta.zeroes, s] using hzeta_ne
  have hbridge :
      kadiriLocalZetaLogDerivPVRemainder T σ = A - PΓ - Ref + Far := by
    rw [kadiriLocalZetaLogDerivPVRemainder_eq_bridge T σ
      (by simpa [s] using hs0) (by simpa [s] using hs1) (by simpa [s] using hsZ)]
    simp [A, PΓ, Ref, Far, s]
    ring
  have hnorm_split :
      ‖A - PΓ - Ref + Far‖ ≤ ‖A‖ + ‖PΓ‖ + ‖Ref‖ + ‖Far‖ := by
    have h1 : ‖A - PΓ - Ref + Far‖ ≤ ‖A - PΓ - Ref‖ + ‖Far‖ :=
      norm_add_le _ _
    have h2 : ‖A - PΓ - Ref‖ ≤ ‖A - PΓ‖ + ‖Ref‖ :=
      norm_sub_le (A - PΓ) Ref
    have h3 : ‖A - PΓ‖ ≤ ‖A‖ + ‖PΓ‖ := norm_sub_le A PΓ
    linarith
  have hA_bound : ‖A‖ ≤ RA * Real.log T := by
    simpa [A] using hA_T
  have hG_bound : ‖PΓ‖ ≤ RG * Real.log T := by
    simpa [PΓ, s] using hG_T σ hσ
  have hRef_bound : ‖Ref‖ ≤ RR * Real.log T := by
    simpa [Ref] using hRef_T
  have hFar_bound : ‖Far‖ ≤ RF * Real.log T := by
    simpa [Far] using hFar_T σ hσ
  calc
    ‖kadiriLocalZetaLogDerivPVRemainder T σ‖
        = ‖A - PΓ - Ref + Far‖ := by rw [hbridge]
    _ ≤ ‖A‖ + ‖PΓ‖ + ‖Ref‖ + ‖Far‖ := hnorm_split
    _ ≤ RA * Real.log T + RG * Real.log T + RR * Real.log T + RF * Real.log T := by
          linarith
    _ = (RA + RG + RR + RF) * Real.log T := by ring
    _ = (RA + RG + RR + RF) * Real.log |T| := by rw [hTabs]

/-- Unconditional selected-height Titchmarsh local partial-fraction bound. -/
theorem kadiriTitchmarshLocalPartialFractionLogBoundOnFilter_unconditional :
    kadiriTitchmarshLocalPartialFractionLogBoundOnFilter
      (kadiriDyadicGoodHeightFilter
        zeroImagDyadicCumulativeCountBoundSource_of_local_window) :=
  kadiriTitchmarshLocalPartialFractionLogBoundOnFilter_of_dyadicGoodHeight
    zeroImagDyadicCumulativeCountBoundSource_of_local_window

end

end Kadiri
