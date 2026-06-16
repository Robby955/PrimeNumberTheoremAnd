import PrimeNumberTheoremAnd.IEANTN.KadiriFarTail
import PrimeNumberTheoremAnd.IEANTN.KadiriLogDerivFullSegment

/-!
# Hadamard/PV bridge for the Kadiri full-segment endpoint

This file isolates the bridge between the finite local zero window used by the
endpoint wrapper and the near-window `zeroes_sum` term produced by Hadamard's
partial-fraction identity.
-/

namespace Kadiri

open Complex
open scoped BigOperators

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

end

end Kadiri
