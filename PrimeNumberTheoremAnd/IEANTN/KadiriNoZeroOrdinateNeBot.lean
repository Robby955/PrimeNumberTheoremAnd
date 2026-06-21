import PrimeNumberTheoremAnd.IEANTN.KadiriQ1HorizontalPVClose
import Mathlib.Analysis.Real.Cardinality

/-!
# Non-vacuity of Kadiri no-zero ordinate filters

This file certifies that the source filters in the faithful horizontal
vanishing statements are nontrivial. The proof uses the existing project lemma
that zeta zeros are finite on compact sets, then covers the plane by closed
balls and applies a countable-image argument to ordinates.
-/

namespace Kadiri

open Filter Set
open scoped Topology

noncomputable section

/-- The zero set of the Riemann zeta function is countable. -/
theorem riemannZeta_setOf_zero_countable :
    {ρ : ℂ | riemannZeta ρ = 0}.Countable := by
  have hcover :
      {ρ : ℂ | riemannZeta ρ = 0} ⊆
        ⋃ n : ℕ, Metric.closedBall (0 : ℂ) (n : ℝ) ∩ riemannZeta.zeroes := by
    intro ρ hρ
    rcases exists_nat_ge ‖ρ‖ with ⟨n, hn⟩
    refine mem_iUnion.2 ⟨n, ?_⟩
    exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hn,
      by simpa [riemannZeta.zeroes] using hρ⟩
  refine (countable_iUnion fun n : ℕ => ?_).mono hcover
  exact (riemannZeta.zeroes_on_Compact_finite'
    (S := Metric.closedBall (0 : ℂ) (n : ℝ))
    (isCompact_closedBall (0 : ℂ) (n : ℝ))).countable

private lemma kadiri_badOrdinate_countable :
    {T : ℝ | ¬ KadiriNoZeroOrdinate T}.Countable := by
  classical
  refine (riemannZeta_setOf_zero_countable.image Complex.im).mono ?_
  intro T hT
  change ¬ (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.im ≠ T) at hT
  push Not at hT
  rcases hT with ⟨ρ, hρ, hρT⟩
  exact ⟨ρ, hρ, hρT⟩

private lemma kadiri_badOrdinate_neg_countable :
    {T : ℝ | ¬ KadiriNoZeroOrdinate (-T)}.Countable := by
  refine (kadiri_badOrdinate_countable.image fun T : ℝ => -T).mono ?_
  intro T hT
  exact ⟨-T, hT, by simp⟩

private lemma kadiri_badOrdinate_twoSided_countable :
    {T : ℝ | ¬ (KadiriNoZeroOrdinate T ∧ KadiriNoZeroOrdinate (-T))}.Countable := by
  classical
  refine (kadiri_badOrdinate_countable.union kadiri_badOrdinate_neg_countable).mono ?_
  intro T hT
  rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
  by_cases htop : KadiriNoZeroOrdinate T
  · exact Or.inr fun hbot => hT ⟨htop, hbot⟩
  · exact Or.inl htop

private lemma frequently_atTop_of_countable_bad {p : ℝ → Prop}
    (hbad : {T : ℝ | ¬ p T}.Countable) :
    ∃ᶠ T in atTop, p T := by
  classical
  rw [frequently_atTop]
  intro M
  by_contra hnone
  push Not at hnone
  have hsubset : Set.Ioc M (M + 1) ⊆ {T : ℝ | ¬ p T} := by
    intro T hT
    exact hnone T (le_of_lt hT.1)
  have hcount : (Set.Ioc M (M + 1)).Countable := hbad.mono hsubset
  have hsmall : Cardinal.mk (Set.Ioc M (M + 1)) ≤ Cardinal.aleph0 :=
    (Cardinal.le_aleph0_iff_set_countable).2 hcount
  have hinterval : Cardinal.mk (Set.Ioc M (M + 1)) = Cardinal.continuum :=
    Cardinal.mk_Ioc_real (by linarith : M < M + 1)
  rw [hinterval] at hsmall
  exact (not_le_of_gt Cardinal.aleph0_lt_continuum) hsmall

/-- Cofinally often, no zero of `ζ` has ordinate `T`. -/
theorem kadiriNoZeroOrdinate_frequently_atTop :
    ∃ᶠ T in atTop, KadiriNoZeroOrdinate T :=
  frequently_atTop_of_countable_bad kadiri_badOrdinate_countable

/-- The top horizontal no-zero-ordinate source filter is nontrivial. -/
instance instNeBot_atTop_inf_principal_kadiriNoZeroOrdinate :
    (Filter.atTop ⊓ Filter.principal {T : ℝ | KadiriNoZeroOrdinate T}).NeBot :=
  Filter.frequently_iff_neBot.mp kadiriNoZeroOrdinate_frequently_atTop

/-- The bottom horizontal no-zero-ordinate source filter is nontrivial. -/
instance instNeBot_atTop_inf_principal_kadiriNoZeroOrdinate_neg :
    (Filter.atTop ⊓ Filter.principal {T : ℝ | KadiriNoZeroOrdinate (-T)}).NeBot :=
  Filter.frequently_iff_neBot.mp
    (frequently_atTop_of_countable_bad kadiri_badOrdinate_neg_countable)

/-- The two-sided no-zero-ordinate source filter is nontrivial. -/
instance instNeBot_atTop_inf_principal_kadiriNoZeroOrdinate_twoSided :
    (Filter.atTop ⊓
      Filter.principal {T : ℝ | KadiriNoZeroOrdinate T ∧ KadiriNoZeroOrdinate (-T)}).NeBot :=
  Filter.frequently_iff_neBot.mp
    (frequently_atTop_of_countable_bad kadiri_badOrdinate_twoSided_countable)

end

end Kadiri
