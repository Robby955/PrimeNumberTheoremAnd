import PrimeNumberTheoremAnd.IEANTN.KadiriLocalZeroWindowCount

/-!
# Near-band zero reference bound

This file isolates the elementary geometry step for the zeros with
`|t - Im rho| <= 1`.  The analytic input is the local zero-count source
`kadiriNearBandZeroCountLogSource`; the contribution of each retained zero at
the reference point `2 + it` is at most one because the real-part separation is
at least one.
-/

namespace Kadiri

open Complex Filter Asymptotics
open scoped BigOperators Topology

noncomputable section

/-- Non-trivial zeta zeros whose ordinates lie within one of `t`. -/
def kadiriNearBandWindow (t : ℝ) : Set NontrivialZeros :=
  {rho | |t - (rho : ℂ).im| ≤ 1}

/-- The near-band window is finite. -/
theorem kadiriNearBandWindow_finite (t : ℝ) :
    (kadiriNearBandWindow t).Finite := by
  apply Set.Finite.subset (nontrivialZeros_abs_im_lt_finite (|t| + 2))
  intro rho hrho
  rw [kadiriNearBandWindow, Set.mem_setOf_eq] at hrho
  rw [Set.mem_setOf_eq]
  have him_le : |(rho : ℂ).im| ≤ |t| + |t - (rho : ℂ).im| := by
    calc
      |(rho : ℂ).im| = |t - (t - (rho : ℂ).im)| := by
        congr 1
        ring
      _ ≤ |t| + |t - (rho : ℂ).im| := abs_sub t (t - (rho : ℂ).im)
  calc
    |(rho : ℂ).im| ≤ |t| + |t - (rho : ℂ).im| := him_le
    _ ≤ |t| + 1 := by linarith
    _ < |t| + 2 := by linarith [abs_nonneg t]

/-- The critical-strip zero rectangle in the near band is finite. -/
theorem kadiriNearBandZeroesRect_finite (t : ℝ) :
    (riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Icc (t - 1) (t + 1))).Finite := by
  rw [riemannZeta.zeroes_rect_eq]
  let S : Set ℂ := (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1) ∩
    (Complex.im ⁻¹' Set.Icc (t - 1) (t + 1))
  have hS : IsCompact S := by
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  refine (riemannZeta.zeroes_on_Compact_finite' (S := S) hS).subset ?_
  intro z hz
  rcases hz with ⟨⟨hre, him⟩, hzero⟩
  exact ⟨⟨⟨le_of_lt hre.1, le_of_lt hre.2⟩, him⟩, hzero⟩

/-- The reference reciprocal sum over the near band. -/
noncomputable def kadiriNearBandReferenceSum (t : ℝ) : ℝ :=
  ∑ rho ∈ (kadiriNearBandWindow_finite t).toFinset,
    ‖(1 : ℂ) / (((2 : ℝ) : ℂ) + (t : ℂ) * I - (rho : ℂ))‖

/-- The multiplicity-weighted near-band reference reciprocal sum. -/
noncomputable def kadiriNearBandWeightedReferenceSum (t : ℝ) : ℝ :=
  riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Icc (t - 1) (t + 1))
    fun rho => ‖(1 : ℂ) / (((2 : ℝ) : ℂ) + (t : ℂ) * I - rho)‖

/-- The multiplicity-weighted near-band zero count. -/
noncomputable def kadiriNearBandWeightedCount (t : ℝ) : ℝ :=
  riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Icc (t - 1) (t + 1))
    fun _ => (1 : ℝ)

/-- Source shape supplied by a Backlund local zero-count bound. -/
def kadiriNearBandZeroCountLogSource : Prop :=
  (fun t : ℝ => ((kadiriNearBandWindow t).ncard : ℝ)) =O[atTop] Real.log

/-- Multiplicity-weighted source shape supplied by a Backlund local zero-count bound. -/
def kadiriNearBandWeightedCountLogSource : Prop :=
  kadiriNearBandWeightedCount =O[atTop] Real.log

/-- At `2 + it`, every non-trivial zero has real-part separation at least one. -/
lemma one_le_norm_two_add_it_sub_zero (t : ℝ) (rho : NontrivialZeros) :
    (1 : ℝ) ≤ ‖(((2 : ℝ) : ℂ) + (t : ℂ) * I - (rho : ℂ))‖ := by
  let z : ℂ := ((2 : ℝ) : ℂ) + (t : ℂ) * I - (rho : ℂ)
  have hzre : z.re = 2 - (rho : ℂ).re := by
    simp [z]
  have hreal_nonneg : 0 ≤ z.re := by
    rw [hzre]
    linarith [rho.property.1.2]
  have hreal_ge : (1 : ℝ) ≤ |z.re| := by
    rw [abs_of_nonneg hreal_nonneg, hzre]
    linarith [rho.property.1.2]
  exact hreal_ge.trans (Complex.abs_re_le_norm z)

/-- Each near-band reference denominator contributes at most one. -/
lemma norm_one_div_two_add_it_sub_zero_le_one (t : ℝ) (rho : NontrivialZeros) :
    ‖(1 : ℂ) / (((2 : ℝ) : ℂ) + (t : ℂ) * I - (rho : ℂ))‖ ≤ 1 := by
  have hnorm := one_le_norm_two_add_it_sub_zero t rho
  have hpos :
      0 < ‖(((2 : ℝ) : ℂ) + (t : ℂ) * I - (rho : ℂ))‖ := by
    linarith
  rw [norm_div, norm_one]
  exact (div_le_one hpos).mpr hnorm

/-- Complex version of the reference denominator bound for zeros in the critical strip. -/
lemma norm_one_div_two_add_it_sub_zero_le_one_of_mem {t : ℝ} {rho : ℂ}
    (hrho : rho ∈ riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Icc (t - 1) (t + 1))) :
    ‖(1 : ℂ) / (((2 : ℝ) : ℂ) + (t : ℂ) * I - rho)‖ ≤ 1 := by
  let z : ℂ := ((2 : ℝ) : ℂ) + (t : ℂ) * I - rho
  have hzre : z.re = 2 - rho.re := by
    simp [z]
  have hreal_nonneg : 0 ≤ z.re := by
    rw [hzre]
    linarith [hrho.1.2]
  have hreal_ge : (1 : ℝ) ≤ |z.re| := by
    rw [abs_of_nonneg hreal_nonneg, hzre]
    linarith [hrho.1.2]
  have hnorm : (1 : ℝ) ≤ ‖z‖ := hreal_ge.trans (Complex.abs_re_le_norm z)
  have hpos : 0 < ‖z‖ := by linarith
  rw [norm_div, norm_one]
  exact (div_le_one hpos).mpr hnorm

/-- The near-band reference sum is bounded by the number of near-band zeros. -/
theorem kadiriNearBandReferenceSum_le_count (t : ℝ) :
    kadiriNearBandReferenceSum t ≤ ((kadiriNearBandWindow t).ncard : ℝ) := by
  classical
  unfold kadiriNearBandReferenceSum
  calc
    (∑ rho ∈ (kadiriNearBandWindow_finite t).toFinset,
        ‖(1 : ℂ) / (((2 : ℝ) : ℂ) + (t : ℂ) * I - (rho : ℂ))‖)
        ≤ ∑ _rho ∈ (kadiriNearBandWindow_finite t).toFinset, (1 : ℝ) := by
          exact Finset.sum_le_sum fun rho _ =>
            norm_one_div_two_add_it_sub_zero_le_one t rho
    _ = (((kadiriNearBandWindow_finite t).toFinset.card : ℕ) : ℝ) := by
          simp
    _ = ((kadiriNearBandWindow t).ncard : ℝ) := by
          rw [Set.ncard_eq_toFinset_card (kadiriNearBandWindow t)
            (kadiriNearBandWindow_finite t)]

/-- The weighted near-band reference sum is bounded by the weighted zero count. -/
theorem kadiriNearBandWeightedReferenceSum_le_count (t : ℝ) :
    kadiriNearBandWeightedReferenceSum t ≤ kadiriNearBandWeightedCount t := by
  classical
  have hfin := kadiriNearBandZeroesRect_finite t
  rw [kadiriNearBandWeightedReferenceSum, kadiriNearBandWeightedCount,
    riemannZeta.zeroes_sum_eq_finset_of_finite
      (I := .Ioo (0 : ℝ) 1) (J := .Icc (t - 1) (t + 1))
      (f := fun rho => ‖(1 : ℂ) / (((2 : ℝ) : ℂ) + (t : ℂ) * I - rho)‖) hfin,
    riemannZeta.zeroes_sum_eq_finset_of_finite
      (I := .Ioo (0 : ℝ) 1) (J := .Icc (t - 1) (t + 1))
      (f := fun _ => (1 : ℝ)) hfin]
  refine Finset.sum_le_sum fun rho hrho => ?_
  have hmem : rho ∈ riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Icc (t - 1) (t + 1)) :=
    hfin.mem_toFinset.mp hrho
  have horder_nonneg : 0 ≤ ((riemannZeta.order rho : ℤ) : ℝ) := by
    exact_mod_cast riemannZeta_order_nonneg (by
      intro hρ
      have hre_lt := hmem.1.2
      rw [hρ] at hre_lt
      norm_num at hre_lt)
  have hterm := norm_one_div_two_add_it_sub_zero_le_one_of_mem (t := t) hmem
  calc
    ‖(1 : ℂ) / (((2 : ℝ) : ℂ) + (t : ℂ) * I - rho)‖ *
        ((riemannZeta.order rho : ℤ) : ℝ)
        ≤ 1 * ((riemannZeta.order rho : ℤ) : ℝ) :=
          mul_le_mul_of_nonneg_right hterm horder_nonneg
    _ = 1 * ((riemannZeta.order rho : ℤ) : ℝ) := rfl

/-- The weighted near-band count is nonnegative. -/
theorem kadiriNearBandWeightedCount_nonneg (t : ℝ) :
    0 ≤ kadiriNearBandWeightedCount t := by
  rw [kadiriNearBandWeightedCount,
    riemannZeta.zeroes_sum_eq_finset_of_finite
      (I := .Ioo (0 : ℝ) 1) (J := .Icc (t - 1) (t + 1))
      (f := fun _ => (1 : ℝ)) (kadiriNearBandZeroesRect_finite t)]
  exact Finset.sum_nonneg fun rho hrho => by
    have hmem := (kadiriNearBandZeroesRect_finite t).mem_toFinset.mp hrho
    exact mul_nonneg zero_le_one (by
      exact_mod_cast riemannZeta_order_nonneg (by
        intro hρ
        have hre_lt := hmem.1.2
        rw [hρ] at hre_lt
        norm_num at hre_lt))

/--
The critical-strip near-band weighted count is bounded by the wider U6a window count.
The U6a count uses `Re rho ∈ [-1,2]`, so it contains the non-trivial zero strip.
-/
theorem kadiriNearBandWeightedCount_le_u6aNearbyZeroCount (t : ℝ) :
    kadiriNearBandWeightedCount t ≤ u6aNearbyZeroCount (-1) 2 t := by
  classical
  let near : Finset ℂ := (kadiriNearBandZeroesRect_finite t).toFinset
  let wide : Finset ℂ := (u6aFTNearbyWindow_finite t).toFinset
  have hnear_sum :
      kadiriNearBandWeightedCount t =
        ∑ rho ∈ near, ((riemannZeta.order rho : ℤ) : ℝ) := by
    simpa [kadiriNearBandWeightedCount, near] using
      riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := .Ioo (0 : ℝ) 1) (J := .Icc (t - 1) (t + 1))
        (f := fun _ => (1 : ℝ)) (kadiriNearBandZeroesRect_finite t)
  have hwide_sum :
      u6aNearbyZeroCount (-1) 2 t =
        ∑ rho ∈ wide, ((riemannZeta.order rho : ℤ) : ℝ) := by
    simpa [u6aNearbyZeroCount, wide] using
      riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := Set.uIcc (-1 : ℝ) 2) (J := Set.Icc (t - 1) (t + 1))
        (f := fun _ => (1 : ℝ)) (u6aFTNearbyWindow_finite t)
  have hsubset : near ⊆ wide := by
    intro rho hrho
    dsimp [near, wide] at hrho ⊢
    have hmem := (kadiriNearBandZeroesRect_finite t).mem_toFinset.mp hrho
    rw [(u6aFTNearbyWindow_finite t).mem_toFinset]
    obtain ⟨hre, him, hzero⟩ := hmem
    unfold u6aFTNearbyWindow riemannZeta.zeroes_rect
    refine ⟨?_, him, hzero⟩
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
    exact ⟨by linarith [hre.1], by linarith [hre.2]⟩
  have hnonneg : ∀ rho ∈ wide, 0 ≤ ((riemannZeta.order rho : ℤ) : ℝ) := by
    intro rho hrho
    dsimp [wide] at hrho
    have hmem := (u6aFTNearbyWindow_finite t).mem_toFinset.mp hrho
    obtain ⟨_hre, _him, hzero⟩ := hmem
    have hrho_ne_one : rho ≠ 1 := fun hρ => riemannZeta_one_ne_zero (hρ ▸ hzero)
    exact_mod_cast riemannZeta_order_nonneg hrho_ne_one
  rw [hnear_sum, hwide_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun rho hrho _hnot => hnonneg rho hrho)

/-- The U6a local-count atom supplies the Codex-10 near-band count source. -/
theorem kadiriNearBandWeightedCountLogSource_of_u6aLocalZeroCount :
    kadiriNearBandWeightedCountLogSource := by
  obtain ⟨C, Tₘᵢₙ, hcnt⟩ := exists_u6aLocalZeroCountLogHypothesis
  rcases hcnt with ⟨hCpos, hcnt⟩
  rw [kadiriNearBandWeightedCountLogSource, Asymptotics.isBigO_iff']
  refine ⟨C, hCpos, ?_⟩
  let T0 : ℝ := max (max |Tₘᵢₙ| 3) 1
  filter_upwards [Filter.eventually_ge_atTop T0] with t ht
  have hT_nonneg : 0 ≤ t := by
    have h1 : (1 : ℝ) ≤ T0 := by
      dsimp [T0]
      exact le_max_right _ _
    linarith
  have hTabs : |t| = t := abs_of_nonneg hT_nonneg
  have hTmin : Tₘᵢₙ ≤ |t| := by
    rw [hTabs]
    calc
      Tₘᵢₙ ≤ |Tₘᵢₙ| := le_abs_self Tₘᵢₙ
      _ ≤ max |Tₘᵢₙ| 3 := le_max_left _ _
      _ ≤ max (max |Tₘᵢₙ| 3) 1 := le_max_left _ _
      _ = T0 := rfl
      _ ≤ t := ht
  have hT_three : (3 : ℝ) ≤ |t| := by
    rw [hTabs]
    calc
      (3 : ℝ) ≤ max |Tₘᵢₙ| 3 := le_max_right _ _
      _ ≤ max (max |Tₘᵢₙ| 3) 1 := le_max_left _ _
      _ = T0 := rfl
      _ ≤ t := ht
  have hlog_nonneg : 0 ≤ Real.log t := by
    exact Real.log_nonneg (by
      have h1 : (1 : ℝ) ≤ T0 := by
        dsimp [T0]
        exact le_max_right _ _
      linarith)
  have hcount :=
    (kadiriNearBandWeightedCount_le_u6aNearbyZeroCount t).trans
      (by simpa [hTabs] using hcnt t hTmin hT_three)
  have hnear_nonneg := kadiriNearBandWeightedCount_nonneg t
  simpa [Real.norm_eq_abs, abs_of_nonneg hnear_nonneg, abs_of_nonneg hlog_nonneg]
    using hcount

/--
Near-band reference bound: assuming the local Backlund count
`# {rho : |t - Im rho| <= 1} = O(log t)`, the reference reciprocal sum at
`2 + it` is also `O(log t)`.
-/
theorem kadiriNearBandReferenceSum_isBigO_log
    (hcount : kadiriNearBandZeroCountLogSource) :
    kadiriNearBandReferenceSum =O[atTop] Real.log := by
  rw [kadiriNearBandZeroCountLogSource] at hcount
  rw [Asymptotics.isBigO_iff'] at hcount ⊢
  rcases hcount with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [hC] with t ht
  have hsum_le := kadiriNearBandReferenceSum_le_count t
  have hsum_nonneg : 0 ≤ kadiriNearBandReferenceSum t := by
    unfold kadiriNearBandReferenceSum
    exact Finset.sum_nonneg fun rho _ => norm_nonneg _
  have hcount_bound :
      ((kadiriNearBandWindow t).ncard : ℝ) ≤ C * ‖Real.log t‖ := by
    have hcard_nonneg : 0 ≤ ((kadiriNearBandWindow t).ncard : ℝ) := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hcard_nonneg] using ht
  rw [Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
  exact hsum_le.trans hcount_bound

/--
Multiplicity-weighted near-band reference bound: assuming the local Backlund
weighted count is `O(log t)`, the weighted reference reciprocal sum at `2 + it`
is also `O(log t)`.
-/
theorem kadiriNearBandWeightedReferenceSum_isBigO_log
    (hcount : kadiriNearBandWeightedCountLogSource) :
    kadiriNearBandWeightedReferenceSum =O[atTop] Real.log := by
  rw [kadiriNearBandWeightedCountLogSource] at hcount
  rw [Asymptotics.isBigO_iff'] at hcount ⊢
  rcases hcount with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [hC] with t ht
  have hsum_le := kadiriNearBandWeightedReferenceSum_le_count t
  have hsum_nonneg : 0 ≤ kadiriNearBandWeightedReferenceSum t := by
    rw [kadiriNearBandWeightedReferenceSum,
      riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := .Ioo (0 : ℝ) 1) (J := .Icc (t - 1) (t + 1))
        (f := fun rho => ‖(1 : ℂ) / (((2 : ℝ) : ℂ) + (t : ℂ) * I - rho)‖)
        (kadiriNearBandZeroesRect_finite t)]
    exact Finset.sum_nonneg fun rho hrho => by
      have hmem := (kadiriNearBandZeroesRect_finite t).mem_toFinset.mp hrho
      exact mul_nonneg (norm_nonneg _) (by
        exact_mod_cast riemannZeta_order_nonneg (by
          intro hρ
          have hre_lt := hmem.1.2
          rw [hρ] at hre_lt
          norm_num at hre_lt))
  have hcount_nonneg : 0 ≤ kadiriNearBandWeightedCount t := by
    rw [kadiriNearBandWeightedCount,
      riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := .Ioo (0 : ℝ) 1) (J := .Icc (t - 1) (t + 1))
        (f := fun _ => (1 : ℝ)) (kadiriNearBandZeroesRect_finite t)]
    exact Finset.sum_nonneg fun rho hrho => by
      have hmem := (kadiriNearBandZeroesRect_finite t).mem_toFinset.mp hrho
      exact mul_nonneg zero_le_one (by
        exact_mod_cast riemannZeta_order_nonneg (by
          intro hρ
          have hre_lt := hmem.1.2
          rw [hρ] at hre_lt
          norm_num at hre_lt))
  have hcount_bound : kadiriNearBandWeightedCount t ≤ C * ‖Real.log t‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hcount_nonneg] using ht
  rw [Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
  exact hsum_le.trans hcount_bound

/-- Consequently, the near-band reference sum has logarithmic growth. -/
theorem kadiriNearBandWeightedReferenceSum_isBigO_log_of_u6aLocalZeroCount :
    kadiriNearBandWeightedReferenceSum =O[atTop] Real.log :=
  kadiriNearBandWeightedReferenceSum_isBigO_log
    kadiriNearBandWeightedCountLogSource_of_u6aLocalZeroCount

end

end Kadiri
