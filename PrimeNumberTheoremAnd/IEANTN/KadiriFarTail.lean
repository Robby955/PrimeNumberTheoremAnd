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

private def kadiriNearZeroesAllEquiv (T : ℝ) :
    {ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.univ : Set ℝ) //
      (ρ : ℂ).im ∈ Set.Icc (T - 1) (T + 1)} ≃
      riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Icc (T - 1) (T + 1)) where
  toFun ρ :=
    ⟨((ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.univ : Set ℝ)) : ℂ), by
      obtain ⟨hre, _him, hζ⟩ :=
        (ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.univ : Set ℝ)).property
      exact ⟨hre, ρ.property, hζ⟩⟩
  invFun ρ :=
    ⟨⟨(ρ : ℂ), by
        obtain ⟨hre, _him, hζ⟩ := ρ.property
        exact ⟨hre, trivial, hζ⟩⟩, by
      exact ρ.property.2.1⟩
  left_inv ρ := by
    ext
    rfl
  right_inv ρ := by
    ext
    rfl

private def kadiriFarZeroesAllEquiv (T : ℝ) :
    {ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.univ : Set ℝ) //
      ¬ (ρ : ℂ).im ∈ Set.Icc (T - 1) (T + 1)} ≃
      riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1)
        ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)}) where
  toFun ρ :=
    ⟨((ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.univ : Set ℝ)) : ℂ), by
      obtain ⟨hre, _him, hζ⟩ :=
        (ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.univ : Set ℝ)).property
      exact ⟨hre, ρ.property, hζ⟩⟩
  invFun ρ :=
    ⟨⟨(ρ : ℂ), by
        obtain ⟨hre, _him, hζ⟩ := ρ.property
        exact ⟨hre, trivial, hζ⟩⟩, by
      exact ρ.property.2.1⟩
  left_inv ρ := by
    ext
    rfl
  right_inv ρ := by
    ext
    rfl

/-- The multiplicity-weighted paired zero term is summable. -/
theorem summable_weighted_one_div_sub_one_div_at_zeros (s w : ℂ) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.univ : Set ℝ) =>
      ((1 : ℂ) / (s - (ρ : ℂ)) - (1 : ℂ) / (w - (ρ : ℂ))) *
        ((riemannZeta.order (ρ : ℂ) : ℤ) : ℂ)) := by
  have hsub := (summable_weighted_one_div_add_one_div_at_zeros s).sub
    (summable_weighted_one_div_add_one_div_at_zeros w)
  refine hsub.congr ?_
  intro ρ
  ring

set_option maxHeartbeats 1200000 in
-- The subtype/complement `zeroes_sum` split has heavy coercion normalization.
/--
Kadiri-specific near/far split of the paired Hadamard zero sum at height `T`.
This uses the upstream subtype/complement summation API rather than a custom
generic splitter.
-/
theorem kadiri_zeroes_sum_split_near_far (T σ : ℝ) :
    riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.univ : Set ℝ)
        (fun ρ => (1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - ρ) -
          (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ)) =
      riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Icc (T - 1) (T + 1))
        (fun ρ => (1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - ρ) -
          (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ)) +
      riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1)
        ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)})
        (fun ρ => (1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - ρ) -
          (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ)) := by
  classical
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  let w : ℂ := (2 : ℂ) + (T : ℂ) * I
  let All := riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.univ : Set ℝ)
  let p : All → Prop := fun ρ => (ρ : ℂ).im ∈ Set.Icc (T - 1) (T + 1)
  let F : All → ℂ := fun ρ =>
    ((1 : ℂ) / (s - (ρ : ℂ)) - (1 : ℂ) / (w - (ρ : ℂ))) *
      ((riemannZeta.order (ρ : ℂ) : ℤ) : ℂ)
  have hF : Summable F := by
    simpa [F, s, w, All] using summable_weighted_one_div_sub_one_div_at_zeros s w
  have hparts := (summable_subtype_and_compl (f := F)
    (s := {ρ : All | p ρ})).mpr hF
  rcases hparts with ⟨hnear, hfar⟩
  have hsum_sum : HasSum
      (fun x : {ρ : All // p ρ} ⊕ {ρ : All // ¬ p ρ} =>
        F (Sum.elim Subtype.val Subtype.val x))
      ((∑' ρ : {ρ : All // p ρ}, F ρ.1) +
        (∑' ρ : {ρ : All // ¬ p ρ}, F ρ.1)) := by
    simpa only [Sum.elim_inl, Sum.elim_inr] using HasSum.sum hnear.hasSum hfar.hasSum
  have hsum_all : HasSum F
      ((∑' ρ : {ρ : All // p ρ}, F ρ.1) +
        (∑' ρ : {ρ : All // ¬ p ρ}, F ρ.1)) := by
    have hcomp : HasSum (F ∘ Equiv.sumCompl p)
        ((∑' ρ : {ρ : All // p ρ}, F ρ.1) +
          (∑' ρ : {ρ : All // ¬ p ρ}, F ρ.1)) := by
      simpa [Function.comp_def, Equiv.sumCompl] using hsum_sum
    exact (Equiv.hasSum_iff (Equiv.sumCompl p)).mp hcomp
  have hall_eq : (∑' ρ : All, F ρ) =
      (∑' ρ : {ρ : All // p ρ}, F ρ.1) +
        (∑' ρ : {ρ : All // ¬ p ρ}, F ρ.1) := hsum_all.tsum_eq
  have hnear_eq :
      (∑' ρ : {ρ : All // p ρ}, F ρ.1) =
        riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Icc (T - 1) (T + 1))
          (fun ρ => (1 : ℂ) / (s - ρ) - (1 : ℂ) / (w - ρ)) := by
    unfold riemannZeta.zeroes_sum
    calc
      (∑' ρ : {ρ : All // p ρ}, F ρ.1)
          = ∑' ρ : {ρ : All // p ρ},
              ((1 : ℂ) / (s - ((kadiriNearZeroesAllEquiv T ρ) : ℂ)) -
                (1 : ℂ) / (w - ((kadiriNearZeroesAllEquiv T ρ) : ℂ))) *
                  ((riemannZeta.order ((kadiriNearZeroesAllEquiv T ρ : _) : ℂ) : ℤ) : ℂ) := by
              apply tsum_congr
              intro ρ
              rfl
      _ = ∑' ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Icc (T - 1) (T + 1)),
              ((1 : ℂ) / (s - (ρ : ℂ)) - (1 : ℂ) / (w - (ρ : ℂ))) *
                ((riemannZeta.order (ρ : ℂ) : ℤ) : ℂ) := by
              exact Equiv.tsum_eq (kadiriNearZeroesAllEquiv T)
                (fun ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Icc (T - 1) (T + 1)) =>
                  ((1 : ℂ) / (s - (ρ : ℂ)) - (1 : ℂ) / (w - (ρ : ℂ))) *
                    ((riemannZeta.order (ρ : ℂ) : ℤ) : ℂ))
  have hfar_eq :
      (∑' ρ : {ρ : All // ¬ p ρ}, F ρ.1) =
        riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1)
          ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)})
          (fun ρ => (1 : ℂ) / (s - ρ) - (1 : ℂ) / (w - ρ)) := by
    unfold riemannZeta.zeroes_sum
    calc
      (∑' ρ : {ρ : All // ¬ p ρ}, F ρ.1)
          = ∑' ρ : {ρ : All // ¬ p ρ},
              ((1 : ℂ) / (s - ((kadiriFarZeroesAllEquiv T ρ) : ℂ)) -
                (1 : ℂ) / (w - ((kadiriFarZeroesAllEquiv T ρ) : ℂ))) *
                  ((riemannZeta.order ((kadiriFarZeroesAllEquiv T ρ : _) : ℂ) : ℤ) : ℂ) := by
              apply tsum_congr
              intro ρ
              rfl
      _ = ∑' ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1)
              ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)}),
              ((1 : ℂ) / (s - (ρ : ℂ)) - (1 : ℂ) / (w - (ρ : ℂ))) *
                ((riemannZeta.order (ρ : ℂ) : ℤ) : ℂ) := by
              exact Equiv.tsum_eq (kadiriFarZeroesAllEquiv T)
                (fun ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1)
                    ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)}) =>
                  ((1 : ℂ) / (s - (ρ : ℂ)) - (1 : ℂ) / (w - (ρ : ℂ))) *
                    ((riemannZeta.order (ρ : ℂ) : ℤ) : ℂ))
  have hmain :
      (∑' ρ : All, F ρ) =
        riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1) (.Icc (T - 1) (T + 1))
          (fun ρ => (1 : ℂ) / (s - ρ) - (1 : ℂ) / (w - ρ)) +
        riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1)
          ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)})
          (fun ρ => (1 : ℂ) / (s - ρ) - (1 : ℂ) / (w - ρ)) := by
    rw [hall_eq, hnear_eq, hfar_eq]
  simpa [riemannZeta.zeroes_sum, F, s, w, All] using hmain

private theorem norm_intCast_complex_of_nonneg (n : ℤ) (hn : 0 ≤ (n : ℝ)) :
    ‖(n : ℂ)‖ = (n : ℝ) := by
  have hsquare : ‖(n : ℂ)‖ ^ (2 : ℕ) = (n : ℝ) ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply, Complex.intCast_re, Complex.intCast_im]
    ring
  nlinarith [norm_nonneg (n : ℂ)]

/-- Coerce a critical-strip far-tail zero rectangle element to a non-trivial zero. -/
private def kadiriFarTailZeroToNontrivial (T : ℝ)
    (ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1)
      ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)})) : NontrivialZeros :=
  ⟨(ρ : ℂ), ⟨ρ.property.1, trivial, ρ.property.2.2⟩⟩

private theorem kadiriFarTailZeroToNontrivial_injective (T : ℝ) :
    Function.Injective (kadiriFarTailZeroToNontrivial T) := by
  intro ρ η h
  apply Subtype.ext
  exact congrArg (fun z : NontrivialZeros => (z : ℂ)) h

/-- The weighted shifted square-height tail is summable over the Kadiri far set. -/
theorem kadiri_far_tail_weighted_height_sq_summable (T : ℝ) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1)
      ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)}) =>
        ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) *
          |T - (ρ : ℂ).im|⁻¹ ^ (2 : ℕ)) := by
  let z : ℂ := (T : ℂ) * I
  have hbase := (Kadiri.weighted_zeroImagSquareTail_shifted_summable z).comp_injective
    (kadiriFarTailZeroToNontrivial_injective T)
  refine hbase.congr ?_
  intro ρ
  simp [kadiriFarTailZeroToNontrivial, z]

/-- The pointwise majorant used for the far-tail paired difference is summable. -/
theorem kadiri_far_tail_weighted_three_height_sq_summable (T : ℝ) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1)
      ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)}) =>
        (3 * |T - (ρ : ℂ).im|⁻¹ ^ (2 : ℕ)) *
          ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ)) := by
  have h := (kadiri_far_tail_weighted_height_sq_summable T).mul_left 3
  refine h.congr ?_
  intro ρ
  ring

/--
The far part of the paired Hadamard zero sum is bounded by the weighted
square-height tail. This is the infinite-sum use of the pointwise far-tail
estimate, before regrouping that real tail into unit bands.
-/
theorem kadiri_far_tail_paired_zeroes_sum_norm_le_height_sq_tail
    (T σ : ℝ) (hσ : σ ∈ Set.uIcc (-1 : ℝ) 2) :
    ‖riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1)
        ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)})
        (fun ρ => (1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - ρ) -
          (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ))‖ ≤
      riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1)
        ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)})
        (fun ρ => 3 * |T - ρ.im|⁻¹ ^ (2 : ℕ)) := by
  classical
  let Far := riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1)
    ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)})
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  let w : ℂ := (2 : ℂ) + (T : ℂ) * I
  let F : Far → ℂ := fun ρ =>
    ((1 : ℂ) / (s - (ρ : ℂ)) - (1 : ℂ) / (w - (ρ : ℂ))) *
      ((riemannZeta.order (ρ : ℂ) : ℤ) : ℂ)
  let G : Far → ℝ := fun ρ =>
    (3 * |T - (ρ : ℂ).im|⁻¹ ^ (2 : ℕ)) *
      ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ)
  have hGsum : Summable G := by
    simpa [G, Far] using kadiri_far_tail_weighted_three_height_sq_summable T
  have hσIcc : σ ∈ Set.Icc (-1 : ℝ) 2 := by
    simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] using hσ
  have hpoint : ∀ ρ : Far, ‖F ρ‖ ≤ G ρ := by
    intro ρ
    have hnot : ¬ (ρ : ℂ).im ∈ Set.Icc (T - 1) (T + 1) := ρ.property.2.1
    have hfar : 1 ≤ |T - (ρ : ℂ).im| := by
      by_cases hle : (ρ : ℂ).im ≤ T + 1
      · have hlt : (ρ : ℂ).im < T - 1 := by
          by_contra hge_not
          have hge : T - 1 ≤ (ρ : ℂ).im := le_of_not_gt hge_not
          exact hnot ⟨hge, hle⟩
        have hnonneg : 0 ≤ T - (ρ : ℂ).im := by linarith
        rw [abs_of_nonneg hnonneg]
        linarith
      · have hgt : T + 1 < (ρ : ℂ).im := lt_of_not_ge hle
        have hnonpos : T - (ρ : ℂ).im ≤ 0 := by linarith
        rw [abs_of_nonpos hnonpos]
        linarith
    let rhoNT : NontrivialZeros := kadiriFarTailZeroToNontrivial T ρ
    have hpoint_raw :
        ‖(1 : ℂ) / (s - (ρ : ℂ)) - (1 : ℂ) / (w - (ρ : ℂ))‖ ≤
          3 * |T - (ρ : ℂ).im|⁻¹ ^ (2 : ℕ) := by
      simpa [s, w, rhoNT, kadiriFarTailZeroToNontrivial] using
        norm_one_div_sub_one_div_at_zero_le_far_height_sq
          (s := s) (t := T) (by simp [s])
          (by simpa [s] using hσIcc.1) (by simpa [s] using hσIcc.2) rhoNT hfar
    have hord_nonneg : 0 ≤ ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) := by
      exact_mod_cast riemannZeta_order_nonneg (by
        intro hρ1
        exact riemannZeta_one_ne_zero (by simpa [hρ1] using ρ.property.2.2))
    have hnorm_order : ‖((riemannZeta.order (ρ : ℂ) : ℤ) : ℂ)‖ =
        ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) :=
      norm_intCast_complex_of_nonneg (riemannZeta.order (ρ : ℂ)) hord_nonneg
    calc
      ‖F ρ‖ = ‖(1 : ℂ) / (s - (ρ : ℂ)) - (1 : ℂ) / (w - (ρ : ℂ))‖ *
          ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) := by
            dsimp [F]
            rw [norm_mul, hnorm_order]
      _ ≤ (3 * |T - (ρ : ℂ).im|⁻¹ ^ (2 : ℕ)) *
          ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) :=
            mul_le_mul_of_nonneg_right hpoint_raw hord_nonneg
      _ = G ρ := rfl
  have hFnorm : Summable fun ρ : Far => ‖F ρ‖ :=
    Summable.of_nonneg_of_le (fun ρ => norm_nonneg (F ρ)) hpoint hGsum
  have hnorm_tsum := norm_tsum_le_tsum_norm hFnorm
  have hle_tsum := Summable.tsum_le_tsum hpoint hFnorm hGsum
  unfold riemannZeta.zeroes_sum
  calc
    ‖∑' ρ : Far,
        ((1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - (ρ : ℂ)) -
          (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - (ρ : ℂ))) *
          ↑(riemannZeta.order (ρ : ℂ))‖
        = ‖∑' ρ : Far, F ρ‖ := by simp [F, s, w, Far]
    _ ≤ ∑' ρ : Far, ‖F ρ‖ := hnorm_tsum
    _ ≤ ∑' ρ : Far, G ρ := hle_tsum
    _ = ∑' ρ : Far,
        (3 * |T - (ρ : ℂ).im|⁻¹ ^ (2 : ℕ)) * ↑(riemannZeta.order (ρ : ℂ)) := by
          simp [G, Far]

/-- A finite wide U6a rectangle containing all unit windows with center `|t| <= B`. -/
private theorem u6aFTWideWindow_finite (B : ℝ) :
    (riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
      (Set.Icc (-(B + 1)) (B + 1))).Finite := by
  rw [riemannZeta.zeroes_rect_eq]
  let S : Set ℂ := (Complex.re ⁻¹' Set.Icc (-1 : ℝ) 2) ∩
    (Complex.im ⁻¹' Set.Icc (-(B + 1)) (B + 1))
  have hS : IsCompact S := by
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  refine (riemannZeta.zeroes_on_Compact_finite' (S := S) hS).subset ?_
  intro z hz
  rcases hz with ⟨⟨hre, him⟩, hzeta⟩
  have hre' : z.re ∈ Set.Icc (-1 : ℝ) 2 := by
    rwa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] at hre
  exact ⟨⟨hre', him⟩, hzeta⟩

private theorem u6aNearbyZeroCount_le_wideWindow {B t : ℝ} (hBt : |t| ≤ B) :
    u6aNearbyZeroCount (-1) 2 t ≤
      riemannZeta.zeroes_sum (Set.uIcc (-1 : ℝ) 2)
        (Set.Icc (-(B + 1)) (B + 1)) fun _ => (1 : ℝ) := by
  classical
  let near : Finset ℂ := (u6aFTNearbyWindow_finite t).toFinset
  let wide : Finset ℂ := (u6aFTWideWindow_finite B).toFinset
  have ht_low : -B ≤ t := by
    linarith [neg_le.mp (neg_le_abs t), hBt]
  have ht_high : t ≤ B := (le_abs_self t).trans hBt
  have hnear_sum :
      u6aNearbyZeroCount (-1) 2 t =
        ∑ rho ∈ near, ((riemannZeta.order rho : ℤ) : ℝ) := by
    simpa [u6aNearbyZeroCount, near] using
      riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := Set.uIcc (-1 : ℝ) 2) (J := Set.Icc (t - 1) (t + 1))
        (f := fun _ => (1 : ℝ)) (u6aFTNearbyWindow_finite t)
  have hwide_sum :
      riemannZeta.zeroes_sum (Set.uIcc (-1 : ℝ) 2)
          (Set.Icc (-(B + 1)) (B + 1)) (fun _ => (1 : ℝ)) =
        ∑ rho ∈ wide, ((riemannZeta.order rho : ℤ) : ℝ) := by
    simpa [wide] using
      riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := Set.uIcc (-1 : ℝ) 2) (J := Set.Icc (-(B + 1)) (B + 1))
        (f := fun _ => (1 : ℝ)) (u6aFTWideWindow_finite B)
  have hsubset : near ⊆ wide := by
    intro rho hrho
    dsimp [near, wide] at hrho ⊢
    have hmem := (u6aFTNearbyWindow_finite t).mem_toFinset.mp hrho
    rw [(u6aFTWideWindow_finite B).mem_toFinset]
    obtain ⟨hre, him, hzero⟩ := hmem
    refine ⟨hre, ?_, hzero⟩
    exact ⟨by linarith [him.1, ht_low], by linarith [him.2, ht_high]⟩
  have hnonneg : ∀ rho ∈ wide, 0 ≤ ((riemannZeta.order rho : ℤ) : ℝ) := by
    intro rho hrho
    have hmem := (u6aFTWideWindow_finite B).mem_toFinset.mp (by simpa [wide] using hrho)
    obtain ⟨_hre, _him, hzero⟩ := hmem
    exact_mod_cast riemannZeta_order_nonneg (by
      intro hρ
      exact riemannZeta_one_ne_zero (by simpa [hρ] using hzero))
  rw [hnear_sum, hwide_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun rho hrho _ => hnonneg rho (by simpa [wide] using hrho))

/--
Global U6a unit-window count bound. The local Jensen count controls large
ordinate centers; a single finite wide rectangle controls the compact range.
-/
theorem exists_u6aNearbyZeroCount_le_log_abs_add_one :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      u6aNearbyZeroCount (-1) 2 t ≤ C * (Real.log (|t| + 2) + 1) := by
  obtain ⟨C₀, Tₘᵢₙ, hcnt⟩ := exists_u6aLocalZeroCountLogHypothesis
  rcases hcnt with ⟨hC₀pos, hcnt⟩
  let B : ℝ := max (max |Tₘᵢₙ| 3) 0
  let M : ℝ := riemannZeta.zeroes_sum (Set.uIcc (-1 : ℝ) 2)
    (Set.Icc (-(B + 1)) (B + 1)) fun _ => (1 : ℝ)
  let C : ℝ := max C₀ M
  have hC_nonneg : 0 ≤ C := le_trans hC₀pos.le (le_max_left C₀ M)
  refine ⟨C, hC_nonneg, ?_⟩
  intro t
  have hB_abs : |Tₘᵢₙ| ≤ B := by
    dsimp [B]
    exact le_trans (le_max_left |Tₘᵢₙ| 3) (le_max_left (max |Tₘᵢₙ| 3) 0)
  have hB_three : (3 : ℝ) ≤ B := by
    dsimp [B]
    exact le_trans (le_max_right |Tₘᵢₙ| 3) (le_max_left (max |Tₘᵢₙ| 3) 0)
  have hlog_abs_add_nonneg : 0 ≤ Real.log (|t| + 2) := by
    exact Real.log_nonneg (by linarith [abs_nonneg t])
  by_cases hlarge : B ≤ |t|
  · have hTmin : Tₘᵢₙ ≤ |t| := by
      exact (le_abs_self Tₘᵢₙ).trans (hB_abs.trans hlarge)
    have hthree : (3 : ℝ) ≤ |t| := hB_three.trans hlarge
    have hcnt_t : u6aNearbyZeroCount (-1) 2 t ≤ C₀ * Real.log |t| :=
      hcnt t hTmin hthree
    have hlog_abs_nonneg : 0 ≤ Real.log |t| :=
      Real.log_nonneg (by linarith)
    have hC₀_le_C : C₀ ≤ C := le_max_left C₀ M
    have hlog_le : Real.log |t| ≤ Real.log (|t| + 2) + 1 := by
      have hpos : 0 < |t| := by linarith
      have hle_add : |t| ≤ |t| + 2 := by linarith
      calc
        Real.log |t| ≤ Real.log (|t| + 2) := Real.log_le_log hpos hle_add
        _ ≤ Real.log (|t| + 2) + 1 := by linarith
    calc
      u6aNearbyZeroCount (-1) 2 t
          ≤ C₀ * Real.log |t| := hcnt_t
      _ ≤ C * Real.log |t| :=
          mul_le_mul_of_nonneg_right hC₀_le_C hlog_abs_nonneg
      _ ≤ C * (Real.log (|t| + 2) + 1) :=
          mul_le_mul_of_nonneg_left hlog_le hC_nonneg
  · have hsmall : |t| ≤ B := le_of_not_ge hlarge
    have hwide := u6aNearbyZeroCount_le_wideWindow (B := B) (t := t) hsmall
    have hM_nonneg : 0 ≤ M := by
      dsimp [M]
      rw [riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := Set.uIcc (-1 : ℝ) 2) (J := Set.Icc (-(B + 1)) (B + 1))
        (f := fun _ => (1 : ℝ)) (u6aFTWideWindow_finite B)]
      exact Finset.sum_nonneg fun rho hrho => by
        have hmem := (u6aFTWideWindow_finite B).mem_toFinset.mp hrho
        exact mul_nonneg zero_le_one (by
          exact_mod_cast riemannZeta_order_nonneg (by
            intro hρ
            exact riemannZeta_one_ne_zero (by simpa [hρ] using hmem.2.2)))
    have hM_le_C : M ≤ C := le_max_right C₀ M
    have hone_le : (1 : ℝ) ≤ Real.log (|t| + 2) + 1 := by
      linarith
    calc
      u6aNearbyZeroCount (-1) 2 t
          ≤ M := by simpa [M] using hwide
      _ ≤ C := hM_le_C
      _ = C * 1 := by ring
      _ ≤ C * (Real.log (|t| + 2) + 1) :=
          mul_le_mul_of_nonneg_left hone_le hC_nonneg

private theorem summable_nat_add_one_inv_sq :
    Summable (fun n : ℕ => (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  simpa [one_div, inv_pow, Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).2 h

private theorem summable_log_nat_add_one_mul_inv_sq :
    Summable (fun n : ℕ =>
      Real.log ((n : ℝ) + 1) * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) := by
  have hgbase : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
    have h := (Real.summable_nat_rpow (p := (-(3 / 2 : ℝ)))).2 (by norm_num)
    simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 h
  refine summable_of_isBigO_nat hgbase ?_
  rw [Asymptotics.isBigO_iff']
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (0 : ℕ)] with n _hn
  let x : ℝ := (n : ℝ) + 1
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hxnonneg : 0 ≤ x := hxpos.le
  have hxge1 : 1 ≤ x := by
    dsimp [x]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hxge1
  have hinv_sq_nonneg : 0 ≤ x⁻¹ ^ (2 : ℕ) := by positivity
  have hlog_le : Real.log x ≤ x ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) :=
    Real.log_le_rpow_div hxnonneg (by norm_num)
  have hmul : Real.log x * (x⁻¹ ^ (2 : ℕ)) ≤
      (x ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2)) * (x⁻¹ ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_right hlog_le hinv_sq_nonneg
  have hsq_inv_rpow : (x ^ (2 : ℕ))⁻¹ = x ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast x 2]
    rw [Real.rpow_neg hxnonneg (2 : ℝ)]
    norm_num
  have hpow : (x ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2)) * (x⁻¹ ^ (2 : ℕ)) =
      2 * x ^ (-(3 / 2 : ℝ)) := by
    rw [div_eq_mul_inv]
    norm_num
    rw [hsq_inv_rpow]
    ring_nf
    rw [← Real.rpow_add hxpos (1 / 2) (-(2 : ℝ))]
    norm_num
  have hmul' : Real.log x * (x⁻¹ ^ (2 : ℕ)) ≤ 2 * x ^ (-(3 / 2 : ℝ)) := by
    calc
      Real.log x * (x⁻¹ ^ (2 : ℕ))
          ≤ (x ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2)) * (x⁻¹ ^ (2 : ℕ)) := hmul
      _ = 2 * x ^ (-(3 / 2 : ℝ)) := hpow
  have htarget : |Real.log x * (x⁻¹ ^ (2 : ℕ))| ≤
      2 * |x ^ (-(3 / 2 : ℝ))| := by
    have lhs_nonneg : 0 ≤ Real.log x * (x⁻¹ ^ (2 : ℕ)) :=
      mul_nonneg hlog_nonneg hinv_sq_nonneg
    have rhs_nonneg : 0 ≤ x ^ (-(3 / 2 : ℝ)) :=
      (Real.rpow_pos_of_pos hxpos _).le
    rw [abs_of_nonneg lhs_nonneg, abs_of_nonneg rhs_nonneg]
    exact hmul'
  simpa [Real.norm_eq_abs, x] using htarget

/-- The unit-band majorant for the paired far-tail zero contribution. -/
noncomputable def kadiriFarTailUnitBandMajorant (T : ℝ) (n : ℕ) : ℝ :=
  (3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) *
    (u6aNearbyZeroCount (-1) 2 (T + ((n : ℝ) + 3 / 2)) +
      u6aNearbyZeroCount (-1) 2 (T - ((n : ℝ) + 3 / 2)))

private lemma kadiriFarTailUnitBandMajorant_nonneg (T : ℝ) (n : ℕ) :
    0 ≤ kadiriFarTailUnitBandMajorant T n := by
  rw [kadiriFarTailUnitBandMajorant]
  refine mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) ?_
  have hcount_nonneg (u : ℝ) : 0 ≤ u6aNearbyZeroCount (-1) 2 u := by
    rw [u6aNearbyZeroCount,
      riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := Set.uIcc (-1 : ℝ) 2) (J := Set.Icc (u - 1) (u + 1))
        (f := fun _ => (1 : ℝ)) (u6aFTNearbyWindow_finite u)]
    exact Finset.sum_nonneg fun rho hrho => by
      have hmem := (u6aFTNearbyWindow_finite u).mem_toFinset.mp hrho
      exact mul_nonneg zero_le_one (by
        exact_mod_cast riemannZeta_order_nonneg (by
          intro hρ
          exact riemannZeta_one_ne_zero (by simpa [hρ] using hmem.2.2)))
  exact add_nonneg (hcount_nonneg _) (hcount_nonneg _)

private abbrev kadiriFarTailZeroes (T : ℝ) :=
  riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1)
    ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)})

private noncomputable def kadiriFarTailHeightSqTerm (T : ℝ)
    (ρ : kadiriFarTailZeroes T) : ℝ :=
  (3 * |T - (ρ : ℂ).im|⁻¹ ^ (2 : ℕ)) *
    ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ)

private lemma kadiriFarTailHeightSqTerm_nonneg (T : ℝ)
    (ρ : kadiriFarTailZeroes T) :
    0 ≤ kadiriFarTailHeightSqTerm T ρ := by
  rw [kadiriFarTailHeightSqTerm]
  refine mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) ?_
  exact_mod_cast riemannZeta_order_nonneg (by
    intro hρ
    exact riemannZeta_one_ne_zero (by simpa [hρ] using ρ.property.2.2))

private theorem kadiriFarTailHeightSqTerm_summable (T : ℝ) :
    Summable (kadiriFarTailHeightSqTerm T) := by
  refine (kadiri_far_tail_weighted_three_height_sq_summable T).congr ?_
  intro ρ
  rw [kadiriFarTailHeightSqTerm]

private noncomputable def kadiriFarTailBandIndex (T : ℝ)
    (ρ : kadiriFarTailZeroes T) : ℕ × Bool :=
  if T < (ρ : ℂ).im then
    (⌊(ρ : ℂ).im - T - 1⌋₊, true)
  else
    (⌊T - (ρ : ℂ).im - 1⌋₊, false)

private noncomputable def kadiriFarTailSignedBandMajorant (T : ℝ) : ℕ × Bool → ℝ
  | (n, true) =>
      (3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) *
        u6aNearbyZeroCount (-1) 2 (T + ((n : ℝ) + 3 / 2))
  | (n, false) =>
      (3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) *
        u6aNearbyZeroCount (-1) 2 (T - ((n : ℝ) + 3 / 2))

private lemma u6aNearbyZeroCount_neg_one_two_nonneg (u : ℝ) :
    0 ≤ u6aNearbyZeroCount (-1) 2 u := by
  rw [u6aNearbyZeroCount,
    riemannZeta.zeroes_sum_eq_finset_of_finite
      (I := Set.uIcc (-1 : ℝ) 2) (J := Set.Icc (u - 1) (u + 1))
      (f := fun _ => (1 : ℝ)) (u6aFTNearbyWindow_finite u)]
  exact Finset.sum_nonneg fun rho hrho => by
    have hmem := (u6aFTNearbyWindow_finite u).mem_toFinset.mp hrho
    exact mul_nonneg zero_le_one (by
      exact_mod_cast riemannZeta_order_nonneg (by
        intro hρ
        exact riemannZeta_one_ne_zero (by simpa [hρ] using hmem.2.2)))

private lemma kadiriFarTailSignedBandMajorant_nonneg (T : ℝ) (j : ℕ × Bool) :
    0 ≤ kadiriFarTailSignedBandMajorant T j := by
  rcases j with ⟨n, b⟩
  cases b
  · rw [kadiriFarTailSignedBandMajorant]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (u6aNearbyZeroCount_neg_one_two_nonneg _)
  · rw [kadiriFarTailSignedBandMajorant]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (u6aNearbyZeroCount_neg_one_two_nonneg _)

private lemma kadiriFarTailBandIndex_upper_mem {T : ℝ} {ρ : kadiriFarTailZeroes T}
    {n : ℕ} (hidx : kadiriFarTailBandIndex T ρ = (n, true)) :
    (ρ : ℂ) ∈ riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1)
      (.Icc (T + ((n : ℝ) + 1)) (T + ((n : ℝ) + 2))) := by
  unfold kadiriFarTailBandIndex at hidx
  split_ifs at hidx with hupper
  · obtain ⟨hre, hnot, hζ⟩ := ρ.property
    have hn_nat : ⌊(ρ : ℂ).im - T - 1⌋₊ = n := congrArg Prod.fst hidx
    have hn_real : (⌊(ρ : ℂ).im - T - 1⌋₊ : ℝ) = (n : ℝ) := by
      exact_mod_cast hn_nat
    have him_gt : T + 1 < (ρ : ℂ).im := by
      by_contra hle_not
      have hle : (ρ : ℂ).im ≤ T + 1 := le_of_not_gt hle_not
      have hge : T - 1 ≤ (ρ : ℂ).im := by linarith
      exact hnot ⟨hge, hle⟩
    let x : ℝ := (ρ : ℂ).im - T - 1
    have hx_nonneg : 0 ≤ x := by dsimp [x]; linarith
    have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx_nonneg
    have hx_lt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    refine ⟨hre, ?_, hζ⟩
    dsimp [x] at hfloor_le hx_lt
    constructor
    · nlinarith
    · nlinarith
  · simp at hidx

private lemma kadiriFarTailBandIndex_lower_mem {T : ℝ} {ρ : kadiriFarTailZeroes T}
    {n : ℕ} (hidx : kadiriFarTailBandIndex T ρ = (n, false)) :
    (ρ : ℂ) ∈ riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1)
      (.Icc (T - ((n : ℝ) + 2)) (T - ((n : ℝ) + 1))) := by
  unfold kadiriFarTailBandIndex at hidx
  split_ifs at hidx with hupper
  · simp at hidx
  · obtain ⟨hre, hnot, hζ⟩ := ρ.property
    have hn_nat : ⌊T - (ρ : ℂ).im - 1⌋₊ = n := congrArg Prod.fst hidx
    have hn_real : (⌊T - (ρ : ℂ).im - 1⌋₊ : ℝ) = (n : ℝ) := by
      exact_mod_cast hn_nat
    have him_lt : (ρ : ℂ).im < T - 1 := by
      by_contra hlt_not
      have hge : T - 1 ≤ (ρ : ℂ).im := le_of_not_gt hlt_not
      have hle : (ρ : ℂ).im ≤ T + 1 := by linarith [le_of_not_gt hupper]
      exact hnot ⟨hge, hle⟩
    let x : ℝ := T - (ρ : ℂ).im - 1
    have hx_nonneg : 0 ≤ x := by dsimp [x]; linarith
    have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx_nonneg
    have hx_lt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    refine ⟨hre, ?_, hζ⟩
    dsimp [x] at hfloor_le hx_lt
    constructor
    · nlinarith
    · nlinarith

private lemma kadiriFarTailUpperFiberSum_le_signedMajorant
    (T : ℝ) (n : ℕ) (s : Finset (kadiriFarTailZeroes T)) :
    ∑ ρ ∈ s with kadiriFarTailBandIndex T ρ = (n, true),
        kadiriFarTailHeightSqTerm T ρ ≤
      kadiriFarTailSignedBandMajorant T (n, true) := by
  classical
  let fiber : Finset (kadiriFarTailZeroes T) :=
    s.filter fun ρ => kadiriFarTailBandIndex T ρ = (n, true)
  let image : Finset ℂ := fiber.image fun ρ : kadiriFarTailZeroes T => (ρ : ℂ)
  let u : ℝ := T + ((n : ℝ) + 3 / 2)
  let wide : Finset ℂ := (u6aFTNearbyWindow_finite u).toFinset
  let coeff : ℝ := 3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))
  have hterm : ∀ ρ ∈ fiber,
      kadiriFarTailHeightSqTerm T ρ ≤
        coeff * ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) := by
    intro ρ hρ
    have hidx : kadiriFarTailBandIndex T ρ = (n, true) :=
      (Finset.mem_filter.mp hρ).2
    have hmem := kadiriFarTailBandIndex_upper_mem (T := T) (ρ := ρ) hidx
    obtain ⟨_hre, him, _hζ⟩ := hmem
    have hdist : ((n : ℝ) + 1) ≤ |T - (ρ : ℂ).im| := by
      have hnonpos : T - (ρ : ℂ).im ≤ 0 := by nlinarith [him.1]
      rw [abs_of_nonpos hnonpos]
      nlinarith [him.1]
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    have hinv : |T - (ρ : ℂ).im|⁻¹ ≤ ((n : ℝ) + 1)⁻¹ :=
      inv_anti₀ hpos hdist
    have hsquare :
        |T - (ρ : ℂ).im|⁻¹ ^ (2 : ℕ) ≤
          ((n : ℝ) + 1)⁻¹ ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hinv 2
    have hord : 0 ≤ ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) := by
      exact_mod_cast riemannZeta_order_nonneg (by
        intro hρ1
        exact riemannZeta_one_ne_zero (by simpa [hρ1] using ρ.property.2.2))
    rw [kadiriFarTailHeightSqTerm]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsquare (by norm_num)) hord
  have himage_sum :
      ∑ z ∈ image, coeff * ((riemannZeta.order z : ℤ) : ℝ) =
        ∑ ρ ∈ fiber, coeff * ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) := by
    dsimp [image]
    rw [Finset.sum_image]
    intro ρ hρ η hη hρη
    exact Subtype.ext hρη
  have hsubset : image ⊆ wide := by
    intro z hz
    have hz' : z ∈ fiber.image (fun ρ : kadiriFarTailZeroes T => (ρ : ℂ)) := by
      simpa [image] using hz
    rcases Finset.mem_image.mp hz' with ⟨ρ, hρ, rfl⟩
    have hidx : kadiriFarTailBandIndex T ρ = (n, true) :=
      (Finset.mem_filter.mp hρ).2
    have hmem := kadiriFarTailBandIndex_upper_mem (T := T) (ρ := ρ) hidx
    obtain ⟨hre, him, hζ⟩ := hmem
    rw [(u6aFTNearbyWindow_finite u).mem_toFinset]
    unfold u6aFTNearbyWindow riemannZeta.zeroes_rect
    refine ⟨?_, ?_, hζ⟩
    · rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
      exact ⟨by linarith [hre.1], by linarith [hre.2]⟩
    · dsimp [u]
      exact ⟨by linarith [him.1], by linarith [him.2]⟩
  have hwide_nonneg : ∀ z ∈ wide,
      0 ≤ coeff * ((riemannZeta.order z : ℤ) : ℝ) := by
    intro z hz
    have hmem := (u6aFTNearbyWindow_finite u).mem_toFinset.mp (by simpa [wide] using hz)
    exact mul_nonneg (by positivity) (by
      exact_mod_cast riemannZeta_order_nonneg (by
        intro hz1
        exact riemannZeta_one_ne_zero (by simpa [hz1] using hmem.2.2)))
  have hwide_sum :
      u6aNearbyZeroCount (-1) 2 u =
        ∑ z ∈ wide, ((riemannZeta.order z : ℤ) : ℝ) := by
    simpa [u6aNearbyZeroCount, wide, u] using
      riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := Set.uIcc (-1 : ℝ) 2) (J := Set.Icc (u - 1) (u + 1))
        (f := fun _ => (1 : ℝ)) (u6aFTNearbyWindow_finite u)
  calc
    ∑ ρ ∈ s with kadiriFarTailBandIndex T ρ = (n, true),
        kadiriFarTailHeightSqTerm T ρ
        = ∑ ρ ∈ fiber, kadiriFarTailHeightSqTerm T ρ := by
          simp [fiber]
    _ ≤ ∑ ρ ∈ fiber, coeff * ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) :=
        Finset.sum_le_sum hterm
    _ = ∑ z ∈ image, coeff * ((riemannZeta.order z : ℤ) : ℝ) :=
        himage_sum.symm
    _ ≤ ∑ z ∈ wide, coeff * ((riemannZeta.order z : ℤ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun z hz _ => hwide_nonneg z (by simpa [wide] using hz))
    _ = coeff * u6aNearbyZeroCount (-1) 2 u := by
        rw [hwide_sum, Finset.mul_sum]
    _ = kadiriFarTailSignedBandMajorant T (n, true) := rfl

private lemma kadiriFarTailLowerFiberSum_le_signedMajorant
    (T : ℝ) (n : ℕ) (s : Finset (kadiriFarTailZeroes T)) :
    ∑ ρ ∈ s with kadiriFarTailBandIndex T ρ = (n, false),
        kadiriFarTailHeightSqTerm T ρ ≤
      kadiriFarTailSignedBandMajorant T (n, false) := by
  classical
  let fiber : Finset (kadiriFarTailZeroes T) :=
    s.filter fun ρ => kadiriFarTailBandIndex T ρ = (n, false)
  let image : Finset ℂ := fiber.image fun ρ : kadiriFarTailZeroes T => (ρ : ℂ)
  let u : ℝ := T - ((n : ℝ) + 3 / 2)
  let wide : Finset ℂ := (u6aFTNearbyWindow_finite u).toFinset
  let coeff : ℝ := 3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))
  have hterm : ∀ ρ ∈ fiber,
      kadiriFarTailHeightSqTerm T ρ ≤
        coeff * ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) := by
    intro ρ hρ
    have hidx : kadiriFarTailBandIndex T ρ = (n, false) :=
      (Finset.mem_filter.mp hρ).2
    have hmem := kadiriFarTailBandIndex_lower_mem (T := T) (ρ := ρ) hidx
    obtain ⟨_hre, him, _hζ⟩ := hmem
    have hdist : ((n : ℝ) + 1) ≤ |T - (ρ : ℂ).im| := by
      have hnonneg : 0 ≤ T - (ρ : ℂ).im := by nlinarith [him.2]
      rw [abs_of_nonneg hnonneg]
      nlinarith [him.2]
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    have hinv : |T - (ρ : ℂ).im|⁻¹ ≤ ((n : ℝ) + 1)⁻¹ :=
      inv_anti₀ hpos hdist
    have hsquare :
        |T - (ρ : ℂ).im|⁻¹ ^ (2 : ℕ) ≤
          ((n : ℝ) + 1)⁻¹ ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hinv 2
    have hord : 0 ≤ ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) := by
      exact_mod_cast riemannZeta_order_nonneg (by
        intro hρ1
        exact riemannZeta_one_ne_zero (by simpa [hρ1] using ρ.property.2.2))
    rw [kadiriFarTailHeightSqTerm]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsquare (by norm_num)) hord
  have himage_sum :
      ∑ z ∈ image, coeff * ((riemannZeta.order z : ℤ) : ℝ) =
        ∑ ρ ∈ fiber, coeff * ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) := by
    dsimp [image]
    rw [Finset.sum_image]
    intro ρ hρ η hη hρη
    exact Subtype.ext hρη
  have hsubset : image ⊆ wide := by
    intro z hz
    have hz' : z ∈ fiber.image (fun ρ : kadiriFarTailZeroes T => (ρ : ℂ)) := by
      simpa [image] using hz
    rcases Finset.mem_image.mp hz' with ⟨ρ, hρ, rfl⟩
    have hidx : kadiriFarTailBandIndex T ρ = (n, false) :=
      (Finset.mem_filter.mp hρ).2
    have hmem := kadiriFarTailBandIndex_lower_mem (T := T) (ρ := ρ) hidx
    obtain ⟨hre, him, hζ⟩ := hmem
    rw [(u6aFTNearbyWindow_finite u).mem_toFinset]
    unfold u6aFTNearbyWindow riemannZeta.zeroes_rect
    refine ⟨?_, ?_, hζ⟩
    · rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
      exact ⟨by linarith [hre.1], by linarith [hre.2]⟩
    · dsimp [u]
      exact ⟨by linarith [him.1], by linarith [him.2]⟩
  have hwide_nonneg : ∀ z ∈ wide,
      0 ≤ coeff * ((riemannZeta.order z : ℤ) : ℝ) := by
    intro z hz
    have hmem := (u6aFTNearbyWindow_finite u).mem_toFinset.mp (by simpa [wide] using hz)
    exact mul_nonneg (by positivity) (by
      exact_mod_cast riemannZeta_order_nonneg (by
        intro hz1
        exact riemannZeta_one_ne_zero (by simpa [hz1] using hmem.2.2)))
  have hwide_sum :
      u6aNearbyZeroCount (-1) 2 u =
        ∑ z ∈ wide, ((riemannZeta.order z : ℤ) : ℝ) := by
    simpa [u6aNearbyZeroCount, wide, u] using
      riemannZeta.zeroes_sum_eq_finset_of_finite
        (I := Set.uIcc (-1 : ℝ) 2) (J := Set.Icc (u - 1) (u + 1))
        (f := fun _ => (1 : ℝ)) (u6aFTNearbyWindow_finite u)
  calc
    ∑ ρ ∈ s with kadiriFarTailBandIndex T ρ = (n, false),
        kadiriFarTailHeightSqTerm T ρ
        = ∑ ρ ∈ fiber, kadiriFarTailHeightSqTerm T ρ := by
          simp [fiber]
    _ ≤ ∑ ρ ∈ fiber, coeff * ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) :=
        Finset.sum_le_sum hterm
    _ = ∑ z ∈ image, coeff * ((riemannZeta.order z : ℤ) : ℝ) :=
        himage_sum.symm
    _ ≤ ∑ z ∈ wide, coeff * ((riemannZeta.order z : ℤ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun z hz _ => hwide_nonneg z (by simpa [wide] using hz))
    _ = coeff * u6aNearbyZeroCount (-1) 2 u := by
        rw [hwide_sum, Finset.mul_sum]
    _ = kadiriFarTailSignedBandMajorant T (n, false) := rfl

private lemma kadiriFarTailBandFiberSum_le_signedMajorant
    (T : ℝ) (s : Finset (kadiriFarTailZeroes T)) (j : ℕ × Bool) :
    ∑ ρ ∈ s with kadiriFarTailBandIndex T ρ = j,
        kadiriFarTailHeightSqTerm T ρ ≤
      kadiriFarTailSignedBandMajorant T j := by
  rcases j with ⟨n, b⟩
  cases b
  · simpa using kadiriFarTailLowerFiberSum_le_signedMajorant T n s
  · simpa using kadiriFarTailUpperFiberSum_le_signedMajorant T n s

private lemma kadiriFarTailSignedBandMajorant_sum_le_unitBandMajorant_sum
    (T : ℝ) (keys : Finset (ℕ × Bool)) :
    ∑ j ∈ keys, kadiriFarTailSignedBandMajorant T j ≤
      ∑ n ∈ keys.image Prod.fst, kadiriFarTailUnitBandMajorant T n := by
  classical
  let ns : Finset ℕ := keys.image Prod.fst
  have hmaps : ∀ j ∈ keys, Prod.fst j ∈ ns := by
    intro j hj
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to (s := keys) (t := ns)
      (g := Prod.fst) hmaps (kadiriFarTailSignedBandMajorant T)
  have hper_n : ∀ n ∈ ns,
      ∑ j ∈ keys with Prod.fst j = n, kadiriFarTailSignedBandMajorant T j ≤
        kadiriFarTailUnitBandMajorant T n := by
    intro n hn
    let pairs : Finset (ℕ × Bool) := {(n, true), (n, false)}
    have hsubset : (keys.filter fun j => Prod.fst j = n) ⊆ pairs := by
      intro j hj
      have hjn : Prod.fst j = n := (Finset.mem_filter.mp hj).2
      rcases j with ⟨m, b⟩
      have hm : m = n := by simpa using hjn
      cases b <;> simp [pairs, hm]
    have hpair_sum :
        ∑ j ∈ pairs, kadiriFarTailSignedBandMajorant T j =
          kadiriFarTailUnitBandMajorant T n := by
      simp [pairs, kadiriFarTailSignedBandMajorant,
        kadiriFarTailUnitBandMajorant, mul_add]
    calc
      ∑ j ∈ keys with Prod.fst j = n, kadiriFarTailSignedBandMajorant T j
          ≤ ∑ j ∈ pairs, kadiriFarTailSignedBandMajorant T j :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubset
              (fun j hj _ => kadiriFarTailSignedBandMajorant_nonneg T j)
      _ = kadiriFarTailUnitBandMajorant T n := hpair_sum
  calc
    ∑ j ∈ keys, kadiriFarTailSignedBandMajorant T j
        = ∑ n ∈ ns,
            ∑ j ∈ keys with Prod.fst j = n, kadiriFarTailSignedBandMajorant T j :=
          hfiber.symm
    _ ≤ ∑ n ∈ ns, kadiriFarTailUnitBandMajorant T n :=
        Finset.sum_le_sum hper_n
    _ = ∑ n ∈ keys.image Prod.fst, kadiriFarTailUnitBandMajorant T n := rfl

private theorem kadiriFarTailFiniteHeightSqTermSum_le_unitBandMajorant_tsum
    (T : ℝ) (hmajorant_sum : Summable (fun n : ℕ => kadiriFarTailUnitBandMajorant T n))
    (s : Finset (kadiriFarTailZeroes T)) :
    ∑ ρ ∈ s, kadiriFarTailHeightSqTerm T ρ ≤
      ∑' n : ℕ, kadiriFarTailUnitBandMajorant T n := by
  classical
  let keys : Finset (ℕ × Bool) := s.image (kadiriFarTailBandIndex T)
  have hmaps : ∀ ρ ∈ s, kadiriFarTailBandIndex T ρ ∈ keys := by
    intro ρ hρ
    exact Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to (s := s) (t := keys)
      (g := kadiriFarTailBandIndex T) hmaps (kadiriFarTailHeightSqTerm T)
  calc
    ∑ ρ ∈ s, kadiriFarTailHeightSqTerm T ρ
        = ∑ j ∈ keys,
            ∑ ρ ∈ s with kadiriFarTailBandIndex T ρ = j,
              kadiriFarTailHeightSqTerm T ρ := hfiber.symm
    _ ≤ ∑ j ∈ keys, kadiriFarTailSignedBandMajorant T j :=
        Finset.sum_le_sum fun j _ =>
          kadiriFarTailBandFiberSum_le_signedMajorant T s j
    _ ≤ ∑ n ∈ keys.image Prod.fst, kadiriFarTailUnitBandMajorant T n :=
        kadiriFarTailSignedBandMajorant_sum_le_unitBandMajorant_sum T keys
    _ ≤ ∑' n : ℕ, kadiriFarTailUnitBandMajorant T n :=
        Summable.sum_le_tsum (s := keys.image Prod.fst)
          (f := fun n : ℕ => kadiriFarTailUnitBandMajorant T n)
          (fun n _ => kadiriFarTailUnitBandMajorant_nonneg T n) hmajorant_sum

/--
Every finite partial square-height far-tail sum is controlled by the concrete
upper/lower floor-band majorant.
-/
theorem kadiriFarTailFiniteHeightSqSum_le_unitBandMajorant_tsum
    (T : ℝ) (hmajorant_sum : Summable (fun n : ℕ => kadiriFarTailUnitBandMajorant T n))
    (s : Finset (riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1)
      ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)}))) :
    ∑ ρ ∈ s,
        (3 * |T - (ρ : ℂ).im|⁻¹ ^ (2 : ℕ)) *
          ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) ≤
      ∑' n : ℕ, kadiriFarTailUnitBandMajorant T n := by
  simpa [kadiriFarTailZeroes, kadiriFarTailHeightSqTerm] using
    kadiriFarTailFiniteHeightSqTermSum_le_unitBandMajorant_tsum T hmajorant_sum s

/--
The regrouped square-height far tail is bounded by the concrete unit-band
majorant. The proof passes finite partial sums through
`Finset.sum_fiberwise_of_maps_to` and then through
`Summable.tsum_le_of_sum_le`.
-/
theorem kadiri_far_tail_weighted_three_height_sq_tsum_le_unitBandMajorant_tsum
    (T : ℝ) (hmajorant_sum : Summable (fun n : ℕ => kadiriFarTailUnitBandMajorant T n)) :
    riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1)
        ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)})
        (fun ρ => 3 * |T - ρ.im|⁻¹ ^ (2 : ℕ)) ≤
      ∑' n : ℕ, kadiriFarTailUnitBandMajorant T n := by
  have hfinite : ∀ s : Finset (kadiriFarTailZeroes T),
      ∑ ρ ∈ s, kadiriFarTailHeightSqTerm T ρ ≤
        ∑' n : ℕ, kadiriFarTailUnitBandMajorant T n :=
    kadiriFarTailFiniteHeightSqTermSum_le_unitBandMajorant_tsum T hmajorant_sum
  have htsum :=
    Summable.tsum_le_of_sum_le (kadiriFarTailHeightSqTerm_summable T) hfinite
  unfold riemannZeta.zeroes_sum
  simpa [kadiriFarTailZeroes, kadiriFarTailHeightSqTerm] using htsum

/--
The paired far-tail Hadamard zero contribution is controlled by the concrete
unit-band majorant.
-/
theorem kadiri_far_tail_paired_zeroes_sum_norm_le_unitBandMajorant_tsum
    (T σ : ℝ) (hσ : σ ∈ Set.uIcc (-1 : ℝ) 2)
    (hmajorant_sum : Summable (fun n : ℕ => kadiriFarTailUnitBandMajorant T n)) :
    ‖riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1)
        ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)})
        (fun ρ => (1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - ρ) -
          (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ))‖ ≤
      ∑' n : ℕ, kadiriFarTailUnitBandMajorant T n := by
  calc
    ‖riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1)
        ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)})
        (fun ρ => (1 : ℂ) / (((σ : ℂ) + (T : ℂ) * I) - ρ) -
          (1 : ℂ) / (((2 : ℂ) + (T : ℂ) * I) - ρ))‖
        ≤ riemannZeta.zeroes_sum (.Ioo (0 : ℝ) 1)
          ({u : ℝ | u ∉ Set.Icc (T - 1) (T + 1)})
          (fun ρ => 3 * |T - ρ.im|⁻¹ ^ (2 : ℕ)) :=
          kadiri_far_tail_paired_zeroes_sum_norm_le_height_sq_tail T σ hσ
    _ ≤ ∑' n : ℕ, kadiriFarTailUnitBandMajorant T n :=
        kadiri_far_tail_weighted_three_height_sq_tsum_le_unitBandMajorant_tsum
          T hmajorant_sum

private lemma log_abs_shift_add_two_le_log_band_product {T : ℝ} (hTnonneg : 0 ≤ T)
    (hT4 : 4 ≤ T) (n : ℕ) (sgn : Bool) :
    Real.log (|T + (if sgn then 1 else -1) * ((n : ℝ) + 3 / 2)| + 2) ≤
      Real.log (T + 4) + Real.log ((n : ℝ) + 1) := by
  let a : ℝ := (n : ℝ) + 3 / 2
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hn1_pos : 0 < (n : ℝ) + 1 := by positivity
  have hT4_pos : 0 < T + 4 := by linarith
  have hleft_pos :
      0 < |T + (if sgn then 1 else -1) * a| + 2 := by
    linarith [abs_nonneg (T + (if sgn then 1 else -1) * a)]
  have hgeom :
      |T + (if sgn then 1 else -1) * a| + 2 ≤ (T + 4) * ((n : ℝ) + 1) := by
    cases sgn
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show T + -1 * a = T - a by ring]
      have habs : |T - a| ≤ T + a := by
        rw [abs_le]
        constructor <;> linarith
      have hstep : |T - a| + 2 ≤ T + a + 2 := by linarith
      have hstep' : T + a + 2 ≤ (T + 4) * ((n : ℝ) + 1) := by
        dsimp [a]
        nlinarith [Nat.cast_nonneg (α := ℝ) n, hTnonneg,
          mul_nonneg hTnonneg (Nat.cast_nonneg (α := ℝ) n)]
      exact hstep.trans hstep'
    · simp only [↓reduceIte, one_mul]
      have hsum_nonneg : 0 ≤ T + a := by linarith
      rw [abs_of_nonneg hsum_nonneg]
      dsimp [a]
      nlinarith [Nat.cast_nonneg (α := ℝ) n, hTnonneg,
        mul_nonneg hTnonneg (Nat.cast_nonneg (α := ℝ) n)]
  calc
    Real.log (|T + (if sgn then 1 else -1) * ((n : ℝ) + 3 / 2)| + 2)
        ≤ Real.log ((T + 4) * ((n : ℝ) + 1)) :=
          Real.log_le_log hleft_pos hgeom
    _ = Real.log (T + 4) + Real.log ((n : ℝ) + 1) := by
          rw [Real.log_mul (ne_of_gt hT4_pos) (ne_of_gt hn1_pos)]

/--
The inverse-square unit-band majorant built from the concrete U6a local counts is
eventually `O(log T)`.
-/
theorem exists_kadiriFarTailUnitBandMajorant_tsum_le_log :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ T : ℝ in Filter.atTop,
      (∑' n : ℕ, kadiriFarTailUnitBandMajorant T n) ≤ R * Real.log T := by
  obtain ⟨C, hC_nonneg, hcount⟩ := exists_u6aNearbyZeroCount_le_log_abs_add_one
  let A : ℕ → ℝ := fun n => (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))
  let L : ℕ → ℝ := fun n => Real.log ((n : ℝ) + 1) * A n
  let A0 : ℝ := ∑' n : ℕ, A n
  let L0 : ℝ := ∑' n : ℕ, L n
  let R : ℝ := 6 * C * (3 * A0 + L0)
  have hA_sum : Summable A := by
    simpa [A] using summable_nat_add_one_inv_sq
  have hL_sum : Summable L := by
    simpa [L, A] using summable_log_nat_add_one_mul_inv_sq
  have hA0_nonneg : 0 ≤ A0 := by
    dsimp [A0, A]
    exact tsum_nonneg fun n => sq_nonneg _
  have hL0_nonneg : 0 ≤ L0 := by
    dsimp [L0, L, A]
    exact tsum_nonneg fun n =>
      mul_nonneg
        (Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) n]))
        (sq_nonneg _)
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    nlinarith [hC_nonneg, hA0_nonneg, hL0_nonneg]
  refine ⟨R, hR_nonneg, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (max 4 (Real.exp 1))] with T hT
  have hT4 : (4 : ℝ) ≤ T := (le_max_left 4 (Real.exp 1)).trans hT
  have hTexp : Real.exp 1 ≤ T := (le_max_right 4 (Real.exp 1)).trans hT
  have hTpos : 0 < T := (Real.exp_pos 1).trans_le hTexp
  have hTnonneg : 0 ≤ T := hTpos.le
  have hlogT_one : 1 ≤ Real.log T :=
    (Real.le_log_iff_exp_le hTpos).mpr hTexp
  have hlogT_nonneg : 0 ≤ Real.log T := by linarith
  let B : ℕ → ℝ := fun n =>
    6 * C * (((Real.log (T + 4) + 1) * A n) + L n)
  have hB_sum : Summable B := by
    have hA_scaled : Summable (fun n : ℕ => (Real.log (T + 4) + 1) * A n) :=
      hA_sum.mul_left (Real.log (T + 4) + 1)
    exact (hA_scaled.add hL_sum).mul_left (6 * C)
  have hmajorant_le_B : ∀ n : ℕ, kadiriFarTailUnitBandMajorant T n ≤ B n := by
    intro n
    let bandLog : ℝ := Real.log (T + 4) + Real.log ((n : ℝ) + 1) + 1
    have hbandLog_nonneg : 0 ≤ bandLog := by
      dsimp [bandLog]
      have hlogT4_nonneg : 0 ≤ Real.log (T + 4) :=
        Real.log_nonneg (by linarith)
      have hlogn_nonneg : 0 ≤ Real.log ((n : ℝ) + 1) :=
        Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
      linarith
    have hcount_le (sgn : Bool) :
        u6aNearbyZeroCount (-1) 2
            (T + (if sgn then 1 else -1) * ((n : ℝ) + 3 / 2)) ≤
          C * bandLog := by
      have hraw :=
        hcount (T + (if sgn then 1 else -1) * ((n : ℝ) + 3 / 2))
      have hlog_le :
          Real.log (|T + (if sgn then 1 else -1) * ((n : ℝ) + 3 / 2)| + 2) + 1
            ≤ bandLog := by
        dsimp [bandLog]
        linarith [log_abs_shift_add_two_le_log_band_product hTnonneg hT4 n sgn]
      exact hraw.trans (mul_le_mul_of_nonneg_left hlog_le hC_nonneg)
    have hcounts :
        u6aNearbyZeroCount (-1) 2 (T + ((n : ℝ) + 3 / 2)) +
            u6aNearbyZeroCount (-1) 2 (T - ((n : ℝ) + 3 / 2)) ≤
          2 * C * bandLog := by
      have hupper : u6aNearbyZeroCount (-1) 2 (T + ((n : ℝ) + 3 / 2)) ≤
          C * bandLog := by
        simpa using hcount_le true
      have hlower : u6aNearbyZeroCount (-1) 2 (T - ((n : ℝ) + 3 / 2)) ≤
          C * bandLog := by
        have harg :
            T + (-(3 / 2) + -(n : ℝ)) =
              T - ((n : ℝ) + 3 / 2) := by
          ring
        simpa [harg] using hcount_le false
      calc
        u6aNearbyZeroCount (-1) 2 (T + ((n : ℝ) + 3 / 2)) +
            u6aNearbyZeroCount (-1) 2 (T - ((n : ℝ) + 3 / 2))
            ≤ C * bandLog + C * bandLog := add_le_add hupper hlower
        _ = 2 * C * bandLog := by ring
    have hA_nonneg : 0 ≤ A n := by
      dsimp [A]
      exact sq_nonneg _
    rw [kadiriFarTailUnitBandMajorant]
    dsimp [B, A, L, bandLog]
    calc
      (3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) *
          (u6aNearbyZeroCount (-1) 2 (T + ((n : ℝ) + 3 / 2)) +
            u6aNearbyZeroCount (-1) 2 (T - ((n : ℝ) + 3 / 2)))
          ≤ (3 * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) *
              (2 * C * (Real.log (T + 4) + Real.log ((n : ℝ) + 1) + 1)) := by
            exact mul_le_mul_of_nonneg_left hcounts
              (mul_nonneg (by norm_num) hA_nonneg)
      _ = 6 * C *
            (((Real.log (T + 4) + 1) * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) +
              Real.log ((n : ℝ) + 1) * (((n : ℝ) + 1)⁻¹ ^ (2 : ℕ))) := by
            ring
  have hmajorant_sum : Summable (fun n : ℕ => kadiriFarTailUnitBandMajorant T n) :=
    Summable.of_nonneg_of_le
      (fun n => kadiriFarTailUnitBandMajorant_nonneg T n) hmajorant_le_B hB_sum
  have htsum_le_B :
      (∑' n : ℕ, kadiriFarTailUnitBandMajorant T n) ≤ ∑' n : ℕ, B n :=
    Summable.tsum_le_tsum hmajorant_le_B hmajorant_sum hB_sum
  have hB_tsum :
      (∑' n : ℕ, B n) =
        6 * C * ((Real.log (T + 4) + 1) * A0 + L0) := by
    rw [show (∑' n : ℕ, B n) =
        ∑' n : ℕ, 6 * C *
          (((Real.log (T + 4) + 1) * A n) + L n) by rfl]
    rw [tsum_mul_left]
    rw [Summable.tsum_add]
    · rw [tsum_mul_left]
    · exact hA_sum.mul_left (Real.log (T + 4) + 1)
    · exact hL_sum
  have hlogT4_le_two_logT : Real.log (T + 4) ≤ 2 * Real.log T := by
    have hT4_pos : 0 < T + 4 := by linarith
    have hT4_le_sq : T + 4 ≤ T ^ (2 : ℕ) := by nlinarith
    calc
      Real.log (T + 4) ≤ Real.log (T ^ (2 : ℕ)) :=
        Real.log_le_log hT4_pos hT4_le_sq
      _ = 2 * Real.log T := by
        rw [Real.log_pow]
        norm_num
  have hlogT4_add_one_le : Real.log (T + 4) + 1 ≤ 3 * Real.log T := by
    linarith
  have hinner :
      (Real.log (T + 4) + 1) * A0 + L0 ≤
        (3 * A0 + L0) * Real.log T := by
    calc
      (Real.log (T + 4) + 1) * A0 + L0
          ≤ (3 * Real.log T) * A0 + L0 * Real.log T := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hlogT4_add_one_le hA0_nonneg)
              (by nlinarith [hL0_nonneg, hlogT_one])
      _ = (3 * A0 + L0) * Real.log T := by ring
  calc
    (∑' n : ℕ, kadiriFarTailUnitBandMajorant T n)
        ≤ ∑' n : ℕ, B n := htsum_le_B
    _ = 6 * C * ((Real.log (T + 4) + 1) * A0 + L0) := hB_tsum
    _ ≤ 6 * C * ((3 * A0 + L0) * Real.log T) :=
        mul_le_mul_of_nonneg_left hinner (mul_nonneg (by norm_num) hC_nonneg)
    _ = R * Real.log T := by
        dsimp [R]
        ring

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
