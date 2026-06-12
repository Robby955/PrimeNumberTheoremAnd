import PrimeNumberTheoremAnd.IEANTN.Kadiri
import PrimeNumberTheoremAnd.IEANTN.KadiriGoodHeights
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard

noncomputable section

namespace Kadiri

open Complex
open scoped Topology

/-- Candidate replacement for the placeholder `hadamardB` in `Kadiri.lean`.

It is the unique derivative-at-zero constant of a degree-one no-monomial Hadamard
factorization of Riemann's xi function. -/
def xiHadamardB : ℂ :=
  Classical.choose existsUnique_riemannXi_hadamard_polynomial_derivative_eval_zero.exists

/-- The xi-derived Hadamard constant is represented by a degree-one xi Hadamard polynomial. -/
theorem xiHadamardB_spec :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧
      (∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) *
          Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z) ∧
      xiHadamardB = Polynomial.eval 0 P.derivative :=
  Classical.choose_spec existsUnique_riemannXi_hadamard_polynomial_derivative_eval_zero.exists

/-- Logarithmic-derivative form of the xi Hadamard factorization using `xiHadamardB`. -/
theorem xiHadamardB_logDeriv {z : ℂ}
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    logDeriv riemannXi z =
      xiHadamardB +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  rcases xiHadamardB_spec with ⟨P, hdeg, hfac, hB⟩
  rw [logDeriv_riemannXi_eq_polynomial_derivative_add_tsum (P := P) hfac hz]
  have hconst : Polynomial.eval z P.derivative = xiHadamardB := by
    calc
      Polynomial.eval z P.derivative = Polynomial.eval 0 P.derivative :=
        Polynomial.eval_derivative_eq_eval_derivative_zero_of_degree_le_one hdeg z
      _ = xiHadamardB := hB.symm
  rw [hconst]

/-- Order-weighted global reindex from xi divisor indices to `riemannZeta.zeroes_sum`:
any summable function of the divisor value tsums to the order-weighted zero sum over the
critical strip.  Each fiber of the divisor index over a non-trivial zero is finite with
cardinality `riemannZeta.order`, and the divisor values are exactly the non-trivial zeros,
so the sigma decomposition collapses fiberwise to the weighted sum. -/
theorem tsum_riemannXi_divisorZeroIndex₀_eq_zeroes_sum {α : Type*} [RCLike α] (φ : ℂ → α)
    (hsum : Summable fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) ↦
      φ (Complex.Hadamard.divisorZeroIndex₀_val p)) :
    ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        φ (Complex.Hadamard.divisorZeroIndex₀_val p) =
      riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) φ := by
  classical
  let e := u6aRiemannXi_divisorZeroIndex₀_equiv_nontrivialZeroSigma
  let g : (Σ ρ : NontrivialZeros, Fin (Int.toNat (riemannZeta.order (ρ : ℂ)))) → α :=
    fun q ↦ φ (q.1 : ℂ)
  have hgsum : Summable g := by
    refine e.summable_iff.mp ?_
    exact hsum
  have h1 : (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      φ (Complex.Hadamard.divisorZeroIndex₀_val p)) = ∑' q, g q := e.tsum_eq g
  have h3 : ∀ ρ : NontrivialZeros,
      (∑' _k : Fin (Int.toNat (riemannZeta.order (ρ : ℂ))), φ (ρ : ℂ)) =
        φ (ρ : ℂ) * (riemannZeta.order (ρ : ℂ) : α) := by
    intro ρ
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_comm]
    congr 1
    have h0 : (0 : ℤ) ≤ riemannZeta.order (ρ : ℂ) :=
      le_of_lt (riemannZeta_order_pos_nontrivialZero ρ)
    exact_mod_cast Int.toNat_of_nonneg h0
  rw [h1, hgsum.tsum_sigma]
  unfold riemannZeta.zeroes_sum
  exact tsum_congr h3

/-- Multiplicity-weighted Hadamard expansion of `-ζ'/ζ` on Kadiri's downstream half-plane. -/
theorem hadamard_identity_weighted {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      -xiHadamardB - (1 / 2 : ℂ) * Real.log Real.pi + 1 / (s - 1) +
      (1 / 2 : ℂ) * digamma (s / 2 + 1) -
      riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
        (fun ρ ↦ 1 / ρ + 1 / (s - ρ)) := by
  obtain ⟨P, hdeg, hfac, hB⟩ := xiHadamardB_spec
  have hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p := by
    intro p heq
    have hmem := u6aRiemannXi_divisorZeroIndex₀_val_mem_nontrivialZero p
    have hlt : (Complex.Hadamard.divisorZeroIndex₀_val p).re < 1 := hmem.1.2
    rw [← heq] at hlt
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num [Complex.one_re] at hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num [Complex.zero_re] at hs
  have hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ) := by
    intro m heq
    have hsval : s = -(m : ℂ) * 2 - 2 := by linear_combination 2 * heq
    have hcast : s = ((-(m : ℝ) * 2 - 2 : ℝ) : ℂ) := by rw [hsval]; push_cast; ring
    have hre : s.re = -(m : ℝ) * 2 - 2 := by rw [hcast, Complex.ofReal_re]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hΓ : zetaGammaFactor s ≠ 0 := by
    unfold zetaGammaFactor
    exact Complex.Gamma_ne_zero hΓdiff
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hmain := neg_zeta_logDeriv_eq_of_riemannXi_hadamard (P := P) (s := s)
    hfac hz hs0 hs1 hΓdiff hΓ hζ
  have hconst : Polynomial.eval s P.derivative = xiHadamardB := by
    calc
      Polynomial.eval s P.derivative = Polynomial.eval 0 P.derivative :=
        Polynomial.eval_derivative_eq_eval_derivative_zero_of_degree_le_one hdeg s
      _ = xiHadamardB := hB.symm
  have hsumm := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ hz
  have hsumm' : Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) ↦
        1 / Complex.Hadamard.divisorZeroIndex₀_val p +
          1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p)) :=
    hsumm.congr fun p ↦ add_comm _ _
  have hswap : (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p)) =
      ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / Complex.Hadamard.divisorZeroIndex₀_val p +
          1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p)) :=
    tsum_congr fun p ↦ add_comm _ _
  have hreidx : (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / Complex.Hadamard.divisorZeroIndex₀_val p +
          1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p))) =
      riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
        (fun ρ ↦ 1 / ρ + 1 / (s - ρ)) :=
    tsum_riemannXi_divisorZeroIndex₀_eq_zeroes_sum (fun ρ ↦ 1 / ρ + 1 / (s - ρ)) hsumm'
  rw [hmain, hconst, hswap, hreidx]
  ring

/-- Reflecting the argument through `w ↦ 1 - w` transports the analytic vanishing order. -/
private lemma analyticOrderAt_comp_one_sub {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f (1 - z₀)) :
    analyticOrderAt (fun w ↦ f (1 - w)) z₀ = analyticOrderAt f (1 - z₀) := by
  have hinner : AnalyticAt ℂ (fun w : ℂ ↦ 1 - w) z₀ := analyticAt_const.sub analyticAt_id
  have hcomp : AnalyticAt ℂ (fun w ↦ f (1 - w)) z₀ := hf.comp hinner
  have hc : Filter.Tendsto (fun w : ℂ ↦ 1 - w) (nhds z₀) (nhds (1 - z₀)) :=
    (continuous_const.sub continuous_id).tendsto z₀
  cases h : analyticOrderAt f (1 - z₀) with
  | top =>
      rw [analyticOrderAt_eq_top] at h ⊢
      filter_upwards [hc.eventually h] with w hw
      exact hw
  | coe n =>
      rw [hf.analyticOrderAt_eq_natCast] at h
      obtain ⟨g, hg, hg0, hfg⟩ := h
      rw [hcomp.analyticOrderAt_eq_natCast]
      refine ⟨fun w ↦ (-1 : ℂ) ^ n * g (1 - w),
        analyticAt_const.mul (hg.comp hinner), ?_, ?_⟩
      · exact mul_ne_zero (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)) hg0
      · filter_upwards [hc.eventually hfg] with w hw
        show f (1 - w) = (w - z₀) ^ n • ((-1 : ℂ) ^ n * g (1 - w))
        rw [hw, smul_eq_mul, smul_eq_mul,
          show (1 - w) - (1 - z₀) = -(w - z₀) by ring, neg_pow]
        ring

/-- The analytic vanishing order of Riemann's xi is symmetric under `s ↦ 1 - s`. -/
private lemma riemannXi_analyticOrderAt_one_sub (z : ℂ) :
    analyticOrderAt riemannXi (1 - z) = analyticOrderAt riemannXi z := by
  have h := analyticOrderAt_comp_one_sub (f := riemannXi) (z₀ := z)
    (Differentiable.analyticAt differentiable_riemannXi (1 - z))
  rw [show (fun w : ℂ ↦ riemannXi (1 - w)) = riemannXi from funext riemannXi_one_sub] at h
  exact h.symm

/-- Inside the critical strip the zeta zero order is symmetric under `s ↦ 1 - s`.
This is the order-preservation half of the `ρ ↦ 1 - ρ` reindex used for `Re B`. -/
theorem riemannZeta_order_one_sub_of_strip {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    riemannZeta.order (1 - ρ) = riemannZeta.order ρ := by
  have hre : ((1 : ℂ) - ρ).re = 1 - ρ.re := by
    simp [Complex.sub_re, Complex.one_re]
  have h0' : 0 < ((1 : ℂ) - ρ).re := by rw [hre]; linarith
  have h1' : ((1 : ℂ) - ρ).re < 1 := by rw [hre]; linarith
  rw [← u6aRiemannXi_divisor_eq_riemannZeta_order_of_criticalStrip h0' h1',
    ← u6aRiemannXi_divisor_eq_riemannZeta_order_of_criticalStrip h0 h1]
  have hmero : MeromorphicOn riemannXi Set.univ := fun x _ ↦
    (Differentiable.analyticAt differentiable_riemannXi x).meromorphicAt
  rw [MeromorphicOn.divisor_apply hmero (Set.mem_univ _),
    MeromorphicOn.divisor_apply hmero (Set.mem_univ _),
    (Differentiable.analyticAt differentiable_riemannXi ((1 : ℂ) - ρ)).meromorphicOrderAt_eq,
    (Differentiable.analyticAt differentiable_riemannXi ρ).meromorphicOrderAt_eq,
    riemannXi_analyticOrderAt_one_sub ρ]

/-- The non-trivial zero set is closed under the reflection `ρ ↦ 1 - ρ`. -/
theorem one_sub_mem_nontrivialZeros (ρ : NontrivialZeros) :
    (1 : ℂ) - (ρ : ℂ) ∈ NontrivialZeros := by
  have h0 : 0 < (ρ : ℂ).re := ρ.property.1.1
  have h1 : (ρ : ℂ).re < 1 := ρ.property.1.2
  have hre : ((1 : ℂ) - (ρ : ℂ)).re = 1 - (ρ : ℂ).re := by
    simp [Complex.sub_re, Complex.one_re]
  have horder : riemannZeta.order ((1 : ℂ) - (ρ : ℂ)) = riemannZeta.order (ρ : ℂ) :=
    riemannZeta_order_one_sub_of_strip h0 h1
  have hpos : 0 < riemannZeta.order (ρ : ℂ) := riemannZeta_order_pos_nontrivialZero ρ
  refine ⟨⟨?_, ?_⟩, Set.mem_univ _, ?_⟩
  · rw [hre]; linarith
  · rw [hre]; linarith
  · show riemannZeta ((1 : ℂ) - (ρ : ℂ)) = 0
    by_contra hne
    have hne1 : (1 : ℂ) - (ρ : ℂ) ≠ 1 := by
      intro hone
      have hzero : (ρ : ℂ) = 0 := sub_eq_self.mp hone
      rw [hzero] at h0
      simp at h0
    have han : AnalyticAt ℂ riemannZeta ((1 : ℂ) - (ρ : ℂ)) :=
      riemannZeta_analyticOn_compl_one _ (Set.mem_compl_singleton_iff.mpr hne1)
    have hzero_order : riemannZeta.order ((1 : ℂ) - (ρ : ℂ)) = 0 := by
      unfold riemannZeta.order
      rw [han.meromorphicOrderAt_eq]
      have h := analyticOrderAt_eq_zero.mpr (Or.inr hne)
      simp [h]
    rw [horder] at hzero_order
    omega

/-- Reflection `ρ ↦ 1 - ρ` as an involution of the non-trivial zero set. -/
noncomputable def nontrivialZerosReflection : NontrivialZeros ≃ NontrivialZeros where
  toFun ρ := ⟨(1 : ℂ) - (ρ : ℂ), one_sub_mem_nontrivialZeros ρ⟩
  invFun ρ := ⟨(1 : ℂ) - (ρ : ℂ), one_sub_mem_nontrivialZeros ρ⟩
  left_inv ρ := Subtype.ext (by ring)
  right_inv ρ := Subtype.ext (by ring)

/-- The order-weighted zero sum over the critical strip is invariant under
precomposition with the reflection `ρ ↦ 1 - ρ`. -/
theorem zeroes_sum_comp_one_sub {α : Type*} [RCLike α] (f : ℂ → α) :
    riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) (fun ρ ↦ f (1 - ρ)) =
      riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) f := by
  calc riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) (fun ρ ↦ f (1 - ρ))
      = ∑' ρ : NontrivialZeros,
          (fun σ : NontrivialZeros ↦ f (σ : ℂ) * (riemannZeta.order (σ : ℂ) : α))
            (nontrivialZerosReflection ρ) := by
        unfold riemannZeta.zeroes_sum
        refine tsum_congr fun ρ ↦ ?_
        show f (1 - (ρ : ℂ)) * (riemannZeta.order ((ρ : ℂ)) : α) =
          f (1 - (ρ : ℂ)) * (riemannZeta.order ((1 : ℂ) - (ρ : ℂ)) : α)
        rw [riemannZeta_order_one_sub_of_strip ρ.property.1.1 ρ.property.1.2]
    _ = ∑' σ : NontrivialZeros, f (σ : ℂ) * (riemannZeta.order (σ : ℂ) : α) :=
        nontrivialZerosReflection.tsum_eq
          (fun σ : NontrivialZeros ↦ f (σ : ℂ) * (riemannZeta.order (σ : ℂ) : α))
    _ = riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) f := rfl

/-- Multiplicity-weighted real-part identity for the xi-derived Hadamard constant. -/
theorem re_hadamardB_weighted_eq :
    xiHadamardB.re =
      -riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
        (fun ρ ↦ (1 / ρ).re) := by
  have hz0 : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      (0 : ℂ) ≠ Complex.Hadamard.divisorZeroIndex₀_val p :=
    fun p ↦ (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p).symm
  have hz1 : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      (1 : ℂ) ≠ Complex.Hadamard.divisorZeroIndex₀_val p := by
    intro p heq
    have hmem := u6aRiemannXi_divisorZeroIndex₀_val_mem_nontrivialZero p
    have hlt : (Complex.Hadamard.divisorZeroIndex₀_val p).re < 1 := hmem.1.2
    rw [← heq] at hlt
    norm_num [Complex.one_re] at hlt
  -- `logDeriv ξ 0 = B`: the genus-one kernel vanishes termwise at the origin.
  have hA : logDeriv riemannXi 0 = xiHadamardB := by
    rw [xiHadamardB_logDeriv hz0]
    have hzero : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / ((0 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) = 0 := by
      intro p
      rw [zero_sub, div_neg]
      exact neg_add_cancel _
    rw [tsum_congr hzero, tsum_zero, add_zero]
  -- `logDeriv ξ 1 = B + S` with `S` the kernel sum at `z = 1`.
  have hB1 : logDeriv riemannXi 1 = xiHadamardB +
      ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / ((1 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) :=
    xiHadamardB_logDeriv hz1
  -- functional-equation antisymmetry of `logDeriv ξ` between `0` and `1`
  have hd01 : deriv riemannXi 0 = -deriv riemannXi 1 := by
    have hinner : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
    have houter : HasDerivAt riemannXi (deriv riemannXi (1 - (0 : ℂ))) (1 - (0 : ℂ)) :=
      (differentiable_riemannXi (1 - (0 : ℂ))).hasDerivAt
    have hcomp : HasDerivAt (fun w : ℂ ↦ riemannXi (1 - w))
        (deriv riemannXi (1 - (0 : ℂ)) * (-1)) 0 := houter.comp 0 hinner
    rw [show (fun w : ℂ ↦ riemannXi (1 - w)) = riemannXi from funext riemannXi_one_sub]
      at hcomp
    rw [hcomp.deriv]
    norm_num
  have hx01 : riemannXi 0 = riemannXi 1 := by
    have h := riemannXi_one_sub 0
    rw [sub_zero] at h
    exact h.symm
  have hC : logDeriv riemannXi 0 = -logDeriv riemannXi 1 := by
    rw [logDeriv_apply, logDeriv_apply, hd01, hx01, neg_div]
  -- `2B = -S`
  have hD : xiHadamardB + xiHadamardB =
      -∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / ((1 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
    have h := hC
    rw [hA, hB1] at h
    linear_combination h
  -- pass to real parts
  have hKsum : Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) ↦
        1 / ((1 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) :=
    summable_riemannXi_logDerivTerms_divisorZeroIndex₀ hz1
  have hDre : xiHadamardB.re + xiHadamardB.re =
      -∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / ((1 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p).re := by
    have h := congrArg Complex.re hD
    rw [Complex.add_re, Complex.neg_re, Complex.re_tsum hKsum] at h
    exact h
  -- both kernel halves have nonnegative real parts on the strip
  have hr1nonneg : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      0 ≤ (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re := by
    intro p
    have hmem := u6aRiemannXi_divisorZeroIndex₀_val_mem_nontrivialZero p
    have h0 : 0 < (Complex.Hadamard.divisorZeroIndex₀_val p).re := hmem.1.1
    rw [one_div, Complex.inv_re]
    exact div_nonneg h0.le (Complex.normSq_nonneg _)
  have hr2nonneg : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      0 ≤ (1 / ((1 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p)).re := by
    intro p
    have hmem := u6aRiemannXi_divisorZeroIndex₀_val_mem_nontrivialZero p
    have h1 : (Complex.Hadamard.divisorZeroIndex₀_val p).re < 1 := hmem.1.2
    rw [one_div, Complex.inv_re]
    refine div_nonneg ?_ (Complex.normSq_nonneg _)
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hKreSum : Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) ↦
        (1 / ((1 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p).re) :=
    (Complex.hasSum_re hKsum.hasSum).summable
  have hr2sum : Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) ↦
        (1 / ((1 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p)).re) := by
    refine Summable.of_nonneg_of_le hr2nonneg (fun p ↦ ?_) hKreSum
    rw [Complex.add_re]
    exact le_add_of_nonneg_right (hr1nonneg p)
  have hr1sum : Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) ↦
        (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re) := by
    refine Summable.of_nonneg_of_le hr1nonneg (fun p ↦ ?_) hKreSum
    rw [Complex.add_re]
    exact le_add_of_nonneg_left (hr2nonneg p)
  have hsplit : (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / ((1 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p).re) =
      (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / ((1 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p)).re) +
      ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re := by
    rw [← hr2sum.tsum_add hr1sum]
    exact tsum_congr fun p ↦ Complex.add_re _ _
  -- reindex both halves to order-weighted zero sums
  have hG1 : (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re) =
      riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) (fun ρ ↦ (1 / ρ).re) :=
    tsum_riemannXi_divisorZeroIndex₀_eq_zeroes_sum (fun ρ ↦ (1 / ρ).re) hr1sum
  have hG2 : (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / ((1 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p)).re) =
      riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
        (fun ρ ↦ (1 / ((1 : ℂ) - ρ)).re) :=
    tsum_riemannXi_divisorZeroIndex₀_eq_zeroes_sum
      (fun ρ ↦ (1 / ((1 : ℂ) - ρ)).re) hr2sum
  -- reflection symmetry collapses the reflected half onto the direct one
  have hH : riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
        (fun ρ ↦ (1 / ((1 : ℂ) - ρ)).re) =
      riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) (fun ρ ↦ (1 / ρ).re) :=
    zeroes_sum_comp_one_sub (fun ρ ↦ (1 / ρ).re)
  rw [hsplit, hG2, hG1, hH] at hDre
  linarith

end Kadiri
