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

/-- Multiplicity-weighted real-part identity for the xi-derived Hadamard constant.

The remaining bridge is the same xi-divisor-to-zeta-order reindex/symmetry package used by
`hadamard_identity_weighted`. -/
theorem re_hadamardB_weighted_eq :
    xiHadamardB.re =
      -riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
        (fun ρ ↦ (1 / ρ).re) := by
  -- Waiting on the barrel-three xi-divisor-to-zeta-order reindex bridge.
  sorry

end Kadiri
