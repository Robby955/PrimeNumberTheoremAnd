import PrimeNumberTheoremAnd.IEANTN.Kadiri
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

/-- Multiplicity-weighted Hadamard expansion of `-ζ'/ζ` on Kadiri's downstream half-plane.

The remaining bridge is the order-weighted reindex from xi divisor indices to
`riemannZeta.zeroes_sum`; the U6a fiber-card machinery supplies it when barrel three merges. -/
theorem hadamard_identity_weighted {s : ℂ} (_hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      -xiHadamardB - (1 / 2 : ℂ) * Real.log Real.pi + 1 / (s - 1) +
      (1 / 2 : ℂ) * digamma (s / 2 + 1) -
      riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
        (fun ρ ↦ 1 / ρ + 1 / (s - ρ)) := by
  -- Waiting on the barrel-three xi-divisor-to-zeta-order reindex bridge.
  sorry

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
