import PrimeNumberTheoremAnd.IEANTN.Kadiri
import PrimeNumberTheoremAnd.IEANTN.KadiriGoodHeights
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard

/-!
# Multiplicity-weighted Hadamard identities for the Kadiri zero-free region

`Kadiri.lean` states the Hadamard expansion of `-ζ'/ζ` (`hadamard_identity`) and the real-part
identity for the Hadamard constant (`re_hadamardB_eq`) as plain `tsum`s over the zero set
`riemannZeta.zeroes_rect (.Ioo 0 1) .univ`, with each zero appearing once regardless of its
order, and with a sorried placeholder constant `hadamardB`. The Hadamard product itself repeats
each zero according to its multiplicity, so those statements agree with the product only if
every non-trivial zero is simple, which is not known.

This file proves the multiplicity-corrected forms. The constant `xiHadamardB` is extracted from
the xi Hadamard factorization of `RiemannZetaHadamard.lean`, and `hadamard_identity_weighted`
and `re_hadamardB_weighted_eq` restate the two sorried lemmas with the order-weighted sum
`riemannZeta.zeroes_sum` in place of the plain `tsum`s. The names mirror the originals so that
the eventual replacement diff in `Kadiri.lean` stays readable.

The reflection section in the middle proves the zero-symmetry input: `ρ ↦ 1 - ρ`, induced by
the functional equation `riemannXi_one_sub`, is an involution of the non-trivial zero set that
preserves `riemannZeta.order` and hence leaves the weighted sums invariant
(`zeroes_sum_comp_one_sub`).

## Conventions

* Zero sums are `riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)` (`ZetaDefinitions.lean`):
  a `tsum` over the subtype of zeros in the window `re ∈ Ioo 0 1`, `im ∈ univ`, with each term
  multiplied by `riemannZeta.order ρ`. As a `tsum` it takes the junk value `0` when the family
  is not summable. The window is exactly `NontrivialZeros`, and it captures every zero of
  `riemannXi` (`u6aRiemannXi_divisorZeroIndex₀_val_mem_nontrivialZero`), so nothing is lost in
  passing from the global xi divisor to this window.
* The zero kernel is the convergence-paired `1/ρ + 1/(s - ρ)`, as in Kadiri's source equation;
  the two halves are not separately summable.
* The gamma term is spelled `digamma (s/2 + 1)`, that is `Γ'/Γ(s/2 + 1)`, matching the gamma
  factor `Γ(s/2 + 1)` of `zetaGammaFactor`; expansions written with `Γ'/Γ(s/2)` differ by the
  shift `digamma (s/2 + 1) = digamma (s/2) + 2/s` (`Complex.digamma_apply_add_one`).
* The zero-set symmetry used here is `ρ ↦ 1 - ρ`, not conjugation: real parts are invariant
  under conjugation, so the conjugation half of the classical `ρ ↔ 1 - conj ρ` symmetrization
  carries no extra information for real-part sums, while `ρ ↦ 1 - ρ` transports multiplicities
  exactly through `riemannXi_one_sub`.
-/

noncomputable section

namespace Kadiri

open Complex
open scoped Topology

/-! ## The xi Hadamard constant -/

/-- The Hadamard constant of Riemann's xi function: the value `P.derivative.eval 0` for a
degree-one, no-monomial Hadamard factorization
`ξ z = exp (P.eval z) * ∏' ρ, (1 - z/ρ) * exp (z/ρ)` of `riemannXi`, the product running over
the xi divisor with multiplicity. The value does not depend on the choice of factorization
(`existsUnique_riemannXi_hadamard_polynomial_derivative_eval_zero`); `Classical.choose`
extracts it.

Since `P.degree ≤ 1` the derivative is constant, and the genus-one kernel vanishes termwise at
the origin, so `xiHadamardB = logDeriv riemannXi 0`, the constant `B = ξ'(0)/ξ(0)` of
Davenport, chapter 12, classically equal to `-γ/2 - 1 + log(4π)/2` (the closed form is not
proved here). Kadiri's blueprint entry for `hadamardB` displays `B` inside a product expansion
of `(s - 1)ζ(s)`; that display is the xi factorization read through
`ξ s = (s - 1) * π^(-s/2) * Γ(s/2 + 1) * ζ s`, with the archimedean factors absorbed into `ξ`.

`Kadiri.lean` declares `hadamardB` as a sorried placeholder for this constant; `xiHadamardB`,
`hadamard_identity_weighted` and `re_hadamardB_weighted_eq` are the candidate replacements for
the placeholder and its two sorried identities. -/
def xiHadamardB : ℂ :=
  Classical.choose existsUnique_riemannXi_hadamard_polynomial_derivative_eval_zero.exists

/-- Choice specification for `xiHadamardB`: some degree-one polynomial `P` realizes the
no-monomial xi Hadamard factorization with `xiHadamardB = P.derivative.eval 0`. -/
theorem xiHadamardB_spec :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧
      (∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) *
          Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z) ∧
      xiHadamardB = Polynomial.eval 0 P.derivative :=
  Classical.choose_spec existsUnique_riemannXi_hadamard_polynomial_derivative_eval_zero.exists

/-- Logarithmic derivative of the xi Hadamard factorization, at any `z` avoiding the xi
divisor values: `logDeriv ξ z = xiHadamardB + ∑' ρ, (1/(z - ρ) + 1/ρ)`.

The sum runs over `Complex.Hadamard.divisorZeroIndex₀ riemannXi Set.univ`, which enumerates
the zeros of `ξ` with multiplicity (one index per unit of divisor). The summand is the
convergence-paired genus-one kernel; neither `∑' 1/ρ` nor `∑' 1/(z - ρ)` is separately
summable. The pairing here is written `1/(z - ρ) + 1/ρ`, while the downstream `zeroes_sum`
statements use the order `1/ρ + 1/(s - ρ)` of Kadiri's equation. -/
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

/-! ## The weighted Hadamard identity -/

/-- Order-weighted reindex from the xi divisor to `riemannZeta.zeroes_sum`: a summable
function of the divisor value tsums to the weighted zero sum over the critical strip.

The bridge has two halves, both from `KadiriGoodHeights.lean`: every xi divisor value lies in
the window `re ∈ Ioo 0 1`, `im ∈ univ` of non-trivial zeros
(`u6aRiemannXi_divisorZeroIndex₀_val_mem_nontrivialZero`), and the divisor fiber over each
non-trivial zero is finite with exactly `riemannZeta.order ρ` elements
(`u6aRiemannXi_divisorZeroIndex₀_equiv_nontrivialZeroSigma`). The sigma decomposition then
collapses fiberwise to the weighted sum
`riemannZeta.zeroes_sum (.Ioo 0 1) .univ φ = ∑' ρ, φ ρ * riemannZeta.order ρ`
(`ZetaDefinitions.lean`). The summability hypothesis is required for the collapse; recall
both `tsum`s take the junk value `0` on non-summable families. -/
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

/-- Hadamard expansion of `-ζ'/ζ` on the half-plane `1 < re s`, with the zero sum counted
with multiplicity (Kadiri's equation after (16); Davenport, chapter 12):

`-ζ'/ζ(s) = -B - log(π)/2 + 1/(s - 1) + Γ'/Γ(s/2 + 1)/2 - ∑ ρ, (1/ρ + 1/(s - ρ))`.

This is the multiplicity-weighted form of the sorried `hadamard_identity` in `Kadiri.lean`,
which it is intended to replace; the name mirrors the original so the replacement diff stays
readable. Dictionary, term by term:

* `xiHadamardB` plays the role of the placeholder `hadamardB`: it is the additive constant of
  the xi Hadamard factorization (`xiHadamardB_logDeriv`), and the displayed identity is that
  factorization differentiated logarithmically through
  `ξ s = (s - 1) * π^(-s/2) * Γ(s/2 + 1) * ζ s`
  (`logDeriv_completedZetaFactor_eq_logDeriv_riemannXi`). The `1/(s - 1)` term comes from the
  pole factor `s - 1`, the `-log(π)/2` term from `π^(-s/2)`, and the digamma term from the
  gamma factor.
* `(1/2) * digamma (s/2 + 1)` is `Γ'/Γ(s/2 + 1)/2`, matching the gamma-factor normalization
  `Γ(s/2 + 1)` of `zetaGammaFactor`. Versions written with `Γ'/Γ(s/2)` differ by `1/s` in
  this term, via the shift `digamma (s/2 + 1) = digamma (s/2) + 2/s`
  (`Complex.digamma_apply_add_one`).
* the zero sum is `riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)`: each non-trivial zero
  `ρ` contributes `(1/ρ + 1/(s - ρ)) * riemannZeta.order ρ`, whereas the sorried original
  counts each zero once. The window is the full non-trivial zero set; see the module
  docstring.
* the summand is the convergence-paired kernel `1/ρ + 1/(s - ρ)` of the source equation; the
  halves are not separately summable.

The hypothesis `1 < re s` replaces the original's `s ≠ 1` and `s ∉ zeroes`: the half-plane is
where Kadiri's downstream zero-free-region argument applies the identity, and it supplies
`ζ s ≠ 0` and the gamma-factor nonvanishing directly. -/
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

/-! ## Zero reflection through `ρ ↦ 1 - ρ`

The weighted real-part identity needs the sum `∑ ρ, re (1/(1 - ρ))` to collapse onto
`∑ ρ, re (1/ρ)`. The reflection used is `ρ ↦ 1 - ρ`, an involution of the non-trivial zero
set induced by the exact functional equation `riemannXi_one_sub`; it preserves
`riemannZeta.order`, so it leaves `riemannZeta.zeroes_sum` invariant. Conjugation symmetry is
never needed: real parts are conjugation-invariant, so the classical `ρ ↔ 1 - conj ρ`
symmetrization produces the same real-part sums as `ρ ↦ 1 - ρ`. -/

/-- Precomposition with the affine reflection `w ↦ 1 - w` transports the analytic vanishing
order: the order of `f (1 - ·)` at `z₀` equals the order of `f` at `1 - z₀`. -/
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

/-- The analytic vanishing order of Riemann's xi is symmetric under `s ↦ 1 - s`, by the
functional equation `riemannXi_one_sub`. -/
private lemma riemannXi_analyticOrderAt_one_sub (z : ℂ) :
    analyticOrderAt riemannXi (1 - z) = analyticOrderAt riemannXi z := by
  have h := analyticOrderAt_comp_one_sub (f := riemannXi) (z₀ := z)
    (Differentiable.analyticAt differentiable_riemannXi (1 - z))
  rw [show (fun w : ℂ ↦ riemannXi (1 - w)) = riemannXi from funext riemannXi_one_sub] at h
  exact h.symm

/-- Inside the open strip `0 < re ρ < 1`, the zeta zero order is symmetric under `ρ ↦ 1 - ρ`.
This is the order-preservation half of the reflection reindex used for `re B`: the order
transports through the xi functional equation, using
`u6aRiemannXi_divisor_eq_riemannZeta_order_of_criticalStrip` to identify `riemannZeta.order`
with the xi divisor on the strip, both at `ρ` and at `1 - ρ` (which lies in the strip again). -/
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

/-- The non-trivial zero set is closed under the reflection `ρ ↦ 1 - ρ`: the window
`re ∈ Ioo 0 1` is symmetric about `re = 1/2`, and the reflected point is again a zero of `ζ`
because its order is positive by `riemannZeta_order_one_sub_of_strip`. -/
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

/-- The reflection `ρ ↦ 1 - ρ` as an involution of the non-trivial zero set. This is the
functional-equation symmetry of `riemannXi`, not conjugation; it is the one that preserves
`riemannZeta.order` exactly (`riemannZeta_order_one_sub_of_strip`), which is what the
weighted sums require. -/
noncomputable def nontrivialZerosReflection : NontrivialZeros ≃ NontrivialZeros where
  toFun ρ := ⟨(1 : ℂ) - (ρ : ℂ), one_sub_mem_nontrivialZeros ρ⟩
  invFun ρ := ⟨(1 : ℂ) - (ρ : ℂ), one_sub_mem_nontrivialZeros ρ⟩
  left_inv ρ := Subtype.ext (by ring)
  right_inv ρ := Subtype.ext (by ring)

/-- The order-weighted zero sum over the critical strip is invariant under precomposition
with the reflection `ρ ↦ 1 - ρ`, for an arbitrary summand `f`: the index set reindexes along
`nontrivialZerosReflection` and the weight is preserved by
`riemannZeta_order_one_sub_of_strip`. No summability hypothesis is needed; reindexing along
an equivalence identifies the two `tsum`s including their junk values. -/
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

/-! ## The weighted real-part identity -/

/-- Real part of the xi Hadamard constant as a multiplicity-weighted zero sum:
`re xiHadamardB = -∑ ρ, re (1/ρ)`, summed over the non-trivial zeros with order weights.

This is the multiplicity-weighted form of the sorried `re_hadamardB_eq` in `Kadiri.lean`,
which it is intended to replace; the name mirrors the original. The statement is phrased with
`xiHadamardB` rather than a `hadamardB`: `xiHadamardB` is the candidate replacement for that
sorried placeholder, pinned to the role of the paper's `B` by `hadamard_identity_weighted`.

Unlike the paired complex kernel, the real parts `re (1/ρ)` are separately summable: both
`re (1/ρ)` and `re (1/(1 - ρ))` are nonnegative on the strip and their paired sum converges,
so each half is dominated by the pair. The zero sum is `riemannZeta.zeroes_sum` with the
usual window; see the module docstring.

Proof shape: `logDeriv ξ 0 = B` (the genus-one kernel vanishes termwise at the origin,
`xiHadamardB_logDeriv`), `logDeriv ξ 1 = B + S` with `S` the kernel sum at `1`, and the
functional equation makes `logDeriv ξ` antisymmetric between `0` and `1`, giving `2B = -S`.
Taking real parts, splitting `re S` into its two halves, and collapsing
`∑ ρ, re (1/(1 - ρ))` onto `∑ ρ, re (1/ρ)` with `zeroes_sum_comp_one_sub` yields the
identity. The symmetrization is through `ρ ↦ 1 - ρ`; conjugation never enters (see the
section comment above). -/
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
