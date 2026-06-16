import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Summability
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaConvexity
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.ZetaFiniteOrder
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# KubZC count atom: the local zero count `N(t+1) - N(t) = O(log t)`

This file discharges `Kadiri.KubZCLocalZeroCountLogHypothesis`, the single
analytic atom left open by `KadiriKubZCFarTail`.  The chain:

1. Euler reflection at the critical line: `‖Γ(1/2 + iu)‖² = π / cosh(πu)`,
   via `Γ(z)Γ(1-z) = π/sin(πz)` and `1 - z = conj z` on `Re z = 1/2`.
2. Gronwall transport of `‖Γ‖` across the strip `Re ∈ [1/2, 7/2]` along the
   digamma logarithmic-derivative bound `‖ψ(σ+it)‖ ≤ C log(|t|+2)`.
3. The packaged product `‖Γ(s) cos(πs/2)‖ ≤ √π (|Im s|+2)^B` on the strip:
   the exponential decay of `Γ` at the left edge exactly cancels the
   exponential growth of `cos`, through `cosh(x)² ≤ cosh(2x)`.
4. The functional equation then gives polynomial growth of `ζ` on
   `Re ∈ [-5/2, 1/2]`; the Abel-summation bound covers `Re ∈ [1/2, 13/2]`.
5. A Jensen disk of radius `9/4` centered at `2 + it` (max-modulus form of
   the divisor-mass bound, fed by the band estimate and the Dirichlet-series
   lower bound `‖ζ(2+it)‖ ≥ 1/4`) counts the order-weighted zeros in the
   Kadiri window, yielding `kubZCNearbyZeroCount (-1) 2 t ≤ C log |t|`.
-/

namespace Kadiri

open Complex Filter Asymptotics

noncomputable section

/-! ## Reflection at the critical line -/

private lemma kubZC_one_sub_eq_conj (u : ℝ) :
    (1 : ℂ) - (1 / 2 + u * I) = starRingEnd ℂ (1 / 2 + u * I) := by
  apply Complex.ext
  · simp
    norm_num
  · simp

/-- Euler reflection on the critical line: `‖Γ(1/2 + iu)‖² = π / cosh(πu)`. -/
theorem kubZC_norm_sq_gamma_half (u : ℝ) :
    ‖Complex.Gamma (1 / 2 + u * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * u) := by
  set z : ℂ := 1 / 2 + u * I with hz
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  rw [hz] at hrefl
  rw [kubZC_one_sub_eq_conj u] at hrefl
  rw [Complex.Gamma_conj, Complex.mul_conj] at hrefl
  have hsin : Complex.sin (↑Real.pi * (1 / 2 + u * I)) = ↑(Real.cosh (Real.pi * u)) := by
    have hexp : (↑Real.pi : ℂ) * (1 / 2 + u * I) =
        ↑Real.pi / 2 + ↑(Real.pi * u) * I := by
      push_cast
      ring
    rw [hexp, Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two,
      Complex.cos_mul_I, Complex.ofReal_cosh]
    ring
  rw [hsin, ← Complex.ofReal_div] at hrefl
  have hreal : Complex.normSq (Complex.Gamma (1 / 2 + u * I)) =
      Real.pi / Real.cosh (Real.pi * u) := by
    exact_mod_cast hrefl
  rw [← Complex.normSq_eq_norm_sq]
  exact hreal

/-- The cosine grows at most like `cosh` of the imaginary part. -/
theorem kubZC_norm_cos_le_cosh (z : ℂ) : ‖Complex.cos z‖ ≤ Real.cosh z.im := by
  rw [Complex.cos]
  have h1 : ‖Complex.exp (z * I) + Complex.exp (-z * I)‖ ≤
      Real.exp (-z.im) + Real.exp z.im := by
    refine le_trans (norm_add_le _ _) ?_
    rw [Complex.norm_exp, Complex.norm_exp]
    have he1 : (z * I).re = -z.im := Complex.mul_I_re z
    have he2 : (-z * I).re = z.im := by
      rw [neg_mul, Complex.neg_re, Complex.mul_I_re]
      ring
    rw [he1, he2]
  rw [norm_div, Real.cosh_eq]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have h3 : Real.exp (-z.im) + Real.exp z.im = Real.exp z.im + Real.exp (-z.im) := by ring
  rw [h3] at h1
  linarith

/-- The exact cancellation: the critical-line value of `‖Γ‖` times the cosh
growth of the half-angle cosine stays below `√π`. -/
theorem kubZC_norm_gamma_half_mul_cosh_le (u : ℝ) :
    ‖Complex.Gamma (1 / 2 + u * I)‖ * Real.cosh (Real.pi * u / 2) ≤
      Real.sqrt Real.pi := by
  have hsq := kubZC_norm_sq_gamma_half u
  have hcosh2 : Real.cosh (Real.pi * u / 2) ^ 2 ≤ Real.cosh (Real.pi * u) := by
    have hdouble := Real.cosh_two_mul (Real.pi * u / 2)
    have h2 : 2 * (Real.pi * u / 2) = Real.pi * u := by ring
    rw [h2] at hdouble
    nlinarith [sq_nonneg (Real.sinh (Real.pi * u / 2))]
  have hpos : 0 < Real.cosh (Real.pi * u) := Real.cosh_pos _
  rw [Real.le_sqrt (by positivity) Real.pi_pos.le]
  have hexpand : (‖Complex.Gamma (1 / 2 + u * I)‖ * Real.cosh (Real.pi * u / 2)) ^ 2 =
      Real.pi / Real.cosh (Real.pi * u) * Real.cosh (Real.pi * u / 2) ^ 2 := by
    rw [mul_pow, hsq]
  rw [hexpand, div_mul_eq_mul_div, div_le_iff₀ hpos]
  nlinarith [hcosh2, Real.pi_pos]

/-! ## Gronwall transport across the strip -/

/-- The vertical line `Re = σ` parametrization of `Γ` is differentiable in
`σ`, with logarithmic derivative `digamma`. -/
private lemma kubZC_hasDerivAt_gamma_line {u : ℝ} (t : ℝ) (hu : 1 / 2 ≤ u) :
    HasDerivAt (fun v : ℝ => Complex.Gamma (↑v + ↑t * I))
      (Complex.Gamma (↑u + ↑t * I) * Complex.digamma (↑u + ↑t * I)) u := by
  have hz : ∀ m : ℕ, (↑u + ↑t * I : ℂ) ≠ -↑m := by
    intro m hc
    have hre := congrArg Complex.re hc
    simp at hre
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hdiff : DifferentiableAt ℂ Complex.Gamma (↑u + ↑t * I) :=
    Complex.differentiableAt_Gamma _ hz
  have hΓval : Complex.Gamma (↑u + ↑t * I) * Complex.digamma (↑u + ↑t * I) =
      deriv Complex.Gamma (↑u + ↑t * I) := by
    rw [Complex.digamma_def, logDeriv_apply,
      mul_div_cancel₀ _ (Complex.Gamma_ne_zero hz)]
  have hΓ : HasDerivAt Complex.Gamma (deriv Complex.Gamma (↑u + ↑t * I))
      (↑u + ↑t * I) := hdiff.hasDerivAt
  have hshift : HasDerivAt (fun w : ℂ => w + ↑t * I) 1 ↑u :=
    (hasDerivAt_id (↑u : ℂ)).add_const _
  have hcomp : HasDerivAt (fun w : ℂ => Complex.Gamma (w + ↑t * I))
      (deriv Complex.Gamma (↑u + ↑t * I) * 1) ↑u := by
    have := HasDerivAt.comp (h₂ := Complex.Gamma) (h := fun w : ℂ => w + ↑t * I)
      ((↑u : ℂ)) hΓ hshift
    simpa [Function.comp_def] using this
  rw [mul_one] at hcomp
  have hreal := HasDerivAt.comp_ofReal (e := fun w : ℂ => Complex.Gamma (w + ↑t * I))
    (e' := deriv Complex.Gamma (↑u + ↑t * I)) (z := u) hcomp
  rw [← hΓval] at hreal
  exact hreal

/-- Gronwall transport of `‖Γ‖` from the critical line across `Re ∈ [1/2, 7/2]`:
the digamma strip bound is the Gronwall constant, so the strip only costs a
polynomial factor `(|t|+2)^(3K)`. -/
theorem kubZC_exists_gamma_transport :
    ∃ K : ℝ, 0 < K ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 7 / 2 →
      ‖Complex.Gamma (↑σ + ↑t * I)‖ ≤
        ‖Complex.Gamma (1 / 2 + ↑t * I)‖ * (|t| + 2) ^ (3 * K) := by
  obtain ⟨K, hK0, hψ⟩ := Complex.exists_norm_digamma_le_log (a := 1 / 2) (b := 7 / 2)
    (by norm_num)
  refine ⟨K, hK0, fun σ t hσ1 hσ2 => ?_⟩
  have hlog2 : 0 < Real.log (|t| + 2) :=
    Real.log_pos (by linarith [abs_nonneg t])
  have hcont : ContinuousOn (fun v : ℝ => Complex.Gamma (↑v + ↑t * I))
      (Set.Icc (1 / 2 : ℝ) (7 / 2)) := fun v hv =>
    ((kubZC_hasDerivAt_gamma_line t hv.1).continuousAt).continuousWithinAt
  have hder : ∀ v ∈ Set.Ico (1 / 2 : ℝ) (7 / 2),
      HasDerivWithinAt (fun v : ℝ => Complex.Gamma (↑v + ↑t * I))
        (Complex.Gamma (↑v + ↑t * I) * Complex.digamma (↑v + ↑t * I))
        (Set.Ici v) v := fun v hv =>
    (kubZC_hasDerivAt_gamma_line t hv.1).hasDerivWithinAt
  have hbound : ∀ v ∈ Set.Ico (1 / 2 : ℝ) (7 / 2),
      ‖Complex.Gamma (↑v + ↑t * I) * Complex.digamma (↑v + ↑t * I)‖ ≤
        K * Real.log (|t| + 2) * ‖Complex.Gamma (↑v + ↑t * I)‖ + 0 := by
    intro v hv
    rw [norm_mul, add_zero]
    have hre : (↑v + ↑t * I : ℂ).re = v := by simp
    have him : (↑v + ↑t * I : ℂ).im = t := by simp
    have hψv := hψ (↑v + ↑t * I) (by rw [hre]; exact hv.1) (by rw [hre]; exact hv.2.le)
    rw [him] at hψv
    calc ‖Complex.Gamma (↑v + ↑t * I)‖ * ‖Complex.digamma (↑v + ↑t * I)‖
        ≤ ‖Complex.Gamma (↑v + ↑t * I)‖ * (K * Real.log (|t| + 2)) :=
          mul_le_mul_of_nonneg_left hψv (norm_nonneg _)
      _ = K * Real.log (|t| + 2) * ‖Complex.Gamma (↑v + ↑t * I)‖ := by ring
  have key := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun v : ℝ => Complex.Gamma (↑v + ↑t * I))
    (f' := fun v : ℝ => Complex.Gamma (↑v + ↑t * I) * Complex.digamma (↑v + ↑t * I))
    (δ := ‖Complex.Gamma (↑(1 / 2 : ℝ) + ↑t * I)‖) (K := K * Real.log (|t| + 2))
    (ε := 0) (a := 1 / 2) (b := 7 / 2) hcont hder le_rfl hbound
  have hσKey := key σ ⟨hσ1, hσ2⟩
  rw [gronwallBound_ε0] at hσKey
  have hhalf : (↑(1 / 2 : ℝ) : ℂ) + ↑t * I = 1 / 2 + ↑t * I := by norm_num
  rw [hhalf] at hσKey
  refine le_trans hσKey ?_
  have hexp : Real.exp (K * Real.log (|t| + 2) * (σ - 1 / 2)) ≤ (|t| + 2) ^ (3 * K) := by
    rw [Real.rpow_def_of_pos (by linarith [abs_nonneg t])]
    apply Real.exp_le_exp.mpr
    have h3 : σ - 1 / 2 ≤ 3 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h3 (mul_pos hK0 hlog2).le]
  exact mul_le_mul_of_nonneg_left hexp (norm_nonneg _)

/-! ## The packaged product `Γ(s) cos(πs/2)` -/

/-- On the strip `Re ∈ [1/2, 7/2]` the product `Γ(s) cos(πs/2)` grows at most
polynomially in `Im s`: the exponential decay of `Γ` cancels the exponential
growth of `cos` exactly, leaving the Gronwall polynomial factor. -/
theorem kubZC_exists_norm_gamma_mul_cos :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 7 / 2 →
      ‖Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)‖ ≤
        Real.sqrt Real.pi * (|s.im| + 2) ^ B := by
  obtain ⟨K, hK0, htrans⟩ := kubZC_exists_gamma_transport
  refine ⟨3 * K, by positivity, fun s h1 h2 => ?_⟩
  have hs : (↑s.re : ℂ) + ↑s.im * I = s := Complex.re_add_im s
  have hΓ : ‖Complex.Gamma s‖ ≤
      ‖Complex.Gamma (1 / 2 + ↑s.im * I)‖ * (|s.im| + 2) ^ (3 * K) := by
    have := htrans s.re s.im h1 h2
    rwa [hs] at this
  have hcos : ‖Complex.cos (↑Real.pi * s / 2)‖ ≤ Real.cosh (Real.pi * s.im / 2) := by
    have hbound := kubZC_norm_cos_le_cosh (↑Real.pi * s / 2)
    have him : (↑Real.pi * s / 2).im = Real.pi * s.im / 2 := by
      have hrw : (↑Real.pi : ℂ) * s / 2 = ↑(Real.pi / 2) * s := by
        push_cast
        ring
      rw [hrw]
      simp [Complex.mul_im]
      ring
    rwa [him] at hbound
  have hrpow : (0 : ℝ) ≤ (|s.im| + 2) ^ (3 * K) :=
    Real.rpow_nonneg (by positivity) _
  calc ‖Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)‖
      = ‖Complex.Gamma s‖ * ‖Complex.cos (↑Real.pi * s / 2)‖ := norm_mul _ _
    _ ≤ (‖Complex.Gamma (1 / 2 + ↑s.im * I)‖ * (|s.im| + 2) ^ (3 * K)) *
        Real.cosh (Real.pi * s.im / 2) :=
        mul_le_mul hΓ hcos (norm_nonneg _) (by positivity)
    _ = (‖Complex.Gamma (1 / 2 + ↑s.im * I)‖ * Real.cosh (Real.pi * s.im / 2)) *
        (|s.im| + 2) ^ (3 * K) := by ring
    _ ≤ Real.sqrt Real.pi * (|s.im| + 2) ^ (3 * K) :=
        mul_le_mul_of_nonneg_right (kubZC_norm_gamma_half_mul_cosh_le s.im) hrpow

/-! ## Polynomial growth of zeta on the band -/

/-- Linear growth of `ζ` right of the critical line, from the Abel-summation
continuation bound. -/
theorem kubZC_norm_riemannZeta_le_right {s : ℂ} (h1 : 1 / 2 ≤ s.re)
    (h2 : s.re ≤ 13 / 2) (him : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 8 * (|s.im| + 2) := by
  have hs1 : s ≠ 1 := by
    intro hc
    rw [hc] at him
    norm_num at him
  have hdom : s ∈ zetaAbelContinuationDomain :=
    ⟨hs1, lt_of_lt_of_le (lt_of_lt_of_le zetaAbelContinuationReLower_lt_half
      (by norm_num)) h1⟩
  have hb := norm_riemannZeta_le s hdom
  have hp1 : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have hge : 1 ≤ ‖s - 1‖ := by
      have him' : |(s - 1).im| = |s.im| := by simp
      calc (1 : ℝ) ≤ |s.im| := him
        _ = |(s - 1).im| := him'.symm
        _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    rw [div_le_one (by linarith)]
    exact hge
  have hp2 : ‖s‖ / s.re ≤ 13 + 2 * |s.im| := by
    have hre : (0 : ℝ) < s.re := by linarith
    have hnorm : ‖s‖ ≤ 13 / 2 + |s.im| := by
      have h := Complex.norm_le_abs_re_add_abs_im s
      have habs : |s.re| ≤ 13 / 2 := abs_le.mpr ⟨by linarith, h2⟩
      linarith
    rw [div_le_iff₀ hre]
    nlinarith [abs_nonneg s.im]
  have hfinal : (1 : ℝ) + 1 + (13 + 2 * |s.im|) ≤ 8 * (|s.im| + 2) := by
    nlinarith [abs_nonneg s.im]
  calc ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := hb
    _ ≤ 1 + 1 + (13 + 2 * |s.im|) := by linarith
    _ ≤ 8 * (|s.im| + 2) := hfinal

/-- Polynomial growth of `ζ` left of the critical line, through the
functional equation and the packaged `Γ cos` bound. -/
theorem kubZC_exists_norm_riemannZeta_le_left :
    ∃ B : ℝ, 0 < B ∧ ∀ w : ℂ, -5 / 2 ≤ w.re → w.re ≤ 1 / 2 → 1 ≤ |w.im| →
      ‖riemannZeta w‖ ≤ 16 * Real.sqrt Real.pi * (|w.im| + 2) ^ (B + 1) := by
  obtain ⟨B, hB0, hΓcos⟩ := kubZC_exists_norm_gamma_mul_cos
  refine ⟨B, hB0, fun w hw1 hw2 him => ?_⟩
  set s : ℂ := 1 - w with hsdef
  have hsre : s.re = 1 - w.re := by simp [hsdef]
  have hsim : |s.im| = |w.im| := by
    have : s.im = -w.im := by simp [hsdef]
    rw [this, abs_neg]
  have hsre1 : 1 / 2 ≤ s.re := by rw [hsre]; linarith
  have hsre2 : s.re ≤ 7 / 2 := by rw [hsre]; linarith
  have hpoles : ∀ n : ℕ, s ≠ -↑n := by
    intro n hc
    have hre := congrArg Complex.re hc
    rw [hsre] at hre
    simp at hre
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hs1 : s ≠ 1 := by
    intro hc
    have him' := congrArg Complex.im hc
    have : s.im = -w.im := by simp [hsdef]
    rw [this] at him'
    have him_neg_zero : -w.im = 0 := by simpa using him'
    have him_zero : w.im = 0 := by linarith
    rw [him_zero] at him
    norm_num at him
  have hFE := riemannZeta_one_sub (s := s) hpoles hs1
  have hw_eq : (1 : ℂ) - s = w := by rw [hsdef]; ring
  rw [hw_eq] at hFE
  rw [hFE]
  have hregroup : (2 : ℂ) * (2 * ↑Real.pi) ^ (-s) * Complex.Gamma s *
      Complex.cos (↑Real.pi * s / 2) * riemannZeta s =
      (2 * (2 * ↑Real.pi) ^ (-s)) *
        ((Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)) * riemannZeta s) := by
    ring
  have e1 : ‖((2 : ℂ) * (2 * ↑Real.pi) ^ (-s)) *
      ((Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)) * riemannZeta s)‖ =
      ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-s)‖ *
        ‖(Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)) * riemannZeta s‖ :=
    norm_mul _ _
  have e2 : ‖(Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)) * riemannZeta s‖ =
      ‖Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)‖ * ‖riemannZeta s‖ :=
    norm_mul _ _
  rw [hregroup, e1, e2]
  have hpre : ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-s)‖ ≤ 2 := by
    rw [norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hbase : ((2 : ℂ) * ↑Real.pi) = ↑(2 * Real.pi : ℝ) := by push_cast; ring
    have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
    have hcpow : ‖((2 : ℂ) * ↑Real.pi) ^ (-s)‖ = (2 * Real.pi) ^ ((-s).re) := by
      rw [hbase]
      exact Complex.norm_cpow_eq_rpow_re_of_pos hpos _
    have hle1 : (2 * Real.pi) ^ ((-s).re) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · nlinarith [Real.pi_gt_three]
      · rw [Complex.neg_re]; linarith
    rw [h2, hcpow]
    nlinarith
  have hΓcosb : ‖Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)‖ ≤
      Real.sqrt Real.pi * (|w.im| + 2) ^ B := by
    have := hΓcos s hsre1 hsre2
    rwa [hsim] at this
  have hζb : ‖riemannZeta s‖ ≤ 8 * (|w.im| + 2) := by
    have := kubZC_norm_riemannZeta_le_right (s := s) hsre1 (by linarith) (by
      rw [hsim]; exact him)
    rwa [hsim] at this
  have hx2 : (0 : ℝ) < |w.im| + 2 := by positivity
  have hrpadd : (|w.im| + 2) ^ B * (|w.im| + 2) = (|w.im| + 2) ^ (B + 1) := by
    rw [Real.rpow_add hx2, Real.rpow_one]
  have hΓnn : (0 : ℝ) ≤ ‖Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)‖ :=
    norm_nonneg _
  have hrpnn : (0 : ℝ) ≤ Real.sqrt Real.pi * (|w.im| + 2) ^ B := by positivity
  calc ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-s)‖ *
      (‖Complex.Gamma s * Complex.cos (↑Real.pi * s / 2)‖ * ‖riemannZeta s‖)
      ≤ 2 * ((Real.sqrt Real.pi * (|w.im| + 2) ^ B) * (8 * (|w.im| + 2))) := by
        apply mul_le_mul hpre
        · exact mul_le_mul hΓcosb hζb (norm_nonneg _) hrpnn
        · positivity
        · norm_num
    _ = 16 * Real.sqrt Real.pi * ((|w.im| + 2) ^ B * (|w.im| + 2)) := by ring
    _ = 16 * Real.sqrt Real.pi * (|w.im| + 2) ^ (B + 1) := by rw [hrpadd]

/-- Polynomial growth of `ζ` on the whole band `Re ∈ [-5/2, 13/2]` needed by
the Jensen disk, away from the real axis. -/
theorem kubZC_exists_norm_riemannZeta_le_band :
    ∃ A B : ℝ, 1 ≤ A ∧ 1 ≤ B ∧ ∀ w : ℂ, -5 / 2 ≤ w.re → w.re ≤ 13 / 2 →
      1 ≤ |w.im| → ‖riemannZeta w‖ ≤ A * (|w.im| + 2) ^ B := by
  obtain ⟨B, hB0, hleft⟩ := kubZC_exists_norm_riemannZeta_le_left
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt Real.pi := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  refine ⟨16 * Real.sqrt Real.pi + 8, B + 1, by nlinarith, by linarith,
    fun w h1 h2 him => ?_⟩
  have hx1 : (1 : ℝ) ≤ |w.im| + 2 := by linarith [abs_nonneg w.im]
  have hrpnn : (0 : ℝ) ≤ (|w.im| + 2) ^ (B + 1) := Real.rpow_nonneg (by positivity) _
  rcases le_total w.re (1 / 2) with hsplit | hsplit
  · have hb := hleft w h1 hsplit him
    nlinarith
  · have hb := kubZC_norm_riemannZeta_le_right (s := w) hsplit h2 him
    have hmono : (|w.im| + 2 : ℝ) ≤ (|w.im| + 2) ^ (B + 1) := by
      calc (|w.im| + 2 : ℝ) = (|w.im| + 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (|w.im| + 2) ^ (B + 1) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    nlinarith

/-! ## The center lower bound `‖ζ(2+it)‖ ≥ 1/4` -/

private lemma kubZC_term_norm (s : ℂ) (hs : s.re = 2) (n : ℕ) :
    ‖(1 : ℂ) / (↑n + 1) ^ s‖ = 1 / ((n : ℝ) + 1) ^ 2 := by
  have hcast : ((n : ℂ) + 1) = ↑((n : ℝ) + 1) := by push_cast; ring
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [norm_div, norm_one, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos, hs]
  norm_num

private lemma kubZC_tail_summable :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr hbase
  simpa [Nat.cast_add] using this

/-- The Dirichlet-series triangle bound: `‖ζ(2+it)‖ ≥ 1/4` uniformly in `t`. -/
theorem kubZC_norm_riemannZeta_two_ge (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖riemannZeta (2 + ↑t * I)‖ := by
  set s : ℂ := 2 + ↑t * I with hsdef
  have hsre : s.re = 2 := by simp [hsdef]
  have h1 : 1 < s.re := by rw [hsre]; norm_num
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow (s := s) h1
  have hnorms : Summable (fun n : ℕ => ‖(1 : ℂ) / (↑n + 1) ^ s‖) := by
    have heq : (fun n : ℕ => ‖(1 : ℂ) / (↑n + 1) ^ s‖) =
        fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 :=
      funext fun n => kubZC_term_norm s hsre n
    rw [heq]
    exact kubZC_tail_summable
  have hsumm : Summable (fun n : ℕ => (1 : ℂ) / (↑n + 1) ^ s) :=
    Summable.of_norm hnorms
  have hsplit := hsumm.tsum_eq_zero_add
  have hfirst : (1 : ℂ) / (↑(0 : ℕ) + 1) ^ s = 1 := by
    norm_num
  rw [hfirst] at hsplit
  -- the tail and its norm
  set T : ℂ := ∑' n : ℕ, (1 : ℂ) / (↑(n + 1) + 1) ^ s with hT
  have htail_norms : Summable (fun n : ℕ => ‖(1 : ℂ) / (↑(n + 1) + 1) ^ s‖) :=
    (summable_nat_add_iff 1).mpr hnorms
  have htail_le : ‖T‖ ≤ ∑' n : ℕ, ‖(1 : ℂ) / (↑(n + 1) + 1) ^ s‖ :=
    norm_tsum_le_tsum_norm htail_norms
  have htail_eq : (∑' n : ℕ, ‖(1 : ℂ) / (↑(n + 1) + 1) ^ s‖) =
      ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 := by
    congr 1
    funext n
    rw [kubZC_term_norm s hsre (n + 1)]
    push_cast
    ring_nf
  -- the Basel tail: ∑ 1/(n+2)² = π²/6 - 1 ≤ 3/4
  have hbasel := hasSum_zeta_two
  have hbasel_sum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := hbasel.summable
  have hshift := hbasel_sum.sum_add_tsum_nat_add 2
  have hhead : (∑ i ∈ Finset.range 2, 1 / ((i : ℝ)) ^ 2) = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  rw [hbasel.tsum_eq, hhead] at hshift
  have htail_val : (∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2) = Real.pi ^ 2 / 6 - 1 := by
    have hcast : (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ) ^ 2) =
        fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2 := by
      funext n
      push_cast
      ring
    rw [← hcast]
    linarith [hshift]
  have htail_bound : ‖T‖ ≤ 3 / 4 := by
    rw [htail_eq, htail_val] at htail_le
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  -- assemble
  rw [hzeta, hsplit]
  have htri : (1 : ℝ) ≤ ‖(1 : ℂ) + T‖ + ‖T‖ := by
    have h := norm_sub_le ((1 : ℂ) + T) T
    simpa using h
  linarith

/-! ## Jensen with a max-modulus input -/

/-- Max-modulus form of the Jensen divisor-mass bound: a pointwise bound on
`log ‖f‖` over the circle of twice the radius controls the zero mass, with
the center value as the lower input.  This replaces the global-growth form
`divisorMassClosedBall₀_le_of_growth`, whose `(1+‖s‖)²` cost is too large at
high centers. -/
theorem kubZC_divisorMassClosedBall₀_le_of_sphere_bound {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {R M : ℝ} (hR : 1 ≤ R) (hf0 : f 0 ≠ 0)
    (hM : ∀ z ∈ Metric.sphere (0 : ℂ) (2 * R), Real.log ‖f z‖ ≤ M) :
    Complex.Hadamard.divisorMassClosedBall₀ f R ≤
      (M - Real.log ‖f 0‖) / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h2R : (0 : ℝ) < 2 * R := by linarith
  have h2Rne : (2 * R : ℝ) ≠ 0 := ne_of_gt h2R
  have hlow := Complex.Hadamard.log_two_mul_divisorMassClosedBall₀_le_logCounting_two_mul
    (f := f) hf hR
  have hjensen := Complex.Hadamard.jensen_formula_logCounting_eq_circleAverage_sub_log_trailingCoeff
    (f := f) hf (R := 2 * R) h2Rne
  have htrail : meromorphicTrailingCoeffAt f 0 = f 0 :=
    (hf.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero hf0
  have hsphere_eq : |2 * R| = 2 * R := abs_of_pos h2R
  have hmero : MeromorphicOn f (Metric.sphere (0 : ℂ) |2 * R|) := fun z _ =>
    ((hf.analyticAt z).meromorphicAt)
  have hint : CircleIntegrable (fun z : ℂ => Real.log ‖f z‖) 0 (2 * R) :=
    MeromorphicOn.circleIntegrable_log_norm hmero
  have havg : Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 (2 * R) ≤ M := by
    refine Real.circleAverage_mono_on_of_le_circle (f := fun z : ℂ => Real.log ‖f z‖)
      hint ?_
    intro z hz
    rw [hsphere_eq] at hz
    exact hM z hz
  have hchain : Real.log 2 * Complex.Hadamard.divisorMassClosedBall₀ f R ≤
      M - Real.log ‖f 0‖ := by
    calc Real.log 2 * Complex.Hadamard.divisorMassClosedBall₀ f R
        ≤ Function.locallyFinsuppWithin.logCounting
            (MeromorphicOn.divisor f (Set.univ : Set ℂ)) (2 * R) := hlow
      _ = Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 (2 * R) -
          Real.log ‖meromorphicTrailingCoeffAt f 0‖ := hjensen
      _ ≤ M - Real.log ‖f 0‖ := by
          rw [htrail]
          linarith
  rw [le_div_iff₀ hlog2]
  calc Complex.Hadamard.divisorMassClosedBall₀ f R * Real.log 2
      = Real.log 2 * Complex.Hadamard.divisorMassClosedBall₀ f R := by ring
    _ ≤ M - Real.log ‖f 0‖ := hchain

/-! ## The window count injects into the Jensen ball -/

/-- The order-weighted local zero count in a unit-height box. -/
noncomputable def kubZCNearbyZeroCount (σ₁ σ₂ t : ℝ) : ℝ :=
  riemannZeta.zeroes_sum (Set.uIcc σ₁ σ₂) (Set.Icc (t - 1) (t + 1))
    fun _ => (1 : ℝ)

/-- The nearby zeta-zero window used by the Jensen disk. -/
def kubZCFTNearbyWindow (t : ℝ) : Set ℂ :=
  riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2) (Set.Icc (t - 1) (t + 1))

theorem kubZCFTNearbyWindow_finite (t : ℝ) : (kubZCFTNearbyWindow t).Finite := by
  rw [kubZCFTNearbyWindow, riemannZeta.zeroes_rect_eq]
  let S : Set ℂ := (Complex.re ⁻¹' Set.Icc (-1 : ℝ) 2) ∩
    (Complex.im ⁻¹' Set.Icc (t - 1) (t + 1))
  have hS : IsCompact S := by
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  refine (riemannZeta.zeroes_on_Compact_finite' (S := S) hS).subset ?_
  intro z hz
  rcases hz with ⟨⟨hre, him⟩, hzeta⟩
  constructor
  · exact ⟨by
      simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] using hre, him⟩
  · exact hzeta

/-- On a finite zero rectangle, `zeroes_sum` is the corresponding finite sum. -/
theorem kubZC_zeroes_sum_eq_finset_of_finite {α : Type*} [RCLike α]
    (I J : Set ℝ) (f : ℂ → α)
    (hfin : (riemannZeta.zeroes_rect I J).Finite) :
    riemannZeta.zeroes_sum I J f =
      ∑ ρ ∈ hfin.toFinset, f ρ * (riemannZeta.order ρ) := by
  classical
  calc
    riemannZeta.zeroes_sum I J f
        = ∑' ρ : riemannZeta.zeroes_rect I J,
            f (ρ : ℂ) * ((riemannZeta.order (ρ : ℂ) : ℤ) : α) := rfl
    _ = ∑' z : ℂ, (riemannZeta.zeroes_rect I J).indicator
          (fun z : ℂ => f z * ((riemannZeta.order z : ℤ) : α)) z :=
        tsum_subtype (riemannZeta.zeroes_rect I J)
          (fun z : ℂ => f z * ((riemannZeta.order z : ℤ) : α))
    _ = ∑ z ∈ hfin.toFinset, (riemannZeta.zeroes_rect I J).indicator
          (fun z : ℂ => f z * ((riemannZeta.order z : ℤ) : α)) z :=
        tsum_eq_sum (fun b hb =>
          Set.indicator_of_notMem (fun hmem => hb (hfin.mem_toFinset.mpr hmem)) _)
    _ = ∑ z ∈ hfin.toFinset, f z * ((riemannZeta.order z : ℤ) : α) :=
        Finset.sum_congr rfl fun z hz => by
          rw [Set.indicator_of_mem (hfin.mem_toFinset.mp hz)]

private lemma kubZC_riemannZeta_eventually_ne_zero_punctured_of_ne_one {s : ℂ}
    (hs : s ≠ 1) :
    ∀ᶠ z in nhdsWithin s ({s}ᶜ), riemannZeta z ≠ 0 := by
  have hmem_compl_one : s ∈ ({1} : Set ℂ)ᶜ := by
    simpa [Set.mem_compl_iff] using hs
  have hdisj : Disjoint (nhdsWithin s ({s}ᶜ))
      (Filter.principal (({1} : Set ℂ)ᶜ \ riemannZeta.zeroesᶜ)) := by
    exact (mem_codiscreteWithin.mp riemannZeta.zeroes_codiscreteWithin_compl_one)
      s hmem_compl_one
  have hnot_zeroes : (({1} : Set ℂ)ᶜ \ riemannZeta.zeroesᶜ)ᶜ ∈
      nhdsWithin s ({s}ᶜ) :=
    Filter.disjoint_principal_right.mp hdisj
  have heventually_compl_one : ∀ᶠ z in nhdsWithin s ({s}ᶜ),
      z ∈ ({1} : Set ℂ)ᶜ := by
    exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hmem_compl_one)
  filter_upwards [hnot_zeroes, heventually_compl_one] with z hznot hz_compl_one hzero
  have hz_zero : z ∈ riemannZeta.zeroes := by
    simpa [riemannZeta.zeroes] using hzero
  exact hznot ⟨hz_compl_one, by simpa using hz_zero⟩

private lemma kubZC_riemannZeta_meromorphicOrderAt_ne_top_of_ne_one {s : ℂ}
    (hs : s ≠ 1) :
    meromorphicOrderAt riemannZeta s ≠ ⊤ := by
  have han := riemannZeta_analyticOn_compl_one s (by simpa [Set.mem_compl_iff] using hs)
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero han.meromorphicAt).2
    (kubZC_riemannZeta_eventually_ne_zero_punctured_of_ne_one hs)

private lemma kubZC_riemannZeta_order_pos_of_zero_ne_one {s : ℂ} (hs : s ≠ 1)
    (hzero : riemannZeta s = 0) :
    0 < riemannZeta.order s := by
  have han := riemannZeta_analyticOn_compl_one s (by simpa [Set.mem_compl_iff] using hs)
  have horder_ne_top : meromorphicOrderAt riemannZeta s ≠ ⊤ :=
    kubZC_riemannZeta_meromorphicOrderAt_ne_top_of_ne_one hs
  have hanOrder_ne_zero : analyticOrderAt riemannZeta s ≠ 0 := by
    intro h
    exact (han.analyticOrderAt_eq_zero.mp h) hzero
  unfold riemannZeta.order
  cases hO : analyticOrderAt riemannZeta s with
  | top =>
      exfalso
      exact horder_ne_top (by simp [han.meromorphicOrderAt_eq, hO])
  | coe n =>
      have hn_pos : 0 < n := by
        exact Nat.pos_of_ne_zero (by
          intro hn
          exact hanOrder_ne_zero (by simp [hO, hn]))
      rw [han.meromorphicOrderAt_eq, hO, ENat.map_coe, WithTop.untopD_coe]
      exact_mod_cast hn_pos

/-- A zeta zero off the real axis lies strictly inside the critical strip. -/
theorem kubZC_riemannZeta_zero_re_mem_Ioo_of_im_ne_zero {ρ : ℂ}
    (hζ : riemannZeta ρ = 0) (him : ρ.im ≠ 0) : ρ.re ∈ Set.Ioo (0 : ℝ) 1 := by
  have hρ0 : ρ ≠ 0 := fun h => him (by rw [h]; simp)
  constructor
  · by_contra h
    push Not at h
    have hΓℝ : Complex.Gammaℝ ρ ≠ 0 := by
      rw [Complex.Gammaℝ_def]
      refine mul_ne_zero ?_ (Complex.Gamma_ne_zero fun m hc => him (by
        have h2 : ρ = -(2 * m : ℂ) := by linear_combination (2 : ℂ) * hc
        have h3 := congrArg Complex.im h2
        simpa using h3))
      rw [Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
      exact Complex.exp_ne_zero _
    have hcompleted : completedRiemannZeta ρ = 0 := by
      have hdef := riemannZeta_def_of_ne_zero hρ0
      rw [hζ] at hdef
      rcases div_eq_zero_iff.mp hdef.symm with h2 | h2
      · exact h2
      · exact absurd h2 hΓℝ
    have hFE : completedRiemannZeta (1 - ρ) = 0 := by
      rw [completedRiemannZeta_one_sub]
      exact hcompleted
    have h1ρ : (1 : ℂ) - ρ ≠ 0 := fun hc => him (by
      have h3 := congrArg Complex.im hc
      simpa using h3)
    have hζ1 : riemannZeta (1 - ρ) = 0 := by
      rw [riemannZeta_def_of_ne_zero h1ρ, hFE, zero_div]
    exact riemannZeta_ne_zero_of_one_le_re
      (by rw [Complex.sub_re, Complex.one_re]; linarith) hζ1
  · by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h hζ

/-- The translated removable extension of `(w - 1)ζ(w)`, centered at `s`. -/
noncomputable def kubZCShiftedZetaPoleRemoved (s z : ℂ) : ℂ :=
  Complex.zetaTimesSMinusOne_entire (s + z)

theorem differentiable_kubZCShiftedZetaPoleRemoved (s : ℂ) :
    Differentiable ℂ (kubZCShiftedZetaPoleRemoved s) := by
  intro z
  unfold kubZCShiftedZetaPoleRemoved
  have hshift : DifferentiableAt ℂ (fun z : ℂ => s + z) z := by
    fun_prop
  exact Complex.zetaTimesSMinusOne_entire_differentiable.differentiableAt.comp z hshift

/-- Away from the pole point, the translated removable extension is the zeta
factor multiplied by `s + z - 1`. -/
theorem kubZCShiftedZetaPoleRemoved_eq_mul_riemannZeta {s z : ℂ}
    (h1 : s + z ≠ 1) :
    kubZCShiftedZetaPoleRemoved s z = (s + z - 1) * riemannZeta (s + z) := by
  simpa [kubZCShiftedZetaPoleRemoved] using
    Complex.zetaTimesSMinusOne_entire_eq_mul_riemannZeta h1

/-- Local product identity for the translated removable zeta extension, away
from the pole point. -/
theorem kubZCShiftedZetaPoleRemoved_eventuallyEq_mul {s z : ℂ}
    (h1 : s + z ≠ 1) :
    kubZCShiftedZetaPoleRemoved s =ᶠ[nhds z]
      fun w => (s + w - 1) * riemannZeta (s + w) := by
  have hcont : ContinuousAt (fun w : ℂ => s + w) z := by fun_prop
  have hnear : {w : ℂ | w ≠ 1} ∈ nhds (s + z) :=
    isOpen_compl_singleton.mem_nhds (by simpa using h1)
  have hpre : (fun w : ℂ => s + w) ⁻¹' {w : ℂ | w ≠ 1} ∈ nhds z :=
    hcont hnear
  filter_upwards [hpre] with w hw
  exact kubZCShiftedZetaPoleRemoved_eq_mul_riemannZeta (s := s) (z := w)
    (by simpa using hw)

/-- Divisor multiplicity transport for the translated removable zeta
extension. -/
theorem kubZCShiftedZetaPoleRemoved_divisor_eq_order {s z : ℂ}
    (h1 : s + z ≠ 1) :
    (MeromorphicOn.divisor (kubZCShiftedZetaPoleRemoved s) Set.univ) z =
      riemannZeta.order (s + z) := by
  have hζan : AnalyticAt ℂ riemannZeta (s + z) :=
    riemannZeta_analyticOn_compl_one _ (Set.mem_compl_singleton_iff.mpr h1)
  have hlin : AnalyticAt ℂ (fun w : ℂ => s + w - 1) z := by fun_prop
  have hmero : MeromorphicOn (kubZCShiftedZetaPoleRemoved s) Set.univ := fun x _ =>
    ((differentiable_kubZCShiftedZetaPoleRemoved s).analyticAt x).meromorphicAt
  rw [MeromorphicOn.divisor_apply hmero (Set.mem_univ z)]
  have hcongr : meromorphicOrderAt (kubZCShiftedZetaPoleRemoved s) z =
      meromorphicOrderAt (fun w : ℂ => (s + w - 1) * riemannZeta (s + w)) z :=
    meromorphicOrderAt_congr
      ((kubZCShiftedZetaPoleRemoved_eventuallyEq_mul (s := s) (z := z) h1).filter_mono
        nhdsWithin_le_nhds)
  have hζcomp : MeromorphicAt (fun w : ℂ => riemannZeta (s + w)) z := by
    have hshift : AnalyticAt ℂ (fun w : ℂ => s + w) z := by fun_prop
    exact hζan.meromorphicAt.comp_analyticAt hshift
  have hmul :
      meromorphicOrderAt (fun w : ℂ => (s + w - 1) * riemannZeta (s + w)) z =
        meromorphicOrderAt (fun w : ℂ => s + w - 1) z +
          meromorphicOrderAt (fun w : ℂ => riemannZeta (s + w)) z :=
    meromorphicOrderAt_mul hlin.meromorphicAt hζcomp
  have hlin0 : meromorphicOrderAt (fun w : ℂ => s + w - 1) z = 0 := by
    rw [hlin.meromorphicOrderAt_eq]
    have h0 : analyticOrderAt (fun w : ℂ => s + w - 1) z = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (by
        change s + z - 1 ≠ 0
        simpa [sub_eq_zero] using h1))
    simp [h0]
  have hshift : AnalyticAt ℂ (fun w : ℂ => s + w) z := by fun_prop
  have hderiv : deriv (fun w : ℂ => s + w) z ≠ 0 := by
    have hd : HasDerivAt (fun w : ℂ => s + w) 1 z := by
      simpa [one_mul] using (hasDerivAt_const z s).add (hasDerivAt_id z)
    rw [hd.deriv]
    norm_num
  have hcomp : meromorphicOrderAt (fun w : ℂ => riemannZeta (s + w)) z =
      meromorphicOrderAt riemannZeta (s + z) := by
    simpa [Function.comp_def] using
      (meromorphicOrderAt_comp_of_deriv_ne_zero (f := riemannZeta)
        (g := fun w : ℂ => s + w) hshift hderiv)
  rw [hcongr, hmul, hlin0, zero_add, hcomp, riemannZeta.order]
  rfl

private lemma kubZCShiftedZetaZeroBallSet_finite (s : ℂ) (R : ℝ) :
    {z : ℂ | ‖z‖ ≤ R ∧ riemannZeta (s + z) = 0}.Finite := by
  let S : Set ℂ := Metric.closedBall s R ∩ riemannZeta.zeroes
  have hS_compact : IsCompact (Metric.closedBall s R) := isCompact_closedBall s R
  have hzeros : S.Finite :=
    riemannZeta.zeroes_on_Compact_finite' (S := Metric.closedBall s R) hS_compact
  refine (hzeros.image fun ρ : ℂ => ρ - s).subset ?_
  intro z hz
  rcases hz with ⟨hzR, hzeta⟩
  refine ⟨s + z, ?_, by ring⟩
  constructor
  · rw [Metric.mem_closedBall, dist_eq_norm]
    simpa [add_sub_cancel_left] using hzR
  · simpa [riemannZeta.zeroes] using hzeta

/-- Translated zeta zeros in a closed ball around `s`, indexed without
multiplicity. -/
noncomputable def kubZCShiftedZetaZeroBallFinset (s : ℂ) (R : ℝ) : Finset ℂ :=
  (kubZCShiftedZetaZeroBallSet_finite s R).toFinset

/-- Jensen-facing shifted zero-mass bridge. -/
theorem kubZCShiftedZetaZeroBallMass_le_divisorMass {s : ℂ} {R : ℝ}
    (hR0 : 0 ≤ R) (hpole : R < ‖s - 1‖) (hcenter : riemannZeta s ≠ 0) :
    (∑ z ∈ kubZCShiftedZetaZeroBallFinset s R, (riemannZeta.order (s + z) : ℝ)) ≤
      Complex.Hadamard.divisorMassClosedBall₀ (kubZCShiftedZetaPoleRemoved s) R := by
  classical
  let D : Function.locallyFinsupp ℂ ℤ :=
    MeromorphicOn.divisor (kubZCShiftedZetaPoleRemoved s) Set.univ
  let SR : Finset ℂ :=
    (Function.locallyFinsuppWithin.finiteSupport
      (Function.locallyFinsuppWithin.toClosedBall R D)
      (isCompact_closedBall (0 : ℂ) |R|)).toFinset
  let S : Finset ℂ := SR.filter fun z : ℂ => z ≠ 0
  have hterm : ∀ z ∈ kubZCShiftedZetaZeroBallFinset s R,
      (riemannZeta.order (s + z) : ℝ) = (D z : ℝ) := by
    intro z hz
    have hzmem : z ∈ {z : ℂ | ‖z‖ ≤ R ∧ riemannZeta (s + z) = 0} :=
      (kubZCShiftedZetaZeroBallSet_finite s R).mem_toFinset.mp hz
    have h1 : s + z ≠ 1 := by
      intro h
      have hs1 : s - 1 = -z := by
        calc
          s - 1 = s - (s + z) := by rw [h]
          _ = -z := by ring
      have hnorm : ‖s - 1‖ = ‖z‖ := by rw [hs1, norm_neg]
      linarith [hzmem.1]
    have hD : D z = riemannZeta.order (s + z) := by
      simpa [D] using kubZCShiftedZetaPoleRemoved_divisor_eq_order (s := s) (z := z) h1
    exact_mod_cast hD.symm
  have hsubset : kubZCShiftedZetaZeroBallFinset s R ⊆ S := by
    intro z hz
    have hzmem : z ∈ {z : ℂ | ‖z‖ ≤ R ∧ riemannZeta (s + z) = 0} :=
      (kubZCShiftedZetaZeroBallSet_finite s R).mem_toFinset.mp hz
    have h1 : s + z ≠ 1 := by
      intro h
      have hs1 : s - 1 = -z := by
        calc
          s - 1 = s - (s + z) := by rw [h]
          _ = -z := by ring
      have hnorm : ‖s - 1‖ = ‖z‖ := by rw [hs1, norm_neg]
      linarith [hzmem.1]
    have hD_eq : D z = riemannZeta.order (s + z) := by
      simpa [D] using kubZCShiftedZetaPoleRemoved_divisor_eq_order (s := s) (z := z) h1
    have hD_ne : D z ≠ 0 := by
      have horder_pos : 0 < riemannZeta.order (s + z) :=
        kubZC_riemannZeta_order_pos_of_zero_ne_one h1 hzmem.2
      rw [hD_eq]
      exact ne_of_gt horder_pos
    have hsupp : z ∈ Function.locallyFinsuppWithin.support D :=
      Function.mem_support.mpr hD_ne
    have hnorm_abs : ‖z‖ ≤ |R| := by simpa [abs_of_nonneg hR0] using hzmem.1
    have hball : z ∈ (Function.locallyFinsuppWithin.toClosedBall R D).support :=
      Function.locallyFinsuppWithin.mem_toClosedBall_support_of_mem_support_of_norm_le_abs
        hsupp hnorm_abs
    have hSR : z ∈ SR :=
      (Set.Finite.mem_toFinset _).mpr hball
    have hz0 : z ≠ 0 := by
      intro hz0
      exact hcenter (by simpa [hz0] using hzmem.2)
    exact Finset.mem_filter.mpr ⟨hSR, hz0⟩
  have hDnonneg : ∀ z : ℂ, 0 ≤ (D z : ℝ) := by
    intro z
    have hnn : (0 : ℤ) ≤ D z := by
      simpa [D] using Differentiable.divisor_nonneg
        (differentiable_kubZCShiftedZetaPoleRemoved s) z
    exact_mod_cast hnn
  calc
    (∑ z ∈ kubZCShiftedZetaZeroBallFinset s R, (riemannZeta.order (s + z) : ℝ))
        = ∑ z ∈ kubZCShiftedZetaZeroBallFinset s R, (D z : ℝ) := by
          exact Finset.sum_congr rfl hterm
    _ ≤ ∑ z ∈ S, (D z : ℝ) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun z _ _ => hDnonneg z)
    _ = Complex.Hadamard.divisorMassClosedBall₀ (kubZCShiftedZetaPoleRemoved s) R := by
          rfl

/-- Source shape for the order-weighted logarithmic local count. -/
def KubZCLocalZeroCountLogHypothesis (C Tmin : ℝ) : Prop :=
  0 < C ∧ ∀ t : ℝ, Tmin ≤ |t| → 3 ≤ |t| →
    kubZCNearbyZeroCount (-1) 2 t ≤ C * Real.log |t|

/-- Every zero of the Kadiri window `Re ∈ [-1,2]`, `|Im - t| ≤ 1` lies in the
ball of radius `9/4` around `2 + it` (its real part is actually in `(0,1)`),
so the order-weighted window count is dominated by the shifted ball sum. -/
theorem kubZC_count_le_ballSum {t : ℝ} (ht : 3 ≤ |t|) :
    kubZCNearbyZeroCount (-1) 2 t ≤
      ∑ z ∈ kubZCShiftedZetaZeroBallFinset (2 + ↑t * I) (9 / 4),
        (riemannZeta.order ((2 + ↑t * I) + z) : ℝ) := by
  classical
  have hfin := kubZCFTNearbyWindow_finite t
  have hcount := kubZC_zeroes_sum_eq_finset_of_finite (I := Set.uIcc (-1 : ℝ) 2)
    (J := Set.Icc (t - 1) (t + 1)) (fun _ => (1 : ℝ)) hfin
  unfold kubZCNearbyZeroCount
  rw [hcount]
  simp only [one_mul]
  set s₀ : ℂ := 2 + ↑t * I with hs₀def
  have hinj : Set.InjOn (fun ρ : ℂ => ρ - s₀) ↑hfin.toFinset := by
    intro ρ₁ _ ρ₂ _ h
    have := congrArg (fun w : ℂ => w + s₀) h
    simpa using this
  have himg_subset : hfin.toFinset.image (fun ρ : ℂ => ρ - s₀) ⊆
      kubZCShiftedZetaZeroBallFinset s₀ (9 / 4) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨ρ, hρ, rfl⟩ := hz
    have hρmem := hfin.mem_toFinset.mp hρ
    obtain ⟨hre, him, hζ⟩ := hρmem
    have hζ0 : riemannZeta ρ = 0 := hζ
    have himne : ρ.im ≠ 0 := by
      intro h0
      rw [h0] at him
      have habs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [him.2], by linarith [him.1]⟩
      linarith
    have hIoo := kubZC_riemannZeta_zero_re_mem_Ioo_of_im_ne_zero hζ0 himne
    unfold kubZCShiftedZetaZeroBallFinset
    rw [Set.Finite.mem_toFinset]
    constructor
    · have hre2 : (ρ - s₀).re = ρ.re - 2 := by simp [hs₀def]
      have him2 : (ρ - s₀).im = ρ.im - t := by simp [hs₀def]
      have hsq : ‖ρ - s₀‖ ^ 2 = (ρ.re - 2) ^ 2 + (ρ.im - t) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre2, him2]
        ring
      have hb1 : (ρ.re - 2) ^ 2 ≤ 4 := by nlinarith [hIoo.1, hIoo.2]
      have hb2 : (ρ.im - t) ^ 2 ≤ 1 := by nlinarith [him.1, him.2]
      have hsqle : ‖ρ - s₀‖ ^ 2 ≤ (9 / 4) ^ 2 := by rw [hsq]; nlinarith
      nlinarith [norm_nonneg (ρ - s₀)]
    · rw [show s₀ + (ρ - s₀) = ρ by ring]
      exact hζ0
  have hsum_eq : (∑ ρ ∈ hfin.toFinset, (riemannZeta.order ρ : ℝ)) =
      ∑ z ∈ hfin.toFinset.image (fun ρ : ℂ => ρ - s₀),
        (riemannZeta.order (s₀ + z) : ℝ) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [show s₀ + (ρ - s₀) = ρ by ring]
  refine le_trans (le_of_eq hsum_eq)
    (Finset.sum_le_sum_of_subset_of_nonneg himg_subset fun z hz _ => ?_)
  have hzmem : ‖z‖ ≤ 9 / 4 ∧ riemannZeta (s₀ + z) = 0 := by
    unfold kubZCShiftedZetaZeroBallFinset at hz
    rw [Set.Finite.mem_toFinset] at hz
    exact hz
  have hne1 : s₀ + z ≠ 1 := fun hc => riemannZeta_one_ne_zero (hc ▸ hzmem.2)
  have hpos := kubZC_riemannZeta_order_pos_of_zero_ne_one hne1 hzmem.2
  exact_mod_cast hpos.le

/-! ## The count atom -/

/-- The KubZC local zero-count atom: the order-weighted zero count of the
Kadiri unit window grows logarithmically.  Jensen disk at `2 + it`, inner
radius `9/4`, outer circle `9/2`, fed by the band growth bound and the
Dirichlet center bound. -/
theorem exists_kubZCLocalZeroCountLogHypothesis :
    ∃ C Tₘᵢₙ : ℝ, KubZCLocalZeroCountLogHypothesis C Tₘᵢₙ := by
  obtain ⟨A, B, hA1, hB1, hband⟩ := kubZC_exists_norm_riemannZeta_le_band
  have h4B : (1 : ℝ) ≤ 4 ^ B := by
    calc (1 : ℝ) = 4 ^ (0 : ℝ) := (Real.rpow_zero 4).symm
      _ ≤ 4 ^ B := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  set A2 : ℝ := 3 * A * 4 ^ B with hA2def
  have hA2_1 : (1 : ℝ) ≤ A2 := by nlinarith
  have hA2_0 : (0 : ℝ) < A2 := by linarith
  have hlogA2 : (0 : ℝ) ≤ Real.log A2 := Real.log_nonneg hA2_1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨(Real.log A2 + Real.log 4 + 2 * (B + 1)) / Real.log 2, 6,
    by positivity, fun t hT _h3 => ?_⟩
  set s₀ : ℂ := 2 + ↑t * I with hs₀def
  have hs₀re : s₀.re = 2 := by simp [hs₀def]
  have hs₀sub : s₀ - 1 = 1 + ↑t * I := by rw [hs₀def]; ring
  have hs₀sub_ge : (1 : ℝ) ≤ ‖s₀ - 1‖ := by
    rw [hs₀sub]
    calc (1 : ℝ) = |(1 + ↑t * I : ℂ).re| := by simp
      _ ≤ ‖(1 + ↑t * I : ℂ)‖ := Complex.abs_re_le_norm _
  have hs₀sub_ge_t : |t| ≤ ‖s₀ - 1‖ := by
    rw [hs₀sub]
    calc |t| = |(1 + ↑t * I : ℂ).im| := by simp
      _ ≤ ‖(1 + ↑t * I : ℂ)‖ := Complex.abs_im_le_norm _
  have hs₀ne1 : s₀ ≠ 1 := by
    intro hc
    have := congrArg Complex.re hc
    rw [hs₀re] at this
    norm_num at this
  have hζs₀ : riemannZeta s₀ ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hs₀re]; norm_num)
  have hx2 : (0 : ℝ) < |t| + 2 := by positivity
  have hx2_1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  -- the sphere bound for the pole-removed translate
  have hM : ∀ z ∈ Metric.sphere (0 : ℂ) (2 * (9 / 4 : ℝ)),
      Real.log ‖kubZCShiftedZetaPoleRemoved s₀ z‖ ≤
        Real.log (A2 * (|t| + 2) ^ (B + 1)) := by
    intro z hz
    have hznorm : ‖z‖ = 9 / 2 := by
      have := Metric.mem_sphere.mp hz
      rw [dist_zero_right] at this
      linarith
    have hzre : |z.re| ≤ 9 / 2 := hznorm ▸ Complex.abs_re_le_norm z
    have hzim : |z.im| ≤ 9 / 2 := hznorm ▸ Complex.abs_im_le_norm z
    have hwre : (s₀ + z).re = 2 + z.re := by simp [hs₀def]
    have hwim : (s₀ + z).im = t + z.im := by simp [hs₀def]
    have hzre' := abs_le.mp hzre
    have hzim' := abs_le.mp hzim
    have hwim_ge : (3 / 2 : ℝ) ≤ |(s₀ + z).im| := by
      rw [hwim]
      have htri : |t| ≤ |t + z.im| + |z.im| := by
        calc |t| = |t + z.im + -z.im| := by ring_nf
          _ ≤ |t + z.im| + |(-z.im)| := abs_add_le _ _
          _ = |t + z.im| + |z.im| := by rw [abs_neg]
      linarith
    have hwim_le : |(s₀ + z).im| ≤ |t| + 9 / 2 := by
      rw [hwim]
      calc |t + z.im| ≤ |t| + |z.im| := abs_add_le _ _
        _ ≤ |t| + 9 / 2 := by linarith
    have hwne1 : s₀ + z ≠ 1 := by
      intro hc
      have him_zero : t + z.im = 0 := by
        simpa [hwim] using congrArg Complex.im hc
      rw [hwim] at hwim_ge
      rw [him_zero] at hwim_ge
      norm_num at hwim_ge
    have hFeq := kubZCShiftedZetaPoleRemoved_eq_mul_riemannZeta (s := s₀) (z := z) hwne1
    have hζw : ‖riemannZeta (s₀ + z)‖ ≤ A * (|(s₀ + z).im| + 2) ^ B := by
      refine hband (s₀ + z) ?_ ?_ (by linarith)
      · rw [hwre]; linarith
      · rw [hwre]; linarith
    have hζw' : ‖riemannZeta (s₀ + z)‖ ≤ A * (4 * (|t| + 2)) ^ B := by
      refine le_trans hζw (mul_le_mul_of_nonneg_left ?_ (by linarith))
      refine Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have hwsub : ‖s₀ + z - 1‖ ≤ 3 * (|t| + 2) := by
      have : s₀ + z - 1 = (s₀ - 1) + z := by ring
      rw [this]
      calc ‖(s₀ - 1) + z‖ ≤ ‖s₀ - 1‖ + ‖z‖ := norm_add_le _ _
        _ ≤ (1 + |t|) + 9 / 2 := by
            have : ‖s₀ - 1‖ ≤ 1 + |t| := by
              rw [hs₀sub]
              calc ‖(1 + ↑t * I : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖(↑t * I : ℂ)‖ := norm_add_le _ _
                _ = 1 + |t| := by simp
            linarith [hznorm]
        _ ≤ 3 * (|t| + 2) := by linarith
    have hFle : ‖kubZCShiftedZetaPoleRemoved s₀ z‖ ≤ A2 * (|t| + 2) ^ (B + 1) := by
      rw [hFeq, norm_mul]
      have hsplit : A * (4 * (|t| + 2)) ^ B = A * 4 ^ B * (|t| + 2) ^ B := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        ring
      calc ‖s₀ + z - 1‖ * ‖riemannZeta (s₀ + z)‖
          ≤ (3 * (|t| + 2)) * (A * 4 ^ B * (|t| + 2) ^ B) := by
            rw [← hsplit]
            exact mul_le_mul hwsub hζw' (norm_nonneg _) (by positivity)
        _ = A2 * ((|t| + 2) ^ B * (|t| + 2)) := by rw [hA2def]; ring
        _ = A2 * (|t| + 2) ^ (B + 1) := by
            rw [Real.rpow_add hx2, Real.rpow_one]
    rcases eq_or_ne ‖kubZCShiftedZetaPoleRemoved s₀ z‖ 0 with hzero | hne
    · rw [hzero, Real.log_zero]
      refine Real.log_nonneg ?_
      have : (1 : ℝ) ≤ (|t| + 2) ^ (B + 1) := by
        calc (1 : ℝ) = (|t| + 2) ^ (0 : ℝ) := (Real.rpow_zero _).symm
          _ ≤ (|t| + 2) ^ (B + 1) :=
            Real.rpow_le_rpow_of_exponent_le hx2_1 (by linarith)
      nlinarith
    · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)) hFle
  -- the center value
  have hF0eq : kubZCShiftedZetaPoleRemoved s₀ 0 = (s₀ - 1) * riemannZeta s₀ := by
    have := kubZCShiftedZetaPoleRemoved_eq_mul_riemannZeta (s := s₀) (z := 0)
      (by rw [add_zero]; exact hs₀ne1)
    rwa [add_zero] at this
  have hF0ne : kubZCShiftedZetaPoleRemoved s₀ 0 ≠ 0 := by
    rw [hF0eq]
    exact mul_ne_zero (sub_ne_zero.mpr hs₀ne1) hζs₀
  have hF0ge : (1 / 4 : ℝ) ≤ ‖kubZCShiftedZetaPoleRemoved s₀ 0‖ := by
    rw [hF0eq, norm_mul]
    have h1 := kubZC_norm_riemannZeta_two_ge t
    rw [← hs₀def] at h1
    nlinarith [norm_nonneg (riemannZeta s₀)]
  have hF0log : -Real.log ‖kubZCShiftedZetaPoleRemoved s₀ 0‖ ≤ Real.log 4 := by
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) hF0ge
    have hquarter : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
      rw [one_div, Real.log_inv]
    linarith
  -- Jensen
  have hmass := kubZC_divisorMassClosedBall₀_le_of_sphere_bound
    (f := kubZCShiftedZetaPoleRemoved s₀) (differentiable_kubZCShiftedZetaPoleRemoved s₀)
    (R := 9 / 4) (M := Real.log (A2 * (|t| + 2) ^ (B + 1))) (by norm_num) hF0ne hM
  -- ball sum below the mass
  have hball := kubZCShiftedZetaZeroBallMass_le_divisorMass (s := s₀) (R := 9 / 4)
    (by norm_num) (by linarith [hs₀sub_ge_t]) hζs₀
  -- log arithmetic
  have hMlog : Real.log (A2 * (|t| + 2) ^ (B + 1)) =
      Real.log A2 + (B + 1) * Real.log (|t| + 2) := by
    rw [Real.log_mul (ne_of_gt hA2_0) (ne_of_gt (Real.rpow_pos_of_pos hx2 _)),
      Real.log_rpow hx2]
  have hlogt1 : (1 : ℝ) ≤ Real.log |t| := by
    have hexp : Real.exp 1 < |t| := by
      calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        _ ≤ |t| := by linarith
    have := (Real.lt_log_iff_exp_lt (by linarith : (0 : ℝ) < |t|)).mpr hexp
    linarith
  have hlogshift : Real.log (|t| + 2) ≤ 2 * Real.log |t| := by
    have hsq : |t| + 2 ≤ |t| ^ 2 := by nlinarith
    calc Real.log (|t| + 2) ≤ Real.log (|t| ^ 2) := Real.log_le_log hx2 hsq
      _ = 2 * Real.log |t| := by
          rw [Real.log_pow]
          norm_num
  -- assemble
  have hchain : kubZCNearbyZeroCount (-1) 2 t ≤
      (Real.log A2 + (B + 1) * Real.log (|t| + 2) + Real.log 4) / Real.log 2 := by
    calc kubZCNearbyZeroCount (-1) 2 t
        ≤ ∑ z ∈ kubZCShiftedZetaZeroBallFinset s₀ (9 / 4),
            (riemannZeta.order (s₀ + z) : ℝ) := kubZC_count_le_ballSum (by linarith)
      _ ≤ Complex.Hadamard.divisorMassClosedBall₀ (kubZCShiftedZetaPoleRemoved s₀)
            (9 / 4) := hball
      _ ≤ (Real.log (A2 * (|t| + 2) ^ (B + 1)) -
            Real.log ‖kubZCShiftedZetaPoleRemoved s₀ 0‖) / Real.log 2 := hmass
      _ ≤ (Real.log A2 + (B + 1) * Real.log (|t| + 2) + Real.log 4) / Real.log 2 := by
          rw [hMlog]
          gcongr
          linarith
  refine le_trans hchain ?_
  rw [div_mul_eq_mul_div]
  gcongr
  nlinarith [mul_le_mul_of_nonneg_left hlogshift (by linarith : (0 : ℝ) ≤ B + 1),
    mul_le_mul_of_nonneg_left hlogt1 hlogA2,
    mul_le_mul_of_nonneg_left hlogt1 hlog4.le]

/-! ## The user-facing non-trivial-zero unit-band bound -/

/-- Non-trivial zeta zeros whose ordinates lie within one of `t`. -/
def kadiriUnitBandWindow (t : ℝ) : Set NontrivialZeros :=
  {rho | |t - (rho : ℂ).im| ≤ 1}

/-- The unit-band window is finite. -/
theorem kadiriUnitBandWindow_finite (t : ℝ) :
    (kadiriUnitBandWindow t).Finite := by
  apply Set.Finite.subset (nontrivialZeros_abs_im_lt_finite (|t| + 2))
  intro rho hrho
  rw [kadiriUnitBandWindow, Set.mem_setOf_eq] at hrho
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

/-- The plain unit-band count is dominated by the multiplicity-weighted
rectangle count used in the Jensen proof. -/
theorem kadiriUnitBandNatCard_le_kubZCNearbyZeroCount (t : ℝ) :
    (Nat.card {rho : NontrivialZeros // |t - (rho : ℂ).im| ≤ 1} : ℝ) ≤
      kubZCNearbyZeroCount (-1) 2 t := by
  classical
  have hrect_fin :
      (riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
        (Set.Icc (t - 1) (t + 1))).Finite := by
    simpa [kubZCFTNearbyWindow] using kubZCFTNearbyWindow_finite t
  haveI : Finite (riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
      (Set.Icc (t - 1) (t + 1))) := Set.finite_coe_iff.mpr hrect_fin
  letI := Fintype.ofFinite (riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
    (Set.Icc (t - 1) (t + 1)))
  let toRect : {rho : NontrivialZeros // |t - (rho : ℂ).im| ≤ 1} →
      riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2) (Set.Icc (t - 1) (t + 1)) :=
    fun rho =>
      ⟨(rho.1 : ℂ), by
        have hre : (rho.1 : ℂ).re ∈ Set.Ioo (0 : ℝ) 1 := rho.1.property.1
        rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
        exact ⟨by linarith [hre.1], by linarith [hre.2]⟩,
        by
          have him := abs_le.mp rho.2
          exact ⟨by linarith [him.2], by linarith [him.1]⟩,
        rho.1.property.2.2⟩
  have hinj : Function.Injective toRect := by
    intro rho eta h
    have hc : (rho.1 : ℂ) = (eta.1 : ℂ) :=
      congrArg (fun x : riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
        (Set.Icc (t - 1) (t + 1)) => (x : ℂ)) h
    exact Subtype.ext (Subtype.ext hc)
  have hcard_nat :
      Nat.card {rho : NontrivialZeros // |t - (rho : ℂ).im| ≤ 1} ≤
        Nat.card (riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
          (Set.Icc (t - 1) (t + 1))) :=
    Nat.card_le_card_of_injective toRect hinj
  have hcard_real :
      (Nat.card {rho : NontrivialZeros // |t - (rho : ℂ).im| ≤ 1} : ℝ) ≤
        (Nat.card (riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
          (Set.Icc (t - 1) (t + 1))) : ℝ) := by
    exact_mod_cast hcard_nat
  have hrect_count :
      (Nat.card (riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
        (Set.Icc (t - 1) (t + 1))) : ℝ) ≤ kubZCNearbyZeroCount (-1) 2 t := by
    unfold kubZCNearbyZeroCount riemannZeta.zeroes_sum
    rw [tsum_fintype]
    simp only [one_mul]
    calc
      (Nat.card (riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
          (Set.Icc (t - 1) (t + 1))) : ℝ)
          = ∑ _rho : riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
              (Set.Icc (t - 1) (t + 1)), (1 : ℝ) := by
            simp [Nat.card_eq_fintype_card]
      _ ≤ ∑ rho : riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
          (Set.Icc (t - 1) (t + 1)),
            ((riemannZeta.order (rho : ℂ) : ℤ) : ℝ) := by
            refine Finset.sum_le_sum fun rho _ => ?_
            have hzero : riemannZeta (rho : ℂ) = 0 := rho.property.2.2
            have hne1 : (rho : ℂ) ≠ 1 := fun hc =>
              riemannZeta_one_ne_zero (by simpa [hc] using hzero)
            have hpos := kubZC_riemannZeta_order_pos_of_zero_ne_one hne1 hzero
            exact_mod_cast (show (1 : ℤ) ≤ riemannZeta.order (rho : ℂ) by
              exact_mod_cast hpos)
  exact hcard_real.trans hrect_count

/-- Crude Backlund/Jensen upper count for the plain unit band, in the raw
`Nat.card` form. -/
theorem exists_nontrivialZeros_unitBand_count_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t →
      (Nat.card {rho : NontrivialZeros // |t - (rho : ℂ).im| ≤ 1} : ℝ) ≤
        C * Real.log (t + 2) := by
  rcases exists_kubZCLocalZeroCountLogHypothesis with ⟨C₀, T₀, hC₀, hcnt⟩
  let H : ℝ := max (max T₀ 3) 2
  let K : ℕ := Nat.card {rho : NontrivialZeros // |(rho : ℂ).im| < H + 2}
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let C : ℝ := C₀ + (((K : ℝ) + 1) / Real.log 4)
  have hH_T₀ : T₀ ≤ H := by
    unfold H
    exact (le_max_left T₀ 3).trans (le_max_left (max T₀ 3) 2)
  have hH3 : 3 ≤ H := by
    unfold H
    exact (le_max_right T₀ 3).trans (le_max_left (max T₀ 3) 2)
  have hH2 : 2 ≤ H := by
    unfold H
    exact le_max_right (max T₀ 3) 2
  have hKfinite : Finite {rho : NontrivialZeros // |(rho : ℂ).im| < H + 2} :=
    Set.finite_coe_iff.mpr (nontrivialZeros_abs_im_lt_finite (H + 2))
  have hCpos : 0 < C := by
    have hsecond_nonneg : 0 ≤ (((K : ℝ) + 1) / Real.log 4) := by
      exact div_nonneg (by positivity) hlog4.le
    unfold C
    linarith
  refine ⟨C, hCpos, fun t ht2 => ?_⟩
  by_cases hlarge : H ≤ t
  · have ht_nonneg : 0 ≤ t := by linarith
    have habs : |t| = t := abs_of_nonneg ht_nonneg
    have hT : T₀ ≤ |t| := by rw [habs]; exact hH_T₀.trans hlarge
    have h3 : 3 ≤ |t| := by rw [habs]; exact hH3.trans hlarge
    have hcount := kadiriUnitBandNatCard_le_kubZCNearbyZeroCount t
    have hweighted := hcnt t hT h3
    have hlog_le : Real.log |t| ≤ Real.log (t + 2) := by
      rw [habs]
      exact Real.log_le_log (by linarith) (by linarith)
    have hC₀_le_C : C₀ ≤ C := by
      have hsecond_nonneg : 0 ≤ (((K : ℝ) + 1) / Real.log 4) := by
        exact div_nonneg (by positivity) hlog4.le
      unfold C
      linarith
    have hlog_nonneg : 0 ≤ Real.log (t + 2) := by
      exact Real.log_nonneg (by linarith)
    calc
      (Nat.card {rho : NontrivialZeros // |t - (rho : ℂ).im| ≤ 1} : ℝ)
          ≤ kubZCNearbyZeroCount (-1) 2 t := hcount
      _ ≤ C₀ * Real.log |t| := hweighted
      _ ≤ C₀ * Real.log (t + 2) :=
          mul_le_mul_of_nonneg_left hlog_le hC₀.le
      _ ≤ C * Real.log (t + 2) :=
          mul_le_mul_of_nonneg_right hC₀_le_C hlog_nonneg
  · have hlt : t < H := lt_of_not_ge hlarge
    have htarget_finite : Finite {rho : NontrivialZeros // |(rho : ℂ).im| < H + 2} :=
      hKfinite
    let toBound :
        {rho : NontrivialZeros // |t - (rho : ℂ).im| ≤ 1} →
          {rho : NontrivialZeros // |(rho : ℂ).im| < H + 2} :=
      fun rho =>
        ⟨rho.1, by
          have him_le : |(rho.1 : ℂ).im| ≤ |t| + |t - (rho.1 : ℂ).im| := by
            calc
              |(rho.1 : ℂ).im| = |t - (t - (rho.1 : ℂ).im)| := by
                congr 1
                ring
              _ ≤ |t| + |t - (rho.1 : ℂ).im| := abs_sub t (t - (rho.1 : ℂ).im)
          have ht_abs : |t| = t := abs_of_nonneg (by linarith)
          rw [ht_abs] at him_le
          linarith [rho.2]⟩
    have hinj : Function.Injective toBound := by
      intro rho eta h
      have hval : (rho.1 : NontrivialZeros) = eta.1 :=
        congrArg
          (fun x : {rho : NontrivialZeros // |(rho : ℂ).im| < H + 2} =>
            (x : NontrivialZeros)) h
      exact Subtype.ext hval
    have hcard_nat :
        Nat.card {rho : NontrivialZeros // |t - (rho : ℂ).im| ≤ 1} ≤ K := by
      have := Nat.card_le_card_of_injective toBound hinj
      simpa [K] using this
    have hcard_real :
        (Nat.card {rho : NontrivialZeros // |t - (rho : ℂ).im| ≤ 1} : ℝ) ≤
          (K : ℝ) := by
      exact_mod_cast hcard_nat
    have hlog_ge : Real.log 4 ≤ Real.log (t + 2) := by
      exact Real.log_le_log (by norm_num) (by linarith)
    have hcoeff_nonneg : 0 ≤ (((K : ℝ) + 1) / Real.log 4) := by
      exact div_nonneg (by positivity) hlog4.le
    have hcoeff_mul :
        (K : ℝ) ≤ (((K : ℝ) + 1) / Real.log 4) * Real.log (t + 2) := by
      calc
        (K : ℝ) ≤ (K : ℝ) + 1 := by linarith
        _ = (((K : ℝ) + 1) / Real.log 4) * Real.log 4 := by
            field_simp [ne_of_gt hlog4]
        _ ≤ (((K : ℝ) + 1) / Real.log 4) * Real.log (t + 2) :=
            mul_le_mul_of_nonneg_left hlog_ge hcoeff_nonneg
    have hcoeff_le_C : (((K : ℝ) + 1) / Real.log 4) ≤ C := by
      unfold C
      linarith
    have hlog_nonneg : 0 ≤ Real.log (t + 2) := by
      exact Real.log_nonneg (by linarith)
    calc
      (Nat.card {rho : NontrivialZeros // |t - (rho : ℂ).im| ≤ 1} : ℝ)
          ≤ (K : ℝ) := hcard_real
      _ ≤ (((K : ℝ) + 1) / Real.log 4) * Real.log (t + 2) := hcoeff_mul
      _ ≤ C * Real.log (t + 2) :=
          mul_le_mul_of_nonneg_right hcoeff_le_C hlog_nonneg

/-- Crude Backlund/Jensen upper count for the plain unit band, in the
`Set.ncard` form consumed by near-band adapters. -/
theorem exists_kadiriUnitBandWindow_ncard_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t →
      ((kadiriUnitBandWindow t).ncard : ℝ) ≤ C * Real.log (t + 2) := by
  rcases exists_nontrivialZeros_unitBand_count_le_log with ⟨C, hC, hCbound⟩
  refine ⟨C, hC, fun t ht => ?_⟩
  have hncard :
      (kadiriUnitBandWindow t).ncard =
        Nat.card {rho : NontrivialZeros // rho ∈ kadiriUnitBandWindow t} := by
    calc
      (kadiriUnitBandWindow t).ncard =
          (Set.univ : Set {rho : NontrivialZeros // rho ∈ kadiriUnitBandWindow t}).ncard :=
        (Set.ncard_coe (kadiriUnitBandWindow t)).symm
      _ = Nat.card {rho : NontrivialZeros // rho ∈ kadiriUnitBandWindow t} := by
        rw [Set.ncard_univ]
  rw [hncard]
  simpa [kadiriUnitBandWindow] using hCbound t ht

/-- Source shape supplied by the local Jensen/Backlund count. -/
def kadiriUnitBandZeroCountLogSource : Prop :=
  (fun t : ℝ => ((kadiriUnitBandWindow t).ncard : ℝ)) =O[atTop] Real.log

/-- Big-O packaging of the unit-band zero-count bound, matching the near-band
consumer's `Set.ncard` source shape. -/
theorem kadiriUnitBandZeroCountLogSource_of_count_le_log :
    kadiriUnitBandZeroCountLogSource := by
  rcases exists_kadiriUnitBandWindow_ncard_le_log with ⟨C, hCpos, hC⟩
  rw [kadiriUnitBandZeroCountLogSource, Asymptotics.isBigO_iff']
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with t ht
  have hbound := hC t ht
  have hvalue_nonneg : 0 ≤ ((kadiriUnitBandWindow t).ncard : ℝ) := by positivity
  have hlog_t_nonneg : 0 ≤ Real.log t :=
    Real.log_nonneg (by linarith)
  have hlog_shift_le : Real.log (t + 2) ≤ 2 * Real.log t := by
    have hpos : 0 < t + 2 := by linarith
    have hsq : t + 2 ≤ t ^ 2 := by nlinarith
    calc
      Real.log (t + 2) ≤ Real.log (t ^ 2) := Real.log_le_log hpos hsq
      _ = 2 * Real.log t := by
          rw [Real.log_pow]
          norm_num
  rw [Real.norm_of_nonneg hvalue_nonneg]
  calc
    ((kadiriUnitBandWindow t).ncard : ℝ)
        ≤ C * Real.log (t + 2) := hbound
    _ ≤ C * (2 * Real.log t) :=
        mul_le_mul_of_nonneg_left hlog_shift_le hCpos.le
    _ = 2 * C * Real.log t := by ring
    _ = 2 * C * ‖Real.log t‖ := by
        rw [Real.norm_of_nonneg hlog_t_nonneg]

end

end Kadiri
