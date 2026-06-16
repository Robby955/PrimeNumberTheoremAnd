import PrimeNumberTheoremAnd.IEANTN.Kadiri
import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting
import PrimeNumberTheoremAnd.IEANTN.HadamardLogDerivative
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard

/-!
# Weighted Hadamard identity for Kadiri

The Hadamard product for `riemannXi` is indexed by the xi divisor, hence repeats
zeros by divisor multiplicity. The Kadiri-facing identity below reindexes that
divisor sum as `riemannZeta.zeroes_sum`, so the zeta-zero packet is weighted by
`riemannZeta.order`. The statement is restricted to `1 < s.re`, the half-plane
where the downstream proposition uses it and where the zeta and gamma
nonvanishing hypotheses are automatic.
-/

noncomputable section

namespace Kadiri

open Complex
open scoped Topology

private theorem hadamardZetaPiFactor_eq_cpow (s : ℂ) :
    zetaPiFactor s = (Real.pi : ℂ) ^ (-(s / 2)) := by
  unfold zetaPiFactor
  rw [Complex.cpow_def_of_ne_zero, Complex.ofReal_log Real.pi_pos.le]
  · ring_nf
  · exact_mod_cast Real.pi_ne_zero

private lemma hadamard_gamma_half_ne_zero_of_re_pos {s : ℂ} (hsre : 0 < s.re) :
    Gamma (s / 2) ≠ 0 := by
  refine Gamma_ne_zero ?_
  intro m hm
  have hre := congrArg Complex.re hm
  have hm_nonneg : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
  simp at hre
  nlinarith

private lemma hadamard_gamma_factor_regular_of_re_pos {s : ℂ} (hsre : 0 < s.re) :
    ∀ m : ℕ, s / 2 + 1 ≠ -m := by
  intro m hm
  have hre := congrArg Complex.re hm
  have hm_nonneg : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
  simp at hre
  nlinarith

private lemma hadamard_gamma_factor_ne_zero_of_re_pos {s : ℂ} (hsre : 0 < s.re) :
    zetaGammaFactor s ≠ 0 := by
  unfold zetaGammaFactor
  exact Gamma_ne_zero (hadamard_gamma_factor_regular_of_re_pos hsre)

private lemma hadamard_gamma_factor_differentiableAt_of_re_pos {s : ℂ} (hsre : 0 < s.re) :
    DifferentiableAt ℂ zetaGammaFactor s := by
  unfold zetaGammaFactor
  refine (differentiableAt_Gamma _ ?_).comp s (by fun_prop)
  exact hadamard_gamma_factor_regular_of_re_pos hsre

private lemma hadamard_gamma_factor_analyticAt_of_re_pos {s : ℂ} (hsre : 0 < s.re) :
    AnalyticAt ℂ zetaGammaFactor s := by
  refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const continuous_re
  filter_upwards [hopen.mem_nhds hsre] with w hw
  exact hadamard_gamma_factor_differentiableAt_of_re_pos hw

private lemma hadamard_completedZetaFactor_eq_riemannXi_of_shift {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    completedZetaFactor s = riemannXi s := by
  have hΓhalf : Gamma (s / 2) ≠ 0 := by
    refine Gamma_ne_zero ?_
    intro m hm
    cases m with
    | zero =>
        apply hs0
        rw [show s = 2 * (s / 2) by ring, hm]
        ring
    | succ m =>
        have hbad : s / 2 + 1 = -(m : ℂ) := by
          rw [hm]
          norm_num
        exact hΓdiff m hbad
  have hGamma :
      Gamma (s / 2 + 1) = (s / 2) * Gamma (s / 2) := by
    exact Gamma_add_one (s / 2) (div_ne_zero hs0 two_ne_zero)
  rw [completedZetaFactor, zetaPoleFactor, zetaGammaFactor, hadamardZetaPiFactor_eq_cpow,
    riemannXi_eq_mul_completedRiemannZeta hs0 hs1, hGamma, riemannZeta_def_of_ne_zero hs0,
    Gammaℝ_def]
  field_simp [hs0, hΓhalf]

private lemma hadamard_completedZetaFactor_eventuallyEq_riemannXi_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) :
    completedZetaFactor =ᶠ[nhds s] riemannXi := by
  have hopen : IsOpen {w : ℂ | 1 < w.re} :=
    isOpen_lt continuous_const continuous_re
  filter_upwards [hopen.mem_nhds hs] with w hw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  have hw1 : w ≠ 1 := by
    intro h
    rw [h] at hw
    norm_num at hw
  exact hadamard_completedZetaFactor_eq_riemannXi_of_shift hw0 hw1
    (hadamard_gamma_factor_regular_of_re_pos (zero_lt_one.trans hw))

private lemma hadamard_logDeriv_completedZetaFactor_eq_logDeriv_riemannXi_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv completedZetaFactor s = logDeriv riemannXi s := by
  have heq := hadamard_completedZetaFactor_eventuallyEq_riemannXi_of_one_lt_re (s := s) hs
  rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.self_of_nhds]

private theorem hadamard_completedZetaFactor_eq_riemannXi_of_criticalStrip {s : ℂ}
    (hsre0 : 0 < s.re) (hsre1 : s.re < 1) :
    completedZetaFactor s = riemannXi s := by
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at hsre0
    norm_num at hsre0
  have hs1 : s ≠ 1 := by
    intro hs
    rw [hs] at hsre1
    norm_num at hsre1
  exact hadamard_completedZetaFactor_eq_riemannXi_of_shift hs0 hs1
    (hadamard_gamma_factor_regular_of_re_pos hsre0)

private lemma hadamard_riemannXi_eventuallyEq_completedZetaFactor_of_criticalStrip {s : ℂ}
    (hsre0 : 0 < s.re) (hsre1 : s.re < 1) :
    riemannXi =ᶠ[nhds s] completedZetaFactor := by
  have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w.re < 1} := by
    exact (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_re continuous_const)
  have hmem : s ∈ {w : ℂ | 0 < w.re ∧ w.re < 1} := ⟨hsre0, hsre1⟩
  filter_upwards [hopen.mem_nhds hmem] with w hw
  exact (hadamard_completedZetaFactor_eq_riemannXi_of_criticalStrip hw.1 hw.2).symm

private lemma hadamard_completedZetaFactor_order_eq_riemannZeta_order_of_criticalStrip
    {s : ℂ} (hsre0 : 0 < s.re) (hsre1 : s.re < 1) :
    meromorphicOrderAt completedZetaFactor s = meromorphicOrderAt riemannZeta s := by
  let G : ℂ → ℂ := fun w => zetaPoleFactor w * zetaPiFactor w * zetaGammaFactor w
  have hG_an : AnalyticAt ℂ G s := by
    dsimp [G, zetaPoleFactor, zetaPiFactor]
    exact (((by fun_prop : AnalyticAt ℂ (fun w : ℂ => w - 1) s).mul
      (by
        rw [show (fun w : ℂ => Complex.exp (-(w / 2) * (Real.log Real.pi : ℂ))) =
          Complex.exp ∘ (fun w : ℂ => -(w / 2) * (Real.log Real.pi : ℂ)) by rfl]
        exact (Complex.differentiable_exp.analyticAt _).comp (by fun_prop))).mul
      (hadamard_gamma_factor_analyticAt_of_re_pos hsre0))
  have hζ_an : AnalyticAt ℂ riemannZeta s := by
    have hs1 : s ≠ 1 := by
      intro hs
      rw [hs] at hsre1
      norm_num at hsre1
    exact riemannZeta_analyticOn_compl_one s (Set.mem_compl_singleton_iff.mpr hs1)
  have hG_ne : G s ≠ 0 := by
    dsimp [G, zetaPoleFactor, zetaPiFactor]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · intro h
      have hs : s = 1 := by simpa [sub_eq_zero] using h
      rw [hs] at hsre1
      norm_num at hsre1
    · exact Complex.exp_ne_zero _
    · exact hadamard_gamma_factor_ne_zero_of_re_pos hsre0
  have hmul :
      meromorphicOrderAt (fun w : ℂ => G w * riemannZeta w) s =
        meromorphicOrderAt G s + meromorphicOrderAt riemannZeta s :=
    meromorphicOrderAt_mul hG_an.meromorphicAt hζ_an.meromorphicAt
  have hG0 : meromorphicOrderAt G s = 0 := by
    rw [hG_an.meromorphicOrderAt_eq]
    have horder : analyticOrderAt G s = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hG_ne)
    simp [horder]
  calc
    meromorphicOrderAt completedZetaFactor s =
        meromorphicOrderAt (fun w : ℂ => G w * riemannZeta w) s := by
          rfl
    _ = meromorphicOrderAt G s + meromorphicOrderAt riemannZeta s := hmul
    _ = meromorphicOrderAt riemannZeta s := by rw [hG0, zero_add]

/-- In the critical strip, the xi divisor counts zeta zeros with zeta order. -/
theorem hadamardRiemannXi_divisor_eq_riemannZeta_order_of_criticalStrip {s : ℂ}
    (hsre0 : 0 < s.re) (hsre1 : s.re < 1) :
    (MeromorphicOn.divisor riemannXi Set.univ) s = riemannZeta.order s := by
  have hmero : MeromorphicOn riemannXi Set.univ := fun x _ =>
    (Differentiable.analyticAt (f := riemannXi) differentiable_riemannXi x).meromorphicAt
  rw [MeromorphicOn.divisor_apply hmero (Set.mem_univ s)]
  have hcongr : meromorphicOrderAt riemannXi s =
      meromorphicOrderAt completedZetaFactor s :=
    meromorphicOrderAt_congr
      ((hadamard_riemannXi_eventuallyEq_completedZetaFactor_of_criticalStrip
        (s := s) hsre0 hsre1).filter_mono nhdsWithin_le_nhds)
  rw [hcongr,
    hadamard_completedZetaFactor_order_eq_riemannZeta_order_of_criticalStrip hsre0 hsre1,
    riemannZeta.order]
  rfl

private lemma hadamard_riemannXi_ne_zero_of_zeta_ne_zero {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0) (hζ : riemannZeta s ≠ 0) :
    riemannXi s ≠ 0 := by
  have heq := hadamard_completedZetaFactor_eq_riemannXi_of_shift hs0 hs1 hΓdiff
  have hpole : zetaPoleFactor s ≠ 0 := by
    simp [zetaPoleFactor, sub_ne_zero, hs1]
  have hpi : zetaPiFactor s ≠ 0 := by
    simp [zetaPiFactor]
  have hcomp : completedZetaFactor s ≠ 0 := by
    unfold completedZetaFactor
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hpole hpi) hΓ) hζ
  exact fun hxi => hcomp (by rwa [heq])

private lemma hadamard_riemannXi_avoids_divisorZeroIndex₀_of_ne_zero {s : ℂ}
    (hxi : riemannXi s ≠ 0) :
    ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p := by
  intro p hs
  have hmero : MeromorphicOn riemannXi Set.univ := fun x _ =>
    (Differentiable.analyticAt (f := riemannXi) differentiable_riemannXi x).meromorphicAt
  have han : AnalyticAt ℂ riemannXi s :=
    Differentiable.analyticAt (f := riemannXi) differentiable_riemannXi s
  have hdiv_s : (MeromorphicOn.divisor riemannXi Set.univ) s = 0 := by
    rw [MeromorphicOn.divisor_apply hmero (Set.mem_univ s)]
    rw [han.meromorphicOrderAt_eq]
    have horder : analyticOrderAt riemannXi s = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hxi)
    simp [horder]
  have hdiv_val : (MeromorphicOn.divisor riemannXi Set.univ)
      (Complex.Hadamard.divisorZeroIndex₀_val p) = 0 := by
    rw [← hs]
    exact hdiv_s
  exact Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support p hdiv_val

private lemma hadamard_gamma_factor_regular_of_one_le_re {s : ℂ} (hsre : 1 ≤ s.re) :
    ∀ m : ℕ, s / 2 + 1 ≠ -m := by
  exact hadamard_gamma_factor_regular_of_re_pos (zero_lt_one.trans_le hsre)

private lemma hadamard_gamma_factor_ne_zero_of_one_le_re {s : ℂ} (hsre : 1 ≤ s.re) :
    zetaGammaFactor s ≠ 0 :=
  hadamard_gamma_factor_ne_zero_of_re_pos (zero_lt_one.trans_le hsre)

/-- Every nonzero xi divisor index value is a non-trivial zeta zero. -/
theorem hadamardRiemannXi_divisorZeroIndex₀_val_mem_nontrivialZero
    (p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    Complex.Hadamard.divisorZeroIndex₀_val p ∈ NontrivialZeros := by
  let z : ℂ := Complex.Hadamard.divisorZeroIndex₀_val p
  have hz0 : z ≠ 0 := by
    dsimp [z]
    exact Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hxi_zero : riemannXi z = 0 := by
    by_contra hxi_ne
    exact hadamard_riemannXi_avoids_divisorZeroIndex₀_of_ne_zero (s := z) hxi_ne p rfl
  have hz1 : z ≠ 1 := by
    intro hz
    have hxi_one : riemannXi (1 : ℂ) = 1 / 2 := by
      simpa [riemannXi_zero] using (riemannXi_one_sub (0 : ℂ))
    have hhalf : (1 / 2 : ℂ) = 0 := by
      rw [← hxi_one, ← hz]
      exact hxi_zero
    norm_num at hhalf
  have hnot_one_le_re : ¬ 1 ≤ z.re := by
    intro hzre
    have hxi_ne : riemannXi z ≠ 0 :=
      hadamard_riemannXi_ne_zero_of_zeta_ne_zero (s := z) hz0 hz1
        (hadamard_gamma_factor_regular_of_one_le_re hzre)
        (hadamard_gamma_factor_ne_zero_of_one_le_re hzre)
        (riemannZeta_ne_zero_of_one_le_re hzre)
    exact hxi_ne hxi_zero
  have hnot_re_nonpos : ¬ z.re ≤ 0 := by
    intro hzre
    let w : ℂ := 1 - z
    have hwre : 1 ≤ w.re := by
      dsimp [w]
      simp
      linarith
    have hw0 : w ≠ 0 := by
      intro hw
      exact hz1 ((sub_eq_zero.mp hw).symm)
    have hw1 : w ≠ 1 := by
      intro hw
      apply hz0
      have hneg : -z = 0 := by
        calc
          -z = w - 1 := by
            dsimp [w]
            ring
          _ = 0 := by
            rw [hw]
            ring
      exact neg_eq_zero.mp hneg
    have hxi_w_zero : riemannXi w = 0 := by
      dsimp [w]
      rw [riemannXi_one_sub z]
      exact hxi_zero
    have hxi_w_ne : riemannXi w ≠ 0 :=
      hadamard_riemannXi_ne_zero_of_zeta_ne_zero (s := w) hw0 hw1
        (hadamard_gamma_factor_regular_of_one_le_re hwre)
        (hadamard_gamma_factor_ne_zero_of_one_le_re hwre)
        (riemannZeta_ne_zero_of_one_le_re hwre)
    exact hxi_w_ne hxi_w_zero
  have hzre0 : 0 < z.re := lt_of_not_ge hnot_re_nonpos
  have hzre1 : z.re < 1 := lt_of_not_ge hnot_one_le_re
  have hdiv_ne :
      (MeromorphicOn.divisor riemannXi Set.univ) z ≠ 0 := by
    dsimp [z]
    exact Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support p
  have horder_ne : riemannZeta.order z ≠ 0 := by
    have hdiv_eq :=
      hadamardRiemannXi_divisor_eq_riemannZeta_order_of_criticalStrip
        (s := z) hzre0 hzre1
    rwa [hdiv_eq] at hdiv_ne
  have hzeta_zero : riemannZeta z = 0 := by
    by_contra hzeta_ne
    have han : AnalyticAt ℂ riemannZeta z :=
      riemannZeta_analyticOn_compl_one z (Set.mem_compl_singleton_iff.mpr hz1)
    have horder_zero : riemannZeta.order z = 0 := by
      unfold riemannZeta.order
      rw [han.meromorphicOrderAt_eq]
      have horder : analyticOrderAt riemannZeta z = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr hzeta_ne)
      simp [horder]
    exact horder_ne horder_zero
  exact ⟨⟨hzre0, hzre1⟩, Set.mem_univ z, hzeta_zero⟩

/-- Xi divisor indices are non-trivial zeta zeros with one slot per unit of zeta order. -/
noncomputable def hadamardRiemannXi_divisorZeroIndex₀_equiv_nontrivialZeroSigma :
    Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) ≃
      Σ ρ : NontrivialZeros, Fin (Int.toNat (riemannZeta.order (ρ : ℂ))) where
  toFun p := by
    let ρ : NontrivialZeros :=
      ⟨Complex.Hadamard.divisorZeroIndex₀_val p,
        hadamardRiemannXi_divisorZeroIndex₀_val_mem_nontrivialZero p⟩
    refine ⟨ρ, ?_⟩
    refine Fin.cast ?_ p.1.2
    have hre := ρ.property.1
    exact congrArg Int.toNat
      (hadamardRiemannXi_divisor_eq_riemannZeta_order_of_criticalStrip
        (s := (ρ : ℂ)) hre.1 hre.2)
  invFun q := by
    refine ⟨⟨(q.1 : ℂ), ?_⟩, nontrivialZero_ne_zero q.1⟩
    refine Fin.cast ?_ q.2
    have hre := q.1.property.1
    exact (congrArg Int.toNat
      (hadamardRiemannXi_divisor_eq_riemannZeta_order_of_criticalStrip
        (s := (q.1 : ℂ)) hre.1 hre.2)).symm
  left_inv p := by
    cases p with
    | mk p hp =>
      cases p with
      | mk z n =>
        simp [Complex.Hadamard.divisorZeroIndex₀_val]
  right_inv q := by
    cases q with
    | mk ρ n =>
      simp [Complex.Hadamard.divisorZeroIndex₀_val]

/-- Reindex a summable xi-divisor `tsum` as a multiplicity-weighted zeta-zero sum. -/
theorem hadamard_tsum_riemannXi_divisorZeroIndex₀_eq_zeroes_sum {α : Type*} [RCLike α]
    (φ : ℂ → α)
    (hsum : Summable fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) ↦
      φ (Complex.Hadamard.divisorZeroIndex₀_val p)) :
    ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        φ (Complex.Hadamard.divisorZeroIndex₀_val p) =
      riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) φ := by
  classical
  let e := hadamardRiemannXi_divisorZeroIndex₀_equiv_nontrivialZeroSigma
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

/-- Logarithmic derivative of the xi Hadamard factorization using `hadamardB`. -/
theorem hadamardB_logDeriv {z : ℂ}
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    logDeriv riemannXi z =
      hadamardB +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  obtain ⟨P, hdeg, hfac, hB⟩ := hadamardB_spec
  rw [logDeriv_riemannXi_eq_polynomial_derivative_add_tsum (P := P) hfac hz]
  have hconst : Polynomial.eval z P.derivative = hadamardB := by
    calc
      Polynomial.eval z P.derivative = Polynomial.eval 0 P.derivative :=
        Polynomial.eval_derivative_eq_eval_derivative_zero_of_degree_le_one hdeg z
      _ = hadamardB := hB.symm
  rw [hconst]

/-- Hadamard expansion of `-ζ'/ζ` on `1 < re s`, with zeta zeros counted by order. -/
theorem hadamard_identity_weighted {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      -hadamardB - (1 / 2 : ℂ) * Real.log Real.pi + 1 / (s - 1) +
      (1 / 2 : ℂ) * digamma (s / 2 + 1) -
      riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
        (fun ρ ↦ 1 / ρ + 1 / (s - ρ)) := by
  obtain ⟨P, hdeg, hfac, hB⟩ := hadamardB_spec
  have hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p := by
    intro p heq
    have hmem := hadamardRiemannXi_divisorZeroIndex₀_val_mem_nontrivialZero p
    have hlt : (Complex.Hadamard.divisorZeroIndex₀_val p).re < 1 := hmem.1.2
    rw [← heq] at hlt
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num [Complex.one_re] at hs
  have hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -(m : ℂ) :=
    hadamard_gamma_factor_regular_of_re_pos (zero_lt_one.trans hs)
  have hΓ : zetaGammaFactor s ≠ 0 :=
    hadamard_gamma_factor_ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hxi_log :
      logDeriv riemannXi s =
        Polynomial.eval s P.derivative +
          ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
            (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
              1 / Complex.Hadamard.divisorZeroIndex₀_val p) :=
    logDeriv_riemannXi_eq_polynomial_derivative_add_tsum (P := P) hfac hz
  have hcomp_log :
      logDeriv completedZetaFactor s =
        Polynomial.eval s P.derivative +
          ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
            (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
              1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
    rw [hadamard_logDeriv_completedZetaFactor_eq_logDeriv_riemannXi_of_one_lt_re hs, hxi_log]
  have hmain := neg_zeta_logDeriv_eq_of_completed_hadamard_logDeriv s
    (Polynomial.eval s P.derivative)
    (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p))
    hs1 hΓdiff hΓ hζ hcomp_log
  have hconst : Polynomial.eval s P.derivative = hadamardB := by
    calc
      Polynomial.eval s P.derivative = Polynomial.eval 0 P.derivative :=
        Polynomial.eval_derivative_eq_eval_derivative_zero_of_degree_le_one hdeg s
      _ = hadamardB := hB.symm
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
    hadamard_tsum_riemannXi_divisorZeroIndex₀_eq_zeroes_sum
      (fun ρ ↦ 1 / ρ + 1 / (s - ρ)) hsumm'
  rw [hmain, hconst, hswap, hreidx]
  ring

/-! ## Zero reflection through `ρ ↦ 1 - ρ` -/

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
        change f (1 - w) = (w - z₀) ^ n • ((-1 : ℂ) ^ n * g (1 - w))
        rw [hw, smul_eq_mul, smul_eq_mul,
          show (1 - w) - (1 - z₀) = -(w - z₀) by ring, neg_pow]
        ring

private lemma riemannXi_analyticOrderAt_one_sub (z : ℂ) :
    analyticOrderAt riemannXi (1 - z) = analyticOrderAt riemannXi z := by
  have h := analyticOrderAt_comp_one_sub (f := riemannXi) (z₀ := z)
    (Differentiable.analyticAt differentiable_riemannXi (1 - z))
  rw [show (fun w : ℂ ↦ riemannXi (1 - w)) = riemannXi from funext riemannXi_one_sub] at h
  exact h.symm

/-- In the open strip, zeta zero order is symmetric under `ρ ↦ 1 - ρ`. -/
theorem riemannZeta_order_one_sub_of_strip {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    riemannZeta.order (1 - ρ) = riemannZeta.order ρ := by
  have hre : ((1 : ℂ) - ρ).re = 1 - ρ.re := by
    simp [Complex.sub_re, Complex.one_re]
  have h0' : 0 < ((1 : ℂ) - ρ).re := by rw [hre]; linarith
  have h1' : ((1 : ℂ) - ρ).re < 1 := by rw [hre]; linarith
  rw [← hadamardRiemannXi_divisor_eq_riemannZeta_order_of_criticalStrip h0' h1',
    ← hadamardRiemannXi_divisor_eq_riemannZeta_order_of_criticalStrip h0 h1]
  have hmero : MeromorphicOn riemannXi Set.univ := fun x _ ↦
    (Differentiable.analyticAt differentiable_riemannXi x).meromorphicAt
  rw [MeromorphicOn.divisor_apply hmero (Set.mem_univ _),
    MeromorphicOn.divisor_apply hmero (Set.mem_univ _),
    (Differentiable.analyticAt differentiable_riemannXi ((1 : ℂ) - ρ)).meromorphicOrderAt_eq,
    (Differentiable.analyticAt differentiable_riemannXi ρ).meromorphicOrderAt_eq,
    riemannXi_analyticOrderAt_one_sub ρ]

/-- The non-trivial zeta-zero set is closed under `ρ ↦ 1 - ρ`. -/
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
  · change riemannZeta ((1 : ℂ) - (ρ : ℂ)) = 0
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

/-- The reflection `ρ ↦ 1 - ρ` as an involution of the non-trivial zero set. -/
noncomputable def nontrivialZerosReflection : NontrivialZeros ≃ NontrivialZeros where
  toFun ρ := ⟨(1 : ℂ) - (ρ : ℂ), one_sub_mem_nontrivialZeros ρ⟩
  invFun ρ := ⟨(1 : ℂ) - (ρ : ℂ), one_sub_mem_nontrivialZeros ρ⟩
  left_inv ρ := Subtype.ext (by ring)
  right_inv ρ := Subtype.ext (by ring)

/-- `zeroes_sum` is invariant under precomposition with `ρ ↦ 1 - ρ`. -/
theorem zeroes_sum_comp_one_sub {α : Type*} [RCLike α] (f : ℂ → α) :
    riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) (fun ρ ↦ f (1 - ρ)) =
      riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) f := by
  calc riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) (fun ρ ↦ f (1 - ρ))
      = ∑' ρ : NontrivialZeros,
          (fun σ : NontrivialZeros ↦ f (σ : ℂ) * (riemannZeta.order (σ : ℂ) : α))
            (nontrivialZerosReflection ρ) := by
        unfold riemannZeta.zeroes_sum
        refine tsum_congr fun ρ ↦ ?_
        change f (1 - (ρ : ℂ)) * (riemannZeta.order ((ρ : ℂ)) : α) =
          f (1 - (ρ : ℂ)) * (riemannZeta.order ((1 : ℂ) - (ρ : ℂ)) : α)
        rw [riemannZeta_order_one_sub_of_strip ρ.property.1.1 ρ.property.1.2]
    _ = ∑' σ : NontrivialZeros, f (σ : ℂ) * (riemannZeta.order (σ : ℂ) : α) :=
        nontrivialZerosReflection.tsum_eq
          (fun σ : NontrivialZeros ↦ f (σ : ℂ) * (riemannZeta.order (σ : ℂ) : α))
    _ = riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) f := rfl

/-! ## The weighted real-part identity -/

/-- Real part of `hadamardB` as a multiplicity-weighted non-trivial zero sum. -/
theorem re_hadamardB_weighted_eq :
    hadamardB.re =
      -riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
        (fun ρ ↦ (1 / ρ).re) := by
  have hz0 : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      (0 : ℂ) ≠ Complex.Hadamard.divisorZeroIndex₀_val p :=
    fun p ↦ (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p).symm
  have hz1 : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      (1 : ℂ) ≠ Complex.Hadamard.divisorZeroIndex₀_val p := by
    intro p heq
    have hmem := hadamardRiemannXi_divisorZeroIndex₀_val_mem_nontrivialZero p
    have hlt : (Complex.Hadamard.divisorZeroIndex₀_val p).re < 1 := hmem.1.2
    rw [← heq] at hlt
    norm_num [Complex.one_re] at hlt
  have hA : logDeriv riemannXi 0 = hadamardB := by
    rw [hadamardB_logDeriv hz0]
    have hzero : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / ((0 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) = 0 := by
      intro p
      rw [zero_sub, div_neg]
      exact neg_add_cancel _
    rw [tsum_congr hzero, tsum_zero, add_zero]
  have hB1 : logDeriv riemannXi 1 = hadamardB +
      ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / ((1 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) :=
    hadamardB_logDeriv hz1
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
  have hD : hadamardB + hadamardB =
      -∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / ((1 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
    have h := hC
    rw [hA, hB1] at h
    linear_combination h
  have hKsum : Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) ↦
        1 / ((1 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) :=
    summable_riemannXi_logDerivTerms_divisorZeroIndex₀ hz1
  have hDre : hadamardB.re + hadamardB.re =
      -∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / ((1 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p).re := by
    have h := congrArg Complex.re hD
    rw [Complex.add_re, Complex.neg_re, Complex.re_tsum hKsum] at h
    exact h
  have hr1nonneg : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      0 ≤ (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re := by
    intro p
    have hmem := hadamardRiemannXi_divisorZeroIndex₀_val_mem_nontrivialZero p
    have h0 : 0 < (Complex.Hadamard.divisorZeroIndex₀_val p).re := hmem.1.1
    rw [one_div, Complex.inv_re]
    exact div_nonneg h0.le (Complex.normSq_nonneg _)
  have hr2nonneg : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      0 ≤ (1 / ((1 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p)).re := by
    intro p
    have hmem := hadamardRiemannXi_divisorZeroIndex₀_val_mem_nontrivialZero p
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
  have hG1 : (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / Complex.Hadamard.divisorZeroIndex₀_val p).re) =
      riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) (fun ρ ↦ (1 / ρ).re) :=
    hadamard_tsum_riemannXi_divisorZeroIndex₀_eq_zeroes_sum (fun ρ ↦ (1 / ρ).re) hr1sum
  have hG2 : (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / ((1 : ℂ) - Complex.Hadamard.divisorZeroIndex₀_val p)).re) =
      riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
        (fun ρ ↦ (1 / ((1 : ℂ) - ρ)).re) :=
    hadamard_tsum_riemannXi_divisorZeroIndex₀_eq_zeroes_sum
      (fun ρ ↦ (1 / ((1 : ℂ) - ρ)).re) hr2sum
  have hH : riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ)
        (fun ρ ↦ (1 / ((1 : ℂ) - ρ)).re) =
      riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) (fun ρ ↦ (1 / ρ).re) :=
    zeroes_sum_comp_one_sub (fun ρ ↦ (1 / ρ).re)
  rw [hsplit, hG2, hG1, hH] at hDre
  linarith

end Kadiri
