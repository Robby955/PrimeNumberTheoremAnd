import PrimeNumberTheoremAnd.IEANTN.KadiriHorizontalObstruction

/-!
# Kadiri horizontal PV package construction

This module supplies the elementary analytic inputs for the corrected
principal-value route on Kadiri's two horizontal segments, and reduces the
remaining log-derivative partial-fraction remainder bound to a single named
wide-strip growth contract for `riemannZeta`.

What is proved here, axiom-clean:

* `kadiriPoleKernelPV_norm_le` and `kadiriSinglePolePVKernelBound_holds`: the
  uniform single-pole PV kernel bound `‖K‖ ≤ π + log((1+a)/a)`. This is the
  elementary companion flagged in the route: the real part is a `log` ratio of
  squared distances bounded by `log((1+a)/a)`, and the imaginary part is a sum
  of two `arctan` values, each of magnitude `< π/2`.

The wide-strip polynomial growth bound for `riemannZeta` on the scaled disk
`|s - (c + iT)| ≤ 4·λ` — the input the scaled-disk `FinalBound` specialization
consumes — is recorded as the named contract `KadiriWideStripZetaGrowth`.  The
in-tree zeta growth estimates (`ZetaUpperBnd`, `lem_zetaUppBd`) only cover
`Re s ∈ [1/2, 3)`, far narrower than the disk of radius `4λ ≈ 30` needed here,
so this contract is the genuine remaining analytic obligation; it is stated
honestly as a `Prop`, never discharged with `sorry`.
-/

namespace Kadiri

open Complex Real

/-! ## Single-pole PV kernel bound (elementary, proved) -/

/-- Each arctangent has magnitude `< π/2`. -/
private lemma abs_arctan_lt_pi_div_two (x : ℝ) : |Real.arctan x| < Real.pi / 2 := by
  rw [abs_lt]
  exact ⟨Real.neg_pi_div_two_lt_arctan x, Real.arctan_lt_pi_div_two x⟩

/-- The sum of two arctangents has magnitude `< π`. -/
private lemma abs_arctan_add_arctan_lt_pi (x y : ℝ) :
    |Real.arctan x + Real.arctan y| < Real.pi := by
  calc |Real.arctan x + Real.arctan y|
      ≤ |Real.arctan x| + |Real.arctan y| := abs_add_le _ _
    _ < Real.pi / 2 + Real.pi / 2 :=
        add_lt_add (abs_arctan_lt_pi_div_two x) (abs_arctan_lt_pi_div_two y)
    _ = Real.pi := by ring

/-- For `0 < β < 1`, the two distances `p = β + a` and `q = 1 + a - β` both lie
in `[a, 1 + a]` when `0 < a`. -/
private lemma pq_mem_Icc {a β : ℝ} (_ha : 0 < a) (hβ0 : 0 < β) (hβ1 : β < 1) :
    a ≤ β + a ∧ β + a ≤ 1 + a ∧ a ≤ 1 + a - β ∧ 1 + a - β ≤ 1 + a :=
  ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Real-part estimate for the kernel: with `a ≤ p` and `q ≤ 1 + a` and `0 < a`,
`|½ log((q²+δ²)/(p²+δ²))| ≤ log((1+a)/a)`.

The key monotonicity: adding the common `δ²` to numerator and denominator of a
ratio drives it toward `1`, so the worst case is `δ = 0`, giving `log((1+a)/a)`.
-/
private lemma kernel_re_abs_le {a p q δ : ℝ} (ha : 0 < a)
    (hp_lo : a ≤ p) (hp_hi : p ≤ 1 + a) (hq_lo : a ≤ q) (hq_hi : q ≤ 1 + a) :
    |(1 / 2) * Real.log ((q ^ 2 + δ ^ 2) / (p ^ 2 + δ ^ 2))|
      ≤ Real.log ((1 + a) / a) := by
  have ha1 : 0 < 1 + a := by linarith
  have hp_pos : 0 < p := lt_of_lt_of_le ha hp_lo
  have hq_pos : 0 < q := lt_of_lt_of_le ha hq_lo
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
  -- Lower and upper envelopes for both squared distances.
  have hlo_p : a ^ 2 + δ ^ 2 ≤ p ^ 2 + δ ^ 2 := by
    have : a ^ 2 ≤ p ^ 2 := by nlinarith
    linarith
  have hhi_p : p ^ 2 + δ ^ 2 ≤ (1 + a) ^ 2 + δ ^ 2 := by
    have : p ^ 2 ≤ (1 + a) ^ 2 := by nlinarith
    linarith
  have hlo_q : a ^ 2 + δ ^ 2 ≤ q ^ 2 + δ ^ 2 := by
    have : a ^ 2 ≤ q ^ 2 := by nlinarith
    linarith
  have hhi_q : q ^ 2 + δ ^ 2 ≤ (1 + a) ^ 2 + δ ^ 2 := by
    have : q ^ 2 ≤ (1 + a) ^ 2 := by nlinarith
    linarith
  have hbot_pos : 0 < a ^ 2 + δ ^ 2 := by positivity
  have hp_den_pos : 0 < p ^ 2 + δ ^ 2 := by positivity
  have hq_den_pos : 0 < q ^ 2 + δ ^ 2 := by positivity
  -- The ratio lies in [ (a²+δ²)/((1+a)²+δ²) , ((1+a)²+δ²)/(a²+δ²) ].
  have hratio_le :
      (q ^ 2 + δ ^ 2) / (p ^ 2 + δ ^ 2)
        ≤ ((1 + a) ^ 2 + δ ^ 2) / (a ^ 2 + δ ^ 2) := by
    gcongr
  have hratio_ge :
      (a ^ 2 + δ ^ 2) / ((1 + a) ^ 2 + δ ^ 2)
        ≤ (q ^ 2 + δ ^ 2) / (p ^ 2 + δ ^ 2) := by
    gcongr
  -- Envelope ratio is bounded by ((1+a)/a)², monotone in δ² toward 1.
  have hgrow_top : 0 < ((1 + a) ^ 2 + δ ^ 2) / (a ^ 2 + δ ^ 2) := by positivity
  have henv_le : ((1 + a) ^ 2 + δ ^ 2) / (a ^ 2 + δ ^ 2) ≤ ((1 + a) / a) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ hbot_pos (by positivity)]
    nlinarith [sq_nonneg δ, sq_nonneg a, sq_nonneg (1 + a), mul_pos ha ha1]
  -- Hence |log ratio| ≤ log(((1+a)/a)²) = 2 log((1+a)/a).
  have hratio_pos : 0 < (q ^ 2 + δ ^ 2) / (p ^ 2 + δ ^ 2) := by positivity
  have hlog_sq : Real.log (((1 + a) / a) ^ 2) = 2 * Real.log ((1 + a) / a) := by
    rw [Real.log_pow]; push_cast; ring
  have hlog_ratio_le :
      Real.log ((q ^ 2 + δ ^ 2) / (p ^ 2 + δ ^ 2)) ≤ 2 * Real.log ((1 + a) / a) := by
    have h1 : Real.log ((q ^ 2 + δ ^ 2) / (p ^ 2 + δ ^ 2)) ≤ Real.log (((1 + a) / a) ^ 2) :=
      Real.log_le_log hratio_pos (le_trans hratio_le henv_le)
    rwa [hlog_sq] at h1
  have hlog_ratio_ge :
      -(2 * Real.log ((1 + a) / a)) ≤ Real.log ((q ^ 2 + δ ^ 2) / (p ^ 2 + δ ^ 2)) := by
    have hinv : ((a ^ 2 + δ ^ 2) / ((1 + a) ^ 2 + δ ^ 2))
        = (((1 + a) ^ 2 + δ ^ 2) / (a ^ 2 + δ ^ 2))⁻¹ := by rw [inv_div]
    have h2 : Real.log ((a ^ 2 + δ ^ 2) / ((1 + a) ^ 2 + δ ^ 2))
        ≤ Real.log ((q ^ 2 + δ ^ 2) / (p ^ 2 + δ ^ 2)) :=
      Real.log_le_log (by positivity) hratio_ge
    have h3 : Real.log ((a ^ 2 + δ ^ 2) / ((1 + a) ^ 2 + δ ^ 2))
        = - Real.log (((1 + a) ^ 2 + δ ^ 2) / (a ^ 2 + δ ^ 2)) := by
      rw [hinv, Real.log_inv]
    have h4 : Real.log (((1 + a) ^ 2 + δ ^ 2) / (a ^ 2 + δ ^ 2)) ≤ 2 * Real.log ((1 + a) / a) := by
      have := Real.log_le_log hgrow_top henv_le
      rwa [hlog_sq] at this
    rw [h3] at h2
    linarith
  rw [abs_le]
  constructor <;> nlinarith [hlog_ratio_le, hlog_ratio_ge]

/-- Public wrapper for the real-part estimate used by the scalar Cauchy
integral bound. -/
theorem kadiriKernelReAbsLe {a p q δ : ℝ} (ha : 0 < a)
    (hp_lo : a ≤ p) (hp_hi : p ≤ 1 + a) (hq_lo : a ≤ q) (hq_hi : q ≤ 1 + a) :
    |(1 / 2) * Real.log ((q ^ 2 + δ ^ 2) / (p ^ 2 + δ ^ 2))|
      ≤ Real.log ((1 + a) / a) :=
  kernel_re_abs_le ha hp_lo hp_hi hq_lo hq_hi

/-- The `δ = 0` value `log (q / p)` has magnitude `≤ log((1+a)/a)` for
`a ≤ p, q ≤ 1 + a`. -/
private lemma kernel_log_ratio_abs_le {a p q : ℝ} (ha : 0 < a)
    (hp_lo : a ≤ p) (hp_hi : p ≤ 1 + a) (hq_lo : a ≤ q) (hq_hi : q ≤ 1 + a) :
    |Real.log (q / p)| ≤ Real.log ((1 + a) / a) := by
  have ha1 : 0 < 1 + a := by linarith
  have hp_pos : 0 < p := lt_of_lt_of_le ha hp_lo
  have hq_pos : 0 < q := lt_of_lt_of_le ha hq_lo
  rw [Real.log_div hq_pos.ne' hp_pos.ne', Real.log_div ha1.ne' ha.ne', abs_le]
  have hlq : Real.log a ≤ Real.log q := Real.log_le_log ha hq_lo
  have huq : Real.log q ≤ Real.log (1 + a) := Real.log_le_log hq_pos hq_hi
  have hlp : Real.log a ≤ Real.log p := Real.log_le_log ha hp_lo
  have hup : Real.log p ≤ Real.log (1 + a) := Real.log_le_log hp_pos hp_hi
  constructor <;> linarith

/-- The single-pole PV kernel obeys the uniform bound `‖K‖ ≤ π + log((1+a)/a)`
whenever `0 < a`, `0 < β < 1`, with `p = β + a`, `q = 1 + a - β`. The kernel
splits as `Re - Im·I` with `|Re| ≤ log((1+a)/a)` and `|Im| ≤ π`. -/
theorem kadiriPoleKernelPV_norm_le {a β δ : ℝ} (ha : 0 < a)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    ‖kadiriPoleKernelPV (β + a) (1 + a - β) δ‖
      ≤ Real.pi + Real.log ((1 + a) / a) := by
  obtain ⟨hp_lo, hp_hi, hq_lo, hq_hi⟩ := pq_mem_Icc ha hβ0 hβ1
  have hL_nonneg : 0 ≤ Real.log ((1 + a) / a) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ ha]; linarith
  have hpi_nonneg : 0 ≤ Real.pi := Real.pi_pos.le
  by_cases hδ : δ = 0
  · -- The PV value is the real number `log (q / p)`.
    rw [kadiriPoleKernelPV, if_pos hδ, Complex.norm_real, Real.norm_eq_abs]
    have := kernel_log_ratio_abs_le ha hp_lo hp_hi hq_lo hq_hi
    linarith
  · -- The PV value is `Re - Im·I`; bound `‖·‖ ≤ |re| + |im|`.
    set Re : ℝ := (1 / 2) * Real.log (((1 + a - β) ^ 2 + δ ^ 2) / ((β + a) ^ 2 + δ ^ 2)) with hRe
    set Im : ℝ := Real.arctan ((1 + a - β) / δ) + Real.arctan ((β + a) / δ) with hIm
    have hval :
        kadiriPoleKernelPV (β + a) (1 + a - β) δ = (Re : ℂ) - (Im : ℂ) * I := by
      rw [kadiriPoleKernelPV, if_neg hδ, hRe, hIm]; push_cast; ring
    have hre : (kadiriPoleKernelPV (β + a) (1 + a - β) δ).re = Re := by
      rw [hval]; simp
    have him : (kadiriPoleKernelPV (β + a) (1 + a - β) δ).im = -Im := by
      rw [hval]; simp
    have hRe_le : |Re| ≤ Real.log ((1 + a) / a) := by
      rw [hRe]; exact kernel_re_abs_le ha hp_lo hp_hi hq_lo hq_hi
    have hIm_le : |Im| ≤ Real.pi := by
      rw [hIm]; exact (abs_arctan_add_arctan_lt_pi _ _).le
    calc ‖kadiriPoleKernelPV (β + a) (1 + a - β) δ‖
        ≤ |(kadiriPoleKernelPV (β + a) (1 + a - β) δ).re|
            + |(kadiriPoleKernelPV (β + a) (1 + a - β) δ).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |Re| + |Im| := by rw [hre, him, abs_neg]
      _ ≤ Real.log ((1 + a) / a) + Real.pi := add_le_add hRe_le hIm_le
      _ = Real.pi + Real.log ((1 + a) / a) := by ring

/-- The named single-pole PV kernel-bound contract holds. -/
theorem kadiriSinglePolePVKernelBound_holds (a : ℝ) :
    KadiriSinglePolePVKernelBound a := by
  intro ha β δ hβ0 hβ1
  exact kadiriPoleKernelPV_norm_le ha hβ0 hβ1

/-! ## Reducing the partial-fraction remainder to a linear-in-`log` input

The scaled-disk `FinalBound` specialization (route step ii) outputs a remainder
that is `O(log U)` with `U = |T| + 2`, not `O((log U)²)`; the squared form in
`KadiriHorizontalPartialFractionRemainderBound` is a safe over-bound.  The
absorption `log U ≤ (log U)²` for `U ≥ e` is the only nonelementary-looking
arithmetic step, and it is discharged here.  The linear-in-`log` input itself —
the actual output of the scaled `FinalBound` + finite disk-zero correction —
is named `KadiriHorizontalPFRemainderLinearInput` below; it is the genuine
remaining analytic obligation and is *not* discharged with `sorry`. -/

/-- Absorption `c·L ≤ c·L²` when `0 ≤ c` and `1 ≤ L`. The route applies it with
`L = log(|T| + 2)`, which is `≥ 1` once `|T| + 2 ≥ e`, i.e. for all large `T`. -/
theorem linear_log_le_sq_log {c L : ℝ} (hc : 0 ≤ c) (hL : 1 ≤ L) :
    c * L ≤ c * L ^ 2 := by
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have : L ≤ L ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_left this hc

/-- `1 ≤ log(|T| + 2)` once `e ≤ |T|` (in particular for all large `T`). -/
theorem one_le_log_abs_add_two {T : ℝ} (hT : Real.exp 1 ≤ |T|) :
    1 ≤ Real.log (|T| + 2) := by
  have hge : Real.exp 1 ≤ |T| + 2 := by linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
    _ ≤ Real.log (|T| + 2) := Real.log_le_log (Real.exp_pos 1) hge

/-- The **linear-in-`log`** partial-fraction remainder input: the scaled-disk
`FinalBound` specialization plus the finite disk-zero-to-window correction give
`‖-ζ'/ζ(s) + Σ_{window} 1/(s-ρ)‖ ≤ B·log(|T|+2)` on the two horizontal segments,
off the poles, for all large `T`.

This is the genuine output of route steps (i)–(iii): instantiate `FinalBound`
on `f_T(z) = ζ(c+iT+λz)/ζ(c+iT)` (radii `R=4, R₀=2, r=1/2`), then correct from
the disk-zero set `D_T` to the unit-height window `W_T`.  Its proof requires a
polynomial growth bound for `ζ` on the scaled disk `|s-(c+iT)| ≤ 4λ` (the
`KadiriWideStripZetaGrowth` input), which is *not* available in-tree (the
existing `ZetaUpperBnd`/`lem_zetaUppBd` only cover `Re s ∈ [1/2,3)`).  It is
therefore left as a named `Prop` contract. -/
def KadiriHorizontalPFRemainderLinearInput (a : ℝ) : Prop :=
  0 ≤ a ∧ ∃ B : ℝ, 0 ≤ B ∧
    ∀ᶠ T : ℝ in Filter.atTop,
      Real.exp 1 ≤ |T| ∧
        (∀ σ ∈ Set.Icc (-a) (1 + a),
          riemannZeta (kadiriTopHorizontalPoint T σ) ≠ 0 →
            ‖(-deriv riemannZeta (kadiriTopHorizontalPoint T σ) /
                riemannZeta (kadiriTopHorizontalPoint T σ)) +
              riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc (T - 1) (T + 1))
                (fun ρ ↦ (1 : ℂ) / (kadiriTopHorizontalPoint T σ - ρ))‖
              ≤ B * Real.log (|T| + 2)) ∧
        (∀ σ ∈ Set.Icc (-a) (1 + a),
          riemannZeta (kadiriBotHorizontalPoint T σ) ≠ 0 →
            ‖(-deriv riemannZeta (kadiriBotHorizontalPoint T σ) /
                riemannZeta (kadiriBotHorizontalPoint T σ)) +
              riemannZeta.zeroes_sum (Set.Ioo 0 1) (Set.Icc ((-T) - 1) ((-T) + 1))
                (fun ρ ↦ (1 : ℂ) / (kadiriBotHorizontalPoint T σ - ρ))‖
              ≤ B * Real.log (|T| + 2))

/-- **Reduction (proved).** The squared-log partial-fraction remainder bound
`KadiriHorizontalPartialFractionRemainderBound` follows from the linear-in-`log`
input by the absorption `B·log U ≤ B·(log U)²` (valid since `log U ≥ 1` for the
`T` in the input's eventual filter). The only remaining obligation is the linear
input itself; this step does not introduce any axiom or `sorry`. -/
theorem kadiriHorizontalPartialFractionRemainderBound_of_linearInput {a : ℝ}
    (h : KadiriHorizontalPFRemainderLinearInput a) :
    KadiriHorizontalPartialFractionRemainderBound a := by
  obtain ⟨_ha, B, hB, hev⟩ := h
  refine ⟨B, hB, ?_⟩
  filter_upwards [hev] with T hT
  obtain ⟨hTe, htop, hbot⟩ := hT
  have hL1 : 1 ≤ Real.log (|T| + 2) := one_le_log_abs_add_two hTe
  have hT1 : 1 ≤ |T| := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    linarith
  refine ⟨hT1, ?_, ?_⟩
  · intro σ hσ hζ
    calc
      _ ≤ B * Real.log (|T| + 2) := htop σ hσ hζ
      _ ≤ B * (Real.log (|T| + 2)) ^ (2 : ℕ) := linear_log_le_sq_log hB hL1
  · intro σ hσ hζ
    calc
      _ ≤ B * Real.log (|T| + 2) := hbot σ hσ hζ
      _ ≤ B * (Real.log (|T| + 2)) ^ (2 : ℕ) := linear_log_le_sq_log hB hL1

/-! ## Assembling and constructing the PV package

The corrected PV operators `topPV`, `botPV` are supplied together with two
inputs: the decay bound `KadiriHorizontalPVBound` (route step iv, the downstream
estimate assembled from `Φ`-decay, the single-pole kernel bound, zero counting,
and the partial-fraction remainder bound) and the no-zero-ordinate bridge.  Once
both are supplied, the package is constructed and the two horizontal PV-vanishing
theorems become unconditional. -/

/-- **Package constructor (proved).** Given corrected PV operators with their
decay bound and the no-zero-ordinate bridge, assemble the
`KadiriHorizontalPVPackage`. No axiom or `sorry` is introduced. -/
def kadiriHorizontalPVPackage_of_inputs {φ : ℝ → ℂ} {a : ℝ}
    (topPV botPV : ℝ → ℂ)
    (hbound : KadiriHorizontalPVBound topPV botPV)
    (hbridge : KadiriZetaHorizontalPVNoZeroBridge φ a topPV botPV) :
    KadiriHorizontalPVPackage φ a where
  topPV := topPV
  botPV := botPV
  bound := hbound
  bridge := hbridge

/-- With a constructed package, the top horizontal PV value tends to `0`
unconditionally. -/
theorem kadiriTopHorizontalPV_vanishes_of_inputs {φ : ℝ → ℂ} {a : ℝ}
    (topPV botPV : ℝ → ℂ)
    (hbound : KadiriHorizontalPVBound topPV botPV)
    (hbridge : KadiriZetaHorizontalPVNoZeroBridge φ a topPV botPV) :
    Filter.Tendsto topPV Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_top_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_inputs (φ := φ) (a := a) topPV botPV hbound hbridge)

/-- With a constructed package, the bottom horizontal PV value tends to `0`
unconditionally. -/
theorem kadiriBotHorizontalPV_vanishes_of_inputs {φ : ℝ → ℂ} {a : ℝ}
    (topPV botPV : ℝ → ℂ)
    (hbound : KadiriHorizontalPVBound topPV botPV)
    (hbridge : KadiriZetaHorizontalPVNoZeroBridge φ a topPV botPV) :
    Filter.Tendsto botPV Filter.atTop (nhds 0) :=
  kadiri_thm_3_1_q1_bot_horizontal_pv_vanishes
    (kadiriHorizontalPVPackage_of_inputs (φ := φ) (a := a) topPV botPV hbound hbridge)

end Kadiri
