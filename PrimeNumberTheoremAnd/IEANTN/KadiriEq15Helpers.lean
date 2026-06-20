import PrimeNumberTheoremAnd.IEANTN.KadiriEq12Foundations
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-!
# Kadiri eq.(15) helpers — the digamma simple-pole residue at `0`

The eq.(15) integrand `½(digamma(s/2) + digamma((1-s)/2))·Φ(-s)` is meromorphic on the
contour rectangle with a single simple pole at `s = 0`, coming entirely from `digamma(s/2)`
(the reflected term `digamma((1-s)/2) → digamma(1/2)` is analytic there). This file isolates
that pole.

`digamma(s/2) = digamma(s/2+1) - (s/2)⁻¹` by the digamma recurrence, and `digamma(s/2+1)` is
analytic at `0` (`Re(s/2+1) → 1 > 0`), so `digamma(s/2)` has principal part `-2/s`, i.e. a
simple pole with residue `-2`. Feeding this into the principal-part residue lemmas gives the
residue of the full first-moment integrand, `-Φ(0)` once the `½` and the `Ψ(0)` are folded in.
-/

open Complex Filter Asymptotics
open scoped Topology

namespace Kadiri

noncomputable section

/-- Principal-part big-O: `digamma(s/2)` minus its simple pole `-2/s` stays bounded near `0`.
This is the single analytic input behind the eq.(15) residue. -/
theorem digamma_half_sub_principal_isBigO :
    ((fun s : ℂ => digamma (s / 2)) - fun z : ℂ => (-2) / (z - 0))
      =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
  have htd : Tendsto (fun s : ℂ => digamma (s / 2 + 1)) (𝓝[≠] (0 : ℂ)) (nhds (digamma 1)) := by
    have hda : ContinuousAt digamma 1 :=
      (analyticAt_digamma_of_re_pos (z₀ := (1 : ℂ)) (by norm_num)).continuousAt
    have hg : ContinuousAt (fun s : ℂ => s / 2 + 1) 0 := by fun_prop
    simpa [Function.comp_def] using
      (hda.comp_of_eq hg (by norm_num)).tendsto.mono_left nhdsWithin_le_nhds
  have hO : (fun s : ℂ => digamma (s / 2 + 1)) =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := htd.isBigO_one ℂ
  have hbridge : ((fun s : ℂ => digamma (s / 2)) - fun z : ℂ => (-2) / (z - 0))
      =ᶠ[𝓝[≠] (0 : ℂ)] (fun s : ℂ => digamma (s / 2 + 1)) := by
    have hball : ∀ᶠ s : ℂ in 𝓝[≠] (0 : ℂ), s ≠ 0 ∧ ‖s‖ < 1 := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)] with s hs0 hsb
      exact ⟨hs0, by simpa [Metric.mem_ball, Complex.dist_eq] using hsb⟩
    filter_upwards [hball] with s hs
    obtain ⟨hs0, hsb⟩ := hs
    have hnn : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m
      rcases m with _ | k
      · have : s / 2 ≠ 0 := div_ne_zero hs0 (by norm_num)
        simpa using this
      · intro hc
        have h1 : ‖s / 2‖ = (k : ℝ) + 1 := by
          rw [hc, norm_neg, Complex.norm_natCast]; push_cast; ring
        have h2 : ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div]; norm_num
        rw [h2] at h1; linarith [hsb, Nat.cast_nonneg (α := ℝ) k]
    have hrec : digamma (s / 2 + 1) = digamma (s / 2) + (s / 2)⁻¹ :=
      Complex.digamma_apply_add_one (s / 2) hnn
    have hps : (-2 : ℂ) / s = -(s / 2)⁻¹ := by field_simp
    simp only [Pi.sub_apply, sub_zero]
    rw [hps, hrec]; ring
  exact hbridge.trans_isBigO hO

/-- The simple-pole residue of `digamma(s/2)` at `0` is `-2`. -/
theorem residue_digamma_half_zero : residue (fun s : ℂ => digamma (s / 2)) 0 = -2 :=
  residue_eq_of_sub_principal_isBigO_one digamma_half_sub_principal_isBigO

/-- The eq.(15)-shaped residue: for any `Ψ` continuous at `0`,
`residue (fun s ↦ digamma(s/2)·Ψ(s)) 0 = -2·Ψ(0)`. With `Ψ = ½·Φ(-·)` this yields the
first-moment integrand residue `-Φ(0)`. -/
theorem residue_digamma_half_mul {Ψ : ℂ → ℂ} (hΨ : ContinuousAt Ψ 0) :
    residue (fun s : ℂ => digamma (s / 2) * Ψ s) 0 = -2 * Ψ 0 :=
  residue_mul_eq_of_sub_principal_isBigO_one digamma_half_sub_principal_isBigO hΨ

end

end Kadiri
