/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import PrimeNumberTheoremAnd.IEANTN.HadamardLogDerivative
import PrimeNumberTheoremAnd.Backlund.ZeroCountCrude
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import PrimeNumberTheoremAnd.ZetaBounds
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.CriticalLineDecay
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaBinet
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Topology.Homotopy.Lifting

/-!
# Eccentric Backlund route constants

This file records small arithmetic pieces for the local eccentric-Jensen Backlund
route. The analytic Phragmen-Lindelöf, Jensen, and pairing inputs are separate
from these final numeric weakenings.
-/

open Real MeasureTheory
open scoped Interval

namespace Backlund

/-- The high-height RHS supplied by the eccentric-Jensen route. -/
noncomputable def eccentricHighRhs (T : ℝ) : ℝ :=
  0.120 * Real.log T + 0.275 * Real.log (Real.log T) + 5.13

/-- Kadiri's published Backlund RHS in the project convention. -/
noncomputable def kadiriRhs (T : ℝ) : ℝ :=
  riemannZeta.RvM 0.137 0.443 6.1 T

/--
On the `σ = 1` edge, the in-tree Euler-Maclaurin estimate gives
`|ζ(1+it)| ≤ C log |t|` for some fixed positive constant.
-/
theorem zeta_one_line_le_const_mul_log :
    ∃ C > 0, ∀ t : ℝ, 3 < |t| →
      ‖riemannZeta ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Real.log |t| := by
  obtain ⟨A, hA, C, hC, hζ⟩ := ZetaUpperBnd
  refine ⟨C, hC, ?_⟩
  intro t ht
  have hlog_pos : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hσ : (1 : ℝ) ∈ Set.Icc (1 - A / Real.log |t|) 2 := by
    constructor
    · have hdiv_nonneg : 0 ≤ A / Real.log |t| := div_nonneg hA.1.le hlog_pos.le
      linarith
    · norm_num
  simpa using hζ 1 t ht hσ

noncomputable def unitNormalize (z : ℂ) (hz : z ≠ 0) : Circle where
  val := z / (‖z‖ : ℂ)
  property := by
    simp [Submonoid.unitSphere, div_self (norm_ne_zero_iff.mpr hz)]

@[simp] theorem coe_unitNormalize (z : ℂ) (hz : z ≠ 0) :
    ((unitNormalize z hz : Circle) : ℂ) = z / (‖z‖ : ℂ) := rfl

noncomputable def normalizeNonzeroPath {a b : ℝ} (f : C(Set.Icc a b, ℂ))
    (hf : ∀ x, f x ≠ 0) : C(Set.Icc a b, Circle) where
  toFun x := unitNormalize (f x) (hf x)
  continuous_toFun := by
    exact Continuous.subtype_mk
      (f.continuous.div (by fun_prop)
        (by intro x; exact_mod_cast norm_ne_zero_iff.mpr (hf x)))
      (by intro x; exact (unitNormalize (f x) (hf x)).property)

structure PhaseLift {a b : ℝ} (γ : C(Set.Icc a b, Circle)) where
  phase : C(Set.Icc a b, ℝ)
  exp_phase : ∀ x, Circle.exp (phase x) = γ x

noncomputable def PhaseLift.change {a b : ℝ} {γ : C(Set.Icc a b, Circle)}
    (θ : PhaseLift γ) (x₀ x : Set.Icc a b) : ℝ :=
  θ.phase x - θ.phase x₀

noncomputable def PhaseLift.leftEndpointChange {a b : ℝ} (h : a ≤ b)
    {γ : C(Set.Icc a b, Circle)} (θ : PhaseLift γ) (x : Set.Icc a b) : ℝ :=
  θ.change ⟨a, by exact ⟨le_rfl, h⟩⟩ x

noncomputable def circlePathOnUnitInterval {a b : ℝ} (h : a < b)
    (γ : C(Set.Icc a b, Circle)) : C(unitInterval, Circle) :=
  γ.comp ((iccHomeoI a b h).symm : C(unitInterval, Set.Icc a b))

noncomputable def phaseLiftOfCirclePath {a b : ℝ} (h : a < b)
    (γ : C(Set.Icc a b, Circle)) : PhaseLift γ := by
  let xleft : Set.Icc a b := ⟨a, by constructor <;> linarith⟩
  let γI : C(unitInterval, Circle) := circlePathOnUnitInterval h γ
  let e0 : ℝ := ((γ xleft : Circle) : ℂ).arg
  have h0 : γI 0 = Circle.exp e0 := by
    dsimp [γI, circlePathOnUnitInterval, e0, xleft]
    have hsymm : ((iccHomeoI a b h).symm (0 : unitInterval) : ℝ) = a := by
      rw [iccHomeoI_symm_apply_coe]
      norm_num
    have hsub : (iccHomeoI a b h).symm (0 : unitInterval) =
        (⟨a, by constructor <;> linarith⟩ : Set.Icc a b) := by
      exact Subtype.ext hsymm
    rw [hsub]
    exact (Circle.exp_arg (γ ⟨a, by constructor <;> linarith⟩)).symm
  let θI : C(unitInterval, ℝ) := Circle.isCoveringMap_exp.liftPath γI e0 h0
  let phase : C(Set.Icc a b, ℝ) :=
    θI.comp (iccHomeoI a b h : C(Set.Icc a b, unitInterval))
  refine ⟨phase, ?_⟩
  intro x
  dsimp [phase]
  have hlift := Circle.isCoveringMap_exp.liftPath_lifts γI e0 h0
  have hpoint := congrFun hlift ((iccHomeoI a b h) x)
  calc
    Circle.exp (θI ((iccHomeoI a b h) x)) = γI ((iccHomeoI a b h) x) := hpoint
    _ = γ x := by
      dsimp [γI, circlePathOnUnitInterval]
      exact congrArg γ ((iccHomeoI a b h).left_inv x)

theorem phaseLiftOfCirclePath_exp_phase {a b : ℝ} (h : a < b)
    (γ : C(Set.Icc a b, Circle)) (x : Set.Icc a b) :
    Circle.exp ((phaseLiftOfCirclePath h γ).phase x) = γ x :=
  (phaseLiftOfCirclePath h γ).exp_phase x

noncomputable def phaseLiftOfNonzeroPath {a b : ℝ} (h : a < b)
    (f : C(Set.Icc a b, ℂ)) (hf : ∀ x, f x ≠ 0) :
    PhaseLift (normalizeNonzeroPath f hf) :=
  phaseLiftOfCirclePath h (normalizeNonzeroPath f hf)

theorem phaseLiftOfNonzeroPath_exp_phase {a b : ℝ} (h : a < b)
    (f : C(Set.Icc a b, ℂ)) (hf : ∀ x, f x ≠ 0) (x : Set.Icc a b) :
    Circle.exp ((phaseLiftOfNonzeroPath h f hf).phase x) =
      unitNormalize (f x) (hf x) :=
  (phaseLiftOfNonzeroPath h f hf).exp_phase x

theorem re_pow_eq_zero_iff_cos_phase_eq_zero (N : ℕ) {z : ℂ} {θ : ℝ}
    (hz : z ≠ 0) (hθ : Circle.exp θ = unitNormalize z hz) :
    (z ^ N).re = 0 ↔ Real.cos ((N : ℝ) * θ) = 0 := by
  have hnorm_ne : (‖z‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hz
  have hcoe : Complex.exp (θ * Complex.I) = z / (‖z‖ : ℂ) := by
    have h := congrArg (fun w : Circle => (w : ℂ)) hθ
    simpa [unitNormalize] using h
  have hz_eq : z = (‖z‖ : ℂ) * Complex.exp (θ * Complex.I) := by
    calc
      z = (‖z‖ : ℂ) * (z / (‖z‖ : ℂ)) := by
        field_simp [hnorm_ne]
      _ = (‖z‖ : ℂ) * Complex.exp (θ * Complex.I) := by
        rw [← hcoe]
  have hexp_pow :
      (Complex.exp (θ * Complex.I)) ^ N =
        Complex.exp (((N : ℝ) * θ : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hpow :
      z ^ N =
        ((‖z‖ ^ N : ℝ) : ℂ) *
          Complex.exp (((N : ℝ) * θ : ℂ) * Complex.I) := by
    calc
      z ^ N = ((‖z‖ : ℂ) * Complex.exp (θ * Complex.I)) ^ N :=
        congrArg (fun w : ℂ => w ^ N) hz_eq
      _ = (‖z‖ : ℂ) ^ N * (Complex.exp (θ * Complex.I)) ^ N := by
        rw [mul_pow]
      _ = ((‖z‖ ^ N : ℝ) : ℂ) *
          Complex.exp (((N : ℝ) * θ : ℂ) * Complex.I) := by
        rw [← Complex.ofReal_pow, hexp_pow]
  have hexp_re :
      (Complex.exp (((N : ℝ) * θ : ℂ) * Complex.I)).re =
        Real.cos ((N : ℝ) * θ) := by
    simpa using Complex.exp_ofReal_mul_I_re ((N : ℝ) * θ)
  have hre : (z ^ N).re = ‖z‖ ^ N * Real.cos ((N : ℝ) * θ) := by
    rw [hpow, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hexp_re]
  rw [hre]
  have hnorm_pow_ne : ‖z‖ ^ N ≠ 0 :=
    pow_ne_zero N (norm_ne_zero_iff.mpr hz)
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hnorm_pow_ne
  · intro h
    simp [h]

theorem phaseLiftOfNonzeroPath_re_pow_eq_zero_iff {a b : ℝ} (h : a < b)
    (f : C(Set.Icc a b, ℂ)) (hf : ∀ x, f x ≠ 0) (N : ℕ)
    (x : Set.Icc a b) :
    (f x ^ N).re = 0 ↔
      Real.cos ((N : ℝ) * (phaseLiftOfNonzeroPath h f hf).phase x) = 0 := by
  exact re_pow_eq_zero_iff_cos_phase_eq_zero N (hf x)
    (phaseLiftOfNonzeroPath_exp_phase h f hf x)

def firstHitSubtypeSet {D : ℝ} (u : C(Set.Icc (0 : ℝ) D, ℝ)) (target : ℝ) :
    Set (Set.Icc (0 : ℝ) D) :=
  {x | u x = target}

def firstHitRealSet (D : ℝ) (u : C(Set.Icc (0 : ℝ) D, ℝ)) (target : ℝ) : Set ℝ :=
  {d | ∃ hd : d ∈ Set.Icc (0 : ℝ) D, u ⟨d, hd⟩ = target}

private theorem firstHitSubtypeSet_isClosed {D : ℝ}
    (u : C(Set.Icc (0 : ℝ) D, ℝ)) (target : ℝ) :
    IsClosed (firstHitSubtypeSet u target) := by
  unfold firstHitSubtypeSet
  exact isClosed_eq u.continuous continuous_const

private theorem firstHitSubtypeSet_nonempty_of_real {D : ℝ}
    {u : C(Set.Icc (0 : ℝ) D, ℝ)} {target : ℝ}
    (hne : (firstHitRealSet D u target).Nonempty) :
    (firstHitSubtypeSet u target).Nonempty := by
  rcases hne with ⟨d, hdI, hdu⟩
  exact ⟨⟨d, hdI⟩, hdu⟩

noncomputable def firstHitPoint {D : ℝ} (u : C(Set.Icc (0 : ℝ) D, ℝ))
    (target : ℝ) (hne : (firstHitRealSet D u target).Nonempty) :
    Set.Icc (0 : ℝ) D :=
  Classical.choose <|
    (firstHitSubtypeSet_isClosed u target).isCompact.exists_isLeast
      (firstHitSubtypeSet_nonempty_of_real hne)

noncomputable def firstHit {D : ℝ} (u : C(Set.Icc (0 : ℝ) D, ℝ))
    (target : ℝ) (hne : (firstHitRealSet D u target).Nonempty) : ℝ :=
  firstHitPoint u target hne

theorem firstHitPoint_isLeast {D : ℝ} (u : C(Set.Icc (0 : ℝ) D, ℝ))
    (target : ℝ) (hne : (firstHitRealSet D u target).Nonempty) :
    IsLeast (firstHitSubtypeSet u target) (firstHitPoint u target hne) :=
  Classical.choose_spec <|
    (firstHitSubtypeSet_isClosed u target).isCompact.exists_isLeast
      (firstHitSubtypeSet_nonempty_of_real hne)

theorem firstHit_mem_Icc {D : ℝ} (u : C(Set.Icc (0 : ℝ) D, ℝ))
    (target : ℝ) (hne : (firstHitRealSet D u target).Nonempty) :
    firstHit u target hne ∈ Set.Icc (0 : ℝ) D :=
  (firstHitPoint u target hne).property

theorem firstHit_mem {D : ℝ} (u : C(Set.Icc (0 : ℝ) D, ℝ))
    (target : ℝ) (hne : (firstHitRealSet D u target).Nonempty) :
    firstHit u target hne ∈ firstHitRealSet D u target := by
  refine ⟨firstHit_mem_Icc u target hne, ?_⟩
  exact (firstHitPoint_isLeast u target hne).1

theorem firstHit_isLeast {D : ℝ} (u : C(Set.Icc (0 : ℝ) D, ℝ))
    (target : ℝ) (hne : (firstHitRealSet D u target).Nonempty) :
    IsLeast (firstHitRealSet D u target) (firstHit u target hne) := by
  constructor
  · exact firstHit_mem u target hne
  · intro y hy
    rcases hy with ⟨hyI, hyu⟩
    have hleast := firstHitPoint_isLeast u target hne
    have hy_sub : (⟨y, hyI⟩ : Set.Icc (0 : ℝ) D) ∈ firstHitSubtypeSet u target := hyu
    exact hleast.2 hy_sub

theorem firstHit_eq_of_nonempty {D : ℝ} (u : C(Set.Icc (0 : ℝ) D, ℝ))
    (target : ℝ) (hne₁ hne₂ : (firstHitRealSet D u target).Nonempty) :
    firstHit u target hne₁ = firstHit u target hne₂ := by
  have h₁ := firstHit_isLeast u target hne₁
  have h₂ := firstHit_isLeast u target hne₂
  exact le_antisymm (h₁.2 h₂.1) (h₂.2 h₁.1)

theorem firstHit_le_of_start_lt_target_of_target_lt_value {D : ℝ}
    (u : C(Set.Icc (0 : ℝ) D, ℝ)) {target d : ℝ}
    (hd : d ∈ Set.Icc (0 : ℝ) D)
    (hstart : u ⟨0, by exact ⟨le_rfl, le_trans hd.1 hd.2⟩⟩ < target)
    (hvalue : target < u ⟨d, hd⟩) :
    ∃ hne : (firstHitRealSet D u target).Nonempty,
      firstHit u target hne ≤ d := by
  have hD : (0 : ℝ) ≤ D := le_trans hd.1 hd.2
  let f : ℝ → ℝ := fun x => u (Set.projIcc (0 : ℝ) D hD x)
  have hf : Continuous f := u.continuous.comp continuous_projIcc
  have hf0 : f 0 = u ⟨0, by exact ⟨le_rfl, hD⟩⟩ := by
    dsimp [f]
    rw [Set.projIcc_of_mem hD]
  have hfd : f d = u ⟨d, hd⟩ := by
    dsimp [f]
    rw [Set.projIcc_of_mem hD hd]
  have htarget : target ∈ Set.Icc (f 0) (f d) := by
    exact ⟨by simpa [hf0] using hstart.le, by simpa [hfd] using hvalue.le⟩
  have hIVT := intermediate_value_Icc hd.1 hf.continuousOn htarget
  rcases hIVT with ⟨x, hxI, hxval_f⟩
  have hxD : x ∈ Set.Icc (0 : ℝ) D := ⟨hxI.1, hxI.2.trans hd.2⟩
  have hxval : u ⟨x, hxD⟩ = target := by
    have hproj : Set.projIcc (0 : ℝ) D hD x = ⟨x, hxD⟩ :=
      Set.projIcc_of_mem hD hxD
    simpa [f, hproj] using hxval_f
  have hne : (firstHitRealSet D u target).Nonempty := by
    exact ⟨x, hxD, hxval⟩
  refine ⟨hne, ?_⟩
  have hx_hit : x ∈ firstHitRealSet D u target := by
    exact ⟨hxD, hxval⟩
  have hfirst_le_x : firstHit u target hne ≤ x :=
    (firstHit_isLeast u target hne).2 hx_hit
  exact hfirst_le_x.trans hxI.2

theorem firstHit_le_of_abs_error_at_value {D : ℝ}
    (v : C(Set.Icc (0 : ℝ) D, ℝ)) {target d value ε : ℝ}
    (hd : d ∈ Set.Icc (0 : ℝ) D)
    (hstart : v ⟨0, by exact ⟨le_rfl, le_trans hd.1 hd.2⟩⟩ < target)
    (herr : |value - v ⟨d, hd⟩| < ε)
    (hgap : target + ε ≤ value) :
    ∃ hne : (firstHitRealSet D v target).Nonempty,
      firstHit v target hne ≤ d := by
  have hdiff : value - v ⟨d, hd⟩ < ε := (abs_lt.mp herr).2
  have hvalue : target < v ⟨d, hd⟩ := by
    linarith
  exact firstHit_le_of_start_lt_target_of_target_lt_value
    (u := v) (target := target) (d := d) hd hstart hvalue

theorem firstHit_le_firstHit_of_abs_error_at_firstHit {D : ℝ}
    (u v : C(Set.Icc (0 : ℝ) D, ℝ)) (hD : (0 : ℝ) ≤ D)
    {leftTarget rightTarget ε : ℝ}
    (hright : (firstHitRealSet D u rightTarget).Nonempty)
    (hstart : v ⟨0, by exact ⟨le_rfl, hD⟩⟩ < leftTarget)
    (herr : ∀ x : Set.Icc (0 : ℝ) D, |u x - v x| < ε)
    (hgap : leftTarget + ε ≤ rightTarget) :
    ∃ hleft : (firstHitRealSet D v leftTarget).Nonempty,
      firstHit v leftTarget hleft ≤ firstHit u rightTarget hright := by
  let d : ℝ := firstHit u rightTarget hright
  have hd : d ∈ Set.Icc (0 : ℝ) D := by
    simpa [d] using firstHit_mem_Icc u rightTarget hright
  have hhit := firstHit_mem u rightTarget hright
  have hvalue : u ⟨d, hd⟩ = rightTarget := by
    rcases hhit with ⟨hd', hval⟩
    have hsub : (⟨d, hd'⟩ : Set.Icc (0 : ℝ) D) = ⟨d, hd⟩ :=
      Subtype.ext rfl
    simpa [d, hsub] using hval
  have herr_d : |rightTarget - v ⟨d, hd⟩| < ε := by
    simpa [hvalue] using herr ⟨d, hd⟩
  exact firstHit_le_of_abs_error_at_value
    (v := v) (target := leftTarget) (d := d) (value := rightTarget)
    (ε := ε) hd (by simpa using hstart) herr_d hgap

theorem firstHit_lt_firstHit_of_start_lt_of_target_lt {D : ℝ}
    (u : C(Set.Icc (0 : ℝ) D, ℝ)) {target₁ target₂ : ℝ}
    (hD : (0 : ℝ) ≤ D)
    (hstart : u ⟨0, by exact ⟨le_rfl, hD⟩⟩ < target₁)
    (htarget : target₁ < target₂)
    (hne₂ : (firstHitRealSet D u target₂).Nonempty) :
    ∃ hne₁ : (firstHitRealSet D u target₁).Nonempty,
      firstHit u target₁ hne₁ < firstHit u target₂ hne₂ := by
  let d₂ : ℝ := firstHit u target₂ hne₂
  have hd₂ : d₂ ∈ Set.Icc (0 : ℝ) D := by
    simpa [d₂] using firstHit_mem_Icc u target₂ hne₂
  have hhit₂ := firstHit_mem u target₂ hne₂
  have hval₂ : u ⟨d₂, hd₂⟩ = target₂ := by
    rcases hhit₂ with ⟨hd₂', hval₂'⟩
    have hsub : (⟨d₂, hd₂'⟩ : Set.Icc (0 : ℝ) D) = ⟨d₂, hd₂⟩ :=
      Subtype.ext rfl
    simpa [d₂, hsub] using hval₂'
  have hstart' :
      u ⟨0, by exact ⟨le_rfl, le_trans hd₂.1 hd₂.2⟩⟩ < target₁ := by
    simpa using hstart
  obtain ⟨hne₁, hle⟩ :=
    firstHit_le_of_start_lt_target_of_target_lt_value
      (u := u) (target := target₁) (d := d₂) hd₂ hstart'
      (by simpa [hval₂] using htarget)
  refine ⟨hne₁, lt_of_le_of_ne hle ?_⟩
  intro heq
  have hhit₁ := firstHit_mem u target₁ hne₁
  have hd₁ : firstHit u target₁ hne₁ ∈ Set.Icc (0 : ℝ) D :=
    firstHit_mem_Icc u target₁ hne₁
  have hval₁ : u ⟨firstHit u target₁ hne₁, hd₁⟩ = target₁ := by
    rcases hhit₁ with ⟨hd₁', hval₁'⟩
    have hsub :
        (⟨firstHit u target₁ hne₁, hd₁'⟩ : Set.Icc (0 : ℝ) D) =
          ⟨firstHit u target₁ hne₁, hd₁⟩ :=
      Subtype.ext rfl
    simpa [hsub] using hval₁'
  have hsubeq :
      (⟨firstHit u target₁ hne₁, hd₁⟩ : Set.Icc (0 : ℝ) D) = ⟨d₂, hd₂⟩ :=
    Subtype.ext heq
  have hval₁_at_d₂ : u ⟨d₂, hd₂⟩ = target₁ := by
    simpa [hsubeq] using hval₁
  linarith

theorem firstHit_strictMono_of_strictMono_targets {D : ℝ} {m : ℕ}
    (u : C(Set.Icc (0 : ℝ) D, ℝ)) (targets : Fin m → ℝ)
    (hD : (0 : ℝ) ≤ D)
    (hstart : ∀ i : Fin m, u ⟨0, by exact ⟨le_rfl, hD⟩⟩ < targets i)
    (htargets : StrictMono targets)
    (hne : ∀ i : Fin m, (firstHitRealSet D u (targets i)).Nonempty) :
    StrictMono fun i : Fin m => firstHit u (targets i) (hne i) := by
  intro i j hij
  obtain ⟨hne_i', hlt⟩ := firstHit_lt_firstHit_of_start_lt_of_target_lt
    (u := u) (target₁ := targets i) (target₂ := targets j)
    hD (hstart i) (htargets hij) (hne j)
  have heq :
      firstHit u (targets i) hne_i' = firstHit u (targets i) (hne i) :=
    firstHit_eq_of_nonempty u (targets i) hne_i' (hne i)
  simpa [← heq] using hlt

theorem firstHit_phaseLift_re_pow_eq_zero {D : ℝ}
    (f : C(Set.Icc (0 : ℝ) D, ℂ)) (hf : ∀ x, f x ≠ 0)
    (θ : PhaseLift (normalizeNonzeroPath f hf)) (N : ℕ) {target : ℝ}
    (hcos : Real.cos ((N : ℝ) * target) = 0)
    (hne : (firstHitRealSet D θ.phase target).Nonempty) :
    (f (firstHitPoint θ.phase target hne) ^ N).re = 0 := by
  have hphase : θ.phase (firstHitPoint θ.phase target hne) = target :=
    (firstHitPoint_isLeast θ.phase target hne).1
  exact (re_pow_eq_zero_iff_cos_phase_eq_zero N
    (hf (firstHitPoint θ.phase target hne))
    (θ.exp_phase (firstHitPoint θ.phase target hne))).2
    (by simpa [hphase] using hcos)

/-- Target phases whose `N`-fold argument has zero cosine. -/
noncomputable def backlundCosZeroTarget (N k : ℕ) : ℝ :=
  (Real.pi / 2 + (k : ℝ) * Real.pi) / (N : ℝ)

theorem backlundCosZeroTarget_cos_eq_zero {N k : ℕ} (hN : 0 < N) :
    Real.cos ((N : ℝ) * backlundCosZeroTarget N k) = 0 := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hmul :
      (N : ℝ) * backlundCosZeroTarget N k =
        Real.pi / 2 + (k : ℝ) * Real.pi := by
    unfold backlundCosZeroTarget
    field_simp [hNne]
  rw [hmul]
  have hk : (k : ℝ) * Real.pi = ((k : ℤ) : ℝ) * Real.pi := by norm_num
  rw [hk, Real.cos_add]
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

theorem strictMono_backlundCosZeroTarget {N m : ℕ} (hN : 0 < N) :
    StrictMono fun i : Fin m => backlundCosZeroTarget N (i : ℕ) := by
  intro i j hij
  unfold backlundCosZeroTarget
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hij' : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
  exact div_lt_div_of_pos_right (by nlinarith [Real.pi_pos]) hNpos

noncomputable def backlundA (s : ℂ) : ℂ := (s - 1) * riemannZeta s

theorem backlundA_conj (z : ℂ) :
    backlundA (star z) = star (backlundA z) := by
  simp [backlundA, riemannZeta_conj]

noncomputable def backlundAHorizontalPathFrom (x₀ D T : ℝ) (hT : T ≠ 0) :
    C(Set.Icc (0 : ℝ) D, ℂ) where
  toFun d := backlundA (((x₀ + (d : ℝ) : ℝ) : ℂ) + (T : ℂ) * Complex.I)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro d
    let p : Set.Icc (0 : ℝ) D → ℂ :=
      fun d => (((x₀ + (d : ℝ) : ℝ) : ℂ) + (T : ℂ) * Complex.I)
    have hp_cont : Continuous p := by
      fun_prop
    have hp_ne_one : p d ≠ 1 := by
      intro h
      have him := congrArg Complex.im h
      have him' : T = 0 := by
        simpa [p, Complex.add_im, Complex.mul_im] using him
      exact hT him'
    have hbacklund_cont : ContinuousAt backlundA (p d) := by
      unfold backlundA
      exact ((continuousAt_id.sub continuousAt_const).mul
        ((differentiableAt_riemannZeta hp_ne_one).continuousAt))
    have hcomp : ContinuousAt (fun y => backlundA (p y)) d :=
      hbacklund_cont.comp hp_cont.continuousAt
    simpa [p] using hcomp

theorem logDeriv_backlundA_eq_zeta {s : ℂ}
    (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    logDeriv backlundA s = 1 / (s - 1) + deriv riemannZeta s / riemannZeta s := by
  unfold backlundA
  have hfactor : (fun z : ℂ => z - 1) s ≠ 0 := sub_ne_zero.mpr hs1
  have hfactor_diff : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := by
    fun_prop
  have hzeta_diff : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs1
  rw [logDeriv_mul s hfactor hζ hfactor_diff hzeta_diff]
  simp [logDeriv_apply, div_eq_mul_inv]

theorem logDeriv_backlundA_add_reflected_eq_archimedean {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hζs : riemannZeta s ≠ 0)
    (hζ1s : riemannZeta (1 - s) ≠ 0) :
    logDeriv backlundA s + logDeriv backlundA (1 - s) =
      1 / (s - 1) + 1 / ((1 - s) - 1) +
        ((Real.log Real.pi : ℝ) : ℂ) -
        (1 / 2 : ℂ) * (Complex.digamma (s / 2) +
          Complex.digamma ((1 - s) / 2)) := by
  have h1s_ne_one : (1 : ℂ) - s ≠ 1 := by
    intro h
    apply hs0
    calc
      s = 1 - (1 - s) := by ring
      _ = 0 := by rw [h]; ring
  have hs_log := logDeriv_backlundA_eq_zeta (s := s) hs1 hζs
  have h1s_log := logDeriv_backlundA_eq_zeta (s := 1 - s) h1s_ne_one hζ1s
  have hfe := Kadiri.zeta_logDeriv_functional_eq
    (s := s) hs1 hs0 hζs hζ1s
  rw [Complex.ofReal_neg] at hfe
  rw [hs_log, h1s_log]
  linear_combination -hfe

/-- The archimedean integrand left after adding reflected `A` log-derivatives. -/
noncomputable def backlundArchimedeanSymmetryIntegrand (s : ℂ) : ℂ :=
  1 / (s - 1) + 1 / ((1 - s) - 1) +
    ((Real.log Real.pi : ℝ) : ℂ) -
    (1 / 2 : ℂ) * (Complex.digamma (s / 2) +
      Complex.digamma ((1 - s) / 2))

theorem reflected_half_ne_neg_nat_of_im_ne_zero {s : ℂ} (him : s.im ≠ 0) :
    ∀ n : ℕ, (1 - s) / 2 ≠ -↑n := by
  intro n h
  apply him
  have h_im := congrArg Complex.im h
  simp [Complex.sub_im] at h_im
  linarith

theorem backlundArchimedeanSymmetryIntegrand_eq_shifted_digamma {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hpoles : ∀ n : ℕ, (1 - s) / 2 ≠ -↑n) :
    backlundArchimedeanSymmetryIntegrand s =
      -1 / s + ((Real.log Real.pi : ℝ) : ℂ) -
        (1 / 2 : ℂ) * (Complex.digamma (s / 2) +
          Complex.digamma ((3 - s) / 2)) := by
  have hrec0 := Complex.digamma_apply_add_one ((1 - s) / 2) hpoles
  have harg : (1 - s) / 2 + 1 = (3 - s) / 2 := by ring
  rw [harg] at hrec0
  have hrec : Complex.digamma ((1 - s) / 2) =
      Complex.digamma ((3 - s) / 2) - ((1 - s) / 2)⁻¹ := by
    linear_combination -hrec0
  unfold backlundArchimedeanSymmetryIntegrand
  rw [hrec]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs_sub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp [hs0, h1s, hs_sub]
  ring_nf

theorem arctan_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.arctan x ≤ x := by
  by_cases hsmall : x < Real.pi / 2
  · have htan : x ≤ Real.tan x := Real.le_tan hx hsmall
    have hmono : Real.arctan x ≤ Real.arctan (Real.tan x) := Real.arctan_mono htan
    rwa [Real.arctan_tan (by linarith) hsmall] at hmono
  · have hpi : Real.pi / 2 ≤ x := le_of_not_gt hsmall
    exact le_trans (le_of_lt (Real.arctan_lt_pi_div_two x)) hpi

theorem abs_arctan_le_abs_self (x : ℝ) :
    |Real.arctan x| ≤ |x| := by
  by_cases hx : 0 ≤ x
  · have hnonneg : 0 ≤ Real.arctan x := Real.arctan_nonneg.mpr hx
    rw [abs_of_nonneg hnonneg, abs_of_nonneg hx]
    exact arctan_le_self_of_nonneg hx
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hatan_nonpos : Real.arctan x ≤ 0 := Real.arctan_le_zero.mpr hxneg.le
    rw [abs_of_nonpos hatan_nonpos, abs_of_neg hxneg]
    have hpos : 0 ≤ -x := by linarith
    have h := arctan_le_self_of_nonneg hpos
    rw [Real.arctan_neg] at h
    linarith

theorem arg_eq_arctan_im_div_re_of_re_pos {z : ℂ} (hre : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) := by
  symm
  apply Real.arctan_eq_of_tan_eq
  · rw [Complex.tan_arg]
  · constructor
    · rw [Complex.neg_pi_div_two_lt_arg_iff]
      exact Or.inl hre
    · rw [Complex.arg_lt_pi_div_two_iff]
      exact Or.inl hre

theorem abs_arg_le_abs_im_div_re_of_re_pos {z : ℂ} (hre : 0 < z.re) :
    |z.arg| ≤ |z.im / z.re| := by
  rw [arg_eq_arctan_im_div_re_of_re_pos hre]
  exact abs_arctan_le_abs_self _

theorem arg_add_mem_Ioc_of_re_pos {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    z.arg + w.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
  have hzlo : -(Real.pi / 2) < z.arg := by
    rw [Complex.neg_pi_div_two_lt_arg_iff]
    exact Or.inl hz
  have hzhi : z.arg < Real.pi / 2 := by
    rw [Complex.arg_lt_pi_div_two_iff]
    exact Or.inl hz
  have hwlo : -(Real.pi / 2) < w.arg := by
    rw [Complex.neg_pi_div_two_lt_arg_iff]
    exact Or.inl hw
  have hwhi : w.arg < Real.pi / 2 := by
    rw [Complex.arg_lt_pi_div_two_iff]
    exact Or.inl hw
  constructor <;> linarith

theorem abs_im_log_add_log_le_mul_im_div_re {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re) (hzw : 0 < (z * w).re) :
    |(Complex.log z + Complex.log w).im| ≤ |(z * w).im / (z * w).re| := by
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num at hz
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  have hlog := Complex.log_mul hzne hwne (arg_add_mem_Ioc_of_re_pos hz hw)
  rw [← hlog, Complex.log_im]
  exact abs_arg_le_abs_im_div_re_of_re_pos hzw

theorem half_reflected_half_product_re (x T : ℝ) :
    ((((x : ℂ) + (T : ℂ) * Complex.I) / 2) *
      (((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2)).re =
        (x * (3 - x) + T ^ 2) / 4 := by
  norm_num [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.normSq,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]
  ring

theorem half_reflected_half_product_im (x T : ℝ) :
    ((((x : ℂ) + (T : ℂ) * Complex.I) / 2) *
      (((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2)).im =
        T * (3 - 2 * x) / 4 := by
  norm_num [Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]
  ring

theorem abs_half_reflected_half_product_im_div_re_le {x T : ℝ}
    (hxl : (1 / 2 : ℝ) ≤ x) (hxu : x ≤ 1 + 3 / 50) (hT : 0 < T) :
    let p : ℂ := (((x : ℂ) + (T : ℂ) * Complex.I) / 2) *
      (((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2)
    |(p.im / p.re)| ≤ 2 / T := by
  dsimp only
  rw [half_reflected_half_product_re, half_reflected_half_product_im]
  have hx_nonneg : 0 ≤ x := by linarith
  have hx3_nonneg : 0 ≤ 3 - x := by linarith
  have hprod_nonneg : 0 ≤ x * (3 - x) := mul_nonneg hx_nonneg hx3_nonneg
  have hden_pos : 0 < (x * (3 - x) + T ^ 2) / 4 := by positivity
  have hden_ge : T ^ 2 / 4 ≤ (x * (3 - x) + T ^ 2) / 4 := by nlinarith
  have hbase_pos : 0 < T ^ 2 / 4 := by positivity
  have habs : |3 - 2 * x| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hnum : |T * (3 - 2 * x) / 4| ≤ T / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_mul, abs_of_pos hT]
    nlinarith [mul_le_mul_of_nonneg_left habs hT.le]
  calc
    |(T * (3 - 2 * x) / 4) / ((x * (3 - x) + T ^ 2) / 4)|
        = |T * (3 - 2 * x) / 4| / ((x * (3 - x) + T ^ 2) / 4) := by
          rw [abs_div, abs_of_pos hden_pos]
    _ ≤ (T / 2) / (T ^ 2 / 4) := by
          exact div_le_div₀ (by positivity) hnum hbase_pos hden_ge
    _ = 2 / T := by
          field_simp [hT.ne']
          ring

theorem abs_im_log_half_add_log_reflected_half_horizontal_le {x T : ℝ}
    (hxl : (1 / 2 : ℝ) ≤ x) (hxu : x ≤ 1 + 3 / 50) (hT : 0 < T) :
    |(Complex.log (((x : ℂ) + (T : ℂ) * Complex.I) / 2) +
        Complex.log (((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2)).im| ≤
      2 / T := by
  let z : ℂ := ((x : ℂ) + (T : ℂ) * Complex.I) / 2
  let w : ℂ := ((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2
  have hz : 0 < z.re := by
    dsimp [z]
    norm_num [Complex.div_re, Complex.normSq, Complex.add_re, Complex.mul_re]
    linarith
  have hw : 0 < w.re := by
    dsimp [w]
    norm_num [Complex.div_re, Complex.normSq, Complex.sub_re, Complex.add_re,
      Complex.mul_re]
    linarith
  have hzw : 0 < (z * w).re := by
    dsimp [z, w]
    rw [half_reflected_half_product_re]
    have hx_nonneg : 0 ≤ x := by linarith
    have hx3_nonneg : 0 ≤ 3 - x := by linarith
    have hprod_nonneg : 0 ≤ x * (3 - x) := mul_nonneg hx_nonneg hx3_nonneg
    positivity
  have hlog : |(Complex.log z + Complex.log w).im| ≤ |(z * w).im / (z * w).re| :=
    abs_im_log_add_log_le_mul_im_div_re hz hw hzw
  have hratio : |(z * w).im / (z * w).re| ≤ 2 / T := by
    exact abs_half_reflected_half_product_im_div_re_le hxl hxu hT
  exact hlog.trans hratio

theorem abs_im_digamma_sub_log_sub_half_inv_le {z : ℂ}
    (hz : (1 / 4 : ℝ) ≤ z.re) :
    |(Complex.digamma z).im - (Complex.log z - z⁻¹ / 2).im| ≤
      1 / (6 * ‖z‖ ^ 2) := by
  have h := Complex.digamma_second_order_full_norm (z := z) hz
  have h_im : |(Complex.digamma z - (Complex.log z - z⁻¹ / 2)).im| ≤
      ‖Complex.digamma z - (Complex.log z - z⁻¹ / 2)‖ :=
    Complex.abs_im_le_norm _
  have h_eq : (Complex.digamma z - (Complex.log z - z⁻¹ / 2)).im =
      (Complex.digamma z).im - (Complex.log z - z⁻¹ / 2).im := by simp
  rw [h_eq] at h_im
  exact h_im.trans h

theorem abs_im_inv_le_inv_abs_im {z : ℂ} (him : z.im ≠ 0) :
    |(z⁻¹).im| ≤ 1 / |z.im| := by
  have him_norm : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have him_pos : 0 < |z.im| := abs_pos.mpr him
  calc
    |(z⁻¹).im| ≤ ‖z⁻¹‖ := Complex.abs_im_le_norm _
    _ = ‖z‖⁻¹ := norm_inv z
    _ ≤ |z.im|⁻¹ := inv_anti₀ him_pos him_norm
    _ = 1 / |z.im| := by ring

theorem abs_im_inv_horizontal_le {x T : ℝ} (hT : T ≠ 0) :
    |(((x : ℂ) + (T : ℂ) * Complex.I)⁻¹).im| ≤ 1 / |T| := by
  have him : (((x : ℂ) + (T : ℂ) * Complex.I).im) ≠ 0 := by
    simpa [Complex.add_im, Complex.mul_im] using hT
  simpa [Complex.add_im, Complex.mul_im] using
    abs_im_inv_le_inv_abs_im
      (z := (x : ℂ) + (T : ℂ) * Complex.I) him

theorem abs_im_inv_half_horizontal_le {x T : ℝ} (hT : T ≠ 0) :
    |(((((x : ℂ) + (T : ℂ) * Complex.I) / 2)⁻¹).im)| ≤ 2 / |T| := by
  have him : ((((x : ℂ) + (T : ℂ) * Complex.I) / 2).im) ≠ 0 := by
    simp [Complex.add_im, Complex.mul_im, hT]
  have h :=
    abs_im_inv_le_inv_abs_im
      (z := ((x : ℂ) + (T : ℂ) * Complex.I) / 2) him
  calc
    |(((((x : ℂ) + (T : ℂ) * Complex.I) / 2)⁻¹).im)|
        ≤ 1 / |(((x : ℂ) + (T : ℂ) * Complex.I) / 2).im| := h
    _ = 2 / |T| := by
          norm_num [Complex.div_im, Complex.normSq, Complex.add_im,
            Complex.mul_im, abs_div]

theorem abs_im_inv_reflected_half_horizontal_le {x T : ℝ} (hT : T ≠ 0) :
    |(((((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2)⁻¹).im)| ≤
      2 / |T| := by
  have him :
      ((((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2).im) ≠ 0 := by
    simp [Complex.sub_im, Complex.add_im, Complex.mul_im, hT]
  have h :=
    abs_im_inv_le_inv_abs_im
      (z := ((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2) him
  calc
    |(((((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2)⁻¹).im)|
        ≤ 1 /
          |((((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2).im)| := h
    _ = 2 / |T| := by
          norm_num [Complex.div_im, Complex.normSq, Complex.sub_im,
            Complex.add_im, Complex.mul_im, abs_div]

theorem norm_sq_half_horizontal (x T : ℝ) :
    ‖(((x : ℂ) + (T : ℂ) * Complex.I) / 2)‖ ^ 2 =
      (x ^ 2 + T ^ 2) / 4 := by
  rw [← Complex.normSq_eq_norm_sq]
  norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.normSq,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

theorem norm_sq_reflected_half_horizontal (x T : ℝ) :
    ‖(((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2)‖ ^ 2 =
      ((3 - x) ^ 2 + T ^ 2) / 4 := by
  rw [← Complex.normSq_eq_norm_sq]
  norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.normSq,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]
  ring

theorem one_div_six_norm_sq_half_horizontal_le_inv {x T : ℝ} (hT : 1 ≤ T) :
    1 / (6 * ‖(((x : ℂ) + (T : ℂ) * Complex.I) / 2)‖ ^ 2) ≤ 1 / T := by
  have hTpos : 0 < T := by linarith
  rw [norm_sq_half_horizontal]
  apply one_div_le_one_div_of_le hTpos
  nlinarith [sq_nonneg x, hT]

theorem one_div_six_norm_sq_reflected_half_horizontal_le_inv {x T : ℝ}
    (hT : 1 ≤ T) :
    1 / (6 * ‖(((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2)‖ ^ 2) ≤
      1 / T := by
  have hTpos : 0 < T := by linarith
  rw [norm_sq_reflected_half_horizontal]
  apply one_div_le_one_div_of_le hTpos
  nlinarith [sq_nonneg (3 - x), hT]

theorem abs_im_inv_pair_average_horizontal_le {x T : ℝ} (hT : 0 < T) :
    let z₁ : ℂ := ((x : ℂ) + (T : ℂ) * Complex.I) / 2
    let z₂ : ℂ := ((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2
    |(((z₁⁻¹ + z₂⁻¹) / 2).im)| ≤ 2 / T := by
  dsimp only
  have hTne : T ≠ 0 := hT.ne'
  have h1 := abs_im_inv_half_horizontal_le (x := x) (T := T) hTne
  have h2 := abs_im_inv_reflected_half_horizontal_le (x := x) (T := T) hTne
  have hT_abs : |T| = T := abs_of_pos hT
  rw [hT_abs] at h1 h2
  let a : ℝ := (((((x : ℂ) + (T : ℂ) * Complex.I) / 2)⁻¹).im)
  let b : ℝ := (((((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2)⁻¹).im)
  have hdiv :
      (((((x : ℂ) + (T : ℂ) * Complex.I) / 2)⁻¹ +
          (((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2)⁻¹) / 2).im =
        (a + b) / 2 := by
    dsimp [a, b]
    norm_num [Complex.div_im, Complex.add_im, Complex.normSq]
  rw [hdiv]
  have ha : |a| ≤ 2 / T := by
    change |(((((x : ℂ) + (T : ℂ) * Complex.I) / 2)⁻¹).im)| ≤ 2 / T
    exact h1
  have hb : |b| ≤ 2 / T := by
    change |(((((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2)⁻¹).im)| ≤ 2 / T
    exact h2
  calc
    |(a + b) / 2| = |a + b| / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 / T + 2 / T) / 2 := by
      exact div_le_div_of_nonneg_right
        ((abs_add_le a b).trans (add_le_add ha hb)) (by norm_num)
    _ = 2 / T := by ring

theorem abs_im_digamma_half_add_reflected_half_horizontal_le {x T : ℝ}
    (hxl : (1 / 2 : ℝ) ≤ x) (hxu : x ≤ 1 + 3 / 50) (hT : 1 ≤ T) :
    |(Complex.digamma (((x : ℂ) + (T : ℂ) * Complex.I) / 2) +
        Complex.digamma (((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2)).im| ≤
      6 / T := by
  let z₁ : ℂ := ((x : ℂ) + (T : ℂ) * Complex.I) / 2
  let z₂ : ℂ := ((3 : ℂ) - ((x : ℂ) + (T : ℂ) * Complex.I)) / 2
  have hTpos : 0 < T := by linarith
  have hz₁re : (1 / 4 : ℝ) ≤ z₁.re := by
    dsimp [z₁]
    norm_num [Complex.div_re, Complex.normSq, Complex.add_re, Complex.mul_re]
    linarith
  have hz₂re : (1 / 4 : ℝ) ≤ z₂.re := by
    dsimp [z₂]
    norm_num [Complex.div_re, Complex.normSq, Complex.sub_re, Complex.add_re,
      Complex.mul_re]
    linarith
  have hR₁ :
      |(Complex.digamma z₁).im - (Complex.log z₁ - z₁⁻¹ / 2).im| ≤ 1 / T := by
    have h := abs_im_digamma_sub_log_sub_half_inv_le (z := z₁) hz₁re
    have hdecay : 1 / (6 * ‖z₁‖ ^ 2) ≤ 1 / T := by
      simpa [z₁] using one_div_six_norm_sq_half_horizontal_le_inv
        (x := x) (T := T) hT
    exact h.trans hdecay
  have hR₂ :
      |(Complex.digamma z₂).im - (Complex.log z₂ - z₂⁻¹ / 2).im| ≤ 1 / T := by
    have h := abs_im_digamma_sub_log_sub_half_inv_le (z := z₂) hz₂re
    have hdecay : 1 / (6 * ‖z₂‖ ^ 2) ≤ 1 / T := by
      simpa [z₂] using one_div_six_norm_sq_reflected_half_horizontal_le_inv
        (x := x) (T := T) hT
    exact h.trans hdecay
  have hlog : |(Complex.log z₁ + Complex.log z₂).im| ≤ 2 / T := by
    simpa [z₁, z₂] using
      abs_im_log_half_add_log_reflected_half_horizontal_le
        (x := x) (T := T) hxl hxu hTpos
  have hinv : |(((z₁⁻¹ + z₂⁻¹) / 2).im)| ≤ 2 / T := by
    simpa [z₁, z₂] using abs_im_inv_pair_average_horizontal_le
      (x := x) (T := T) hTpos
  have hmain_eq :
      (Complex.log z₁ - z₁⁻¹ / 2).im + (Complex.log z₂ - z₂⁻¹ / 2).im =
        (Complex.log z₁ + Complex.log z₂).im - (((z₁⁻¹ + z₂⁻¹) / 2).im) := by
    simp
    ring
  have hmain :
      |(Complex.log z₁ - z₁⁻¹ / 2).im + (Complex.log z₂ - z₂⁻¹ / 2).im| ≤
        4 / T := by
    rw [hmain_eq]
    calc
      |(Complex.log z₁ + Complex.log z₂).im - (((z₁⁻¹ + z₂⁻¹) / 2).im)|
          ≤ |(Complex.log z₁ + Complex.log z₂).im| +
              |(((z₁⁻¹ + z₂⁻¹) / 2).im)| := by
            simpa [sub_eq_add_neg] using
              abs_add_le (Complex.log z₁ + Complex.log z₂).im
                (-(((z₁⁻¹ + z₂⁻¹) / 2).im))
      _ ≤ 2 / T + 2 / T := add_le_add hlog hinv
      _ = 4 / T := by ring
  have hdecomp :
      (Complex.digamma z₁ + Complex.digamma z₂).im =
        ((Complex.log z₁ - z₁⁻¹ / 2).im + (Complex.log z₂ - z₂⁻¹ / 2).im) +
          ((Complex.digamma z₁).im - (Complex.log z₁ - z₁⁻¹ / 2).im) +
          ((Complex.digamma z₂).im - (Complex.log z₂ - z₂⁻¹ / 2).im) := by
    simp
    ring
  rw [hdecomp]
  let A : ℝ := (Complex.log z₁ - z₁⁻¹ / 2).im + (Complex.log z₂ - z₂⁻¹ / 2).im
  let B : ℝ := (Complex.digamma z₁).im - (Complex.log z₁ - z₁⁻¹ / 2).im
  let C : ℝ := (Complex.digamma z₂).im - (Complex.log z₂ - z₂⁻¹ / 2).im
  change |A + B + C| ≤ 6 / T
  have hA : |A| ≤ 4 / T := by simpa [A] using hmain
  have hB : |B| ≤ 1 / T := by simpa [B] using hR₁
  have hC : |C| ≤ 1 / T := by simpa [C] using hR₂
  calc
    |A + B + C| ≤ |A + B| + |C| := abs_add_le _ _
    _ ≤ |A| + |B| + |C| := by nlinarith [abs_add_le A B]
    _ ≤ 4 / T + 1 / T + 1 / T := by nlinarith
    _ = 6 / T := by ring

theorem abs_im_backlundArchimedeanSymmetryIntegrand_horizontal_le {x T : ℝ}
    (hxl : (1 / 2 : ℝ) ≤ x) (hxu : x ≤ 1 + 3 / 50) (hT : 1 ≤ T) :
    |(backlundArchimedeanSymmetryIntegrand
        ((x : ℂ) + (T : ℂ) * Complex.I)).im| ≤ 4 / T := by
  let s : ℂ := (x : ℂ) + (T : ℂ) * Complex.I
  have hTpos : 0 < T := by linarith
  have hTne : T ≠ 0 := hTpos.ne'
  have hs_im : s.im = T := by simp [s, Complex.add_im, Complex.mul_im]
  have him : s.im ≠ 0 := by simpa [hs_im] using hTne
  have hs0 : s ≠ 0 := by
    intro h
    apply him
    rw [h]
    norm_num
  have hs1 : s ≠ 1 := by
    intro h
    apply him
    rw [h]
    norm_num
  have hshift := backlundArchimedeanSymmetryIntegrand_eq_shifted_digamma
    (s := s) hs0 hs1 (reflected_half_ne_neg_nat_of_im_ne_zero him)
  have hinv0 : |(s⁻¹).im| ≤ 1 / T := by
    have h := abs_im_inv_horizontal_le (x := x) (T := T) hTne
    have hT_abs : |T| = T := abs_of_pos hTpos
    rw [hT_abs] at h
    change |(((x : ℂ) + (T : ℂ) * Complex.I)⁻¹).im| ≤ 1 / T
    exact h
  have hinv : |((-1 / s).im)| ≤ 1 / T := by
    have him_eq : (-1 / s).im = -(s⁻¹).im := by
      simp [div_eq_mul_inv]
    rw [him_eq, abs_neg]
    exact hinv0
  have hdig :
      |(Complex.digamma (s / 2) + Complex.digamma ((3 - s) / 2)).im| ≤ 6 / T := by
    simpa [s] using abs_im_digamma_half_add_reflected_half_horizontal_le
      (x := x) (T := T) hxl hxu hT
  rw [hshift]
  let D : ℂ := Complex.digamma (s / 2) + Complex.digamma ((3 - s) / 2)
  have him_eq : (-1 / s + ↑(Real.log Real.pi) - (1 / 2 : ℂ) * D).im =
      (-1 / s).im - D.im / 2 := by
    simp [D]
    ring
  rw [him_eq]
  calc
    |(-1 / s).im - D.im / 2| ≤ |(-1 / s).im| + |D.im / 2| := by
      simpa [sub_eq_add_neg] using abs_add_le (-1 / s).im (-(D.im / 2))
    _ ≤ 1 / T + (6 / T) / 2 := by
      have hDhalf : |D.im / 2| ≤ (6 / T) / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact div_le_div_of_nonneg_right (by simpa [D] using hdig) (by norm_num)
      exact add_le_add hinv hDhalf
    _ = 4 / T := by ring

theorem abs_im_HIntegral_le_of_norm_le_const {f : ℂ → ℂ} {x₁ x₂ y C : ℝ}
    (hbound :
      ∀ x ∈ [[x₁, x₂]],
        ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C) :
    |(HIntegral f x₁ x₂ y).im| ≤ C * |x₂ - x₁| := by
  calc
    |(HIntegral f x₁ x₂ y).im|
        ≤ ‖HIntegral f x₁ x₂ y‖ := Complex.abs_im_le_norm _
    _ ≤ C * |x₂ - x₁| := by
          unfold HIntegral
          exact intervalIntegral.norm_integral_le_of_norm_le_const
            (fun x hx => hbound x (Set.uIoc_subset_uIcc hx))

theorem abs_im_HIntegral_backlundArchimedeanSymmetryIntegrand_le_of_norm_le_const
    {σ₁ T C : ℝ}
    (hbound :
      ∀ x ∈ [[(1 / 2 : ℝ), σ₁]],
        ‖backlundArchimedeanSymmetryIntegrand
          ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤ C) :
    |(HIntegral backlundArchimedeanSymmetryIntegrand (1 / 2) σ₁ T).im| ≤
      C * |σ₁ - 1 / 2| := by
  exact abs_im_HIntegral_le_of_norm_le_const
    (f := backlundArchimedeanSymmetryIntegrand)
    (x₁ := (1 / 2 : ℝ)) (x₂ := σ₁) (y := T) (C := C) hbound

theorem abs_im_HIntegral_le_of_abs_im_le_const_of_le {f : ℂ → ℂ} {x₁ x₂ y C : ℝ}
    (hle : x₁ ≤ x₂)
    (hint : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I)) volume x₁ x₂)
    (hbound :
      ∀ x ∈ Set.Icc x₁ x₂,
        |(f ((x : ℂ) + (y : ℂ) * Complex.I)).im| ≤ C) :
    |(HIntegral f x₁ x₂ y).im| ≤ C * (x₂ - x₁) := by
  let g : ℝ → ℂ := fun x => f ((x : ℂ) + (y : ℂ) * Complex.I)
  have hint_set : Integrable g (volume.restrict (Set.Ioc x₁ x₂)) := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 hint
  have him_eq : (HIntegral f x₁ x₂ y).im = ∫ x in x₁..x₂, (g x).im := by
    unfold HIntegral
    rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle]
    simpa [g] using (integral_im (μ := volume.restrict (Set.Ioc x₁ x₂)) hint_set).symm
  have him_int : IntervalIntegrable (fun x : ℝ => (g x).im) volume x₁ x₂ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
    exact hint_set.im
  rw [him_eq]
  calc
    |∫ x in x₁..x₂, (g x).im|
        ≤ ∫ x in x₁..x₂, |(g x).im| :=
          intervalIntegral.abs_integral_le_integral_abs hle
    _ ≤ ∫ _x in x₁..x₂, C := by
          exact intervalIntegral.integral_mono_on hle him_int.abs
            intervalIntegral.intervalIntegrable_const
            (fun x hx => by simpa [g] using hbound x hx)
    _ = C * (x₂ - x₁) := by
          rw [intervalIntegral.integral_const]
          ring

theorem abs_im_HIntegral_backlundArchimedeanSymmetryIntegrand_le_of_abs_im_le_const
    {σ₁ T C : ℝ}
    (hle : (1 / 2 : ℝ) ≤ σ₁)
    (hint : IntervalIntegrable
      (fun x : ℝ =>
        backlundArchimedeanSymmetryIntegrand ((x : ℂ) + (T : ℂ) * Complex.I))
      volume (1 / 2) σ₁)
    (hbound :
      ∀ x ∈ Set.Icc (1 / 2 : ℝ) σ₁,
        |(backlundArchimedeanSymmetryIntegrand
          ((x : ℂ) + (T : ℂ) * Complex.I)).im| ≤ C) :
    |(HIntegral backlundArchimedeanSymmetryIntegrand (1 / 2) σ₁ T).im| ≤
      C * (σ₁ - 1 / 2) := by
  exact abs_im_HIntegral_le_of_abs_im_le_const_of_le
    (f := backlundArchimedeanSymmetryIntegrand)
    (x₁ := (1 / 2 : ℝ)) (x₂ := σ₁) (y := T) (C := C) hle hint hbound

private theorem HIntegral_reflect_one (f : ℂ → ℂ) (a b T : ℝ) :
    HIntegral f (1 - b) (1 - a) (-T) =
      HIntegral (fun s => f (1 - s)) a b T := by
  unfold HIntegral
  rw [← intervalIntegral.integral_comp_sub_left
    (f := fun x : ℝ => f ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
    (a := a) (b := b) (d := 1)]
  apply intervalIntegral.integral_congr
  intro x _hx
  push_cast
  ring_nf

/--
Backlund's real-part auxiliary
`F_N(z) = (A(z+iT)^N + A(z-iT)^N)/2`.
This raw version is for horizontal-line real-part bookkeeping; Jensen's theorem
uses `backlundFEntire`, built from the patched entire surrogate.
-/
noncomputable def backlundF (N : ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (backlundA (z + (T : ℂ) * Complex.I) ^ N +
      backlundA (z - (T : ℂ) * Complex.I) ^ N)

theorem backlundF_real_eq_re (N : ℕ) (σ T : ℝ) :
    backlundF N T (σ : ℂ) =
      ((backlundA ((σ : ℂ) + (T : ℂ) * Complex.I) ^ N).re : ℂ) := by
  have hreflect :
      (σ : ℂ) - (T : ℂ) * Complex.I =
        star ((σ : ℂ) + (T : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp [Complex.add_re, Complex.sub_re, Complex.mul_re]
    · simp [Complex.add_im, Complex.sub_im, Complex.mul_im]
  unfold backlundF
  rw [hreflect, backlundA_conj]
  rw [← star_pow]
  let w : ℂ := backlundA ((σ : ℂ) + (T : ℂ) * Complex.I) ^ N
  change (1 / 2 : ℂ) * (w + star w) = (w.re : ℂ)
  apply Complex.ext
  · simp [Complex.mul_re, Complex.add_re]
    ring
  · simp [Complex.mul_im, Complex.add_im]

theorem backlundF_real_eq_zero_iff (N : ℕ) (σ T : ℝ) :
    backlundF N T (σ : ℂ) = 0 ↔
      (backlundA ((σ : ℂ) + (T : ℂ) * Complex.I) ^ N).re = 0 := by
  rw [backlundF_real_eq_re]
  exact Complex.ofReal_eq_zero

/-! ### Local surfaces for the eccentric Backlund pairing -/

/--
Unwrapped horizontal argument variation of `A(s)` along `x + iT`,
represented as the imaginary part of the logarithmic-derivative integral.
-/
noncomputable def backlundAHorizontalArgumentVariation (x₁ x₂ T : ℝ) : ℝ :=
  (HIntegral (logDeriv backlundA) x₁ x₂ T).im

theorem backlundAHorizontalArgumentVariation_self (x T : ℝ) :
    backlundAHorizontalArgumentVariation x x T = 0 := by
  simp [backlundAHorizontalArgumentVariation, HIntegral]

theorem backlundAHorizontalArgumentVariation_symm (x₁ x₂ T : ℝ) :
    backlundAHorizontalArgumentVariation x₁ x₂ T =
      -backlundAHorizontalArgumentVariation x₂ x₁ T := by
  rw [backlundAHorizontalArgumentVariation, backlundAHorizontalArgumentVariation,
    HIntegral_symm]
  simp

/--
The symmetry defect in Backlund's argument comparison. The intended lemma 4
bounds the absolute value of this quantity by the gamma/functional-equation
error term.
-/
noncomputable def backlundArgumentSymmetryDefect (σ₁ T : ℝ) : ℝ :=
  backlundAHorizontalArgumentVariation (1 / 2) σ₁ T +
    backlundAHorizontalArgumentVariation (1 - σ₁) (1 / 2) (-T)

theorem backlundArgumentSymmetryDefect_self (T : ℝ) :
    backlundArgumentSymmetryDefect (1 / 2) T = 0 := by
  rw [backlundArgumentSymmetryDefect]
  norm_num
  simp [backlundAHorizontalArgumentVariation_self]

/-- The high-height gamma/functional-equation error budget used in lemma 4. -/
noncomputable def backlundArgumentSymmetryErrorBound (T₀ : ℝ) : ℝ :=
  4.4 / T₀

theorem backlundArgumentSymmetryErrorBound_pos {T₀ : ℝ} (hT₀ : 0 < T₀) :
    0 < backlundArgumentSymmetryErrorBound T₀ := by
  unfold backlundArgumentSymmetryErrorBound
  positivity

theorem backlundArgumentSymmetryDefect_eq_archimedeanIntegral {σ₁ T : ℝ}
    (hs0 : ∀ x ∈ [[(1 / 2 : ℝ), σ₁]],
      ((x : ℂ) + (T : ℂ) * Complex.I) ≠ 0)
    (hs1 : ∀ x ∈ [[(1 / 2 : ℝ), σ₁]],
      ((x : ℂ) + (T : ℂ) * Complex.I) ≠ 1)
    (hζ : ∀ x ∈ [[(1 / 2 : ℝ), σ₁]],
      riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) ≠ 0)
    (hζref : ∀ x ∈ [[(1 / 2 : ℝ), σ₁]],
      riemannZeta (1 - ((x : ℂ) + (T : ℂ) * Complex.I)) ≠ 0)
    (hint :
      IntervalIntegrable
        (fun x : ℝ => logDeriv backlundA ((x : ℂ) + (T : ℂ) * Complex.I))
        volume (1 / 2) σ₁)
    (hint_ref :
      IntervalIntegrable
        (fun x : ℝ => logDeriv backlundA (1 - ((x : ℂ) + (T : ℂ) * Complex.I)))
        volume (1 / 2) σ₁) :
    backlundArgumentSymmetryDefect σ₁ T =
      (HIntegral backlundArchimedeanSymmetryIntegrand (1 / 2) σ₁ T).im := by
  have hsum :
      HIntegral (fun s => logDeriv backlundA s + logDeriv backlundA (1 - s))
          (1 / 2) σ₁ T =
        HIntegral (logDeriv backlundA) (1 / 2) σ₁ T +
          HIntegral (fun s => logDeriv backlundA (1 - s)) (1 / 2) σ₁ T :=
    HIntegral_add hint hint_ref
  have hcongr :
      HIntegral (fun s => logDeriv backlundA s + logDeriv backlundA (1 - s))
          (1 / 2) σ₁ T =
        HIntegral backlundArchimedeanSymmetryIntegrand (1 / 2) σ₁ T := by
    unfold HIntegral
    apply intervalIntegral.integral_congr
    intro x hx
    simpa [backlundArchimedeanSymmetryIntegrand] using
      logDeriv_backlundA_add_reflected_eq_archimedean
        (s := (x : ℂ) + (T : ℂ) * Complex.I)
        (hs0 x hx) (hs1 x hx) (hζ x hx) (hζref x hx)
  have hreflect :
      HIntegral (logDeriv backlundA) (1 - σ₁) (1 / 2) (-T) =
        HIntegral (fun s => logDeriv backlundA (1 - s)) (1 / 2) σ₁ T := by
    have hreflect0 :=
      HIntegral_reflect_one (f := logDeriv backlundA)
        (a := (1 / 2 : ℝ)) (b := σ₁) (T := T)
    have hhalf : (1 : ℝ) - (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by norm_num
    simpa [hhalf] using hreflect0
  rw [backlundArgumentSymmetryDefect]
  simp only [backlundAHorizontalArgumentVariation]
  rw [hreflect]
  rw [← Complex.add_im, ← hsum, hcongr]

theorem backlundArgumentSymmetryError_of_archimedeanIntegral_bound {σ₁ T T₀ E : ℝ}
    (hs0 : ∀ x ∈ [[(1 / 2 : ℝ), σ₁]],
      ((x : ℂ) + (T : ℂ) * Complex.I) ≠ 0)
    (hs1 : ∀ x ∈ [[(1 / 2 : ℝ), σ₁]],
      ((x : ℂ) + (T : ℂ) * Complex.I) ≠ 1)
    (hζ : ∀ x ∈ [[(1 / 2 : ℝ), σ₁]],
      riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) ≠ 0)
    (hζref : ∀ x ∈ [[(1 / 2 : ℝ), σ₁]],
      riemannZeta (1 - ((x : ℂ) + (T : ℂ) * Complex.I)) ≠ 0)
    (hint :
      IntervalIntegrable
        (fun x : ℝ => logDeriv backlundA ((x : ℂ) + (T : ℂ) * Complex.I))
        volume (1 / 2) σ₁)
    (hint_ref :
      IntervalIntegrable
        (fun x : ℝ => logDeriv backlundA (1 - ((x : ℂ) + (T : ℂ) * Complex.I)))
        volume (1 / 2) σ₁)
    (harch :
      |(HIntegral backlundArchimedeanSymmetryIntegrand (1 / 2) σ₁ T).im| < E)
    (hE : E ≤ backlundArgumentSymmetryErrorBound T₀) :
    |backlundArgumentSymmetryDefect σ₁ T| <
      backlundArgumentSymmetryErrorBound T₀ := by
  have hred :=
    backlundArgumentSymmetryDefect_eq_archimedeanIntegral
      (σ₁ := σ₁) (T := T) hs0 hs1 hζ hζref hint hint_ref
  rw [hred]
  exact harch.trans_le hE

/--
Zeros of the real part `Re(A(σ+iT)^N)` on a real interval. These are the
ordered zeros used by Backlund's pairing argument, not zeta zeros.
-/
def backlundRealPartZeroSet (N : ℕ) (T a b : ℝ) : Set ℝ :=
  {σ | σ ∈ Set.Icc a b ∧
    (backlundA ((σ : ℂ) + (T : ℂ) * Complex.I) ^ N).re = 0}

theorem mem_backlundRealPartZeroSet_iff (N : ℕ) (T a b σ : ℝ) :
    σ ∈ backlundRealPartZeroSet N T a b ↔
      σ ∈ Set.Icc a b ∧
        (backlundA ((σ : ℂ) + (T : ℂ) * Complex.I) ^ N).re = 0 := by
  rfl

theorem mem_backlundRealPartZeroSet_iff_backlundF (N : ℕ) (T a b σ : ℝ) :
    σ ∈ backlundRealPartZeroSet N T a b ↔
      σ ∈ Set.Icc a b ∧ backlundF N T (σ : ℂ) = 0 := by
  rw [mem_backlundRealPartZeroSet_iff, backlundF_real_eq_zero_iff]

theorem firstHit_backlundAHorizontalPathFrom_mem_realPartZeroSet {x₀ D T : ℝ}
    (hT : T ≠ 0)
    (hf : ∀ x, backlundAHorizontalPathFrom x₀ D T hT x ≠ 0)
    (θ : PhaseLift (normalizeNonzeroPath (backlundAHorizontalPathFrom x₀ D T hT) hf))
    (N : ℕ) {target : ℝ}
    (hcos : Real.cos ((N : ℝ) * target) = 0)
    (hne : (firstHitRealSet D θ.phase target).Nonempty) :
    x₀ + firstHit θ.phase target hne ∈
      backlundRealPartZeroSet N T x₀ (x₀ + D) := by
  have hI : firstHit θ.phase target hne ∈ Set.Icc (0 : ℝ) D :=
    firstHit_mem_Icc θ.phase target hne
  have hzero := firstHit_phaseLift_re_pow_eq_zero
    (f := backlundAHorizontalPathFrom x₀ D T hT) (hf := hf) (θ := θ)
    (N := N) hcos hne
  constructor
  · constructor
    · simpa [add_comm] using add_le_add_left hI.1 x₀
    · simpa [add_comm] using add_le_add_left hI.2 x₀
  · simpa [backlundAHorizontalPathFrom, firstHit, add_assoc] using hzero

noncomputable def backlundRealPartZeroCount (N : ℕ) (T a b : ℝ) : ℕ :=
  (backlundRealPartZeroSet N T a b).ncard

theorem backlundRealPartZeroCount_eq_toFinset_card {N : ℕ} {T a b : ℝ}
    (hfin : (backlundRealPartZeroSet N T a b).Finite) :
    backlundRealPartZeroCount N T a b =
      hfin.toFinset.card := by
  exact Set.ncard_eq_toFinset_card _ hfin

def backlundOrderedRealPartZeros (N k : ℕ) (T a b : ℝ) (xs : Fin k → ℝ) : Prop :=
  StrictMono xs ∧ ∀ i, xs i ∈ backlundRealPartZeroSet N T a b

theorem backlundOrderedRealPartZeros_count_le {N k : ℕ} {T a b : ℝ} {xs : Fin k → ℝ}
    (hfin : (backlundRealPartZeroSet N T a b).Finite)
    (hxs : backlundOrderedRealPartZeros N k T a b xs) :
    k ≤ backlundRealPartZeroCount N T a b := by
  have hsub : Set.range xs ⊆ backlundRealPartZeroSet N T a b := by
    rintro x ⟨i, rfl⟩
    exact hxs.2 i
  have hrange_card : (Set.range xs).ncard = k := by
    rw [Set.ncard_range_of_injective hxs.1.injective]
    simp
  rw [backlundRealPartZeroCount, ← hrange_card]
  exact Set.ncard_le_ncard hsub hfin

theorem backlundCosZeroFirstHits_orderedRealPartZeros {x₀ D T : ℝ}
    (hD : (0 : ℝ) ≤ D) (hT : T ≠ 0)
    (hf : ∀ x, backlundAHorizontalPathFrom x₀ D T hT x ≠ 0)
    (θ : PhaseLift (normalizeNonzeroPath (backlundAHorizontalPathFrom x₀ D T hT) hf))
    {N m : ℕ} (hN : 0 < N)
    (hstart : ∀ i : Fin m,
      θ.phase ⟨0, by exact ⟨le_rfl, hD⟩⟩ < backlundCosZeroTarget N (i : ℕ))
    (hne : ∀ i : Fin m,
      (firstHitRealSet D θ.phase (backlundCosZeroTarget N (i : ℕ))).Nonempty) :
    backlundOrderedRealPartZeros N m T x₀ (x₀ + D)
      (fun i : Fin m =>
        x₀ + firstHit θ.phase (backlundCosZeroTarget N (i : ℕ)) (hne i)) := by
  constructor
  · have htargets : StrictMono fun i : Fin m => backlundCosZeroTarget N (i : ℕ) :=
      strictMono_backlundCosZeroTarget hN
    have hhits :
        StrictMono fun i : Fin m =>
          firstHit θ.phase (backlundCosZeroTarget N (i : ℕ)) (hne i) :=
      firstHit_strictMono_of_strictMono_targets
        (u := θ.phase)
        (targets := fun i : Fin m => backlundCosZeroTarget N (i : ℕ))
        hD hstart htargets hne
    intro i j hij
    simpa [add_comm, add_left_comm, add_assoc] using add_lt_add_left (hhits hij) x₀
  · intro i
    exact firstHit_backlundAHorizontalPathFrom_mem_realPartZeroSet
      (x₀ := x₀) (D := D) (T := T) hT hf θ N
      (backlundCosZeroTarget_cos_eq_zero hN) (hne i)

/-- The ordered-pairing loss `⌊N E / π⌋` from the argument-symmetry error. -/
noncomputable def backlundPairingLoss (N : ℕ) (E : ℝ) : ℕ :=
  Nat.floor ((N : ℝ) * E / Real.pi)

theorem backlundCosZeroTarget_add_gap {N j q : ℕ} (hN : 0 < N) :
    backlundCosZeroTarget N (j + q + 1) - backlundCosZeroTarget N j =
      (((q + 1 : ℕ) : ℝ) * Real.pi) / (N : ℝ) := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  unfold backlundCosZeroTarget
  field_simp [hNne]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring

theorem backlundCosZeroTarget_add_le_of_mul_le {N j q : ℕ} {ε : ℝ}
    (hN : 0 < N) (hε : (N : ℝ) * ε ≤ ((q + 1 : ℕ) : ℝ) * Real.pi) :
    backlundCosZeroTarget N j + ε ≤ backlundCosZeroTarget N (j + q + 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hε' : ε ≤ (((q + 1 : ℕ) : ℝ) * Real.pi) / (N : ℝ) := by
    exact (le_div_iff₀ hNpos).2 (by simpa [mul_comm] using hε)
  have hgap := backlundCosZeroTarget_add_gap (N := N) (j := j) (q := q) hN
  linarith

theorem nat_mul_error_lt_pairingLoss_succ_mul_pi {N : ℕ} {E : ℝ} (_hE : 0 ≤ E) :
    (N : ℝ) * E < ((backlundPairingLoss N E + 1 : ℕ) : ℝ) * Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hfloor := Nat.lt_floor_add_one ((N : ℝ) * E / Real.pi)
  unfold backlundPairingLoss at hfloor ⊢
  have hmul : ((N : ℝ) * E / Real.pi) * Real.pi <
      (↑(Nat.floor ((N : ℝ) * E / Real.pi)) + 1) * Real.pi :=
    mul_lt_mul_of_pos_right hfloor hpi
  have hleft : ((N : ℝ) * E / Real.pi) * Real.pi = (N : ℝ) * E := by
    field_simp [hpi.ne']
  have hright : (↑(Nat.floor ((N : ℝ) * E / Real.pi)) + 1) * Real.pi =
      ((Nat.floor ((N : ℝ) * E / Real.pi) + 1 : ℕ) : ℝ) * Real.pi := by
    norm_num
  simpa [hleft, hright] using hmul

theorem cosZeroTarget_leftFirstHits_le_rightShiftedFirstHits {D ε : ℝ}
    (u v : C(Set.Icc (0 : ℝ) D, ℝ)) (hD : (0 : ℝ) ≤ D)
    {N q m : ℕ} (hN : 0 < N)
    (hε : (N : ℝ) * ε ≤ ((q + 1 : ℕ) : ℝ) * Real.pi)
    (hstart : ∀ i : Fin m,
      v ⟨0, by exact ⟨le_rfl, hD⟩⟩ < backlundCosZeroTarget N (i : ℕ))
    (herr : ∀ x : Set.Icc (0 : ℝ) D, |u x - v x| < ε)
    (hright : ∀ i : Fin m,
      (firstHitRealSet D u
        (backlundCosZeroTarget N ((i : ℕ) + q + 1))).Nonempty) :
    ∃ hleft : ∀ i : Fin m,
      (firstHitRealSet D v (backlundCosZeroTarget N (i : ℕ))).Nonempty,
      ∀ i : Fin m,
        firstHit v (backlundCosZeroTarget N (i : ℕ)) (hleft i) ≤
          firstHit u (backlundCosZeroTarget N ((i : ℕ) + q + 1)) (hright i) := by
  have hpair : ∀ i : Fin m,
      ∃ hleft : (firstHitRealSet D v (backlundCosZeroTarget N (i : ℕ))).Nonempty,
        firstHit v (backlundCosZeroTarget N (i : ℕ)) hleft ≤
          firstHit u (backlundCosZeroTarget N ((i : ℕ) + q + 1)) (hright i) := by
    intro i
    exact firstHit_le_firstHit_of_abs_error_at_firstHit
      (u := u) (v := v) hD
      (leftTarget := backlundCosZeroTarget N (i : ℕ))
      (rightTarget := backlundCosZeroTarget N ((i : ℕ) + q + 1))
      (ε := ε) (hright i) (hstart i) herr
      (backlundCosZeroTarget_add_le_of_mul_le
        (N := N) (j := (i : ℕ)) (q := q) hN hε)
  refine ⟨fun i => Classical.choose (hpair i), ?_⟩
  intro i
  exact Classical.choose_spec (hpair i)

/-- The guaranteed paired-zero count in Backlund's ordered pairing lemma. -/
noncomputable def backlundOrderedPairingLowerCount (N n : ℕ) (E : ℝ) : ℕ :=
  n - 2 - backlundPairingLoss N E

theorem backlundOrderedPairingLowerCount_eq_source (N n : ℕ) (E : ℝ) :
    backlundOrderedPairingLowerCount N n E =
      n - 2 - backlundPairingLoss N E := rfl

/-- Backlund's eccentric Jensen center offset `η = 3/50`. -/
noncomputable def backlundEta : ℝ := 3 / 50

/-- Backlund's eccentric Jensen small radius `r = 52/25`. -/
noncomputable def backlundSmallRadius : ℝ := 52 / 25

/-- The paired-product height parameter `H = 14/25`. -/
noncomputable def backlundPairingH : ℝ := 14 / 25

/-- Backlund's eccentric Jensen large radius `R = 728/625`. -/
noncomputable def backlundLargeRadius : ℝ := 728 / 625

noncomputable def backlundPhi₁ : ℝ := Real.arcsin (75 / 1456)

noncomputable def backlundPhi₂ : ℝ := Real.arcsin (25 / 52)

noncomputable def backlundPhi₃ : ℝ := Real.arcsin (1325 / 1456)

theorem backlundEta_pos : 0 < backlundEta := by
  norm_num [backlundEta]

theorem backlundSmallRadius_pos : 0 < backlundSmallRadius := by
  norm_num [backlundSmallRadius]

theorem backlundPairingH_pos : 0 < backlundPairingH := by
  norm_num [backlundPairingH]

theorem backlundLargeRadius_pos : 0 < backlundLargeRadius := by
  norm_num [backlundLargeRadius]

/-- The center `1 + η` of the eccentric Jensen disk. -/
noncomputable def backlundEccentricCenter (η : ℝ) : ℂ :=
  ((1 + η : ℝ) : ℂ)

theorem norm_ofReal_sub_backlundEccentricCenter_eq {η x : ℝ}
    (hx : x ≤ 1 + η) :
    ‖((x : ℂ) - backlundEccentricCenter η)‖ = 1 + η - x := by
  unfold backlundEccentricCenter
  apply (sq_eq_sq₀ (norm_nonneg _) (by linarith)).1
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
  ring

theorem norm_ofReal_sub_backlundEccentricCenter_le_pairingH {x : ℝ}
    (hxlo : (1 / 2 : ℝ) ≤ x) (hxhi : x ≤ 1 + backlundEta) :
    ‖((x : ℂ) - backlundEccentricCenter backlundEta)‖ ≤ backlundPairingH := by
  rw [norm_ofReal_sub_backlundEccentricCenter_eq hxhi]
  norm_num [backlundEta, backlundPairingH] at *
  linarith

theorem norm_pair_of_backlund_reflected_le_pairingH_sq {a b : ℝ}
    (ha : a ≤ 1 + backlundEta) (hb : b ≤ 1 / 2)
    (hpair : 1 - b ≤ a) :
    ‖((a : ℂ) - backlundEccentricCenter backlundEta)‖ *
        ‖((b : ℂ) - backlundEccentricCenter backlundEta)‖ ≤
      backlundPairingH ^ 2 := by
  have hb_center : b ≤ 1 + backlundEta := by
    norm_num [backlundEta] at *
    linarith
  rw [norm_ofReal_sub_backlundEccentricCenter_eq ha,
    norm_ofReal_sub_backlundEccentricCenter_eq hb_center]
  have hfactor :
      1 + backlundEta - a ≤ backlundEta + b := by
    linarith
  have hright_nonneg : 0 ≤ 1 + backlundEta - b := by
    norm_num [backlundEta] at *
    linarith
  have hmul :
      (1 + backlundEta - a) * (1 + backlundEta - b) ≤
        (backlundEta + b) * (1 + backlundEta - b) :=
    mul_le_mul_of_nonneg_right hfactor hright_nonneg
  have hquad :
      (backlundEta + b) * (1 + backlundEta - b) ≤ backlundPairingH ^ 2 := by
    norm_num [backlundEta, backlundPairingH]
    nlinarith [sq_nonneg (b - 1 / 2)]
  exact hmul.trans hquad

theorem prod_norm_pairs_of_backlund_reflected_le_pairingH_pow {m : ℕ}
    {right left : Fin m → ℝ}
    (hright : ∀ i : Fin m, right i ≤ 1 + backlundEta)
    (hleft : ∀ i : Fin m, left i ≤ 1 / 2)
    (hpair : ∀ i : Fin m, 1 - left i ≤ right i) :
    (∏ i : Fin m,
        (‖((right i : ℂ) - backlundEccentricCenter backlundEta)‖ *
          ‖((left i : ℂ) - backlundEccentricCenter backlundEta)‖)) ≤
      backlundPairingH ^ (2 * m) := by
  have hprod :
      (∏ i : Fin m,
          (‖((right i : ℂ) - backlundEccentricCenter backlundEta)‖ *
            ‖((left i : ℂ) - backlundEccentricCenter backlundEta)‖)) ≤
        ∏ _i : Fin m, backlundPairingH ^ 2 := by
    refine Finset.prod_le_prod ?_ ?_
    · intro i _hi
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · intro i _hi
      exact norm_pair_of_backlund_reflected_le_pairingH_sq
        (a := right i) (b := left i) (hright i) (hleft i) (hpair i)
  calc
    (∏ i : Fin m,
        (‖((right i : ℂ) - backlundEccentricCenter backlundEta)‖ *
          ‖((left i : ℂ) - backlundEccentricCenter backlundEta)‖))
        ≤ ∏ _i : Fin m, backlundPairingH ^ 2 := hprod
    _ = (backlundPairingH ^ 2) ^ m := by simp
    _ = backlundPairingH ^ (2 * m) := by rw [pow_mul]

theorem prod_norm_pairs_of_backlund_reflected_dist_le_pairingH_pow {m : ℕ}
    {rightDist leftDist : Fin m → ℝ}
    (hright : ∀ i : Fin m, (1 / 2 : ℝ) + rightDist i ≤ 1 + backlundEta)
    (hleft_nonneg : ∀ i : Fin m, 0 ≤ leftDist i)
    (hpair : ∀ i : Fin m, leftDist i ≤ rightDist i) :
    (∏ i : Fin m,
        (‖((((1 / 2 : ℝ) + rightDist i : ℝ) : ℂ) -
            backlundEccentricCenter backlundEta)‖ *
          ‖((((1 / 2 : ℝ) - leftDist i : ℝ) : ℂ) -
            backlundEccentricCenter backlundEta)‖)) ≤
      backlundPairingH ^ (2 * m) := by
  exact prod_norm_pairs_of_backlund_reflected_le_pairingH_pow
    (right := fun i : Fin m => (1 / 2 : ℝ) + rightDist i)
    (left := fun i : Fin m => (1 / 2 : ℝ) - leftDist i)
    hright
    (by intro i; linarith [hleft_nonneg i])
    (by intro i; linarith [hpair i])

theorem norm_ofReal_sub_backlundEccentricCenter_le_largeRadius
    {σ₁ x : ℝ}
    (hσ₁ : σ₁ ≤ 1 + backlundEta) (hx : x ∈ Set.Icc (1 - σ₁) σ₁) :
    ‖((x : ℂ) - backlundEccentricCenter backlundEta)‖ ≤
      backlundLargeRadius := by
  have hxhi : x ≤ 1 + backlundEta := hx.2.trans hσ₁
  rw [norm_ofReal_sub_backlundEccentricCenter_eq hxhi]
  have hxl : 1 - σ₁ ≤ x := hx.1
  have hbound : 1 + backlundEta - x ≤ 1 + 2 * backlundEta := by
    linarith
  have hnum : 1 + 2 * backlundEta ≤ backlundLargeRadius := by
    norm_num [backlundEta, backlundLargeRadius]
  exact hbound.trans hnum

theorem abs_im_HIntegral_backlundArchimedeanSymmetryIntegrand_lt_errorBound
    {σ₁ T T₀ : ℝ}
    (hle : (1 / 2 : ℝ) ≤ σ₁) (hσ₁ : σ₁ ≤ 1 + backlundEta)
    (hT₀ : 1 ≤ T₀) (hT : T₀ ≤ T)
    (hint : IntervalIntegrable
      (fun x : ℝ =>
        backlundArchimedeanSymmetryIntegrand ((x : ℂ) + (T : ℂ) * Complex.I))
      MeasureTheory.volume (1 / 2) σ₁) :
    |(HIntegral backlundArchimedeanSymmetryIntegrand (1 / 2) σ₁ T).im| <
      backlundArgumentSymmetryErrorBound T₀ := by
  have hT1 : 1 ≤ T := by linarith
  have hT₀pos : 0 < T₀ := by linarith
  have hσ₁' : σ₁ ≤ 1 + 3 / 50 := by simpa [backlundEta] using hσ₁
  have hpoint :
      ∀ x ∈ Set.Icc (1 / 2 : ℝ) σ₁,
        |(backlundArchimedeanSymmetryIntegrand
          ((x : ℂ) + (T : ℂ) * Complex.I)).im| ≤ 4 / T := by
    intro x hx
    exact abs_im_backlundArchimedeanSymmetryIntegrand_horizontal_le
      hx.1 (hx.2.trans hσ₁') hT1
  have hH := abs_im_HIntegral_backlundArchimedeanSymmetryIntegrand_le_of_abs_im_le_const
    (σ₁ := σ₁) (T := T) (C := 4 / T) hle hint hpoint
  have hlen_le : σ₁ - 1 / 2 ≤ 14 / 25 := by
    linarith
  have hcoef_nonneg : 0 ≤ 4 / T := by positivity
  have hstep1 : (4 / T) * (σ₁ - 1 / 2) ≤ (4 / T) * (14 / 25) := by
    exact mul_le_mul_of_nonneg_left hlen_le hcoef_nonneg
  have hInv : 1 / T ≤ 1 / T₀ := one_div_le_one_div_of_le hT₀pos hT
  have hstep2 : (4 / T) * (14 / 25) ≤ (4 / T₀) * (14 / 25) := by
    calc
      (4 / T) * (14 / 25) = (56 / 25) * (1 / T) := by ring
      _ ≤ (56 / 25) * (1 / T₀) := by
            exact mul_le_mul_of_nonneg_left hInv (by norm_num)
      _ = (4 / T₀) * (14 / 25) := by ring
  have hstep3 : (4 / T₀) * (14 / 25) < backlundArgumentSymmetryErrorBound T₀ := by
    unfold backlundArgumentSymmetryErrorBound
    field_simp [hT₀pos.ne']
    norm_num
  have hfinal : (4 / T) * (σ₁ - 1 / 2) < backlundArgumentSymmetryErrorBound T₀ :=
    hstep1.trans_lt (hstep2.trans_lt hstep3)
  exact hH.trans_lt hfinal

theorem backlund_argument_symmetry_error {σ₁ T T₀ : ℝ}
    (hle : (1 / 2 : ℝ) ≤ σ₁) (hσ₁ : σ₁ ≤ 1 + backlundEta)
    (hT₀ : 1 ≤ T₀) (hT : T₀ ≤ T)
    (hs0 : ∀ x ∈ [[(1 / 2 : ℝ), σ₁]],
      ((x : ℂ) + (T : ℂ) * Complex.I) ≠ 0)
    (hs1 : ∀ x ∈ [[(1 / 2 : ℝ), σ₁]],
      ((x : ℂ) + (T : ℂ) * Complex.I) ≠ 1)
    (hζ : ∀ x ∈ [[(1 / 2 : ℝ), σ₁]],
      riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) ≠ 0)
    (hζref : ∀ x ∈ [[(1 / 2 : ℝ), σ₁]],
      riemannZeta (1 - ((x : ℂ) + (T : ℂ) * Complex.I)) ≠ 0)
    (hint :
      IntervalIntegrable
        (fun x : ℝ => logDeriv backlundA ((x : ℂ) + (T : ℂ) * Complex.I))
        volume (1 / 2) σ₁)
    (hint_ref :
      IntervalIntegrable
        (fun x : ℝ => logDeriv backlundA (1 - ((x : ℂ) + (T : ℂ) * Complex.I)))
        volume (1 / 2) σ₁)
    (hint_arch : IntervalIntegrable
      (fun x : ℝ =>
        backlundArchimedeanSymmetryIntegrand ((x : ℂ) + (T : ℂ) * Complex.I))
      MeasureTheory.volume (1 / 2) σ₁) :
    |backlundArgumentSymmetryDefect σ₁ T| <
      backlundArgumentSymmetryErrorBound T₀ := by
  exact backlundArgumentSymmetryError_of_archimedeanIntegral_bound
    (σ₁ := σ₁) (T := T) (T₀ := T₀)
    hs0 hs1 hζ hζref hint hint_ref
    (abs_im_HIntegral_backlundArchimedeanSymmetryIntegrand_lt_errorBound
      (σ₁ := σ₁) (T := T) (T₀ := T₀) hle hσ₁ hT₀ hT hint_arch)
    le_rfl

/-- The raw circle integrand `log |F_N(center + R e^{iφ})|`. -/
noncomputable def backlundEccentricJensenIntegrand (N : ℕ) (T η R φ : ℝ) : ℝ :=
  Real.log ‖backlundF N T (circleMap (backlundEccentricCenter η) R φ)‖

/--
The unnormalized raw circle integral. The Jensen theorem should use
`backlundEccentricJensenIntegralEntire`.
-/
noncomputable def backlundEccentricJensenIntegral (N : ℕ) (T η R : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..(2 * Real.pi),
    backlundEccentricJensenIntegrand N T η R φ

/-- Raw RHS shape with the factor-2 denominator `4π log r`. -/
noncomputable def backlundEccentricJensenZeroCountRhs
    (N : ℕ) (T η R r E : ℝ) : ℝ :=
  backlundEccentricJensenIntegral N T η R / (4 * Real.pi * Real.log r) -
    Real.log ‖backlundF N T (backlundEccentricCenter η)‖ / (2 * Real.log r) +
      1 / 2 + (N : ℝ) * E / (2 * Real.pi)

private lemma sin_pi_one_add_mul_I (y : ℝ) :
    Complex.sin ((Real.pi : ℂ) * ((1 : ℂ) + (y : ℂ) * Complex.I)) =
      -((Real.sinh (Real.pi * y) : ℝ) : ℂ) * Complex.I := by
  have harg : (Real.pi : ℂ) * ((1 : ℂ) + (y : ℂ) * Complex.I) =
      (Real.pi : ℂ) + ((Real.pi * y : ℝ) : ℂ) * Complex.I := by
    norm_num [Complex.ofReal_mul]
    ring_nf
  rw [harg]
  simp [Complex.sin_add, Complex.sin_pi, Complex.cos_pi, Complex.sin_mul_I,
    Complex.cos_mul_I, Complex.ofReal_sinh]

private lemma gamma_pure_imag_norm_sq_pos {y : ℝ} (hy : 0 < y) :
    ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ ^ 2 =
      Real.pi / (y * Real.sinh (Real.pi * y)) := by
  let z : ℂ := (y : ℂ) * Complex.I
  have hz_ne : z ≠ 0 := by
    simp [z, hy.ne']
  have hconj : (starRingEnd ℂ) z = -z := by
    simp [z]
  have hsin : Complex.sin ((Real.pi : ℂ) * ((1 : ℂ) + z)) =
      -((Real.sinh (Real.pi * y) : ℝ) : ℂ) * Complex.I := by
    simpa [z] using sin_pi_one_add_mul_I y
  have hleft :
      Complex.Gamma ((1 : ℂ) + z) * Complex.Gamma (1 - ((1 : ℂ) + z)) =
        z * ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) := by
    have hΓadd : Complex.Gamma (z + 1) = z * Complex.Gamma z :=
      Complex.Gamma_add_one z hz_ne
    calc
      Complex.Gamma ((1 : ℂ) + z) * Complex.Gamma (1 - ((1 : ℂ) + z))
          = (z * Complex.Gamma z) * Complex.Gamma (-z) := by
            rw [show (1 : ℂ) + z = z + 1 by ring, hΓadd]
            ring_nf
      _ = (z * Complex.Gamma z) * (starRingEnd ℂ) (Complex.Gamma z) := by
            rw [← hconj, Complex.Gamma_conj]
      _ = z * (Complex.Gamma z * (starRingEnd ℂ) (Complex.Gamma z)) := by ring
      _ = z * ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have href := Complex.Gamma_mul_Gamma_one_sub ((1 : ℂ) + z)
  rw [hleft, hsin] at href
  have hsinh_pos : 0 < Real.sinh (Real.pi * y) := by
    rw [Real.sinh_eq]
    have harg : -(Real.pi * y) < Real.pi * y := by nlinarith [Real.pi_pos, hy]
    have hexp : Real.exp (-(Real.pi * y)) < Real.exp (Real.pi * y) := Real.exp_lt_exp.mpr harg
    nlinarith
  have href' : ((y * ‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) * Complex.I =
      ((Real.pi / Real.sinh (Real.pi * y) : ℝ) : ℂ) * Complex.I := by
    unfold z at href
    calc
      ((y * ‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) * Complex.I
          = ((y : ℂ) * Complex.I) * ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) := by
              push_cast
              ring
      _ = (Real.pi : ℂ) / (-((Real.sinh (Real.pi * y) : ℝ) : ℂ) * Complex.I) := href
      _ = ((Real.pi / Real.sinh (Real.pi * y) : ℝ) : ℂ) * Complex.I := by
              field_simp [Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr hsinh_pos.ne']
              simp
  have hcomplex := mul_right_cancel₀ Complex.I_ne_zero href'
  have hreal : y * ‖Complex.Gamma z‖ ^ 2 = Real.pi / Real.sinh (Real.pi * y) :=
    Complex.ofReal_injective hcomplex
  have hy_ne : y ≠ 0 := hy.ne'
  calc
    ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ ^ 2
        = (y * ‖Complex.Gamma z‖ ^ 2) / y := by
          simp [z]
          field_simp [hy_ne]
    _ = (Real.pi / Real.sinh (Real.pi * y)) / y := by rw [hreal]
    _ = Real.pi / (y * Real.sinh (Real.pi * y)) := by ring

private lemma gamma_pure_imag_norm_sq {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma ((t : ℂ) * Complex.I)‖ ^ 2 =
      Real.pi / (|t| * Real.sinh (Real.pi * |t|)) := by
  by_cases hpos : 0 < t
  · simpa [abs_of_pos hpos] using gamma_pure_imag_norm_sq_pos hpos
  · have hneg : t < 0 := lt_of_le_of_ne (le_of_not_gt hpos) ht
    have habs_pos : 0 < |t| := abs_pos.mpr ht
    have harg : (t : ℂ) * Complex.I = (starRingEnd ℂ) (((|t| : ℝ) : ℂ) * Complex.I) := by
      simp [abs_of_neg hneg]
    have hnorm : ‖Complex.Gamma ((t : ℂ) * Complex.I)‖ =
        ‖Complex.Gamma (((|t| : ℝ) : ℂ) * Complex.I)‖ := by
      rw [harg, Complex.Gamma_conj]
      simp
    rw [hnorm]
    simpa using gamma_pure_imag_norm_sq_pos habs_pos

private lemma gammaReal_vertical_norm_sq {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gammaℝ ((t : ℂ) * Complex.I)‖ ^ 2 =
      Real.pi / ((|t| / 2) * Real.sinh (Real.pi * (|t| / 2))) := by
  have ht2_ne : t / 2 ≠ 0 := by exact div_ne_zero ht two_ne_zero
  have hpow : ‖(Real.pi : ℂ) ^ (-((t : ℂ) * Complex.I) / 2)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.I_re]
  have harg : ((t : ℂ) * Complex.I) / 2 = (((t / 2 : ℝ) : ℂ) * Complex.I) := by
    norm_num [Complex.ofReal_div]
    ring
  rw [Complex.Gammaℝ_def, norm_mul, mul_pow, hpow]
  norm_num
  rw [harg]
  convert gamma_pure_imag_norm_sq ht2_ne using 1
  · rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

private lemma gammaReal_one_sub_vertical_norm_sq (t : ℝ) :
    ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I)‖ ^ 2 =
      1 / Real.cosh (Real.pi * (t / 2)) := by
  have hpow : ‖(Real.pi : ℂ) ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ =
      Real.pi ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re]
    norm_num
  have harg : ((1 : ℂ) - (t : ℂ) * Complex.I) / 2 =
      (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I) := by
    norm_num [Complex.ofReal_div]
    ring
  rw [Complex.Gammaℝ_def, norm_mul, mul_pow, hpow, harg]
  rw [Complex.gamma_half_vertical_norm_sq]
  have hcosh : Real.cosh (Real.pi * (-t / 2)) = Real.cosh (Real.pi * (t / 2)) := by
    rw [show Real.pi * (-t / 2) = -(Real.pi * (t / 2)) by ring, Real.cosh_neg]
  rw [hcosh]
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hcosh_pos : 0 < Real.cosh (Real.pi * (t / 2)) := Real.cosh_pos _
  rw [Real.rpow_neg hpi_pos.le]
  have hpi_half_sq : (Real.pi ^ (1 / 2 : ℝ)) ^ 2 = Real.pi := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hpi_pos.le
  field_simp [hpi_pos.ne', hcosh_pos.ne', hpi_half_sq]
  exact hpi_half_sq.symm

private lemma sinh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.sinh x := by
  rw [Real.sinh_eq]
  have hexp : Real.exp (-x) < Real.exp x := Real.exp_lt_exp.mpr (by linarith)
  nlinarith

private lemma sinh_le_cosh_of_nonneg {x : ℝ} (_hx : 0 ≤ x) : Real.sinh x ≤ Real.cosh x := by
  rw [Real.sinh_eq, Real.cosh_eq]
  nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

private lemma cosh_mul_half_abs (t : ℝ) :
    Real.cosh (Real.pi * (t / 2)) = Real.cosh (Real.pi * (|t| / 2)) := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · have hneg : t < 0 := lt_of_not_ge ht
    rw [abs_of_neg hneg]
    have harg : Real.pi * (t / 2) = -(Real.pi * (-t / 2)) := by ring
    rw [harg, Real.cosh_neg]

private lemma gammaReal_one_sub_vertical_div_vertical_norm_sq_le {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
        Complex.Gammaℝ ((t : ℂ) * Complex.I)‖ ^ 2 ≤ |t| / (2 * Real.pi) := by
  have ht_abs_pos : 0 < |t| := abs_pos.mpr ht
  have hx_pos : 0 < Real.pi * (|t| / 2) := by positivity
  have hsinh_pos : 0 < Real.sinh (Real.pi * (|t| / 2)) := sinh_pos_of_pos hx_pos
  have hcosh_pos : 0 < Real.cosh (Real.pi * (|t| / 2)) := Real.cosh_pos _
  have hcosh_t_pos : 0 < Real.cosh (Real.pi * (t / 2)) := Real.cosh_pos _
  have hsinh_le_cosh : Real.sinh (Real.pi * (|t| / 2)) ≤
      Real.cosh (Real.pi * (|t| / 2)) := sinh_le_cosh_of_nonneg hx_pos.le
  rw [norm_div, div_pow]
  rw [gammaReal_one_sub_vertical_norm_sq, gammaReal_vertical_norm_sq ht]
  rw [cosh_mul_half_abs]
  field_simp [Real.pi_pos.ne', hsinh_pos.ne', hcosh_pos.ne', hcosh_t_pos.ne']
  have hsinh_le_cosh' : Real.sinh (Real.pi * |t| / 2) ≤
      Real.cosh (Real.pi * |t| / 2) := by
    have harg : Real.pi * (|t| / 2) = Real.pi * |t| / 2 := by ring
    simpa [harg] using hsinh_le_cosh
  linarith

private lemma gammaReal_one_sub_vertical_div_vertical_norm_le {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
        Complex.Gammaℝ ((t : ℂ) * Complex.I)‖ ≤ Real.sqrt (|t| / (2 * Real.pi)) := by
  refine (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp ?_
  rw [Real.sq_sqrt]
  · exact gammaReal_one_sub_vertical_div_vertical_norm_sq_le ht
  · positivity

private lemma riemannZeta_vertical_eq_one_sub_mul_gammaRatio {t : ℝ} (ht : t ≠ 0) :
    riemannZeta ((t : ℂ) * Complex.I) =
      riemannZeta ((1 : ℂ) - (t : ℂ) * Complex.I) *
        (Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
          Complex.Gammaℝ ((t : ℂ) * Complex.I)) := by
  let s : ℂ := (t : ℂ) * Complex.I
  have hs_ne : s ≠ 0 := by simp [s, ht]
  have hw_ne : (1 : ℂ) - s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  have hΓw : Complex.Gammaℝ ((1 : ℂ) - s) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp [s]
  have hζs := riemannZeta_def_of_ne_zero (s := s) hs_ne
  have hζw := riemannZeta_def_of_ne_zero (s := (1 : ℂ) - s) hw_ne
  have hcompleted_w : completedRiemannZeta ((1 : ℂ) - s) =
      riemannZeta ((1 : ℂ) - s) * Complex.Gammaℝ ((1 : ℂ) - s) := by
    rw [hζw]
    field_simp [hΓw]
  calc
    riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s := hζs
    _ = completedRiemannZeta ((1 : ℂ) - s) / Complex.Gammaℝ s := by
      rw [completedRiemannZeta_one_sub]
    _ = (riemannZeta ((1 : ℂ) - s) * Complex.Gammaℝ ((1 : ℂ) - s)) /
          Complex.Gammaℝ s := by rw [hcompleted_w]
    _ = riemannZeta ((1 : ℂ) - s) *
          (Complex.Gammaℝ ((1 : ℂ) - s) / Complex.Gammaℝ s) := by ring

private lemma norm_vertical_sub_one_eq_norm_one_add_vertical (t : ℝ) :
    ‖(t : ℂ) * Complex.I - 1‖ = ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]

theorem backlundA_zero_line_le_const_mul_log_sqrt :
    ∃ C > 0, ∀ t : ℝ, 3 < |t| →
      ‖backlundA ((t : ℂ) * Complex.I)‖ ≤
        C * ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ * Real.log |t| *
          Real.sqrt (|t| / (2 * Real.pi)) := by
  obtain ⟨C, hC, hζline⟩ := zeta_one_line_le_const_mul_log
  refine ⟨C, hC, ?_⟩
  intro t ht
  have ht_ne : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    norm_num at ht
  have hζsym := riemannZeta_vertical_eq_one_sub_mul_gammaRatio ht_ne
  have hζline_t : ‖riemannZeta ((1 : ℂ) - (t : ℂ) * Complex.I)‖ ≤ C * Real.log |t| := by
    have h := hζline (-t) (by simpa [abs_neg] using ht)
    simpa [sub_eq_add_neg, neg_mul] using h
  have hgamma := gammaReal_one_sub_vertical_div_vertical_norm_le ht_ne
  have hlog_pos : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hClog_nonneg : 0 ≤ C * Real.log |t| := mul_nonneg hC.le hlog_pos.le
  unfold backlundA
  rw [hζsym]
  calc
    ‖(((t : ℂ) * Complex.I) - 1) *
        (riemannZeta ((1 : ℂ) - (t : ℂ) * Complex.I) *
          (Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
            Complex.Gammaℝ ((t : ℂ) * Complex.I)))‖
        ≤ ‖((t : ℂ) * Complex.I) - 1‖ *
            (‖riemannZeta ((1 : ℂ) - (t : ℂ) * Complex.I)‖ *
              ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
                Complex.Gammaℝ ((t : ℂ) * Complex.I)‖) := by
          calc
            ‖(((t : ℂ) * Complex.I) - 1) *
                (riemannZeta ((1 : ℂ) - (t : ℂ) * Complex.I) *
                  (Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
                    Complex.Gammaℝ ((t : ℂ) * Complex.I)))‖
                ≤ ‖((t : ℂ) * Complex.I) - 1‖ *
                    ‖riemannZeta ((1 : ℂ) - (t : ℂ) * Complex.I) *
                      (Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
                        Complex.Gammaℝ ((t : ℂ) * Complex.I))‖ := norm_mul_le _ _
            _ ≤ ‖((t : ℂ) * Complex.I) - 1‖ *
                    (‖riemannZeta ((1 : ℂ) - (t : ℂ) * Complex.I)‖ *
                      ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
                        Complex.Gammaℝ ((t : ℂ) * Complex.I)‖) := by
              exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ‖((t : ℂ) * Complex.I) - 1‖ *
            ((C * Real.log |t|) * Real.sqrt (|t| / (2 * Real.pi))) := by
          gcongr
    _ = C * ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ * Real.log |t| *
          Real.sqrt (|t| / (2 * Real.pi)) := by
          rw [norm_vertical_sub_one_eq_norm_one_add_vertical]
          ring

private lemma sqrt_abs_div_two_pi_le_two_pi_neg_half_mul_norm_one_add_vertical (t : ℝ) :
    Real.sqrt (|t| / (2 * Real.pi)) ≤
      (2 * Real.pi) ^ (-(1 / 2 : ℝ)) *
        ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ^ (1 / 2 : ℝ) := by
  let R : ℝ := ‖(1 : ℂ) + (t : ℂ) * Complex.I‖
  have hbase_pos : 0 < 2 * Real.pi := by positivity
  have hbase_nonneg : 0 ≤ 2 * Real.pi := hbase_pos.le
  have hR_nonneg : 0 ≤ R := norm_nonneg _
  have habs_le_R : |t| ≤ R := by
    have h := Complex.abs_im_le_norm ((1 : ℂ) + (t : ℂ) * Complex.I)
    simpa [R, Complex.add_im, Complex.mul_im] using h
  refine (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp ?_
  rw [Real.sq_sqrt]
  · have hbase_half_sq : ((2 * Real.pi) ^ (1 / 2 : ℝ)) ^ 2 = 2 * Real.pi := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sq_sqrt hbase_nonneg
    have hbase_neg_half_sq : ((2 * Real.pi) ^ (-(1 / 2 : ℝ))) ^ 2 = (2 * Real.pi)⁻¹ := by
      rw [Real.rpow_neg hbase_nonneg]
      field_simp [hbase_pos.ne', hbase_half_sq]
      exact hbase_half_sq.symm
    have hR_half_sq : (R ^ (1 / 2 : ℝ)) ^ 2 = R := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sq_sqrt hR_nonneg
    rw [mul_pow, hbase_neg_half_sq, hR_half_sq]
    field_simp [hbase_pos.ne']
    nlinarith
  · positivity

theorem backlundA_zero_line_le_const_mul_log :
    ∃ C > 0, ∀ t : ℝ, 3 < |t| →
      ‖backlundA ((t : ℂ) * Complex.I)‖ ≤
        C * ((2 * Real.pi) ^ (-(1 / 2 : ℝ)) *
          ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) * Real.log |t|) := by
  obtain ⟨C, hC, hA⟩ := backlundA_zero_line_le_const_mul_log_sqrt
  refine ⟨C, hC, ?_⟩
  intro t ht
  have h := hA t ht
  have hlog_pos : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hsqrt := sqrt_abs_div_two_pi_le_two_pi_neg_half_mul_norm_one_add_vertical t
  let R : ℝ := ‖(1 : ℂ) + (t : ℂ) * Complex.I‖
  have hR_pos : 0 < R := by
    apply norm_pos_iff.mpr
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
  calc
    ‖backlundA ((t : ℂ) * Complex.I)‖
        ≤ C * R * Real.log |t| * Real.sqrt (|t| / (2 * Real.pi)) := by
          simpa [R] using h
    _ ≤ C * R * Real.log |t| *
          ((2 * Real.pi) ^ (-(1 / 2 : ℝ)) * R ^ (1 / 2 : ℝ)) := by
          gcongr
    _ = C * ((2 * Real.pi) ^ (-(1 / 2 : ℝ)) * R ^ (3 / 2 : ℝ) * Real.log |t|) := by
          have hR_pow : R * R ^ (1 / 2 : ℝ) = R ^ (3 / 2 : ℝ) := by
            calc
              R * R ^ (1 / 2 : ℝ) = R ^ (1 : ℝ) * R ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
              _ = R ^ ((1 : ℝ) + 1 / 2) := by rw [← Real.rpow_add hR_pos]
              _ = R ^ (3 / 2 : ℝ) := by norm_num
          calc
            C * R * Real.log |t| *
                ((2 * Real.pi) ^ (-(1 / 2 : ℝ)) * R ^ (1 / 2 : ℝ))
                = C * (2 * Real.pi) ^ (-(1 / 2 : ℝ)) *
                    (R * R ^ (1 / 2 : ℝ)) * Real.log |t| := by ring
            _ = C * (2 * Real.pi) ^ (-(1 / 2 : ℝ)) *
                    R ^ (3 / 2 : ℝ) * Real.log |t| := by rw [hR_pow]
            _ = C * ((2 * Real.pi) ^ (-(1 / 2 : ℝ)) *
                    R ^ (3 / 2 : ℝ) * Real.log |t|) := by ring

private lemma log_abs_im_le_norm_log {z : ℂ} {t : ℝ}
    (him : z.im = t) (ht : (1 : ℝ) < |t|) :
    Real.log |t| ≤ ‖Complex.log z‖ := by
  have him_le_norm : |t| ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    simpa [him] using h
  have hlog_le : Real.log |t| ≤ Real.log ‖z‖ :=
    Real.log_le_log (by linarith) him_le_norm
  have hlog_norm_le : Real.log ‖z‖ ≤ ‖Complex.log z‖ := by
    rw [← Complex.log_re]
    exact le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  exact hlog_le.trans hlog_norm_le

private lemma norm_one_add_vertical_le_norm_shifted_vertical {Q t : ℝ}
    (hQ : (1 : ℝ) ≤ Q) :
    ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  nlinarith

theorem zetaSurrogate_zero_line_le_const_mul_shiftedLog {Q : ℝ} (hQ : (1 : ℝ) < Q) :
    ∃ C > 0, ∀ t : ℝ, 3 < |t| →
      ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤
        C * (‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖) := by
  obtain ⟨C, hC, hA⟩ := backlundA_zero_line_le_const_mul_log
  let C₀ : ℝ := C * (2 * Real.pi) ^ (-(1 / 2 : ℝ))
  have hfactor_pos : (0 : ℝ) < (2 * Real.pi) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  refine ⟨C₀, by positivity, ?_⟩
  intro t ht
  have ht_ne : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    norm_num at ht
  have hsurrogate_eq : zetaSurrogate ((t : ℂ) * Complex.I) =
      backlundA ((t : ℂ) * Complex.I) := by
    have hs : (t : ℂ) * Complex.I ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
    simp [zetaSurrogate, backlundA, hs]
  have hR_le :
      ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) ≤
        ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _)
      (norm_one_add_vertical_le_norm_shifted_vertical hQ.le) (by norm_num)
  have hlog_le :
      Real.log |t| ≤ ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖ :=
    log_abs_im_le_norm_log
      (z := (Q : ℂ) + (t : ℂ) * Complex.I) (t := t) (by simp) (by linarith)
  have hlog_nonneg : 0 ≤ Real.log |t| := (Real.log_pos (by linarith)).le
  have htarget_pow_nonneg :
      0 ≤ ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hprod_le :
      ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) * Real.log |t| ≤
        ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖ :=
    mul_le_mul hR_le hlog_le hlog_nonneg htarget_pow_nonneg
  rw [hsurrogate_eq]
  calc
    ‖backlundA ((t : ℂ) * Complex.I)‖
        ≤ C * ((2 * Real.pi) ^ (-(1 / 2 : ℝ)) *
          ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) * Real.log |t|) := hA t ht
    _ = C₀ * (‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          Real.log |t|) := by ring
    _ ≤ C₀ * (‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖) := by
        exact mul_le_mul_of_nonneg_left hprod_le (by positivity)

theorem zetaSurrogate_one_line_le_const_mul_shiftedLog {Q : ℝ} (_hQ : (1 : ℝ) < Q) :
    ∃ C > 0, ∀ t : ℝ, 3 < |t| →
      ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) := by
  obtain ⟨C, hC, hζ⟩ := zeta_one_line_le_const_mul_log
  refine ⟨C, hC, ?_⟩
  intro t ht
  have ht_ne : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    norm_num at ht
  have hs : ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [ht_ne] at him
  have hsurrogate_eq :
      zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I) =
        ((t : ℂ) * Complex.I) * riemannZeta ((1 : ℂ) + (t : ℂ) * Complex.I) := by
    rw [zetaSurrogate, if_neg hs]
    ring
  have him_le :
      |t| ≤ ‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ := by
    have h := Complex.abs_im_le_norm (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
    simpa [Complex.add_im, Complex.mul_im] using h
  have hlog_le :
      Real.log |t| ≤ ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
    log_abs_im_le_norm_log
      (z := ((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) (t := t) (by simp) (by linarith)
  have hlog_nonneg : 0 ≤ Real.log |t| := (Real.log_pos (by linarith)).le
  have hnorm_nonneg : 0 ≤ ‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ := norm_nonneg _
  have hprod_le :
      |t| * Real.log |t| ≤
        ‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
    mul_le_mul him_le hlog_le hlog_nonneg hnorm_nonneg
  have hnorm_t : ‖(t : ℂ) * Complex.I‖ = |t| := by simp
  rw [hsurrogate_eq, norm_mul]
  have hζt := hζ t ht
  calc
    ‖(t : ℂ) * Complex.I‖ * ‖riemannZeta ((1 : ℂ) + (t : ℂ) * Complex.I)‖
        = |t| * ‖riemannZeta ((1 : ℂ) + (t : ℂ) * Complex.I)‖ := by rw [hnorm_t]
    _ ≤ |t| * (C * Real.log |t|) := by
          exact mul_le_mul_of_nonneg_left hζt (abs_nonneg t)
    _ = C * (|t| * Real.log |t|) := by ring
    _ ≤ C * (‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) := by
        exact mul_le_mul_of_nonneg_left hprod_le hC.le

/--
At the high-height cutoff from the eccentric-Jensen route, the sharper local RHS is
bounded by Kadiri's published RHS.
-/
theorem eccentricHighRhs_le_kadiriRhs {T : ℝ} (hT : (6800000 : ℝ) ≤ T) :
    eccentricHighRhs T ≤ kadiriRhs T := by
  unfold eccentricHighRhs kadiriRhs riemannZeta.RvM
  have hT_one : (1 : ℝ) ≤ T := by linarith
  have hlog_nonneg : 0 ≤ Real.log T := Real.log_nonneg hT_one
  have hlog_ge_one : (1 : ℝ) ≤ Real.log T := by
    have hexp6800000 : Real.exp (1 : ℝ) ≤ (6800000 : ℝ) := by
      linarith [Real.exp_one_lt_d9]
    have hexp : Real.exp (1 : ℝ) ≤ T := le_trans hexp6800000 hT
    exact (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < T)).2 hexp
  have hloglog_nonneg : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hlog_ge_one
  have h1 : (0.120 : ℝ) * Real.log T ≤ 0.137 * Real.log T :=
    mul_le_mul_of_nonneg_right (by norm_num : (0.120 : ℝ) ≤ 0.137) hlog_nonneg
  have h2 :
      (0.275 : ℝ) * Real.log (Real.log T) ≤ 0.443 * Real.log (Real.log T) :=
    mul_le_mul_of_nonneg_right (by norm_num : (0.275 : ℝ) ≤ 0.443) hloglog_nonneg
  have h3 : (5.13 : ℝ) ≤ 6.1 := by norm_num
  linarith

/-- A point with real part greater than one has nonzero principal complex log. -/
theorem log_ne_zero_of_one_lt_re {z : ℂ} (hz : (1 : ℝ) < z.re) :
    Complex.log z ≠ 0 := by
  intro hlog
  have hnorm : (1 : ℝ) < ‖z‖ := lt_of_lt_of_le hz (Complex.re_le_norm z)
  have hlog_pos : (0 : ℝ) < Real.log ‖z‖ := Real.log_pos hnorm
  have hlog_re : (Complex.log z).re = 0 := by rw [hlog]; simp
  rw [Complex.log_re] at hlog_re
  linarith

theorem zetaSurrogate_zero_line_le_const_mul_shiftedLog_global {Q : ℝ}
    (hQ : (1 : ℝ) < Q) :
    ∃ C > 0, ∀ t : ℝ,
      ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤
        C * (‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖) := by
  obtain ⟨Chigh, hChigh, hhigh⟩ :=
    zetaSurrogate_zero_line_le_const_mul_shiftedLog hQ
  let D : ℝ → ℝ := fun t =>
    ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
      ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖
  have hD_pos : ∀ t : ℝ, 0 < D t := by
    intro t
    have hbase_re : (1 : ℝ) < (((Q : ℂ) + (t : ℂ) * Complex.I).re) := by
      simp [Complex.add_re, Complex.mul_re]
      linarith
    have hbase_ne : ((Q : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp [Complex.add_re, Complex.mul_re] at hre
      linarith
    have hpow_pos :
        0 < ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr hbase_ne) _
    have hlog_pos :
        0 < ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖ :=
      norm_pos_iff.mpr (log_ne_zero_of_one_lt_re hbase_re)
    exact mul_pos hpow_pos hlog_pos
  have hratio_cont : ContinuousOn
      (fun t : ℝ => ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ / D t)
      (Set.Icc (-3 : ℝ) 3) := by
    have hpath_cont : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by fun_prop
    have hnum_cont : Continuous fun t : ℝ => ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ :=
      (zetaSurrogate_differentiable.continuous.comp hpath_cont).norm
    have hshift_cont : Continuous fun t : ℝ => (Q : ℂ) + (t : ℂ) * Complex.I := by fun_prop
    have hpow_cont : Continuous fun t : ℝ =>
        ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) :=
      hshift_cont.norm.rpow_const (fun t => by
        have hne : ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ≠ 0 := by
          apply norm_ne_zero_iff.mpr
          intro h
          have hre := congrArg Complex.re h
          simp [Complex.add_re, Complex.mul_re] at hre
          linarith
        exact Or.inl hne)
    have hlog_cont : Continuous fun t : ℝ =>
        Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I) := by
      refine hshift_cont.clog ?_
      intro t
      refine Or.inl ?_
      simp [Complex.add_re, Complex.mul_re]
      linarith
    have hD_cont : Continuous D := by
      change Continuous (fun t : ℝ =>
        ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖)
      exact hpow_cont.mul hlog_cont.norm
    exact hnum_cont.continuousOn.div hD_cont.continuousOn
      (fun t _ => ne_of_gt (hD_pos t))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hratio_cont
  let C : ℝ := max Chigh (M + 1)
  refine ⟨C, lt_of_lt_of_le hChigh (le_max_left _ _), ?_⟩
  intro t
  by_cases ht : (3 : ℝ) < |t|
  · exact (hhigh t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left Chigh (M + 1))
        (le_of_lt (hD_pos t)))
  · have habs : |t| ≤ (3 : ℝ) := le_of_not_gt ht
    have htIcc : t ∈ Set.Icc (-3 : ℝ) 3 := by
      simpa [Set.mem_Icc] using (abs_le.mp habs)
    have hratio_le_M :
        ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ / D t ≤ M := by
      exact (le_abs_self _).trans (hM t htIcc)
    have hmain :
        ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤ M * D t :=
      (div_le_iff₀ (hD_pos t)).mp hratio_le_M
    have hM_le_C : M ≤ C := by
      calc
        M ≤ M + 1 := by linarith
        _ ≤ C := le_max_right _ _
    exact hmain.trans (mul_le_mul_of_nonneg_right hM_le_C (le_of_lt (hD_pos t)))

theorem zetaSurrogate_one_line_le_const_mul_shiftedLog_global {Q : ℝ}
    (hQ : (1 : ℝ) < Q) :
    ∃ C > 0, ∀ t : ℝ,
      ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) := by
  obtain ⟨Chigh, hChigh, hhigh⟩ :=
    zetaSurrogate_one_line_le_const_mul_shiftedLog hQ
  let D : ℝ → ℝ := fun t =>
    ‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
      ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
  have hD_pos : ∀ t : ℝ, 0 < D t := by
    intro t
    have hbase_re : (1 : ℝ) <
        ((((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re) := by
      simp [Complex.add_re, Complex.mul_re]
      linarith
    have hbase_ne : (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp [Complex.add_re, Complex.mul_re] at hre
      linarith
    have hnorm_pos :
        0 < ‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ :=
      norm_pos_iff.mpr hbase_ne
    have hlog_pos :
        0 < ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
      norm_pos_iff.mpr (log_ne_zero_of_one_lt_re hbase_re)
    exact mul_pos hnorm_pos hlog_pos
  have hratio_cont : ContinuousOn
      (fun t : ℝ => ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ / D t)
      (Set.Icc (-3 : ℝ) 3) := by
    have hpath_cont : Continuous fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I := by fun_prop
    have hnum_cont : Continuous fun t : ℝ =>
        ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ :=
      (zetaSurrogate_differentiable.continuous.comp hpath_cont).norm
    have hshift_cont : Continuous fun t : ℝ =>
        ((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by fun_prop
    have hlog_cont : Continuous fun t : ℝ =>
        Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
      refine hshift_cont.clog ?_
      intro t
      refine Or.inl ?_
      simp [Complex.add_re, Complex.mul_re]
      linarith
    have hD_cont : Continuous D := by
      change Continuous (fun t : ℝ =>
        ‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
      exact hshift_cont.norm.mul hlog_cont.norm
    exact hnum_cont.continuousOn.div hD_cont.continuousOn
      (fun t _ => ne_of_gt (hD_pos t))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hratio_cont
  let C : ℝ := max Chigh (M + 1)
  refine ⟨C, lt_of_lt_of_le hChigh (le_max_left _ _), ?_⟩
  intro t
  by_cases ht : (3 : ℝ) < |t|
  · exact (hhigh t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left Chigh (M + 1))
        (le_of_lt (hD_pos t)))
  · have habs : |t| ≤ (3 : ℝ) := le_of_not_gt ht
    have htIcc : t ∈ Set.Icc (-3 : ℝ) 3 := by
      simpa [Set.mem_Icc] using (abs_le.mp habs)
    have hratio_le_M :
        ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ / D t ≤ M := by
      exact (le_abs_self _).trans (hM t htIcc)
    have hmain :
        ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * D t :=
      (div_le_iff₀ (hD_pos t)).mp hratio_le_M
    have hM_le_C : M ≤ C := by
      calc
        M ≤ M + 1 := by linarith
        _ ≤ C := le_max_right _ _
    exact hmain.trans (mul_le_mul_of_nonneg_right hM_le_C (le_of_lt (hD_pos t)))

/-- On a shifted vertical closed strip with positive real part, `Q + z` is in the slit plane. -/
theorem shifted_mem_slitPlane_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (0 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    (Q : ℂ) + z ∈ Complex.slitPlane := by
  refine Or.inl ?_
  have hzre : σ₀ ≤ z.re := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.1
  have hpos : (0 : ℝ) < Q + z.re := by nlinarith
  simpa using hpos

/-- On a shifted vertical closed strip with `Q + σ₀ > 1`, `log (Q + z)` is nonzero. -/
theorem shifted_log_ne_zero_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (1 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    Complex.log ((Q : ℂ) + z) ≠ 0 := by
  apply log_ne_zero_of_one_lt_re
  have hzre : σ₀ ≤ z.re := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.1
  have hpos : (1 : ℝ) < Q + z.re := by nlinarith
  simpa using hpos

/-- On a shifted vertical closed strip with `Q + σ₀ > 1`, `log (Q + z)` is in the slit plane. -/
theorem shifted_log_mem_slitPlane_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (1 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    Complex.log ((Q : ℂ) + z) ∈ Complex.slitPlane := by
  refine Or.inl ?_
  rw [Complex.log_re]
  apply Real.log_pos
  have hzre : σ₀ ≤ z.re := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.1
  have hpos : (1 : ℝ) < (((Q : ℂ) + z).re) := by
    simp
    nlinarith
  exact lt_of_lt_of_le hpos (Complex.re_le_norm _)

/-- The closure of a Hadamard open vertical strip is the corresponding closed strip. -/
theorem verticalStrip_closure_eq_verticalClosedStrip {σ₀ σ₁ : ℝ} (hσ : σ₀ ≠ σ₁) :
    closure (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁) =
      Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁ := by
  rw [Complex.HadamardThreeLines.verticalStrip, Complex.HadamardThreeLines.verticalClosedStrip,
    Complex.closure_preimage_re, closure_Ioo hσ]

/-- The shifted principal log is differentiable on a positive-real-part vertical strip. -/
theorem shifted_log_diffContOnCl_on_verticalStrip {Q σ₀ σ₁ : ℝ}
    (hσ : σ₀ < σ₁) (hQ : (0 : ℝ) < Q + σ₀) :
    DiffContOnCl ℂ (fun z : ℂ => Complex.log ((Q : ℂ) + z))
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁) := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [verticalStrip_closure_eq_verticalClosedStrip hσ.ne]
  exact ((differentiableOn_const (Q : ℂ)).add differentiableOn_id).clog
    (fun z hz => shifted_mem_slitPlane_on_verticalClosedStrip hQ hz)

/-- Constant complex powers of `Q + z` are differentiable on a positive shifted strip. -/
theorem shifted_cpow_const_diffContOnCl_on_verticalStrip {Q σ₀ σ₁ : ℝ} (c : ℂ)
    (hσ : σ₀ < σ₁) (hQ : (0 : ℝ) < Q + σ₀) :
    DiffContOnCl ℂ (fun z : ℂ => ((Q : ℂ) + z) ^ c)
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁) := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [verticalStrip_closure_eq_verticalClosedStrip hσ.ne]
  exact ((differentiableOn_const (Q : ℂ)).add differentiableOn_id).cpow_const
    (fun z hz => shifted_mem_slitPlane_on_verticalClosedStrip hQ hz)

/-- Constant complex powers of `log (Q + z)` are differentiable on a shifted strip. -/
theorem shifted_log_cpow_const_diffContOnCl_on_verticalStrip {Q σ₀ σ₁ : ℝ} (c : ℂ)
    (hσ : σ₀ < σ₁) (hQ : (1 : ℝ) < Q + σ₀) :
    DiffContOnCl ℂ (fun z : ℂ => (Complex.log ((Q : ℂ) + z)) ^ c)
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁) := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [verticalStrip_closure_eq_verticalClosedStrip hσ.ne]
  have hQ0 : (0 : ℝ) < Q + σ₀ := by linarith
  exact (((differentiableOn_const (Q : ℂ)).add differentiableOn_id).clog
    (fun z hz => shifted_mem_slitPlane_on_verticalClosedStrip hQ0 hz)).cpow_const
    (fun z hz => shifted_log_mem_slitPlane_on_verticalClosedStrip hQ hz)

/-- The shifted log-power normalizer used by the PL-log interpolation shell. -/
noncomputable def shiftedLogPowerNormalizer (Q : ℝ) (α β : ℂ) (z : ℂ) : ℂ :=
  ((Q : ℂ) + z) ^ α * (Complex.log ((Q : ℂ) + z)) ^ β

/-- For real exponent weights, the normalizer norm is the expected product of real powers. -/
theorem norm_shiftedLogPowerNormalizer_ofReal (Q α β : ℝ) (z : ℂ) :
    ‖shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) z‖ =
      ‖(Q : ℂ) + z‖ ^ α * ‖Complex.log ((Q : ℂ) + z)‖ ^ β := by
  unfold shiftedLogPowerNormalizer
  rw [norm_mul]
  simp

/-- The shifted log-power normalizer is nonzero on shifted strips with `Q + σ₀ > 1`. -/
theorem shiftedLogPowerNormalizer_ne_zero_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ}
    (α β : ℂ) {z : ℂ} (hQ : (1 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    shiftedLogPowerNormalizer Q α β z ≠ 0 := by
  unfold shiftedLogPowerNormalizer
  refine mul_ne_zero ?_ ?_
  · rw [Complex.cpow_ne_zero_iff]
    have hQ0 : (0 : ℝ) < Q + σ₀ := by linarith
    exact Or.inl (Complex.slitPlane_ne_zero
      (shifted_mem_slitPlane_on_verticalClosedStrip hQ0 hz))
  · rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (Complex.slitPlane_ne_zero
      (shifted_log_mem_slitPlane_on_verticalClosedStrip hQ hz))

/-- The shifted log-power normalizer is differentiable on shifted positive strips. -/
theorem shiftedLogPowerNormalizer_diffContOnCl_on_verticalStrip {Q σ₀ σ₁ : ℝ}
    (α β : ℂ) (hσ : σ₀ < σ₁) (hQ : (1 : ℝ) < Q + σ₀) :
    DiffContOnCl ℂ (shiftedLogPowerNormalizer Q α β)
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁) := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [verticalStrip_closure_eq_verticalClosedStrip hσ.ne]
  unfold shiftedLogPowerNormalizer
  have hQ0 : (0 : ℝ) < Q + σ₀ := by linarith
  exact
    (((differentiableOn_const (Q : ℂ)).add differentiableOn_id).cpow_const
      (fun z hz => shifted_mem_slitPlane_on_verticalClosedStrip hQ0 hz)).mul
    ((((differentiableOn_const (Q : ℂ)).add differentiableOn_id).clog
      (fun z hz => shifted_mem_slitPlane_on_verticalClosedStrip hQ0 hz)).cpow_const
      (fun z hz => shifted_log_mem_slitPlane_on_verticalClosedStrip hQ hz))

/-- Rotated shifted base for the two-edge Backlund convexity normalizer. -/
noncomputable def rotatedShiftedBase (Q : ℝ) (z : ℂ) : ℂ :=
  -Complex.I * ((Q : ℂ) + z)

theorem rotatedShiftedBase_im (Q : ℝ) (z : ℂ) :
    (rotatedShiftedBase Q z).im = -(Q + z.re) := by
  simp [rotatedShiftedBase, Complex.mul_im]

theorem rotatedShiftedBase_norm (Q : ℝ) (z : ℂ) :
    ‖rotatedShiftedBase Q z‖ = ‖(Q : ℂ) + z‖ := by
  simp [rotatedShiftedBase]

/-- On a positive shifted vertical strip, the rotated base misses the log branch cut. -/
theorem rotatedShiftedBase_mem_slitPlane_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (0 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    rotatedShiftedBase Q z ∈ Complex.slitPlane := by
  refine Or.inr ?_
  have hzre : σ₀ ≤ z.re := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.1
  have hpos : (0 : ℝ) < Q + z.re := by nlinarith
  rw [rotatedShiftedBase_im]
  exact neg_ne_zero.mpr hpos.ne'

theorem rotatedShiftedBase_ne_zero_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (0 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    rotatedShiftedBase Q z ≠ 0 :=
  Complex.slitPlane_ne_zero (rotatedShiftedBase_mem_slitPlane_on_verticalClosedStrip hQ hz)

/-- The principal log of the rotated base is nonzero on a positive shifted strip. -/
theorem rotatedShiftedBase_log_ne_zero_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (0 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    Complex.log (rotatedShiftedBase Q z) ≠ 0 := by
  intro hlog
  have hbase_ne := rotatedShiftedBase_ne_zero_on_verticalClosedStrip hQ hz
  have hbase_one : rotatedShiftedBase Q z = 1 := by
    calc
      rotatedShiftedBase Q z = Complex.exp (Complex.log (rotatedShiftedBase Q z)) := by
        rw [Complex.exp_log hbase_ne]
      _ = 1 := by simp [hlog]
  have him := congrArg Complex.im hbase_one
  have hzre : σ₀ ≤ z.re := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.1
  have hpos : (0 : ℝ) < Q + z.re := by nlinarith
  rw [rotatedShiftedBase_im] at him
  simp at him
  nlinarith

/-- Complex-linear exponent interpolating two real edge powers. -/
noncomputable def twoEdgeExponent (σ₀ σ₁ α₀ α₁ : ℝ) (z : ℂ) : ℂ :=
  (α₀ : ℂ) + (((α₁ - α₀) / (σ₁ - σ₀) : ℝ) : ℂ) * (z - (σ₀ : ℂ))

/-- The rotated two-edge log-power normalizer. -/
noncomputable def rotatedShiftedLogPowerTwoEdgeNormalizer
    (Q σ₀ σ₁ α₀ α₁ : ℝ) (z : ℂ) : ℂ :=
  rotatedShiftedBase Q z ^ twoEdgeExponent σ₀ σ₁ α₀ α₁ z *
    Complex.log (rotatedShiftedBase Q z)

theorem rotatedShiftedLogPowerTwoEdgeNormalizer_ne_zero_on_verticalClosedStrip
    {Q σ₀ σ₁ α₀ α₁ : ℝ} {z : ℂ} (hQ : (0 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    rotatedShiftedLogPowerTwoEdgeNormalizer Q σ₀ σ₁ α₀ α₁ z ≠ 0 := by
  unfold rotatedShiftedLogPowerTwoEdgeNormalizer
  refine mul_ne_zero ?_ ?_
  · rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (rotatedShiftedBase_ne_zero_on_verticalClosedStrip hQ hz)
  · exact rotatedShiftedBase_log_ne_zero_on_verticalClosedStrip hQ hz

/--
The rotated two-edge normalizer is differentiable on positive shifted vertical strips.
This packages the branch-control part of the weighted PL route.
-/
theorem rotatedShiftedLogPowerTwoEdgeNormalizer_diffContOnCl_on_verticalStrip
    {Q σ₀ σ₁ α₀ α₁ : ℝ} (hσ : σ₀ < σ₁) (hQ : (0 : ℝ) < Q + σ₀) :
    DiffContOnCl ℂ (rotatedShiftedLogPowerTwoEdgeNormalizer Q σ₀ σ₁ α₀ α₁)
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁) := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [verticalStrip_closure_eq_verticalClosedStrip hσ.ne]
  unfold rotatedShiftedLogPowerTwoEdgeNormalizer rotatedShiftedBase twoEdgeExponent
  have hbase : DifferentiableOn ℂ (fun z : ℂ => -Complex.I * ((Q : ℂ) + z))
      (Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) := by
    fun_prop
  have hexponent : DifferentiableOn ℂ
      (fun z : ℂ =>
        (α₀ : ℂ) + (((α₁ - α₀) / (σ₁ - σ₀) : ℝ) : ℂ) * (z - (σ₀ : ℂ)))
      (Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) := by
    fun_prop
  exact
    (hbase.cpow hexponent
      (fun z hz => rotatedShiftedBase_mem_slitPlane_on_verticalClosedStrip
        (Q := Q) (σ₀ := σ₀) (σ₁ := σ₁) hQ hz)).mul
    (hbase.clog
      (fun z hz => rotatedShiftedBase_mem_slitPlane_on_verticalClosedStrip
        (Q := Q) (σ₀ := σ₀) (σ₁ := σ₁) hQ hz))

theorem twoEdgeExponent_re (σ₀ σ₁ α₀ α₁ : ℝ) (z : ℂ) :
    (twoEdgeExponent σ₀ σ₁ α₀ α₁ z).re =
      α₀ + ((α₁ - α₀) / (σ₁ - σ₀)) * (z.re - σ₀) := by
  simp only [twoEdgeExponent, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.sub_re, Complex.sub_im, zero_mul, sub_zero]

theorem twoEdgeExponent_im (σ₀ σ₁ α₀ α₁ : ℝ) (z : ℂ) :
    (twoEdgeExponent σ₀ σ₁ α₀ α₁ z).im =
      ((α₁ - α₀) / (σ₁ - σ₀)) * z.im := by
  simp only [twoEdgeExponent, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.sub_im, Complex.sub_re, zero_add, zero_mul]
  ring

theorem twoEdgeExponent_re_eq_interp {σ₀ σ₁ α₀ α₁ : ℝ} (hσ : σ₀ < σ₁)
    (z : ℂ) :
    (twoEdgeExponent σ₀ σ₁ α₀ α₁ z).re =
      α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
        α₁ * ((z.re - σ₀) / (σ₁ - σ₀)) := by
  rw [twoEdgeExponent_re]
  have hσne : σ₁ - σ₀ ≠ 0 := sub_ne_zero.mpr hσ.ne'
  field_simp [hσne]
  ring

/--
On the upper half of a positive shifted strip with decreasing edge exponents,
the rotated two-edge normalizer has exactly the polynomial-log size needed for
the Backlund convexity read-off.
-/
theorem rotatedShiftedLogPowerTwoEdgeNormalizer_norm_le_of_upperHalf
    {Q σ₀ σ₁ α₀ α₁ : ℝ} {z : ℂ} (hσ : σ₀ < σ₁)
    (hQ : (0 : ℝ) < Q + σ₀)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)
    (hα : α₁ ≤ α₀) (hz_im : 0 ≤ z.im) :
    ‖rotatedShiftedLogPowerTwoEdgeNormalizer Q σ₀ σ₁ α₀ α₁ z‖ ≤
      ‖rotatedShiftedBase Q z‖ ^
        (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
          α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
        ‖Complex.log (rotatedShiftedBase Q z)‖ := by
  have hbase_ne := rotatedShiftedBase_ne_zero_on_verticalClosedStrip hQ hz
  have hzre : σ₀ ≤ z.re := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.1
  have hbase_im_neg : (rotatedShiftedBase Q z).im < 0 := by
    rw [rotatedShiftedBase_im]
    nlinarith
  have harg_nonpos : Complex.arg (rotatedShiftedBase Q z) ≤ 0 :=
    (Complex.arg_neg_iff.mpr hbase_im_neg).le
  have hcoef_nonpos : (α₁ - α₀) / (σ₁ - σ₀) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hα) (sub_nonneg.mpr hσ.le)
  have him_nonpos : (twoEdgeExponent σ₀ σ₁ α₀ α₁ z).im ≤ 0 := by
    rw [twoEdgeExponent_im]
    exact mul_nonpos_of_nonpos_of_nonneg hcoef_nonpos hz_im
  have hprod_nonneg :
      0 ≤ Complex.arg (rotatedShiftedBase Q z) *
        (twoEdgeExponent σ₀ σ₁ α₀ α₁ z).im :=
    mul_nonneg_of_nonpos_of_nonpos harg_nonpos him_nonpos
  have hexp_ge_one :
      (1 : ℝ) ≤ Real.exp (Complex.arg (rotatedShiftedBase Q z) *
        (twoEdgeExponent σ₀ σ₁ α₀ α₁ z).im) :=
    by simpa using Real.exp_le_exp.mpr hprod_nonneg
  have hpow_nonneg :
      0 ≤ ‖rotatedShiftedBase Q z‖ ^
        (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
          α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) :=
    Real.rpow_nonneg (norm_nonneg _) _
  unfold rotatedShiftedLogPowerTwoEdgeNormalizer
  rw [norm_mul, Complex.norm_cpow_of_ne_zero hbase_ne,
    twoEdgeExponent_re_eq_interp hσ]
  have hdiv_le :
      ‖rotatedShiftedBase Q z‖ ^
          (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
            α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) /
        Real.exp (Complex.arg (rotatedShiftedBase Q z) *
          (twoEdgeExponent σ₀ σ₁ α₀ α₁ z).im)
        ≤
      ‖rotatedShiftedBase Q z‖ ^
          (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
            α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) := by
    rw [div_le_iff₀ (Real.exp_pos _)]
    simpa using mul_le_mul_of_nonneg_left hexp_ge_one hpow_nonneg
  exact mul_le_mul_of_nonneg_right hdiv_le (norm_nonneg _)

/--
Phragmen-Lindelöf growth and uniform boundary control imply boundedness of the
norm on the corresponding closed vertical strip.
-/
theorem bddAbove_norm_on_verticalClosedStrip_of_phragmen_lindelof {g : ℂ → ℂ}
    {σ₀ σ₁ C : ℝ}
    (hd : DiffContOnCl ℂ g (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁))
    (hgrowth : ∃ c < Real.pi / (σ₁ - σ₀), ∃ B,
      g =O[Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo σ₀ σ₁)]
        fun z => Real.exp (B * Real.exp (c * |z.im|)))
    (hleft : ∀ z : ℂ, z.re = σ₀ → ‖g z‖ ≤ C)
    (hright : ∀ z : ℂ, z.re = σ₁ → ‖g z‖ ≤ C) :
    BddAbove (Set.image (fun z => ‖g z‖)
      (Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)) := by
  refine ⟨C, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact PhragmenLindelof.vertical_strip
    (f := g) (a := σ₀) (b := σ₁) (z := z)
    (by simpa [Complex.HadamardThreeLines.verticalStrip] using hd)
    hgrowth hleft hright
    (by simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.1)
    (by simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.2)

/--
Hadamard three-lines for a function after division by a supplied nonzero
normalizer. This is the reusable PL-log shell: the concrete shifted log-power
normalizer is a separate input.
-/
theorem log_phragmen_lindelof_normalized {f normalizer : ℂ → ℂ}
    {σ₀ σ₁ C₀ C₁ : ℝ} {z : ℂ} (hσ : σ₀ < σ₁)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)
    (hnormalizer :
      ∀ w ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁, normalizer w ≠ 0)
    (hd : DiffContOnCl ℂ (fun w => f w / normalizer w)
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁))
    (hB : BddAbove (Set.image (fun w => ‖f w / normalizer w‖)
      (Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)))
    (hleft : ∀ w : ℂ, w.re = σ₀ → ‖f w‖ ≤ C₀ * ‖normalizer w‖)
    (hright : ∀ w : ℂ, w.re = σ₁ → ‖f w‖ ≤ C₁ * ‖normalizer w‖) :
    ‖f z‖ ≤
      (C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
        C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀))) * ‖normalizer z‖ := by
  have hleft' :
      ∀ w ∈ Complex.re ⁻¹' ({σ₀} : Set ℝ), ‖f w / normalizer w‖ ≤ C₀ := by
    intro w hw
    have hwre : w.re = σ₀ := by simpa using hw
    have hwstrip : w ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁ := by
      simp [Complex.HadamardThreeLines.verticalClosedStrip, hwre, hσ.le]
    have hnorm_pos : 0 < ‖normalizer w‖ :=
      norm_pos_iff.mpr (hnormalizer w hwstrip)
    rw [norm_div]
    exact (div_le_iff₀ hnorm_pos).2 (hleft w hwre)
  have hright' :
      ∀ w ∈ Complex.re ⁻¹' ({σ₁} : Set ℝ), ‖f w / normalizer w‖ ≤ C₁ := by
    intro w hw
    have hwre : w.re = σ₁ := by simpa using hw
    have hwstrip : w ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁ := by
      simp [Complex.HadamardThreeLines.verticalClosedStrip, hwre, hσ.le]
    have hnorm_pos : 0 < ‖normalizer w‖ :=
      norm_pos_iff.mpr (hnormalizer w hwstrip)
    rw [norm_div]
    exact (div_le_iff₀ hnorm_pos).2 (hright w hwre)
  have hnorm :
      ‖f z / normalizer z‖ ≤
        C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
          C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀)) :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (f := fun w => f w / normalizer w) (z := z) (a := C₀) (b := C₁)
      (l := σ₀) (u := σ₁) hσ hz hd hB hleft' hright'
  have hnormalizer_z : normalizer z ≠ 0 := hnormalizer z hz
  have hmul : ‖f z / normalizer z‖ * ‖normalizer z‖ = ‖f z‖ := by
    rw [norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hnormalizer_z)]
  rw [← hmul]
  exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg (normalizer z))

/--
Hadamard three-lines with the concrete shifted log-power normalizer and real
exponent weights.
-/
theorem log_phragmen_lindelof_shiftedLogPower {f : ℂ → ℂ}
    {Q σ₀ σ₁ C₀ C₁ α β : ℝ} {z : ℂ} (hσ : σ₀ < σ₁)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)
    (hQ : (1 : ℝ) < Q + σ₀)
    (hd : DiffContOnCl ℂ
      (fun w => f w / shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w)
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁))
    (hB : BddAbove (Set.image
      (fun w => ‖f w / shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w‖)
      (Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)))
    (hleft : ∀ w : ℂ, w.re = σ₀ →
      ‖f w‖ ≤ C₀ * (‖(Q : ℂ) + w‖ ^ α * ‖Complex.log ((Q : ℂ) + w)‖ ^ β))
    (hright : ∀ w : ℂ, w.re = σ₁ →
      ‖f w‖ ≤ C₁ * (‖(Q : ℂ) + w‖ ^ α * ‖Complex.log ((Q : ℂ) + w)‖ ^ β)) :
    ‖f z‖ ≤
      (C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
        C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀))) *
        (‖(Q : ℂ) + z‖ ^ α * ‖Complex.log ((Q : ℂ) + z)‖ ^ β) := by
  have hmain := log_phragmen_lindelof_normalized
    (f := f) (normalizer := shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ))
    (hσ := hσ) hz
    (fun w hw => shiftedLogPowerNormalizer_ne_zero_on_verticalClosedStrip
      (α : ℂ) (β : ℂ) hQ hw)
    hd hB
    (fun w hw => by
      simpa [norm_shiftedLogPowerNormalizer_ofReal] using hleft w hw)
    (fun w hw => by
      simpa [norm_shiftedLogPowerNormalizer_ofReal] using hright w hw)
  simpa [norm_shiftedLogPowerNormalizer_ofReal] using hmain

/--
Log-augmented Phragmen-Lindelöf in a vertical strip with shifted log-power
weights. The normalized quotient is controlled by the usual PL growth condition,
so no closed-strip boundedness hypothesis is required.
-/
theorem log_phragmen_lindelof {f : ℂ → ℂ}
    {Q σ₀ σ₁ C₀ C₁ α β : ℝ} {z : ℂ} (hσ : σ₀ < σ₁)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)
    (hQ : (1 : ℝ) < Q + σ₀)
    (hd : DiffContOnCl ℂ
      (fun w => f w / shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w)
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁))
    (hgrowth : ∃ c < Real.pi / (σ₁ - σ₀), ∃ B,
      (fun w => f w / shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w)
        =O[Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            Filter.principal (Complex.re ⁻¹' Set.Ioo σ₀ σ₁)]
          fun w => Real.exp (B * Real.exp (c * |w.im|)))
    (hleft : ∀ w : ℂ, w.re = σ₀ →
      ‖f w‖ ≤ C₀ * (‖(Q : ℂ) + w‖ ^ α * ‖Complex.log ((Q : ℂ) + w)‖ ^ β))
    (hright : ∀ w : ℂ, w.re = σ₁ →
      ‖f w‖ ≤ C₁ * (‖(Q : ℂ) + w‖ ^ α * ‖Complex.log ((Q : ℂ) + w)‖ ^ β)) :
    ‖f z‖ ≤
      (C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
        C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀))) *
        (‖(Q : ℂ) + z‖ ^ α * ‖Complex.log ((Q : ℂ) + z)‖ ^ β) := by
  let g : ℂ → ℂ := fun w => f w / shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w
  have hleft_g : ∀ w : ℂ, w.re = σ₀ → ‖g w‖ ≤ C₀ := by
    intro w hw
    have hwstrip : w ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁ := by
      simp [Complex.HadamardThreeLines.verticalClosedStrip, hw, hσ.le]
    have hnorm_pos : 0 < ‖shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w‖ :=
      norm_pos_iff.mpr (shiftedLogPowerNormalizer_ne_zero_on_verticalClosedStrip
        (Q := Q) (σ₀ := σ₀) (σ₁ := σ₁) (α := (α : ℂ)) (β := (β : ℂ)) hQ hwstrip)
    change ‖f w / shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w‖ ≤ C₀
    rw [norm_div]
    exact (div_le_iff₀ hnorm_pos).2 (by
      simpa [norm_shiftedLogPowerNormalizer_ofReal] using hleft w hw)
  have hright_g : ∀ w : ℂ, w.re = σ₁ → ‖g w‖ ≤ C₁ := by
    intro w hw
    have hwstrip : w ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁ := by
      simp [Complex.HadamardThreeLines.verticalClosedStrip, hw, hσ.le]
    have hnorm_pos : 0 < ‖shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w‖ :=
      norm_pos_iff.mpr (shiftedLogPowerNormalizer_ne_zero_on_verticalClosedStrip
        (Q := Q) (σ₀ := σ₀) (σ₁ := σ₁) (α := (α : ℂ)) (β := (β : ℂ)) hQ hwstrip)
    change ‖f w / shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w‖ ≤ C₁
    rw [norm_div]
    exact (div_le_iff₀ hnorm_pos).2 (by
      simpa [norm_shiftedLogPowerNormalizer_ofReal] using hright w hw)
  have hB : BddAbove (Set.image
      (fun w => ‖f w / shiftedLogPowerNormalizer Q (α : ℂ) (β : ℂ) w‖)
      (Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)) := by
    simpa [g] using
      bddAbove_norm_on_verticalClosedStrip_of_phragmen_lindelof
        (g := g) (σ₀ := σ₀) (σ₁ := σ₁) (C := max C₀ C₁)
        (by simpa [g] using hd)
        (by simpa [g] using hgrowth)
        (fun w hw => (hleft_g w hw).trans (le_max_left C₀ C₁))
        (fun w hw => (hright_g w hw).trans (le_max_right C₀ C₁))
  exact log_phragmen_lindelof_shiftedLogPower
    (f := f) (Q := Q) (σ₀ := σ₀) (σ₁ := σ₁)
    (C₀ := C₀) (C₁ := C₁) (α := α) (β := β)
    hσ hz hQ hd hB hleft hright

/--
Two-edge Phragmen-Lindelöf with a rotated log-power normalizer. The geometric
read-off from the rotated normalizer is derived for decreasing edge powers on
the upper half-strip.
-/
theorem log_phragmen_lindelof_shiftedLogPower_twoEdge {f : ℂ → ℂ}
    {Q σ₀ σ₁ C₀ C₁ α₀ α₁ k : ℝ} {z : ℂ} (hσ : σ₀ < σ₁)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)
    (hQ : (0 : ℝ) < Q + σ₀) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hα : α₁ ≤ α₀) (hz_im : 0 ≤ z.im) (hk : (1 : ℝ) ≤ k)
    (hd : DiffContOnCl ℂ
      (fun w => f w / rotatedShiftedLogPowerTwoEdgeNormalizer Q σ₀ σ₁ α₀ α₁ w)
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁))
    (hgrowth : ∃ c < Real.pi / (σ₁ - σ₀), ∃ B,
      (fun w => f w / rotatedShiftedLogPowerTwoEdgeNormalizer Q σ₀ σ₁ α₀ α₁ w)
        =O[Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            Filter.principal (Complex.re ⁻¹' Set.Ioo σ₀ σ₁)]
          fun w => Real.exp (B * Real.exp (c * |w.im|)))
    (hleft : ∀ w : ℂ, w.re = σ₀ →
      ‖f w‖ ≤ C₀ * ‖rotatedShiftedLogPowerTwoEdgeNormalizer Q σ₀ σ₁ α₀ α₁ w‖)
    (hright : ∀ w : ℂ, w.re = σ₁ →
      ‖f w‖ ≤ C₁ * ‖rotatedShiftedLogPowerTwoEdgeNormalizer Q σ₀ σ₁ α₀ α₁ w‖) :
    ‖f z‖ ≤
      (C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
        C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀))) *
        k * (‖rotatedShiftedBase Q z‖ ^
          (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
            α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
          ‖Complex.log (rotatedShiftedBase Q z)‖) := by
  let normalizer : ℂ → ℂ :=
    rotatedShiftedLogPowerTwoEdgeNormalizer Q σ₀ σ₁ α₀ α₁
  let g : ℂ → ℂ := fun w => f w / normalizer w
  have hnormalizer :
      ∀ w ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁, normalizer w ≠ 0 := by
    intro w hw
    exact rotatedShiftedLogPowerTwoEdgeNormalizer_ne_zero_on_verticalClosedStrip hQ hw
  have hleft_g : ∀ w : ℂ, w.re = σ₀ → ‖g w‖ ≤ C₀ := by
    intro w hw
    have hwstrip : w ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁ := by
      simp [Complex.HadamardThreeLines.verticalClosedStrip, hw, hσ.le]
    have hnorm_pos : 0 < ‖normalizer w‖ := norm_pos_iff.mpr (hnormalizer w hwstrip)
    change ‖f w / normalizer w‖ ≤ C₀
    rw [norm_div]
    exact (div_le_iff₀ hnorm_pos).2 (by simpa [normalizer] using hleft w hw)
  have hright_g : ∀ w : ℂ, w.re = σ₁ → ‖g w‖ ≤ C₁ := by
    intro w hw
    have hwstrip : w ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁ := by
      simp [Complex.HadamardThreeLines.verticalClosedStrip, hw, hσ.le]
    have hnorm_pos : 0 < ‖normalizer w‖ := norm_pos_iff.mpr (hnormalizer w hwstrip)
    change ‖f w / normalizer w‖ ≤ C₁
    rw [norm_div]
    exact (div_le_iff₀ hnorm_pos).2 (by simpa [normalizer] using hright w hw)
  have hB : BddAbove (Set.image (fun w => ‖f w / normalizer w‖)
      (Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁)) := by
    simpa [g, normalizer] using
      bddAbove_norm_on_verticalClosedStrip_of_phragmen_lindelof
        (g := g) (σ₀ := σ₀) (σ₁ := σ₁) (C := max C₀ C₁)
        (by simpa [g, normalizer] using hd)
        (by simpa [g, normalizer] using hgrowth)
        (fun w hw => (hleft_g w hw).trans (le_max_left C₀ C₁))
        (fun w hw => (hright_g w hw).trans (le_max_right C₀ C₁))
  have hmain := log_phragmen_lindelof_normalized
    (f := f) (normalizer := normalizer) (hσ := hσ) hz
    hnormalizer hd hB hleft hright
  have hinterp_nonneg :
      0 ≤ C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
        C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀)) := by
    exact mul_nonneg (Real.rpow_nonneg hC₀ _) (Real.rpow_nonneg hC₁ _)
  have hgeom :
      ‖normalizer z‖ ≤
        k * (‖rotatedShiftedBase Q z‖ ^
          (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
            α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
          ‖Complex.log (rotatedShiftedBase Q z)‖) := by
    have hgeom_one :=
      rotatedShiftedLogPowerTwoEdgeNormalizer_norm_le_of_upperHalf
        (Q := Q) (σ₀ := σ₀) (σ₁ := σ₁) (α₀ := α₀) (α₁ := α₁)
        (z := z) hσ hQ hz hα hz_im
    have htarget_nonneg :
        0 ≤ ‖rotatedShiftedBase Q z‖ ^
          (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
            α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
          ‖Complex.log (rotatedShiftedBase Q z)‖ := by
      exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)
    exact hgeom_one.trans (by
      calc
        ‖rotatedShiftedBase Q z‖ ^
            (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
              α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
            ‖Complex.log (rotatedShiftedBase Q z)‖
            ≤ 1 * (‖rotatedShiftedBase Q z‖ ^
              (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
                α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
              ‖Complex.log (rotatedShiftedBase Q z)‖) := by rw [one_mul]
        _ ≤ k * (‖rotatedShiftedBase Q z‖ ^
              (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
                α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
              ‖Complex.log (rotatedShiftedBase Q z)‖) := by
            exact mul_le_mul_of_nonneg_right hk htarget_nonneg)
  calc
    ‖f z‖ ≤
        (C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
          C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀))) * ‖normalizer z‖ := hmain
    _ ≤
        (C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
          C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀))) *
          (k * (‖rotatedShiftedBase Q z‖ ^
            (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
              α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
            ‖Complex.log (rotatedShiftedBase Q z)‖)) := by
          exact mul_le_mul_of_nonneg_left (by simpa [normalizer] using hgeom) hinterp_nonneg
    _ =
        (C₀ ^ (1 - (z.re - σ₀) / (σ₁ - σ₀)) *
          C₁ ^ ((z.re - σ₀) / (σ₁ - σ₀))) *
          k * (‖rotatedShiftedBase Q z‖ ^
            (α₀ * (1 - (z.re - σ₀) / (σ₁ - σ₀)) +
              α₁ * ((z.re - σ₀) / (σ₁ - σ₀))) *
            ‖Complex.log (rotatedShiftedBase Q z)‖) := by ring

/-- Reflected product used in the midpoint convexity step. -/
noncomputable def midpointReflectedProduct (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z * star (f ((1 : ℂ) - star z))

/-- Constant-exponent majorant for the midpoint reflected-product route. -/
noncomputable def midpointReflectedProductMajorant (Q C₀ C₁ : ℝ) (z : ℂ) : ℂ :=
  ((C₀ * C₁ : ℝ) : ℂ) *
    (((Q : ℂ) + z) ^ (((3 / 2 : ℝ) : ℂ)) *
      (((Q + 1 : ℝ) : ℂ) - z) *
      Complex.log ((Q : ℂ) + z) *
      Complex.log ((((Q + 1 : ℝ) : ℂ) - z)))

theorem zetaSurrogate_conj (z : ℂ) :
    zetaSurrogate (star z) = star (zetaSurrogate z) := by
  by_cases hz : z = 1
  · subst hz
    simp [zetaSurrogate]
  · have hstar : star z ≠ 1 := by
      intro h
      have h' := congrArg (starRingEnd ℂ) h
      exact hz (by simpa [Complex.conj_conj] using h')
    rw [zetaSurrogate, if_neg hstar, zetaSurrogate, if_neg hz]
    simp [riemannZeta_conj]

/--
The entire Backlund auxiliary used for Jensen's theorem. It uses the patched
surrogate for `A`, so no removable singularity is present inside the disk.
-/
noncomputable def backlundFEntire (N : ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (zetaSurrogate (z + (T : ℂ) * Complex.I) ^ N +
      zetaSurrogate (z - (T : ℂ) * Complex.I) ^ N)

theorem backlundFEntire_real_eq_re (N : ℕ) (σ T : ℝ) :
    backlundFEntire N T (σ : ℂ) =
      ((zetaSurrogate ((σ : ℂ) + (T : ℂ) * Complex.I) ^ N).re : ℂ) := by
  have hreflect :
      (σ : ℂ) - (T : ℂ) * Complex.I =
        star ((σ : ℂ) + (T : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp [Complex.add_re, Complex.sub_re, Complex.mul_re]
    · simp [Complex.add_im, Complex.sub_im, Complex.mul_im]
  unfold backlundFEntire
  rw [hreflect, zetaSurrogate_conj]
  rw [← star_pow]
  let w : ℂ := zetaSurrogate ((σ : ℂ) + (T : ℂ) * Complex.I) ^ N
  change (1 / 2 : ℂ) * (w + star w) = (w.re : ℂ)
  apply Complex.ext
  · simp [Complex.mul_re, Complex.add_re]
    ring
  · simp [Complex.mul_im, Complex.add_im]

theorem backlundFEntire_eq_backlundF_of_shift_ne_one
    {N : ℕ} {T : ℝ} {z : ℂ}
    (hplus : z + (T : ℂ) * Complex.I ≠ 1)
    (hminus : z - (T : ℂ) * Complex.I ≠ 1) :
    backlundFEntire N T z = backlundF N T z := by
  simp [backlundFEntire, backlundF, zetaSurrogate, backlundA, hplus, hminus]

/-- The circle integrand for Jensen's theorem, using the entire auxiliary. -/
noncomputable def backlundEccentricJensenIntegrandEntire
    (N : ℕ) (T η R φ : ℝ) : ℝ :=
  Real.log ‖backlundFEntire N T (circleMap (backlundEccentricCenter η) R φ)‖

/--
The unnormalized Jensen circle integral for the entire auxiliary
`F_N = (A(z+iT)^N + A(z-iT)^N)/2`.
-/
noncomputable def backlundEccentricJensenIntegralEntire
    (N : ℕ) (T η R : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..(2 * Real.pi),
    backlundEccentricJensenIntegrandEntire N T η R φ

/-- The lemma-6 Jensen RHS built from the entire auxiliary. -/
noncomputable def backlundEccentricJensenZeroCountRhsEntire
    (N : ℕ) (T η R r E : ℝ) : ℝ :=
  backlundEccentricJensenIntegralEntire N T η R / (4 * Real.pi * Real.log r) -
    Real.log ‖backlundFEntire N T (backlundEccentricCenter η)‖ / (2 * Real.log r) +
      1 / 2 + (N : ℝ) * E / (2 * Real.pi)

theorem backlundEccentricJensenIntegralEntire_eq_two_pi_mul_circleAverage
    (N : ℕ) (T η R : ℝ) :
    backlundEccentricJensenIntegralEntire N T η R =
      (2 * Real.pi) *
        Real.circleAverage
          (fun z : ℂ => Real.log ‖backlundFEntire N T z‖)
          (backlundEccentricCenter η) R := by
  rw [Real.circleAverage]
  simp [backlundEccentricJensenIntegralEntire,
    backlundEccentricJensenIntegrandEntire, smul_eq_mul]
  field_simp [Real.pi_ne_zero]

theorem backlundFEntire_differentiable (N : ℕ) (T : ℝ) :
    Differentiable ℂ (backlundFEntire N T) := by
  unfold backlundFEntire
  have hplus : Differentiable ℂ (fun z : ℂ => z + (T : ℂ) * Complex.I) :=
    differentiable_id.add (differentiable_const ((T : ℂ) * Complex.I))
  have hminus : Differentiable ℂ (fun z : ℂ => z - (T : ℂ) * Complex.I) :=
    differentiable_id.sub (differentiable_const ((T : ℂ) * Complex.I))
  have hplusA : Differentiable ℂ (fun z : ℂ =>
      zetaSurrogate (z + (T : ℂ) * Complex.I)) :=
    zetaSurrogate_differentiable.comp hplus
  have hminusA : Differentiable ℂ (fun z : ℂ =>
      zetaSurrogate (z - (T : ℂ) * Complex.I)) :=
    zetaSurrogate_differentiable.comp hminus
  exact ((hplusA.pow N).add (hminusA.pow N)).const_mul (1 / 2 : ℂ)

theorem backlundFEntire_translate_differentiable (N : ℕ) (T η : ℝ) :
    Differentiable ℂ (fun z : ℂ =>
      backlundFEntire N T (z + backlundEccentricCenter η)) := by
  exact (backlundFEntire_differentiable N T).comp
    (differentiable_id.add (differentiable_const (backlundEccentricCenter η)))

theorem backlundFEntire_translate_jensen_logCounting
    (N : ℕ) (T η : ℝ) {R : ℝ} (hR : R ≠ 0) :
    Function.locallyFinsuppWithin.logCounting
        (MeromorphicOn.divisor
          (fun z : ℂ => backlundFEntire N T (z + backlundEccentricCenter η))
          (Set.univ : Set ℂ)) R =
      Real.circleAverage
          (fun z : ℂ =>
            Real.log ‖backlundFEntire N T (z + backlundEccentricCenter η)‖)
          0 R -
        Real.log
          ‖meromorphicTrailingCoeffAt
            (fun z : ℂ => backlundFEntire N T (z + backlundEccentricCenter η)) 0‖ := by
  exact Complex.Hadamard.jensen_formula_logCounting_eq_circleAverage_sub_log_trailingCoeff
    (backlundFEntire_translate_differentiable N T η) hR

theorem backlundEccentricJensenIntegralEntire_eq_two_pi_mul_logCounting_add_trailingCoeff
    (N : ℕ) (T η : ℝ) {R : ℝ} (hR : R ≠ 0) :
    backlundEccentricJensenIntegralEntire N T η R =
      (2 * Real.pi) *
        (Function.locallyFinsuppWithin.logCounting
            (MeromorphicOn.divisor
              (fun z : ℂ => backlundFEntire N T (z + backlundEccentricCenter η))
              (Set.univ : Set ℂ)) R +
          Real.log
            ‖meromorphicTrailingCoeffAt
              (fun z : ℂ => backlundFEntire N T (z + backlundEccentricCenter η)) 0‖) := by
  have hcircle :
      Real.circleAverage
          (fun z : ℂ => Real.log ‖backlundFEntire N T z‖)
          (backlundEccentricCenter η) R =
        Real.circleAverage
          (fun z : ℂ =>
            Real.log ‖backlundFEntire N T (z + backlundEccentricCenter η)‖)
          0 R := by
    symm
    simpa using
      (Real.circleAverage_map_add_const
        (f := fun z : ℂ => Real.log ‖backlundFEntire N T z‖)
        (c := backlundEccentricCenter η) (R := R))
  have hlog :=
    backlundFEntire_translate_jensen_logCounting (N := N) (T := T) (η := η) hR
  have hcircle_log :
      Real.circleAverage
          (fun z : ℂ =>
            Real.log ‖backlundFEntire N T (z + backlundEccentricCenter η)‖)
          0 R =
        Function.locallyFinsuppWithin.logCounting
            (MeromorphicOn.divisor
              (fun z : ℂ => backlundFEntire N T (z + backlundEccentricCenter η))
              (Set.univ : Set ℂ)) R +
          Real.log
            ‖meromorphicTrailingCoeffAt
              (fun z : ℂ => backlundFEntire N T (z + backlundEccentricCenter η)) 0‖ := by
    linarith
  rw [backlundEccentricJensenIntegralEntire_eq_two_pi_mul_circleAverage,
    hcircle, hcircle_log]

theorem backlundEccentricJensenZeroCountRhsEntire_eq_logCounting_form
    (N : ℕ) (T η R E : ℝ) {r : ℝ} (hR : R ≠ 0) (hr : Real.log r ≠ 0) :
    backlundEccentricJensenZeroCountRhsEntire N T η R r E =
      (Function.locallyFinsuppWithin.logCounting
          (MeromorphicOn.divisor
            (fun z : ℂ => backlundFEntire N T (z + backlundEccentricCenter η))
            (Set.univ : Set ℂ)) R +
        Real.log
          ‖meromorphicTrailingCoeffAt
            (fun z : ℂ => backlundFEntire N T (z + backlundEccentricCenter η)) 0‖) /
        (2 * Real.log r) -
      Real.log ‖backlundFEntire N T (backlundEccentricCenter η)‖ /
        (2 * Real.log r) +
      1 / 2 + (N : ℝ) * E / (2 * Real.pi) := by
  rw [backlundEccentricJensenZeroCountRhsEntire,
    backlundEccentricJensenIntegralEntire_eq_two_pi_mul_logCounting_add_trailingCoeff
      (N := N) (T := T) (η := η) (R := R) hR]
  field_simp [Real.pi_ne_zero, hr]
  ring

noncomputable def backlundEccentricTranslatedDivisor (N : ℕ) (T η : ℝ) :
    Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ :=
  MeromorphicOn.divisor
    (fun z : ℂ => backlundFEntire N T (z + backlundEccentricCenter η))
    (Set.univ : Set ℂ)

theorem backlundEccentricTranslatedDivisor_one_le_of_zero
    {N : ℕ} {T η : ℝ} {z : ℂ}
    (hnot :
      ∃ w : ℂ, backlundFEntire N T (w + backlundEccentricCenter η) ≠ 0)
    (hz : backlundFEntire N T (z + backlundEccentricCenter η) = 0) :
    (1 : ℤ) ≤ backlundEccentricTranslatedDivisor N T η z := by
  let f : ℂ → ℂ := fun w => backlundFEntire N T (w + backlundEccentricCenter η)
  have hf : Differentiable ℂ f := backlundFEntire_translate_differentiable N T η
  have hz' : f z = 0 := hz
  have hnotTop : analyticOrderAt f z ≠ ⊤ :=
    Complex.Hadamard.analyticOrderAt_ne_top_of_exists_ne_zero hf hnot z
  have horder_ne_zero : analyticOrderNatAt f z ≠ 0 := by
    intro hzero
    have hcast : (analyticOrderNatAt f z : ENat) = analyticOrderAt f z :=
      Nat.cast_analyticOrderNatAt (f := f) (z₀ := z) hnotTop
    have horder_zero : analyticOrderAt f z = 0 := by
      simpa [hzero] using hcast.symm
    exact ((hf.analyticAt z).analyticOrderAt_ne_zero.mpr hz') horder_zero
  have horder_pos : 0 < analyticOrderNatAt f z :=
    Nat.pos_of_ne_zero horder_ne_zero
  rw [backlundEccentricTranslatedDivisor]
  change (1 : ℤ) ≤ MeromorphicOn.divisor f (Set.univ : Set ℂ) z
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int (f := f) hf z]
  exact_mod_cast horder_pos

theorem backlundEccentricTranslatedDivisor_one_le_of_realPartZero
    {N : ℕ} {T η a b σ : ℝ}
    (hnot :
      ∃ w : ℂ, backlundFEntire N T (w + backlundEccentricCenter η) ≠ 0)
    (hσ : σ ∈ backlundRealPartZeroSet N T a b)
    (hplus : ((σ : ℂ) + (T : ℂ) * Complex.I) ≠ 1)
    (hminus : ((σ : ℂ) - (T : ℂ) * Complex.I) ≠ 1) :
    (1 : ℤ) ≤
      backlundEccentricTranslatedDivisor N T η
        ((σ : ℂ) - backlundEccentricCenter η) := by
  have hraw : backlundF N T (σ : ℂ) = 0 :=
    (mem_backlundRealPartZeroSet_iff_backlundF N T a b σ).1 hσ |>.2
  have hentire : backlundFEntire N T (σ : ℂ) = 0 := by
    rw [backlundFEntire_eq_backlundF_of_shift_ne_one
      (N := N) (T := T) (z := (σ : ℂ)) hplus hminus]
    exact hraw
  refine backlundEccentricTranslatedDivisor_one_le_of_zero
    (N := N) (T := T) (η := η)
    (z := (σ : ℂ) - backlundEccentricCenter η) hnot ?_
  simpa using hentire

theorem backlundEccentricTranslatedDivisor_one_le_of_orderedRealPartZeros
    {N k : ℕ} {T η a b : ℝ} {xs : Fin k → ℝ}
    (hnot :
      ∃ w : ℂ, backlundFEntire N T (w + backlundEccentricCenter η) ≠ 0)
    (hxs : backlundOrderedRealPartZeros N k T a b xs)
    (hplus : ∀ i : Fin k, ((xs i : ℂ) + (T : ℂ) * Complex.I) ≠ 1)
    (hminus : ∀ i : Fin k, ((xs i : ℂ) - (T : ℂ) * Complex.I) ≠ 1) :
    ∀ i : Fin k,
      (1 : ℤ) ≤
        backlundEccentricTranslatedDivisor N T η
          ((xs i : ℂ) - backlundEccentricCenter η) := by
  intro i
  exact backlundEccentricTranslatedDivisor_one_le_of_realPartZero
    (N := N) (T := T) (η := η) (a := a) (b := b) (σ := xs i)
    hnot (hxs.2 i) (hplus i) (hminus i)

private theorem finset_sum_fun_apply {α β γ : Type*} [AddCommMonoid β]
    (s : Finset α) (f : α → γ → β) (x : γ) :
    (∑ a ∈ s, f a) x = ∑ a ∈ s, f a x := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | insert a s ha ih =>
      simp [ha]

theorem logCounting_lower_bound_of_product
    {m : ℕ} {D : Function.locallyFinsupp ℂ ℤ} {zs : Fin m → ℂ}
    {R H r : ℝ}
    (hDnonneg : 0 ≤ D)
    (hR : 1 ≤ R)
    (hr : 0 < r)
    (hH : 0 < H)
    (hR_eq : R = r * H)
    (hinj : Function.Injective zs)
    (hz0 : ∀ i : Fin m, zs i ≠ 0)
    (hzD : ∀ i : Fin m, (1 : ℤ) ≤ D (zs i))
    (hzR : ∀ i : Fin m, ‖zs i‖ ≤ R)
    (hprod : (∏ i : Fin m, ‖zs i‖) ≤ H ^ m) :
    (m : ℝ) * Real.log r ≤ Function.locallyFinsuppWithin.logCounting D R := by
  classical
  have hSle :
      (∑ i : Fin m, Function.locallyFinsuppWithin.single (zs i) (1 : ℤ)) ≤ D := by
    intro z
    by_cases hz : ∃ i : Fin m, zs i = z
    · rcases hz with ⟨i, rfl⟩
      have hsum :
          (∑ j : Fin m,
              Function.locallyFinsuppWithin.single (zs j) (1 : ℤ) (zs i)) =
            (1 : ℤ) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _hj hji
          have hne : zs i ≠ zs j := by
            intro h
            exact hji (hinj h.symm)
          simp [Function.locallyFinsuppWithin.single_apply, hne]
        · intro hi
          exact False.elim (hi (Finset.mem_univ i))
      rw [Function.locallyFinsuppWithin.coe_sum]
      rw [finset_sum_fun_apply (s := Finset.univ)
        (f := fun j : Fin m =>
          (Function.locallyFinsuppWithin.single (zs j) (1 : ℤ) : ℂ → ℤ))
        (x := zs i)]
      change (∑ j : Fin m,
        Function.locallyFinsuppWithin.single (zs j) (1 : ℤ) (zs i)) ≤ D (zs i)
      rw [hsum]
      exact hzD i
    · have hsum :
          (∑ j : Fin m,
              Function.locallyFinsuppWithin.single (zs j) (1 : ℤ) z) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j _hj
        have hne : z ≠ zs j := by
          intro h
          exact hz ⟨j, h.symm⟩
        simp [Function.locallyFinsuppWithin.single_apply, hne]
      rw [Function.locallyFinsuppWithin.coe_sum]
      rw [finset_sum_fun_apply (s := Finset.univ)
        (f := fun j : Fin m =>
          (Function.locallyFinsuppWithin.single (zs j) (1 : ℤ) : ℂ → ℤ))
        (x := z)]
      change (∑ j : Fin m,
        Function.locallyFinsuppWithin.single (zs j) (1 : ℤ) z) ≤ D z
      rw [hsum]
      exact hDnonneg z
  have hSlog_le :
      Function.locallyFinsuppWithin.logCounting
          (∑ i : Fin m, Function.locallyFinsuppWithin.single (zs i) (1 : ℤ)) R ≤
        Function.locallyFinsuppWithin.logCounting D R :=
    Function.locallyFinsuppWithin.logCounting_le hSle hR
  have hSlog :
      Function.locallyFinsuppWithin.logCounting
          (∑ i : Fin m, Function.locallyFinsuppWithin.single (zs i) (1 : ℤ)) R =
        ∑ i : Fin m,
          Function.locallyFinsuppWithin.logCounting
            (Function.locallyFinsuppWithin.single (zs i) (1 : ℤ)) R := by
    simp [map_sum]
  have hsingle :
      ∀ i : Fin m,
        Function.locallyFinsuppWithin.logCounting
            (Function.locallyFinsuppWithin.single (zs i) (1 : ℤ)) R =
          Real.log R - Real.log ‖zs i‖ := by
    intro i
    simpa using
      (Function.locallyFinsuppWithin.logCounting_single_eq_log_sub_const
        (e := zs i) (r := R) (n := (1 : ℤ)) (hr := hzR i))
  have hlogS :
      Function.locallyFinsuppWithin.logCounting
          (∑ i : Fin m, Function.locallyFinsuppWithin.single (zs i) (1 : ℤ)) R =
        ∑ i : Fin m, (Real.log R - Real.log ‖zs i‖) := by
    rw [hSlog]
    exact Finset.sum_congr rfl fun i _ => hsingle i
  have hprod_pos : 0 < ∏ i : Fin m, ‖zs i‖ :=
    Finset.prod_pos fun i _ => norm_pos_iff.mpr (hz0 i)
  have hHpow_pos : 0 < H ^ m := pow_pos hH m
  have hsum_log_le :
      (∑ i : Fin m, Real.log ‖zs i‖) ≤ (m : ℝ) * Real.log H := by
    have hlogprod_le : Real.log (∏ i : Fin m, ‖zs i‖) ≤ Real.log (H ^ m) :=
      Real.log_le_log hprod_pos hprod
    rw [Real.log_prod (s := Finset.univ)
        (f := fun i : Fin m => ‖zs i‖)
        (by intro i _; exact norm_ne_zero_iff.mpr (hz0 i)),
      Real.log_pow] at hlogprod_le
    simpa using hlogprod_le
  have hsum_lower :
      (m : ℝ) * Real.log r ≤
        ∑ i : Fin m, (Real.log R - Real.log ‖zs i‖) := by
    have hlogR : Real.log R = Real.log r + Real.log H := by
      rw [hR_eq, Real.log_mul hr.ne' hH.ne']
    have hsum_const :
        (∑ _i : Fin m, Real.log R) = (m : ℝ) * Real.log R := by
      simp
    rw [Finset.sum_sub_distrib, hsum_const, hlogR]
    nlinarith
  calc
    (m : ℝ) * Real.log r
        ≤ ∑ i : Fin m, (Real.log R - Real.log ‖zs i‖) := hsum_lower
    _ = Function.locallyFinsuppWithin.logCounting
          (∑ i : Fin m, Function.locallyFinsuppWithin.single (zs i) (1 : ℤ)) R := hlogS.symm
    _ ≤ Function.locallyFinsuppWithin.logCounting D R := hSlog_le

noncomputable def backlundEccentricJensenLogCountingTerm
    (N : ℕ) (T η R : ℝ) : ℝ :=
  Function.locallyFinsuppWithin.logCounting
      (backlundEccentricTranslatedDivisor N T η) R +
    Real.log
      ‖meromorphicTrailingCoeffAt
        (fun z : ℂ => backlundFEntire N T (z + backlundEccentricCenter η)) 0‖ -
    Real.log ‖backlundFEntire N T (backlundEccentricCenter η)‖

theorem backlundEccentricJensenLogCountingTerm_eq_logCounting_of_center_ne_zero
    {N : ℕ} {T η R : ℝ}
    (hcenter : backlundFEntire N T (backlundEccentricCenter η) ≠ 0) :
    backlundEccentricJensenLogCountingTerm N T η R =
      Function.locallyFinsuppWithin.logCounting
        (backlundEccentricTranslatedDivisor N T η) R := by
  let f : ℂ → ℂ := fun z => backlundFEntire N T (z + backlundEccentricCenter η)
  have hf : Differentiable ℂ f := backlundFEntire_translate_differentiable N T η
  have htrail : meromorphicTrailingCoeffAt f 0 = f 0 := by
    exact (hf.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero (by simpa [f] using hcenter)
  rw [backlundEccentricJensenLogCountingTerm]
  change Function.locallyFinsuppWithin.logCounting
      (backlundEccentricTranslatedDivisor N T η) R +
        Real.log ‖meromorphicTrailingCoeffAt f 0‖ -
        Real.log ‖backlundFEntire N T (backlundEccentricCenter η)‖ =
      Function.locallyFinsuppWithin.logCounting
        (backlundEccentricTranslatedDivisor N T η) R
  rw [htrail]
  simp [f]

theorem backlundEccentricJensenLogCountingTerm_lower_bound_of_orderedRealPartZeros_product
    {N m : ℕ} {T η a b R H r : ℝ} {xs : Fin m → ℝ}
    (hcenter : backlundFEntire N T (backlundEccentricCenter η) ≠ 0)
    (hR : 1 ≤ R)
    (hr : 0 < r)
    (hH : 0 < H)
    (hR_eq : R = r * H)
    (hxs : backlundOrderedRealPartZeros N m T a b xs)
    (hplus : ∀ i : Fin m, ((xs i : ℂ) + (T : ℂ) * Complex.I) ≠ 1)
    (hminus : ∀ i : Fin m, ((xs i : ℂ) - (T : ℂ) * Complex.I) ≠ 1)
    (hz0 : ∀ i : Fin m, ((xs i : ℂ) - backlundEccentricCenter η) ≠ 0)
    (hzR : ∀ i : Fin m, ‖((xs i : ℂ) - backlundEccentricCenter η)‖ ≤ R)
    (hprod :
      (∏ i : Fin m, ‖((xs i : ℂ) - backlundEccentricCenter η)‖) ≤ H ^ m) :
    (m : ℝ) * Real.log r ≤
      backlundEccentricJensenLogCountingTerm N T η R := by
  let zs : Fin m → ℂ := fun i => (xs i : ℂ) - backlundEccentricCenter η
  have hnot :
      ∃ w : ℂ, backlundFEntire N T (w + backlundEccentricCenter η) ≠ 0 := by
    refine ⟨0, ?_⟩
    simpa using hcenter
  have hDnonneg : 0 ≤ backlundEccentricTranslatedDivisor N T η := by
    unfold backlundEccentricTranslatedDivisor
    exact Differentiable.divisor_nonneg
      (backlundFEntire_translate_differentiable N T η)
  have hinj : Function.Injective zs := by
    intro i j hij
    apply hxs.1.injective
    apply Complex.ofReal_injective
    have hcx : (xs i : ℂ) = (xs j : ℂ) := by
      simpa [zs] using congrArg (fun z : ℂ => z + backlundEccentricCenter η) hij
    exact hcx
  have hzD :
      ∀ i : Fin m,
        (1 : ℤ) ≤ backlundEccentricTranslatedDivisor N T η (zs i) := by
    intro i
    simpa [zs] using
      backlundEccentricTranslatedDivisor_one_le_of_orderedRealPartZeros
        (N := N) (k := m) (T := T) (η := η) (a := a) (b := b)
        (xs := xs) hnot hxs hplus hminus i
  have hlower :
      (m : ℝ) * Real.log r ≤
        Function.locallyFinsuppWithin.logCounting
          (backlundEccentricTranslatedDivisor N T η) R := by
    exact logCounting_lower_bound_of_product
      (D := backlundEccentricTranslatedDivisor N T η) (zs := zs)
      (R := R) (H := H) (r := r)
      hDnonneg hR hr hH hR_eq hinj
      (by simpa [zs] using hz0) hzD (by simpa [zs] using hzR)
      (by simpa [zs] using hprod)
  rw [backlundEccentricJensenLogCountingTerm_eq_logCounting_of_center_ne_zero
    (N := N) (T := T) (η := η) (R := R) hcenter]
  exact hlower

theorem backlundOrderedRealPartZeros_ne_eccentricCenter
    {N k : ℕ} {T η a b : ℝ} {xs : Fin k → ℝ}
    (hcenter : backlundFEntire N T (backlundEccentricCenter η) ≠ 0)
    (hxs : backlundOrderedRealPartZeros N k T a b xs)
    (hplus : ∀ i : Fin k, ((xs i : ℂ) + (T : ℂ) * Complex.I) ≠ 1)
    (hminus : ∀ i : Fin k, ((xs i : ℂ) - (T : ℂ) * Complex.I) ≠ 1) :
    ∀ i : Fin k, ((xs i : ℂ) - backlundEccentricCenter η) ≠ 0 := by
  intro i hzero
  have hσ : (xs i : ℂ) = backlundEccentricCenter η := sub_eq_zero.mp hzero
  have hraw : backlundF N T (xs i : ℂ) = 0 :=
    (mem_backlundRealPartZeroSet_iff_backlundF N T a b (xs i)).1 (hxs.2 i) |>.2
  have hentire : backlundFEntire N T (xs i : ℂ) = 0 := by
    rw [backlundFEntire_eq_backlundF_of_shift_ne_one
      (N := N) (T := T) (z := (xs i : ℂ)) (hplus i) (hminus i)]
    exact hraw
  exact hcenter (by simpa [hσ] using hentire)

theorem backlundOrderedRealPartZeros_norm_le_largeRadius
    {N k : ℕ} {T σ₁ : ℝ} {xs : Fin k → ℝ}
    (hσ₁ : σ₁ ≤ 1 + backlundEta)
    (hxs : backlundOrderedRealPartZeros N k T (1 - σ₁) σ₁ xs) :
    ∀ i : Fin k,
      ‖((xs i : ℂ) - backlundEccentricCenter backlundEta)‖ ≤
        backlundLargeRadius := by
  intro i
  have hxI : xs i ∈ Set.Icc (1 - σ₁) σ₁ :=
    (mem_backlundRealPartZeroSet_iff N T (1 - σ₁) σ₁ (xs i)).1 (hxs.2 i) |>.1
  exact norm_ofReal_sub_backlundEccentricCenter_le_largeRadius hσ₁ hxI

theorem backlundPairingLoss_le {N : ℕ} {E : ℝ} (hE : 0 ≤ E) :
    (backlundPairingLoss N E : ℝ) ≤ (N : ℝ) * E / Real.pi := by
  unfold backlundPairingLoss
  exact Nat.floor_le (by positivity)

theorem eccentric_jensen_zero_count_of_logCounting_lower_bound
    {N n : ℕ} {T η R E r : ℝ}
    (hR : R ≠ 0) (hrlog : 0 < Real.log r) (hE : 0 ≤ E)
    (hlower :
      (2 * (n : ℝ) - 1 - (backlundPairingLoss N E : ℝ)) * Real.log r ≤
        backlundEccentricJensenLogCountingTerm N T η R) :
    (n : ℝ) ≤ backlundEccentricJensenZeroCountRhsEntire N T η R r E := by
  let L := backlundEccentricJensenLogCountingTerm N T η R
  have hRhs :
      backlundEccentricJensenZeroCountRhsEntire N T η R r E =
        L / (2 * Real.log r) + 1 / 2 + (N : ℝ) * E / (2 * Real.pi) := by
    rw [backlundEccentricJensenZeroCountRhsEntire_eq_logCounting_form
      (N := N) (T := T) (η := η) (R := R) (E := E) hR (ne_of_gt hrlog)]
    simp only [L, backlundEccentricJensenLogCountingTerm,
      backlundEccentricTranslatedDivisor]
    ring
  have hlowerL :
      (2 * (n : ℝ) - 1 - (backlundPairingLoss N E : ℝ)) * Real.log r ≤ L := by
    simpa [L] using hlower
  have hcount :
      2 * (n : ℝ) - 1 - (backlundPairingLoss N E : ℝ) ≤ L / Real.log r :=
    (le_div_iff₀ hrlog).2 hlowerL
  have hcount_half :
      (2 * (n : ℝ) - 1 - (backlundPairingLoss N E : ℝ)) / 2 ≤
        L / (2 * Real.log r) := by
    have h := div_le_div_of_nonneg_right hcount (by norm_num : (0 : ℝ) ≤ 2)
    have hden : (L / Real.log r) / 2 = L / (2 * Real.log r) := by
      field_simp [ne_of_gt hrlog, two_ne_zero]
    simpa [hden] using h
  have hloss_half :
      (backlundPairingLoss N E : ℝ) / 2 ≤ (N : ℝ) * E / (2 * Real.pi) := by
    have hloss := backlundPairingLoss_le (N := N) hE
    have h := div_le_div_of_nonneg_right hloss (by norm_num : (0 : ℝ) ≤ 2)
    have hden : ((N : ℝ) * E / Real.pi) / 2 = (N : ℝ) * E / (2 * Real.pi) := by
      field_simp [Real.pi_ne_zero, two_ne_zero]
    simpa [hden] using h
  rw [hRhs]
  calc
    (n : ℝ)
        = (2 * (n : ℝ) - 1 - (backlundPairingLoss N E : ℝ)) / 2 +
            1 / 2 + (backlundPairingLoss N E : ℝ) / 2 := by ring
    _ ≤ L / (2 * Real.log r) + 1 / 2 + (N : ℝ) * E / (2 * Real.pi) := by
      nlinarith

theorem eccentric_jensen_zero_count_of_orderedRealPartZeros_product
    {N n m : ℕ} {T η a b R H r E : ℝ} {xs : Fin m → ℝ}
    (hcenter : backlundFEntire N T (backlundEccentricCenter η) ≠ 0)
    (hR : 1 ≤ R)
    (hr : 0 < r)
    (hrlog : 0 < Real.log r)
    (hE : 0 ≤ E)
    (hH : 0 < H)
    (hR_eq : R = r * H)
    (hcount : 2 * (n : ℝ) - 1 - (backlundPairingLoss N E : ℝ) ≤ m)
    (hxs : backlundOrderedRealPartZeros N m T a b xs)
    (hplus : ∀ i : Fin m, ((xs i : ℂ) + (T : ℂ) * Complex.I) ≠ 1)
    (hminus : ∀ i : Fin m, ((xs i : ℂ) - (T : ℂ) * Complex.I) ≠ 1)
    (hz0 : ∀ i : Fin m, ((xs i : ℂ) - backlundEccentricCenter η) ≠ 0)
    (hzR : ∀ i : Fin m, ‖((xs i : ℂ) - backlundEccentricCenter η)‖ ≤ R)
    (hprod :
      (∏ i : Fin m, ‖((xs i : ℂ) - backlundEccentricCenter η)‖) ≤ H ^ m) :
    (n : ℝ) ≤ backlundEccentricJensenZeroCountRhsEntire N T η R r E := by
  have hlower_m :
      (m : ℝ) * Real.log r ≤
        backlundEccentricJensenLogCountingTerm N T η R :=
    backlundEccentricJensenLogCountingTerm_lower_bound_of_orderedRealPartZeros_product
      (N := N) (m := m) (T := T) (η := η) (a := a) (b := b)
      (R := R) (H := H) (r := r) (xs := xs)
      hcenter hR hr hH hR_eq hxs hplus hminus hz0 hzR hprod
  have hlower :
      (2 * (n : ℝ) - 1 - (backlundPairingLoss N E : ℝ)) * Real.log r ≤
        backlundEccentricJensenLogCountingTerm N T η R := by
    exact (mul_le_mul_of_nonneg_right hcount hrlog.le).trans hlower_m
  exact eccentric_jensen_zero_count_of_logCounting_lower_bound
    (N := N) (n := n) (T := T) (η := η) (R := R) (E := E) (r := r)
    (by linarith) hrlog hE hlower

theorem eccentric_jensen_zero_count_of_orderedRealPartZeros_product_on_backlundInterval
    {N n m : ℕ} {T σ₁ H r E : ℝ} {xs : Fin m → ℝ}
    (hcenter : backlundFEntire N T (backlundEccentricCenter backlundEta) ≠ 0)
    (hr : 0 < r)
    (hrlog : 0 < Real.log r)
    (hE : 0 ≤ E)
    (hH : 0 < H)
    (hR_eq : backlundLargeRadius = r * H)
    (hσ₁ : σ₁ ≤ 1 + backlundEta)
    (hcount : 2 * (n : ℝ) - 1 - (backlundPairingLoss N E : ℝ) ≤ m)
    (hxs : backlundOrderedRealPartZeros N m T (1 - σ₁) σ₁ xs)
    (hplus : ∀ i : Fin m, ((xs i : ℂ) + (T : ℂ) * Complex.I) ≠ 1)
    (hminus : ∀ i : Fin m, ((xs i : ℂ) - (T : ℂ) * Complex.I) ≠ 1)
    (hprod :
      (∏ i : Fin m, ‖((xs i : ℂ) - backlundEccentricCenter backlundEta)‖) ≤ H ^ m) :
    (n : ℝ) ≤
      backlundEccentricJensenZeroCountRhsEntire N T backlundEta backlundLargeRadius r E := by
  have hR : 1 ≤ backlundLargeRadius := by
    norm_num [backlundLargeRadius]
  exact eccentric_jensen_zero_count_of_orderedRealPartZeros_product
    (N := N) (n := n) (m := m) (T := T) (η := backlundEta)
    (a := 1 - σ₁) (b := σ₁) (R := backlundLargeRadius)
    (H := H) (r := r) (E := E) (xs := xs)
    hcenter hR hr hrlog hE hH hR_eq hcount hxs hplus hminus
    (backlundOrderedRealPartZeros_ne_eccentricCenter
      (N := N) (k := m) (T := T) (η := backlundEta)
      (a := 1 - σ₁) (b := σ₁) (xs := xs) hcenter hxs hplus hminus)
    (backlundOrderedRealPartZeros_norm_le_largeRadius
      (N := N) (k := m) (T := T) (σ₁ := σ₁) (xs := xs) hσ₁ hxs)
    hprod

theorem midpointReflectedProduct_zetaSurrogate_eq (z : ℂ) :
    midpointReflectedProduct zetaSurrogate z =
      zetaSurrogate z * zetaSurrogate ((1 : ℂ) - z) := by
  unfold midpointReflectedProduct
  have harg : (1 : ℂ) - star z = star ((1 : ℂ) - z) := by
    simp
  rw [harg, zetaSurrogate_conj]
  simp

/-- Reflected shifted base `Q + 1 - z` stays off the log branch cut on a strip. -/
theorem reflectedShifted_mem_slitPlane_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (0 : ℝ) < Q + 1 - σ₁)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    (((Q + 1 : ℝ) : ℂ) - z) ∈ Complex.slitPlane := by
  refine Or.inl ?_
  have hzre : z.re ≤ σ₁ := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.2
  have hpos : (0 : ℝ) < Q + 1 - z.re := by nlinarith
  simpa [Complex.sub_re] using hpos

theorem reflectedShifted_log_ne_zero_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (1 : ℝ) < Q + 1 - σ₁)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    Complex.log ((((Q + 1 : ℝ) : ℂ) - z)) ≠ 0 := by
  apply log_ne_zero_of_one_lt_re
  have hzre : z.re ≤ σ₁ := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.2
  have hpos : (1 : ℝ) < Q + 1 - z.re := by nlinarith
  simpa [Complex.sub_re] using hpos

theorem reflectedShifted_log_mem_slitPlane_on_verticalClosedStrip {Q σ₀ σ₁ : ℝ} {z : ℂ}
    (hQ : (1 : ℝ) < Q + 1 - σ₁)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ₀ σ₁) :
    Complex.log ((((Q + 1 : ℝ) : ℂ) - z)) ∈ Complex.slitPlane := by
  refine Or.inl ?_
  rw [Complex.log_re]
  apply Real.log_pos
  have hzre : z.re ≤ σ₁ := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.2
  have hpos : (1 : ℝ) < ((((Q + 1 : ℝ) : ℂ) - z).re) := by
    simp [Complex.sub_re]
    nlinarith
  exact lt_of_lt_of_le hpos (Complex.re_le_norm _)

theorem reflectedShifted_log_diffContOnCl_on_verticalStrip {Q σ₀ σ₁ : ℝ}
    (hσ : σ₀ < σ₁) (hQ : (0 : ℝ) < Q + 1 - σ₁) :
    DiffContOnCl ℂ (fun z : ℂ => Complex.log ((((Q + 1 : ℝ) : ℂ) - z)))
      (Complex.HadamardThreeLines.verticalStrip σ₀ σ₁) := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [verticalStrip_closure_eq_verticalClosedStrip hσ.ne]
  exact ((differentiableOn_const (((Q + 1 : ℝ) : ℂ))).sub differentiableOn_id).clog
    (fun z hz => reflectedShifted_mem_slitPlane_on_verticalClosedStrip hQ hz)

theorem midpointReflectedProductMajorant_ne_zero_on_verticalClosedStrip
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : C₀ ≠ 0) (hC₁ : C₁ ≠ 0)
    {z : ℂ} (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) :
    midpointReflectedProductMajorant Q C₀ C₁ z ≠ 0 := by
  unfold midpointReflectedProductMajorant
  refine mul_ne_zero ?_ ?_
  · exact_mod_cast mul_ne_zero hC₀ hC₁
  · refine mul_ne_zero ?_ ?_
    · refine mul_ne_zero ?_ ?_
      · refine mul_ne_zero ?_ ?_
        · rw [Complex.cpow_ne_zero_iff]
          exact Or.inl (Complex.slitPlane_ne_zero
            (shifted_mem_slitPlane_on_verticalClosedStrip
              (Q := Q) (σ₀ := 0) (σ₁ := 1) (by linarith) hz))
        · exact Complex.slitPlane_ne_zero
            (reflectedShifted_mem_slitPlane_on_verticalClosedStrip
              (Q := Q) (σ₀ := 0) (σ₁ := 1) (by linarith) hz)
      · exact shifted_log_ne_zero_on_verticalClosedStrip
          (Q := Q) (σ₀ := 0) (σ₁ := 1) (by linarith) hz
    · exact reflectedShifted_log_ne_zero_on_verticalClosedStrip
        (Q := Q) (σ₀ := 0) (σ₁ := 1) (by linarith) hz

private lemma norm_ge_of_re_ge {z : ℂ} {A : ℝ} (hz : A ≤ z.re) :
    A ≤ ‖z‖ :=
  hz.trans (Complex.re_le_norm z)

private lemma log_le_norm_log_of_re_ge {z : ℂ} {A : ℝ} (hA : (1 : ℝ) < A)
    (hz : A ≤ z.re) :
    Real.log A ≤ ‖Complex.log z‖ := by
  have hA_norm : A ≤ ‖z‖ := norm_ge_of_re_ge hz
  have hlog_le : Real.log A ≤ Real.log ‖z‖ :=
    Real.log_le_log (by linarith) hA_norm
  have hlog_norm_le : Real.log ‖z‖ ≤ ‖Complex.log z‖ := by
    rw [← Complex.log_re]
    exact le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  exact hlog_le.trans hlog_norm_le

theorem midpointReflectedProductMajorant_norm_lower_on_verticalClosedStrip
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    {z : ℂ} (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) :
    (C₀ * C₁) * (Q ^ (5 / 2 : ℝ) * (Real.log Q) ^ 2) ≤
      ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ := by
  let qz : ℂ := (Q : ℂ) + z
  let rz : ℂ := (((Q + 1 : ℝ) : ℂ) - z)
  have hzleft : (0 : ℝ) ≤ z.re := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.1
  have hzright : z.re ≤ (1 : ℝ) := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz.2
  have hqz_re : Q ≤ qz.re := by
    simp [qz, Complex.add_re]
    linarith
  have hrz_re : Q ≤ rz.re := by
    simp [rz, Complex.sub_re]
    linarith
  have hqz_ne : qz ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [qz, Complex.add_re] at hre
    linarith
  have hqnorm : Q ≤ ‖qz‖ := norm_ge_of_re_ge hqz_re
  have hrnorm : Q ≤ ‖rz‖ := norm_ge_of_re_ge hrz_re
  have hqlog : Real.log Q ≤ ‖Complex.log qz‖ :=
    log_le_norm_log_of_re_ge hQ hqz_re
  have hrlog : Real.log Q ≤ ‖Complex.log rz‖ :=
    log_le_norm_log_of_re_ge hQ hrz_re
  have hlogQ_nonneg : 0 ≤ Real.log Q := (Real.log_pos hQ).le
  have hqpow :
      Q ^ (3 / 2 : ℝ) ≤ ‖qz‖ ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hqnorm (by norm_num)
  have hcore :
      Q ^ (3 / 2 : ℝ) * Q * (Real.log Q * Real.log Q) ≤
        ‖qz‖ ^ (3 / 2 : ℝ) * ‖rz‖ *
          (‖Complex.log qz‖ * ‖Complex.log rz‖) := by
    have hright_nonneg : 0 ≤ ‖qz‖ ^ (3 / 2 : ℝ) * ‖rz‖ :=
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)
    exact mul_le_mul
      (mul_le_mul hqpow hrnorm (by linarith : (0 : ℝ) ≤ Q)
        (Real.rpow_nonneg (norm_nonneg _) _))
      (mul_le_mul hqlog hrlog hlogQ_nonneg (norm_nonneg _))
      (mul_nonneg hlogQ_nonneg hlogQ_nonneg) hright_nonneg
  have hnorm_eq :
      ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ =
        (C₀ * C₁) * (‖qz‖ ^ (3 / 2 : ℝ) * ‖rz‖ *
          (‖Complex.log qz‖ * ‖Complex.log rz‖)) := by
    have hcpow :
        ‖qz ^ (((3 / 2 : ℝ) : ℂ))‖ = ‖qz‖ ^ (3 / 2 : ℝ) := by
      rw [Complex.norm_cpow_of_ne_zero hqz_ne]
      norm_num
    unfold midpointReflectedProductMajorant
    change
      ‖((C₀ * C₁ : ℝ) : ℂ) *
        (qz ^ (((3 / 2 : ℝ) : ℂ)) * rz *
          Complex.log qz * Complex.log rz)‖ =
        (C₀ * C₁) * (‖qz‖ ^ (3 / 2 : ℝ) * ‖rz‖ *
          (‖Complex.log qz‖ * ‖Complex.log rz‖))
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hcpow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (mul_pos hC₀ hC₁)]
    ring
  rw [hnorm_eq]
  calc
    (C₀ * C₁) * (Q ^ (5 / 2 : ℝ) * (Real.log Q) ^ 2)
        = (C₀ * C₁) * (Q ^ (3 / 2 : ℝ) * Q *
            (Real.log Q * Real.log Q)) := by
          have hQpow : Q ^ (5 / 2 : ℝ) = Q ^ (3 / 2 : ℝ) * Q := by
            rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add (by linarith : 0 < Q)]
            rw [Real.rpow_one]
          rw [hQpow, pow_two]
    _ ≤ (C₀ * C₁) * (‖qz‖ ^ (3 / 2 : ℝ) * ‖rz‖ *
          (‖Complex.log qz‖ * ‖Complex.log rz‖)) := by
          exact mul_le_mul_of_nonneg_left hcore (mul_nonneg hC₀.le hC₁.le)

theorem zetaSurrogate_midpointReflectedProduct_norm_le_exp_quadratic :
    ∃ C > 0, ∀ z : ℂ,
      ‖midpointReflectedProduct zetaSurrogate z‖ ≤
        Real.exp (C * ((1 + ‖z‖) ^ (2 : ℝ) +
          (1 + ‖(1 : ℂ) - star z‖) ^ (2 : ℝ))) := by
  obtain ⟨C, hCpos, hC⟩ := zetaSurrogate_log_growth
  have hnorm : ∀ z : ℂ,
      ‖zetaSurrogate z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (2 : ℝ)) :=
    Real.norm_le_exp_mul_rpow_of_log_growth
      (f := zetaSurrogate) (r := fun z : ℂ => 1 + ‖z‖)
      (C := C) (ρ := (3 / 2 : ℝ)) (τ := (2 : ℝ))
      hCpos.le (fun z => by linarith [norm_nonneg z]) (by norm_num) hC
  refine ⟨C, hCpos, fun z => ?_⟩
  unfold midpointReflectedProduct
  rw [norm_mul, norm_star]
  calc
    ‖zetaSurrogate z‖ * ‖zetaSurrogate ((1 : ℂ) - star z)‖
        ≤ Real.exp (C * (1 + ‖z‖) ^ (2 : ℝ)) *
            Real.exp (C * (1 + ‖(1 : ℂ) - star z‖) ^ (2 : ℝ)) :=
          mul_le_mul (hnorm z) (hnorm ((1 : ℂ) - star z))
            (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (C * ((1 + ‖z‖) ^ (2 : ℝ) +
          (1 + ‖(1 : ℂ) - star z‖) ^ (2 : ℝ))) := by
          rw [← Real.exp_add]
          ring_nf

theorem zetaSurrogate_midpointReflectedProduct_quotient_norm_le_exp_quadratic
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    ∃ C > 0, ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1,
      ‖midpointReflectedProduct zetaSurrogate z /
          midpointReflectedProductMajorant Q C₀ C₁ z‖ ≤
        Real.exp (C * ((1 + ‖z‖) ^ (2 : ℝ) +
          (1 + ‖(1 : ℂ) - star z‖) ^ (2 : ℝ))) /
          ((C₀ * C₁) * (Q ^ (5 / 2 : ℝ) * (Real.log Q) ^ 2)) := by
  obtain ⟨C, hCpos, hC⟩ := zetaSurrogate_midpointReflectedProduct_norm_le_exp_quadratic
  refine ⟨C, hCpos, fun z hz => ?_⟩
  set D : ℝ := (C₀ * C₁) * (Q ^ (5 / 2 : ℝ) * (Real.log Q) ^ 2)
  have hDpos : 0 < D := by
    have hlog : 0 < Real.log Q := Real.log_pos hQ
    have hpow : 0 < Q ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    dsimp [D]
    positivity
  have hden :
      D ≤ ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ := by
    simpa [D] using midpointReflectedProductMajorant_norm_lower_on_verticalClosedStrip
      hQ hC₀ hC₁ hz
  rw [norm_div]
  calc
    ‖midpointReflectedProduct zetaSurrogate z‖ /
        ‖midpointReflectedProductMajorant Q C₀ C₁ z‖
        ≤ ‖midpointReflectedProduct zetaSurrogate z‖ / D :=
          div_le_div_of_nonneg_left (norm_nonneg _) hDpos hden
    _ ≤ Real.exp (C * ((1 + ‖z‖) ^ (2 : ℝ) +
          (1 + ‖(1 : ℂ) - star z‖) ^ (2 : ℝ))) / D :=
          div_le_div_of_nonneg_right (hC z) hDpos.le

private lemma one_add_norm_le_two_mul_exp_abs_im_of_re_mem_Ioo {z : ℂ}
    (hz : z.re ∈ Set.Ioo (0 : ℝ) 1) :
    1 + ‖z‖ ≤ 2 * Real.exp |z.im| := by
  have hz_re_icc : z.re ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨by linarith [hz.1], le_of_lt hz.2⟩
  have hnorm : ‖z‖ ≤ |z.im| + 1 := by
    calc ‖z‖
        = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := by rw [Complex.re_add_im]
      _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |z.re| + |z.im| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, Complex.norm_real]
          simp only [norm_eq_abs, mul_one]
      _ ≤ 1 + |z.im| := by
          have hre : |z.re| ≤ 1 := abs_le.mpr hz_re_icc
          linarith
      _ = |z.im| + 1 := by ring
  calc
    1 + ‖z‖ ≤ |z.im| + 2 := by linarith
    _ ≤ 2 * (1 + |z.im|) := by nlinarith [abs_nonneg z.im]
    _ ≤ 2 * Real.exp |z.im| :=
        mul_le_mul_of_nonneg_left
          (by simpa [add_comm] using Real.add_one_le_exp |z.im|) (by norm_num)

private lemma reflected_quadratic_le_eight_exp_two_abs_im {z : ℂ}
    (hz : z.re ∈ Set.Ioo (0 : ℝ) 1) :
    (1 + ‖z‖) ^ (2 : ℝ) + (1 + ‖(1 : ℂ) - star z‖) ^ (2 : ℝ) ≤
      8 * Real.exp (2 * |z.im|) := by
  have hz_ref : ((1 : ℂ) - star z).re ∈ Set.Ioo (0 : ℝ) 1 := by
    simp only [RCLike.star_def, Complex.sub_re, Complex.one_re, Complex.conj_re,
      Set.mem_Ioo, sub_pos, sub_lt_self_iff]
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hz_bound := one_add_norm_le_two_mul_exp_abs_im_of_re_mem_Ioo hz
  have href_bound :=
    one_add_norm_le_two_mul_exp_abs_im_of_re_mem_Ioo hz_ref
  have href_bound' :
      1 + ‖(1 : ℂ) - star z‖ ≤ 2 * Real.exp |z.im| := by
    simpa [Complex.sub_im] using href_bound
  have hpos_z : 0 ≤ 1 + ‖z‖ := by positivity
  have hpos_ref : 0 ≤ 1 + ‖(1 : ℂ) - star z‖ := by positivity
  have hexp_pos : 0 < Real.exp |z.im| := Real.exp_pos _
  have hz_sq :
      (1 + ‖z‖) ^ 2 ≤ (2 * Real.exp |z.im|) ^ 2 := by
    nlinarith
  have href_sq :
      (1 + ‖(1 : ℂ) - star z‖) ^ 2 ≤ (2 * Real.exp |z.im|) ^ 2 := by
    nlinarith
  have hexp_sq : (2 * Real.exp |z.im|) ^ 2 = 4 * Real.exp (2 * |z.im|) := by
    rw [sq, show 2 * |z.im| = |z.im| + |z.im| by ring, Real.exp_add]
    ring
  rw [Real.rpow_two, Real.rpow_two]
  nlinarith

theorem zetaSurrogate_midpointReflectedProduct_PL_growth
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    ∃ c < Real.pi / ((1 : ℝ) - 0), ∃ B,
      (fun z => midpointReflectedProduct zetaSurrogate z /
          midpointReflectedProductMajorant Q C₀ C₁ z)
        =O[Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            Filter.principal (Complex.re ⁻¹' Set.Ioo 0 1)]
          fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
  obtain ⟨C, hCpos, hC⟩ :=
    zetaSurrogate_midpointReflectedProduct_quotient_norm_le_exp_quadratic
      hQ hC₀ hC₁
  set D : ℝ := (C₀ * C₁) * (Q ^ (5 / 2 : ℝ) * (Real.log Q) ^ 2)
  have hDpos : 0 < D := by
    have hlog : 0 < Real.log Q := Real.log_pos hQ
    have hpow : 0 < Q ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    dsimp [D]
    positivity
  refine ⟨2, by
    have htwo_lt_pi : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
    simpa using htwo_lt_pi, 8 * C, ?_⟩
  apply Asymptotics.IsBigO.of_bound D⁻¹
  filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self
    (Complex.re ⁻¹' Set.Ioo (0 : ℝ) 1))] with z hzstrip
  have hzre : z.re ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa using hzstrip
  have hzclosed : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using
      (show z.re ∈ Set.Icc (0 : ℝ) 1 from ⟨le_of_lt hzre.1, le_of_lt hzre.2⟩)
  have hquot := hC z hzclosed
  have hquad := reflected_quadratic_le_eight_exp_two_abs_im hzre
  have hexp_le :
      Real.exp (C * ((1 + ‖z‖) ^ (2 : ℝ) +
          (1 + ‖(1 : ℂ) - star z‖) ^ (2 : ℝ))) ≤
        Real.exp ((8 * C) * Real.exp (2 * |z.im|)) := by
    refine Real.exp_le_exp.2 ?_
    have hexp_nonneg : 0 ≤ Real.exp (2 * |z.im|) := (Real.exp_pos _).le
    nlinarith
  calc
    ‖midpointReflectedProduct zetaSurrogate z /
        midpointReflectedProductMajorant Q C₀ C₁ z‖
        ≤ Real.exp (C * ((1 + ‖z‖) ^ (2 : ℝ) +
          (1 + ‖(1 : ℂ) - star z‖) ^ (2 : ℝ))) / D := by
          simpa [D] using hquot
    _ ≤ Real.exp ((8 * C) * Real.exp (2 * |z.im|)) / D :=
          div_le_div_of_nonneg_right hexp_le hDpos.le
    _ = D⁻¹ * ‖Real.exp ((8 * C) * Real.exp (2 * |z.im|))‖ := by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          ring

theorem midpointReflectedProductMajorant_diffContOnCl_on_verticalStrip
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) :
    DiffContOnCl ℂ (midpointReflectedProductMajorant Q C₀ C₁)
      (Complex.HadamardThreeLines.verticalStrip 0 1) := by
  refine DifferentiableOn.diffContOnCl ?_
  rw [verticalStrip_closure_eq_verticalClosedStrip (by norm_num : (0 : ℝ) ≠ 1)]
  unfold midpointReflectedProductMajorant
  have hpow : DifferentiableOn ℂ (fun z : ℂ => ((Q : ℂ) + z) ^ (((3 / 2 : ℝ) : ℂ)))
      (Complex.HadamardThreeLines.verticalClosedStrip 0 1) :=
    ((differentiableOn_const (Q : ℂ)).add differentiableOn_id).cpow_const
      (fun z hz => shifted_mem_slitPlane_on_verticalClosedStrip
        (Q := Q) (σ₀ := 0) (σ₁ := 1) (by linarith) hz)
  have hlinear : DifferentiableOn ℂ (fun z : ℂ => (((Q + 1 : ℝ) : ℂ) - z))
      (Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    fun_prop
  have hlog : DifferentiableOn ℂ (fun z : ℂ => Complex.log ((Q : ℂ) + z))
      (Complex.HadamardThreeLines.verticalClosedStrip 0 1) :=
    ((differentiableOn_const (Q : ℂ)).add differentiableOn_id).clog
      (fun z hz => shifted_mem_slitPlane_on_verticalClosedStrip
        (Q := Q) (σ₀ := 0) (σ₁ := 1) (by linarith) hz)
  have hreflectedLog : DifferentiableOn ℂ
      (fun z : ℂ => Complex.log ((((Q + 1 : ℝ) : ℂ) - z)))
      (Complex.HadamardThreeLines.verticalClosedStrip 0 1) :=
    ((differentiableOn_const (((Q + 1 : ℝ) : ℂ))).sub differentiableOn_id).clog
      (fun z hz => reflectedShifted_mem_slitPlane_on_verticalClosedStrip
        (Q := Q) (σ₀ := 0) (σ₁ := 1) (by linarith) hz)
  exact (differentiableOn_const (((C₀ * C₁ : ℝ) : ℂ))).mul
    (((hpow.mul hlinear).mul hlog).mul hreflectedLog)

theorem zetaSurrogate_midpointReflectedProduct_PL_inputs
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : C₀ ≠ 0) (hC₁ : C₁ ≠ 0) :
    (∀ w ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1,
      midpointReflectedProductMajorant Q C₀ C₁ w ≠ 0) ∧
    DiffContOnCl ℂ
      (fun w => midpointReflectedProduct zetaSurrogate w /
        midpointReflectedProductMajorant Q C₀ C₁ w)
      (Complex.HadamardThreeLines.verticalStrip 0 1) := by
  constructor
  · intro w hw
    exact midpointReflectedProductMajorant_ne_zero_on_verticalClosedStrip hQ hC₀ hC₁ hw
  · have hσ : (0 : ℝ) < 1 := by norm_num
    have hsurrogate : DiffContOnCl ℂ zetaSurrogate
        (Complex.HadamardThreeLines.verticalStrip 0 1) :=
      zetaSurrogate_differentiable.diffContOnCl
    have hreflectArg : DiffContOnCl ℂ (fun w : ℂ => (1 : ℂ) - w)
        (Complex.HadamardThreeLines.verticalStrip 0 1) :=
      ((differentiable_const (1 : ℂ)).sub differentiable_id).diffContOnCl
    have hreflectSurrogate : DiffContOnCl ℂ (fun w : ℂ => zetaSurrogate ((1 : ℂ) - w))
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
      simpa [Function.comp_def] using
        zetaSurrogate_differentiable.comp_diffContOnCl hreflectArg
    have hnumerator : DiffContOnCl ℂ
        (fun w : ℂ => zetaSurrogate w * zetaSurrogate ((1 : ℂ) - w))
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
      simpa [smul_eq_mul] using hsurrogate.smul hreflectSurrogate
    have hmajorant : DiffContOnCl ℂ (midpointReflectedProductMajorant Q C₀ C₁)
        (Complex.HadamardThreeLines.verticalStrip 0 1) :=
      midpointReflectedProductMajorant_diffContOnCl_on_verticalStrip hQ
    have hmajorant_inv : DiffContOnCl ℂ
        (fun w => (midpointReflectedProductMajorant Q C₀ C₁ w)⁻¹)
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
      refine hmajorant.inv ?_
      intro w hw
      rw [verticalStrip_closure_eq_verticalClosedStrip hσ.ne] at hw
      exact midpointReflectedProductMajorant_ne_zero_on_verticalClosedStrip hQ hC₀ hC₁ hw
    have hquot : DiffContOnCl ℂ
        (fun w => (zetaSurrogate w * zetaSurrogate ((1 : ℂ) - w)) /
          midpointReflectedProductMajorant Q C₀ C₁ w)
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        hmajorant_inv.smul hnumerator
    simpa [midpointReflectedProduct_zetaSurrogate_eq] using hquot

private theorem one_sub_star_midline (t : ℝ) :
    (1 : ℂ) - star ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
      (1 / 2 : ℂ) + (t : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
    norm_num
  · simp [Complex.sub_im, Complex.add_im, Complex.mul_im]

theorem midpointReflectedProduct_norm_midline (f : ℂ → ℂ) (t : ℝ) :
    ‖midpointReflectedProduct f ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ =
      ‖f ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  unfold midpointReflectedProduct
  rw [one_sub_star_midline]
  simp [pow_two]

theorem midpointReflectedProductMajorant_norm_midline
    {Q C₀ C₁ t : ℝ} (hQ : (1 : ℝ) < Q) :
    ‖midpointReflectedProductMajorant Q C₀ C₁
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ =
      |C₀| * |C₁| *
        ‖(Q : ℂ) + ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ (5 / 2 : ℝ) *
        ‖Complex.log ((Q : ℂ) + ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2 := by
  let z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  let qz : ℂ := (Q : ℂ) + z
  have hqz_re : (0 : ℝ) < qz.re := by
    simp [qz, z, Complex.add_re, Complex.mul_re]
    linarith
  have hqz_ne : qz ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [h] at hqz_re
    simp at hqz_re
  have hreflect : (((Q + 1 : ℝ) : ℂ) - z) = star qz := by
    apply Complex.ext
    · simp [qz, z, Complex.sub_re, Complex.add_re, Complex.mul_re]
      ring_nf
    · simp [qz, z, Complex.sub_im, Complex.add_im, Complex.mul_im]
  have harg_ne : qz.arg ≠ Real.pi := by
    intro harg
    have harg' := Complex.arg_eq_pi_iff.mp harg
    linarith
  have hlog_conj : Complex.log (star qz) = star (Complex.log qz) := by
    simpa using Complex.log_conj qz harg_ne
  have hcpow :
      ‖qz ^ (((3 / 2 : ℝ) : ℂ) : ℂ)‖ = ‖qz‖ ^ (3 / 2 : ℝ) := by
    rw [Complex.norm_cpow_of_ne_zero hqz_ne]
    simp
  unfold midpointReflectedProductMajorant
  simp only [z, qz] at *
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hcpow, hreflect, hlog_conj]
  simp only [norm_star]
  have hqz_pos : 0 < ‖qz‖ := norm_pos_iff.mpr hqz_ne
  have hpow : ‖qz‖ ^ (3 / 2 : ℝ) * ‖qz‖ = ‖qz‖ ^ (5 / 2 : ℝ) := by
    calc
      ‖qz‖ ^ (3 / 2 : ℝ) * ‖qz‖ =
          ‖qz‖ ^ (3 / 2 : ℝ) * ‖qz‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ‖qz‖ ^ ((3 / 2 : ℝ) + 1) := by rw [← Real.rpow_add hqz_pos]
      _ = ‖qz‖ ^ (5 / 2 : ℝ) := by norm_num
  rw [hpow]
  simp [qz, z, pow_two, mul_comm, mul_left_comm, mul_assoc]

theorem midpointReflectedProductMajorant_norm_left_boundary
    {Q C₀ C₁ t : ℝ} (hQ : (1 : ℝ) < Q) :
    ‖midpointReflectedProductMajorant Q C₀ C₁ ((t : ℂ) * Complex.I)‖ =
      |C₀| * |C₁| *
        (‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖) *
        (‖((Q + 1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖) := by
  let z : ℂ := (t : ℂ) * Complex.I
  let qz : ℂ := (Q : ℂ) + z
  have hqz_re : (0 : ℝ) < qz.re := by
    simp [qz, z, Complex.add_re, Complex.mul_re]
    linarith
  have hqz_ne : qz ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [h] at hqz_re
    simp at hqz_re
  have hreflect :
      (((Q + 1 : ℝ) : ℂ) - z) =
        ((Q + 1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [z, Complex.sub_re, Complex.add_re, Complex.mul_re]
    · simp [z, Complex.sub_im, Complex.add_im, Complex.mul_im]
  have hcpow :
      ‖qz ^ (((3 / 2 : ℝ) : ℂ) : ℂ)‖ = ‖qz‖ ^ (3 / 2 : ℝ) := by
    rw [Complex.norm_cpow_of_ne_zero hqz_ne]
    simp
  unfold midpointReflectedProductMajorant
  simp only [z, qz] at *
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hcpow, hreflect]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem midpointReflectedProductMajorant_norm_right_boundary
    {Q C₀ C₁ t : ℝ} (hQ : (1 : ℝ) < Q) :
    ‖midpointReflectedProductMajorant Q C₀ C₁ ((1 : ℂ) + (t : ℂ) * Complex.I)‖ =
      |C₀| * |C₁| *
        (‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) *
        (‖(Q : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖ *
          ‖Complex.log ((Q : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖) := by
  let z : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I
  let qz : ℂ := (Q : ℂ) + z
  have hqz_re : (0 : ℝ) < qz.re := by
    simp [qz, z, Complex.add_re, Complex.mul_re]
    linarith
  have hqz_ne : qz ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [h] at hqz_re
    simp at hqz_re
  have hqz_eq :
      qz = ((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    simp [qz, z]
    ring
  have hreflect :
      (((Q + 1 : ℝ) : ℂ) - z) =
        (Q : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [z, Complex.sub_re, Complex.add_re, Complex.mul_re]
    · simp [z, Complex.sub_im, Complex.add_im, Complex.mul_im]
  have hcpow :
      ‖qz ^ (((3 / 2 : ℝ) : ℂ) : ℂ)‖ = ‖qz‖ ^ (3 / 2 : ℝ) := by
    rw [Complex.norm_cpow_of_ne_zero hqz_ne]
    simp
  unfold midpointReflectedProductMajorant
  simp only [z, qz] at *
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hcpow, hqz_eq, hreflect]
  simp [mul_comm, mul_left_comm, mul_assoc]

private lemma rpow_three_halves_mul_le_swap {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    a ^ (3 / 2 : ℝ) * b ≤ b ^ (3 / 2 : ℝ) * a := by
  have hhalf : a ^ (1 / 2 : ℝ) ≤ b ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow ha.le hab (by norm_num)
  have ha32 : a ^ (3 / 2 : ℝ) = a * a ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ha]
    rw [Real.rpow_one]
  have hb32 : b ^ (3 / 2 : ℝ) = b * b ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hb]
    rw [Real.rpow_one]
  rw [ha32, hb32]
  nlinarith [mul_nonneg ha.le hb.le, hhalf]

theorem zetaSurrogate_midpointReflectedProduct_left_boundary_le_one_of_edge_bounds
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hzero : ∀ t : ℝ,
      ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤
        C₀ * (‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖))
    (hone : ∀ t : ℝ,
      ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C₁ * (‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)) :
    ∀ t : ℝ,
      ‖midpointReflectedProduct zetaSurrogate ((t : ℂ) * Complex.I) /
        midpointReflectedProductMajorant Q C₀ C₁ ((t : ℂ) * Complex.I)‖ ≤ 1 := by
  intro t
  let D₀ : ℝ :=
    ‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
      ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖
  let D₁ : ℝ :=
    ‖((Q + 1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖ *
      ‖Complex.log (((Q + 1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖
  have hD₀_nonneg : 0 ≤ D₀ := by
    exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)
  have hD₁_nonneg : 0 ≤ D₁ := by
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hzero_t : ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤ C₀ * D₀ := by
    simpa [D₀] using hzero t
  have hone_neg_t :
      ‖zetaSurrogate ((1 : ℂ) - (t : ℂ) * Complex.I)‖ ≤ C₁ * D₁ := by
    have h := hone (-t)
    simpa [D₁, sub_eq_add_neg, neg_mul] using h
  have hnum :
      ‖midpointReflectedProduct zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤
        (C₀ * D₀) * (C₁ * D₁) := by
    rw [midpointReflectedProduct_zetaSurrogate_eq, norm_mul]
    exact mul_le_mul hzero_t hone_neg_t
      (norm_nonneg _) (mul_nonneg hC₀.le hD₀_nonneg)
  have hmaj_norm :
      ‖midpointReflectedProductMajorant Q C₀ C₁ ((t : ℂ) * Complex.I)‖ =
        (C₀ * D₀) * (C₁ * D₁) := by
    rw [midpointReflectedProductMajorant_norm_left_boundary (Q := Q) (C₀ := C₀)
      (C₁ := C₁) (t := t) hQ]
    rw [abs_of_pos hC₀, abs_of_pos hC₁]
    ring
  have hzstrip :
      ((t : ℂ) * Complex.I) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, Complex.mul_re]
  have hmajorant_pos :
      0 < ‖midpointReflectedProductMajorant Q C₀ C₁ ((t : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr
      (midpointReflectedProductMajorant_ne_zero_on_verticalClosedStrip hQ hC₀.ne'
        hC₁.ne' hzstrip)
  rw [norm_div]
  exact (div_le_iff₀ hmajorant_pos).2 (by simpa [hmaj_norm] using hnum)

theorem zetaSurrogate_midpointReflectedProduct_left_boundary_le_one_of_re_eq_zero
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hzero : ∀ t : ℝ,
      ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤
        C₀ * (‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖))
    (hone : ∀ t : ℝ,
      ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C₁ * (‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)) :
    ∀ w : ℂ, w.re = 0 →
      ‖midpointReflectedProduct zetaSurrogate w /
        midpointReflectedProductMajorant Q C₀ C₁ w‖ ≤ 1 := by
  intro w hw
  have hw_eq : w = (w.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [hw, Complex.mul_re]
    · simp [Complex.mul_im]
  rw [hw_eq]
  exact zetaSurrogate_midpointReflectedProduct_left_boundary_le_one_of_edge_bounds
    hQ hC₀ hC₁ hzero hone w.im

theorem zetaSurrogate_midpointReflectedProduct_right_boundary_le_one_of_edge_bounds
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hzero : ∀ t : ℝ,
      ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤
        C₀ * (‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖))
    (hone : ∀ t : ℝ,
      ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C₁ * (‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)) :
    ∀ t : ℝ,
      ‖midpointReflectedProduct zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I) /
        midpointReflectedProductMajorant Q C₀ C₁ ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 := by
  intro t
  let R₀ : ℝ := ‖(Q : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖
  let L₀ : ℝ := ‖Complex.log ((Q : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖
  let R₁ : ℝ := ‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖
  let L₁ : ℝ := ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
  have hR₀_pos : 0 < R₀ := by
    apply norm_pos_iff.mpr
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re] at hre
    linarith
  have hR₁_pos : 0 < R₁ := by
    apply norm_pos_iff.mpr
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re] at hre
    linarith
  have hR₀_le_R₁ : R₀ ≤ R₁ := by
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]
    nlinarith
  have hpower_swap : R₀ ^ (3 / 2 : ℝ) * R₁ ≤ R₁ ^ (3 / 2 : ℝ) * R₀ :=
    rpow_three_halves_mul_le_swap hR₀_pos hR₁_pos hR₀_le_R₁
  have hlog_nonneg : 0 ≤ L₀ * L₁ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hswap :
      (R₁ * L₁) * (R₀ ^ (3 / 2 : ℝ) * L₀) ≤
        (R₁ ^ (3 / 2 : ℝ) * L₁) * (R₀ * L₀) := by
    calc
      (R₁ * L₁) * (R₀ ^ (3 / 2 : ℝ) * L₀)
          = (R₀ ^ (3 / 2 : ℝ) * R₁) * (L₀ * L₁) := by ring
      _ ≤ (R₁ ^ (3 / 2 : ℝ) * R₀) * (L₀ * L₁) := by
          exact mul_le_mul_of_nonneg_right hpower_swap hlog_nonneg
      _ = (R₁ ^ (3 / 2 : ℝ) * L₁) * (R₀ * L₀) := by ring
  have hone_t : ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      C₁ * (R₁ * L₁) := by
    simpa [R₁, L₁] using hone t
  have hzero_neg_t : ‖zetaSurrogate (((-t : ℝ) : ℂ) * Complex.I)‖ ≤
      C₀ * (R₀ ^ (3 / 2 : ℝ) * L₀) := by
    simpa [R₀, L₀] using hzero (-t)
  have hsecond :
      ‖zetaSurrogate ((1 : ℂ) - ((1 : ℂ) + (t : ℂ) * Complex.I))‖ =
        ‖zetaSurrogate (((-t : ℝ) : ℂ) * Complex.I)‖ := by
    have harg :
        (1 : ℂ) - ((1 : ℂ) + (t : ℂ) * Complex.I) =
          ((-t : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [Complex.mul_re]
      · simp [Complex.mul_im]
    rw [harg]
  have hnum :
      ‖midpointReflectedProduct zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (C₁ * (R₁ * L₁)) * (C₀ * (R₀ ^ (3 / 2 : ℝ) * L₀)) := by
    rw [midpointReflectedProduct_zetaSurrogate_eq, norm_mul, hsecond]
    exact mul_le_mul hone_t hzero_neg_t (norm_nonneg _)
      (mul_nonneg hC₁.le (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hmaj_norm :
      ‖midpointReflectedProductMajorant Q C₀ C₁
          ((1 : ℂ) + (t : ℂ) * Complex.I)‖ =
        (C₀ * C₁) * ((R₁ ^ (3 / 2 : ℝ) * L₁) * (R₀ * L₀)) := by
    rw [midpointReflectedProductMajorant_norm_right_boundary (Q := Q) (C₀ := C₀)
      (C₁ := C₁) (t := t) hQ]
    rw [abs_of_pos hC₀, abs_of_pos hC₁]
    simp [R₀, L₀, R₁, L₁, mul_comm, mul_left_comm, mul_assoc]
  have hnum_le_major :
      ‖midpointReflectedProduct zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        ‖midpointReflectedProductMajorant Q C₀ C₁
          ((1 : ℂ) + (t : ℂ) * Complex.I)‖ := by
    refine hnum.trans ?_
    rw [hmaj_norm]
    calc
      (C₁ * (R₁ * L₁)) * (C₀ * (R₀ ^ (3 / 2 : ℝ) * L₀))
          = (C₀ * C₁) * ((R₁ * L₁) * (R₀ ^ (3 / 2 : ℝ) * L₀)) := by ring
      _ ≤ (C₀ * C₁) * ((R₁ ^ (3 / 2 : ℝ) * L₁) * (R₀ * L₀)) := by
          exact mul_le_mul_of_nonneg_left hswap (mul_nonneg hC₀.le hC₁.le)
  have hzstrip :
      ((1 : ℂ) + (t : ℂ) * Complex.I) ∈
        Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, Complex.add_re, Complex.mul_re]
  have hmajorant_pos :
      0 < ‖midpointReflectedProductMajorant Q C₀ C₁
        ((1 : ℂ) + (t : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr
      (midpointReflectedProductMajorant_ne_zero_on_verticalClosedStrip hQ hC₀.ne'
        hC₁.ne' hzstrip)
  rw [norm_div]
  exact (div_le_iff₀ hmajorant_pos).2 (by simpa [one_mul] using hnum_le_major)

theorem zetaSurrogate_midpointReflectedProduct_right_boundary_le_one_of_re_eq_one
    {Q C₀ C₁ : ℝ} (hQ : (1 : ℝ) < Q) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hzero : ∀ t : ℝ,
      ‖zetaSurrogate ((t : ℂ) * Complex.I)‖ ≤
        C₀ * (‖(Q : ℂ) + (t : ℂ) * Complex.I‖ ^ (3 / 2 : ℝ) *
          ‖Complex.log ((Q : ℂ) + (t : ℂ) * Complex.I)‖))
    (hone : ∀ t : ℝ,
      ‖zetaSurrogate ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C₁ * (‖((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
          ‖Complex.log (((Q + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)) :
    ∀ w : ℂ, w.re = 1 →
      ‖midpointReflectedProduct zetaSurrogate w /
        midpointReflectedProductMajorant Q C₀ C₁ w‖ ≤ 1 := by
  intro w hw
  have hw_eq : w = (1 : ℂ) + (w.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [hw, Complex.add_re, Complex.mul_re]
    · simp [Complex.add_im, Complex.mul_im]
  rw [hw_eq]
  exact zetaSurrogate_midpointReflectedProduct_right_boundary_le_one_of_edge_bounds
    hQ hC₀ hC₁ hzero hone w.im

theorem zetaSurrogate_midpointReflectedProduct_boundary_controls {Q : ℝ} (hQ : (1 : ℝ) < Q) :
    ∃ C₀ > 0, ∃ C₁ > 0,
      (∀ w : ℂ, w.re = 0 →
        ‖midpointReflectedProduct zetaSurrogate w /
          midpointReflectedProductMajorant Q C₀ C₁ w‖ ≤ 1) ∧
      (∀ w : ℂ, w.re = 1 →
        ‖midpointReflectedProduct zetaSurrogate w /
          midpointReflectedProductMajorant Q C₀ C₁ w‖ ≤ 1) := by
  obtain ⟨C₀, hC₀, hzero⟩ := zetaSurrogate_zero_line_le_const_mul_shiftedLog_global hQ
  obtain ⟨C₁, hC₁, hone⟩ := zetaSurrogate_one_line_le_const_mul_shiftedLog_global hQ
  refine ⟨C₀, hC₀, C₁, hC₁, ?_, ?_⟩
  · exact zetaSurrogate_midpointReflectedProduct_left_boundary_le_one_of_re_eq_zero
      hQ hC₀ hC₁ hzero hone
  · exact zetaSurrogate_midpointReflectedProduct_right_boundary_le_one_of_re_eq_one
      hQ hC₀ hC₁ hzero hone

/--
Midpoint reflected-product Phragmen-Lindelöf core. Once the reflected quotient
has PL growth and unit boundary control on the two strip edges, its midpoint
specialization bounds the square of the original function by the midpoint
majorant.
-/
theorem midpoint_reflectedProduct_norm_sq_le_majorant_of_verticalStrip {f : ℂ → ℂ}
    {Q C₀ C₁ t : ℝ}
    (hmajorant :
      midpointReflectedProductMajorant Q C₀ C₁
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hd : DiffContOnCl ℂ
      (fun w => midpointReflectedProduct f w /
        midpointReflectedProductMajorant Q C₀ C₁ w)
      (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hgrowth : ∃ c < Real.pi / ((1 : ℝ) - 0), ∃ B,
      (fun w => midpointReflectedProduct f w /
        midpointReflectedProductMajorant Q C₀ C₁ w)
        =O[Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            Filter.principal (Complex.re ⁻¹' Set.Ioo 0 1)]
          fun w => Real.exp (B * Real.exp (c * |w.im|)))
    (hleft : ∀ w : ℂ, w.re = 0 →
      ‖midpointReflectedProduct f w / midpointReflectedProductMajorant Q C₀ C₁ w‖ ≤ 1)
    (hright : ∀ w : ℂ, w.re = 1 →
      ‖midpointReflectedProduct f w / midpointReflectedProductMajorant Q C₀ C₁ w‖ ≤ 1) :
    ‖f ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 ≤
      ‖midpointReflectedProductMajorant Q C₀ C₁
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
  let z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have hzre : z.re = (1 / 2 : ℝ) := by
    simp [z, Complex.add_re, Complex.mul_re]
  have hzleft : (0 : ℝ) ≤ z.re := by
    rw [hzre]
    norm_num
  have hzright : z.re ≤ (1 : ℝ) := by
    rw [hzre]
    norm_num
  have hquot :
      ‖midpointReflectedProduct f z / midpointReflectedProductMajorant Q C₀ C₁ z‖ ≤
        (1 : ℝ) :=
    PhragmenLindelof.vertical_strip
      (f := fun w => midpointReflectedProduct f w /
        midpointReflectedProductMajorant Q C₀ C₁ w)
      (a := 0) (b := 1) (C := 1) (z := z)
      hd hgrowth hleft hright hzleft hzright
  have hmajorant_pos :
      0 < ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ :=
    norm_pos_iff.mpr (by simpa [z] using hmajorant)
  have hproduct :
      ‖midpointReflectedProduct f z‖ ≤
        ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ := by
    rw [norm_div] at hquot
    have hmul :
        ‖midpointReflectedProduct f z‖ ≤
          (1 : ℝ) * ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ :=
      (div_le_iff₀ hmajorant_pos).mp (by simpa using hquot)
    simpa [one_mul] using hmul
  rw [show z = (1 / 2 : ℂ) + (t : ℂ) * Complex.I by rfl] at hproduct
  rw [midpointReflectedProduct_norm_midline] at hproduct
  exact hproduct

theorem zetaSurrogate_midpoint_norm_sq_le_majorant {Q : ℝ} (hQ : (1 : ℝ) < Q) :
    ∃ C₀ > 0, ∃ C₁ > 0,
      ∀ t : ℝ,
        ‖zetaSurrogate ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 ≤
          ‖midpointReflectedProductMajorant Q C₀ C₁
            ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ := by
  obtain ⟨C₀, hC₀, C₁, hC₁, hleft, hright⟩ :=
    zetaSurrogate_midpointReflectedProduct_boundary_controls hQ
  obtain ⟨hnonzero, hd⟩ :=
    zetaSurrogate_midpointReflectedProduct_PL_inputs hQ hC₀.ne' hC₁.ne'
  refine ⟨C₀, hC₀, C₁, hC₁, ?_⟩
  intro t
  have hzmid :
      ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ∈
        Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, Complex.add_re, Complex.mul_re]
    norm_num
  exact midpoint_reflectedProduct_norm_sq_le_majorant_of_verticalStrip
    (f := zetaSurrogate) (Q := Q) (C₀ := C₀) (C₁ := C₁) (t := t)
    (hnonzero _ hzmid) hd
    (zetaSurrogate_midpointReflectedProduct_PL_growth hQ hC₀ hC₁)
    hleft hright

theorem A_critical_line_quarter_log {Q : ℝ} (hQ : (1 : ℝ) < Q) :
    ∃ k₁ > 0,
      ∀ t : ℝ,
        ‖backlundA ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          k₁ * (‖(Q : ℂ) + ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ (5 / 4 : ℝ) *
            ‖Complex.log ((Q : ℂ) + ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))‖) := by
  obtain ⟨C₀, hC₀, C₁, hC₁, hsquare⟩ :=
    zetaSurrogate_midpoint_norm_sq_le_majorant (Q := Q) hQ
  let k₁ : ℝ := Real.sqrt (C₀ * C₁)
  refine ⟨k₁, by positivity, ?_⟩
  intro t
  let z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  let R : ℝ := ‖(Q : ℂ) + z‖
  let L : ℝ := ‖Complex.log ((Q : ℂ) + z)‖
  have hRpos : 0 < R := by
    apply norm_pos_iff.mpr
    intro h
    have hre := congrArg Complex.re h
    simp [z, Complex.add_re, Complex.mul_re] at hre
    linarith
  have hLpos : 0 < L := by
    apply norm_pos_iff.mpr
    exact log_ne_zero_of_one_lt_re (by simp [z, Complex.add_re, Complex.mul_re]; linarith)
  have hksq : k₁ ^ 2 = C₀ * C₁ := by
    simpa [k₁] using Real.sq_sqrt (mul_nonneg hC₀.le hC₁.le)
  have hRpow :
      (R ^ (5 / 4 : ℝ)) ^ 2 = R ^ (5 / 2 : ℝ) := by
    rw [sq, ← Real.rpow_add hRpos]
    norm_num
  have hmajorant_norm :
      ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ =
        C₀ * C₁ * R ^ (5 / 2 : ℝ) * L ^ 2 := by
    rw [show z = (1 / 2 : ℂ) + (t : ℂ) * Complex.I by rfl]
    rw [midpointReflectedProductMajorant_norm_midline (Q := Q) (C₀ := C₀)
      (C₁ := C₁) (t := t) hQ]
    rw [abs_of_pos hC₀, abs_of_pos hC₁]
  have htarget_sq :
      ‖zetaSurrogate z‖ ^ 2 ≤
        (k₁ * (R ^ (5 / 4 : ℝ) * L)) ^ 2 := by
    have hsquare' :
        ‖zetaSurrogate z‖ ^ 2 ≤ ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ := by
      simpa [z] using hsquare t
    calc
      ‖zetaSurrogate z‖ ^ 2
          ≤ ‖midpointReflectedProductMajorant Q C₀ C₁ z‖ := hsquare'
      _ = C₀ * C₁ * R ^ (5 / 2 : ℝ) * L ^ 2 := hmajorant_norm
      _ = (k₁ * (R ^ (5 / 4 : ℝ) * L)) ^ 2 := by
          rw [mul_pow, mul_pow, hksq, hRpow]
          ring
  have htarget_nonneg : 0 ≤ k₁ * (R ^ (5 / 4 : ℝ) * L) := by
    positivity
  have hsurrogate_le :
      ‖zetaSurrogate z‖ ≤ k₁ * (R ^ (5 / 4 : ℝ) * L) :=
    (sq_le_sq₀ (norm_nonneg _) htarget_nonneg).mp htarget_sq
  have hz_ne : z ≠ 1 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp [z, Complex.add_re, Complex.mul_re] at hre
  have hsurrogate_eq : zetaSurrogate z = backlundA z := by
    simp [zetaSurrogate, backlundA, hz_ne]
  rw [show ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = z by rfl]
  rw [← hsurrogate_eq]
  simpa [R, L] using hsurrogate_le

/--
The fixed shifted log-power quotient for the entire zeta surrogate has the
analytic side conditions needed by the PL shell on the strip `0 < re z < 1`.
-/
theorem zetaSurrogate_shiftedLogPower_PL_inputs {Q : ℝ} (hQ : (1 : ℝ) < Q) :
    (∀ w ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1,
      shiftedLogPowerNormalizer Q ((5 / 4 : ℝ) : ℂ) (1 : ℂ) w ≠ 0) ∧
    DiffContOnCl ℂ
      (fun w => zetaSurrogate w /
        shiftedLogPowerNormalizer Q ((5 / 4 : ℝ) : ℂ) (1 : ℂ) w)
      (Complex.HadamardThreeLines.verticalStrip 0 1) := by
  have hσ : (0 : ℝ) < 1 := by norm_num
  have hQstrip : (1 : ℝ) < Q + (0 : ℝ) := by simpa using hQ
  constructor
  · intro w hw
    exact shiftedLogPowerNormalizer_ne_zero_on_verticalClosedStrip
      ((5 / 4 : ℝ) : ℂ) (1 : ℂ) hQstrip hw
  · have hsurrogate : DiffContOnCl ℂ zetaSurrogate
        (Complex.HadamardThreeLines.verticalStrip 0 1) :=
      zetaSurrogate_differentiable.diffContOnCl
    have hnormalizer : DiffContOnCl ℂ
        (shiftedLogPowerNormalizer Q ((5 / 4 : ℝ) : ℂ) (1 : ℂ))
        (Complex.HadamardThreeLines.verticalStrip 0 1) :=
      shiftedLogPowerNormalizer_diffContOnCl_on_verticalStrip
        ((5 / 4 : ℝ) : ℂ) (1 : ℂ) hσ hQstrip
    have hnormalizer_inv : DiffContOnCl ℂ
        (fun w =>
          (shiftedLogPowerNormalizer Q ((5 / 4 : ℝ) : ℂ) (1 : ℂ) w)⁻¹)
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
      refine hnormalizer.inv ?_
      intro w hw
      rw [verticalStrip_closure_eq_verticalClosedStrip hσ.ne] at hw
      exact shiftedLogPowerNormalizer_ne_zero_on_verticalClosedStrip
        ((5 / 4 : ℝ) : ℂ) (1 : ℂ) hQstrip hw
    simpa [div_eq_mul_inv, mul_comm] using hnormalizer_inv.smul hsurrogate

end Backlund
