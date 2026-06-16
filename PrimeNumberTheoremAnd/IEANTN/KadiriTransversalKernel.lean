import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Transversal pole-crossing kernel

This file contains the elementary complex-analysis kernel for a horizontal contour crossing a
simple pole transversally. It is independent of the zeta function and Kadiri's test functions.
-/

open Complex MeasureTheory

open scoped Interval

private lemma shifted_line_mem_slitPlane {β δ σ : ℝ} (hδ : δ ≠ 0) :
    (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  simpa using hδ

private lemma hasDerivAt_log_shifted_line {β δ σ : ℝ} (hδ : δ ≠ 0) :
    HasDerivAt
      (fun τ : ℝ => Complex.log (((τ : ℂ) - (β : ℂ)) + (δ : ℂ) * I))
      ((((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹) σ := by
  have hline :
      HasDerivAt (fun τ : ℝ => ((τ : ℂ) - (β : ℂ)) + (δ : ℂ) * I) (1 : ℂ) σ := by
    simpa using
      ((Complex.ofRealCLM.hasDerivAt (x := σ)).sub_const (β : ℂ)).add_const
        ((δ : ℂ) * I)
  simpa [div_eq_mul_inv] using hline.clog_real (shifted_line_mem_slitPlane hδ)

private lemma abs_log_le_of_bounds {e M y : ℝ} (he : 0 < e) (hey : e ≤ y)
    (hyM : y ≤ M) :
    |Real.log y| ≤ |Real.log e| + |Real.log M| := by
  have hy : 0 < y := lt_of_lt_of_le he hey
  have hM : 0 < M := lt_of_lt_of_le hy hyM
  rw [abs_le]
  constructor
  · have hlog : Real.log e ≤ Real.log y := Real.log_le_log he hey
    have hneg : -(|Real.log e| + |Real.log M|) ≤ Real.log e := by
      have h₁ : -|Real.log e| ≤ Real.log e := neg_abs_le (Real.log e)
      have h₂ : 0 ≤ |Real.log M| := abs_nonneg (Real.log M)
      linarith
    linarith
  · have hlog : Real.log y ≤ Real.log M := Real.log_le_log hy hyM
    have hMle : Real.log M ≤ |Real.log e| + |Real.log M| := by
      have h₁ : Real.log M ≤ |Real.log M| := le_abs_self (Real.log M)
      have h₂ : 0 ≤ |Real.log e| := abs_nonneg (Real.log e)
      linarith
    linarith

private lemma norm_log_le_of_norm_bounds {z : ℂ} {e M : ℝ} (he : 0 < e)
    (hze : e ≤ ‖z‖) (hzM : ‖z‖ ≤ M) :
    ‖Complex.log z‖ ≤ |Real.log e| + |Real.log M| + Real.pi := by
  calc
    ‖Complex.log z‖
        ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
          Complex.norm_le_abs_re_add_abs_im (Complex.log z)
    _ = |Real.log ‖z‖| + |Complex.arg z| := by rw [Complex.log_re, Complex.log_im]
    _ ≤ (|Real.log e| + |Real.log M|) + Real.pi :=
      add_le_add (abs_log_le_of_bounds he hze hzM) (Complex.abs_arg_le_pi z)
    _ = |Real.log e| + |Real.log M| + Real.pi := by ring

private lemma right_endpoint_norm_lower {a β δ e : ℝ} (he : 0 < e)
    (hβ : β ∈ Set.Icc (-a + e) (1 + a - e)) :
    e ≤ ‖(((1 + a : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖ := by
  let z : ℂ := ((1 + a : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I
  have hre : z.re = 1 + a - β := by simp [z]
  have hx : e ≤ |z.re| := by
    have hx_nonneg : 0 ≤ 1 + a - β := by linarith [he.le, hβ.2]
    have hx_lower : e ≤ 1 + a - β := by linarith [hβ.2]
    simpa [hre, abs_of_nonneg hx_nonneg] using hx_lower
  exact hx.trans (Complex.abs_re_le_norm z)

private lemma left_endpoint_norm_lower {a β δ e : ℝ} (he : 0 < e)
    (hβ : β ∈ Set.Icc (-a + e) (1 + a - e)) :
    e ≤ ‖(((-a : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖ := by
  let z : ℂ := (((-a : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)
  have hre : z.re = -a - β := by simp [z]
  have hx : e ≤ |z.re| := by
    have hx_nonpos : -a - β ≤ 0 := by linarith [he, hβ.1]
    have hx_lower : e ≤ β + a := by linarith [hβ.1]
    simpa [hre, abs_of_nonpos hx_nonpos] using hx_lower
  exact hx.trans (Complex.abs_re_le_norm z)

private lemma right_endpoint_norm_upper {a β δ e : ℝ} (he : 0 < e) (hδ : |δ| ≤ 1)
    (hβ : β ∈ Set.Icc (-a + e) (1 + a - e)) :
    ‖(((1 + a : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖
      ≤ 1 + |1 + 2 * a| + |e| := by
  let z : ℂ := ((1 + a : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I
  have hre : z.re = 1 + a - β := by simp [z]
  have him : z.im = δ := by simp [z]
  have hx : |z.re| ≤ |1 + 2 * a| + |e| := by
    have hx_nonneg : 0 ≤ 1 + a - β := by linarith [hβ.2]
    have hx_upper : 1 + a - β ≤ 1 + 2 * a - e := by linarith [hβ.1]
    have hlen : 1 + 2 * a - e ≤ |1 + 2 * a| + |e| := by
      have h₁ : 1 + 2 * a ≤ |1 + 2 * a| := le_abs_self (1 + 2 * a)
      have h₂ : -e ≤ |e| := neg_le_abs e
      linarith
    simpa [hre, abs_of_nonneg hx_nonneg] using hx_upper.trans hlen
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ (|1 + 2 * a| + |e|) + 1 := add_le_add hx (by simpa [him] using hδ)
    _ = 1 + |1 + 2 * a| + |e| := by ring

private lemma left_endpoint_norm_upper {a β δ e : ℝ} (he : 0 < e) (hδ : |δ| ≤ 1)
    (hβ : β ∈ Set.Icc (-a + e) (1 + a - e)) :
    ‖(((-a : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖
      ≤ 1 + |1 + 2 * a| + |e| := by
  let z : ℂ := (((-a : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)
  have hre : z.re = -a - β := by simp [z]
  have him : z.im = δ := by simp [z]
  have hx : |z.re| ≤ |1 + 2 * a| + |e| := by
    have hx_nonpos : -a - β ≤ 0 := by linarith [he, hβ.1]
    have hx_upper : β + a ≤ 1 + 2 * a - e := by linarith [hβ.2]
    have hlen : 1 + 2 * a - e ≤ |1 + 2 * a| + |e| := by
      have h₁ : 1 + 2 * a ≤ |1 + 2 * a| := le_abs_self (1 + 2 * a)
      have h₂ : -e ≤ |e| := neg_le_abs e
      linarith
    simpa [hre, abs_of_nonpos hx_nonpos] using hx_upper.trans hlen
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ (|1 + 2 * a| + |e|) + 1 := add_le_add hx (by simpa [him] using hδ)
    _ = 1 + |1 + 2 * a| + |e| := by ring

/-- Closed form for the transversal crossing of a simple pole by a real horizontal segment. -/
lemma transversal_pole_crossing_eq (a β δ : ℝ) (hδ : δ ≠ 0) :
    (∫ σ in (-a)..(1 + a), (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹)
      = Complex.log (((1 + a : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)
        - Complex.log (((-a : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I) := by
  have hderiv :
      ∀ σ ∈ Set.uIcc (-a) (1 + a),
        HasDerivAt
          (fun τ : ℝ => Complex.log (((τ : ℂ) - (β : ℂ)) + (δ : ℂ) * I))
          ((((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹) σ := by
    intro σ _hσ
    exact hasDerivAt_log_shifted_line hδ
  have hcont :
      ContinuousOn
        (fun σ : ℝ => (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹)
        (Set.uIcc (-a) (1 + a)) := by
    have hline_cont :
        Continuous fun σ : ℝ => ((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I := by
      fun_prop
    refine hline_cont.continuousOn.inv₀ ?_
    intro σ _hσ hzero
    apply hδ
    simpa using congrArg Complex.im hzero
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]

/-- Uniform norm bound for the transversal crossing away from the segment endpoints. -/
lemma transversal_pole_crossing_norm_le (a e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ δ : ℝ, δ ≠ 0 → ∀ β : ℝ,
        β ∈ Set.Icc (-a + e) (1 + a - e) →
          ‖∫ σ in (-a)..(1 + a), (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹‖ ≤ C := by
  let M : ℝ := 1 + |1 + 2 * a| + |e|
  let B : ℝ := |Real.log e| + |Real.log M| + Real.pi
  refine ⟨2 * B + (1 + |1 + 2 * a|), ?_, ?_⟩
  · have hB : 0 ≤ B := by
      dsimp [B]
      positivity
    have htail : 0 ≤ 1 + |1 + 2 * a| := by positivity
    nlinarith
  · intro δ hδ β hβ
    by_cases hδ_small : |δ| ≤ 1
    · have hright :
          ‖Complex.log (((1 + a : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖ ≤ B := by
        dsimp [B, M]
        exact norm_log_le_of_norm_bounds he
          (right_endpoint_norm_lower he hβ)
          (right_endpoint_norm_upper he hδ_small hβ)
      have hleft :
          ‖Complex.log (((-a : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖ ≤ B := by
        dsimp [B, M]
        exact norm_log_le_of_norm_bounds he
          (left_endpoint_norm_lower he hβ)
          (left_endpoint_norm_upper he hδ_small hβ)
      rw [transversal_pole_crossing_eq a β δ hδ]
      calc
        ‖Complex.log (((1 + a : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I) -
            Complex.log (((-a : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖
            ≤ ‖Complex.log (((1 + a : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖ +
                ‖Complex.log (((-a : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add hright hleft
        _ ≤ 2 * B + (1 + |1 + 2 * a|) := by
          have htail : 0 ≤ 1 + |1 + 2 * a| := by positivity
          linarith
    · have hδ_large : 1 ≤ |δ| := (lt_of_not_ge hδ_small).le
      have hpoint :
          ∀ σ ∈ Ι (-a) (1 + a),
            ‖(((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹‖ ≤ (1 : ℝ) := by
        intro σ _hσ
        let z : ℂ := ((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I
        have him : z.im = δ := by simp [z]
        have hz_norm : 1 ≤ ‖z‖ := by
          calc
            1 ≤ |δ| := hδ_large
            _ = |z.im| := by rw [him]
            _ ≤ ‖z‖ := Complex.abs_im_le_norm z
        change ‖z⁻¹‖ ≤ (1 : ℝ)
        rw [norm_inv]
        exact inv_le_one_of_one_le₀ hz_norm
      have hlarge :
          ‖∫ σ in (-a)..(1 + a), (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹‖
            ≤ |1 + 2 * a| := by
        simpa [one_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_mul] using
          (intervalIntegral.norm_integral_le_of_norm_le_const
            (a := -a) (b := 1 + a) (C := (1 : ℝ))
            (f := fun σ : ℝ => (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹) hpoint)
      exact hlarge.trans (by
        have hB : 0 ≤ B := by
          dsimp [B]
          positivity
        linarith)

/-- Closed form for a simple-pole crossing on a variable right endpoint `[0, x]`. -/
lemma transversal_pole_crossing_zero_to_eq (x β δ : ℝ) (hδ : δ ≠ 0) :
    (∫ σ in 0..x, (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹)
      = Complex.log (((x : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)
        - Complex.log (((0 : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I) := by
  have hderiv :
      ∀ σ ∈ Set.uIcc 0 x,
        HasDerivAt
          (fun τ : ℝ => Complex.log (((τ : ℂ) - (β : ℂ)) + (δ : ℂ) * I))
          ((((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹) σ := by
    intro σ _hσ
    exact hasDerivAt_log_shifted_line hδ
  have hcont :
      ContinuousOn
        (fun σ : ℝ => (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹)
        (Set.uIcc 0 x) := by
    have hline_cont :
        Continuous fun σ : ℝ => ((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I := by
      fun_prop
    refine hline_cont.continuousOn.inv₀ ?_
    intro σ _hσ hzero
    apply hδ
    simpa using congrArg Complex.im hzero
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]

/--
Uniform norm bound for a transversal crossing on `[0, x]` when the pole's real
part stays at least `e` from `0` and at least `d` from the moving right endpoint.
-/
lemma transversal_pole_crossing_zero_to_norm_le (a e d : ℝ)
    (ha : 0 ≤ a) (he : 0 < e) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x δ β : ℝ, 0 ≤ x → x ≤ 1 + a → δ ≠ 0 → e ≤ β → β + d ≤ x →
        ‖∫ σ in 0..x, (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹‖ ≤ C := by
  let η : ℝ := min e d
  have hη : 0 < η := lt_min he hd
  let M : ℝ := 1 + |1 + a| + |e| + |d|
  let B : ℝ := |Real.log η| + |Real.log M| + Real.pi
  refine ⟨2 * B + (1 + a), ?_, ?_⟩
  · have hB : 0 ≤ B := by
      dsimp [B]
      positivity
    have htail : 0 ≤ 1 + a := by linarith
    nlinarith
  · intro x δ β hx0 hx_le hδ hβ_left hβ_right
    by_cases hδ_small : |δ| ≤ 1
    · have hright_lower :
          η ≤ ‖(((x : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖ := by
        let z : ℂ := (((x : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)
        have hz_re : z.re = x - β := by simp [z]
        have hxβ_nonneg : 0 ≤ x - β := by linarith
        have hd_le : d ≤ x - β := by linarith
        have hηd : η ≤ d := by dsimp [η]; exact min_le_right _ _
        calc
          η ≤ d := hηd
          _ ≤ |z.re| := by simpa [hz_re, abs_of_nonneg hxβ_nonneg] using hd_le
          _ ≤ ‖z‖ := Complex.abs_re_le_norm z
      have hright_upper :
          ‖(((x : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖ ≤ M := by
        let z : ℂ := (((x : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)
        have hz_re : z.re = x - β := by simp [z]
        have hz_im : z.im = δ := by simp [z]
        have hxβ_nonneg : 0 ≤ x - β := by linarith
        have hxβ_upper : x - β ≤ 1 + a - e := by linarith
        have hre_bound : |z.re| ≤ |1 + a| + |e| + |d| := by
          have htail : 1 + a - e ≤ |1 + a| + |e| + |d| := by
            have h₁ : 1 + a ≤ |1 + a| := le_abs_self (1 + a)
            have h₂ : -e ≤ |e| := neg_le_abs e
            have h₃ : 0 ≤ |d| := abs_nonneg d
            linarith
          simpa [hz_re, abs_of_nonneg hxβ_nonneg] using hxβ_upper.trans htail
        calc
          ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
          _ ≤ (|1 + a| + |e| + |d|) + 1 :=
            add_le_add hre_bound (by simpa [hz_im] using hδ_small)
          _ = M := by ring
      have hleft_lower :
          η ≤ ‖(((0 : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖ := by
        let z : ℂ := (((0 : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)
        have hz_re : z.re = -β := by simp [z]
        have hβ_nonneg : 0 ≤ β := le_trans he.le hβ_left
        have hηe : η ≤ e := by dsimp [η]; exact min_le_left _ _
        calc
          η ≤ e := hηe
          _ ≤ |z.re| := by simpa [hz_re, abs_of_nonpos (by linarith : -β ≤ 0)] using hβ_left
          _ ≤ ‖z‖ := Complex.abs_re_le_norm z
      have hleft_upper :
          ‖(((0 : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖ ≤ M := by
        let z : ℂ := (((0 : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)
        have hz_re : z.re = -β := by simp [z]
        have hz_im : z.im = δ := by simp [z]
        have hβ_nonneg : 0 ≤ β := le_trans he.le hβ_left
        have hβ_upper : β ≤ 1 + a - d := by linarith
        have hre_bound : |z.re| ≤ |1 + a| + |e| + |d| := by
          have htail : 1 + a - d ≤ |1 + a| + |e| + |d| := by
            have h₁ : 1 + a ≤ |1 + a| := le_abs_self (1 + a)
            have h₂ : -d ≤ |d| := neg_le_abs d
            have h₃ : 0 ≤ |e| := abs_nonneg e
            linarith
          simpa [hz_re, abs_of_nonpos (by linarith : -β ≤ 0)] using hβ_upper.trans htail
        calc
          ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
          _ ≤ (|1 + a| + |e| + |d|) + 1 :=
            add_le_add hre_bound (by simpa [hz_im] using hδ_small)
          _ = M := by ring
      have hright_log :
          ‖Complex.log (((x : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖ ≤ B := by
        dsimp [B]
        exact norm_log_le_of_norm_bounds hη hright_lower hright_upper
      have hleft_log :
          ‖Complex.log (((0 : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖ ≤ B := by
        dsimp [B]
        exact norm_log_le_of_norm_bounds hη hleft_lower hleft_upper
      rw [transversal_pole_crossing_zero_to_eq x β δ hδ]
      calc
        ‖Complex.log (((x : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I) -
            Complex.log (((0 : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖
            ≤ ‖Complex.log (((x : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖ +
                ‖Complex.log (((0 : ℝ) : ℂ) - (β : ℂ) + (δ : ℂ) * I)‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add hright_log hleft_log
        _ ≤ 2 * B + (1 + a) := by
          have htail : 0 ≤ 1 + a := by linarith
          linarith
    · have hδ_large : 1 ≤ |δ| := (lt_of_not_ge hδ_small).le
      have hpoint :
          ∀ σ ∈ Ι 0 x,
            ‖(((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹‖ ≤ (1 : ℝ) := by
        intro σ _hσ
        let z : ℂ := ((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I
        have him : z.im = δ := by simp [z]
        have hz_norm : 1 ≤ ‖z‖ := by
          calc
            1 ≤ |δ| := hδ_large
            _ = |z.im| := by rw [him]
            _ ≤ ‖z‖ := Complex.abs_im_le_norm z
        change ‖z⁻¹‖ ≤ (1 : ℝ)
        rw [norm_inv]
        exact inv_le_one_of_one_le₀ hz_norm
      have hlarge :
          ‖∫ σ in 0..x, (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹‖
            ≤ 1 + a := by
        have hnorm :=
          intervalIntegral.norm_integral_le_of_norm_le_const
            (a := 0) (b := x) (C := (1 : ℝ))
            (f := fun σ : ℝ => (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹) hpoint
        calc
          ‖∫ σ in 0..x, (((σ : ℂ) - (β : ℂ)) + (δ : ℂ) * I)⁻¹‖
              ≤ (1 : ℝ) * |x - 0| := hnorm
          _ = x := by rw [one_mul, sub_zero, abs_of_nonneg hx0]
          _ ≤ 1 + a := hx_le
      exact hlarge.trans (by
        have hB : 0 ≤ B := by
          dsimp [B]
          positivity
        linarith)
