module

public import PrimeNumberTheoremAnd.EulerMaclaurin
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# Second-order Euler-Maclaurin kernel

This file packages the periodized second Bernoulli kernel and the integration-by-parts
identity needed to upgrade the first-order Euler-Maclaurin formula.
-/

@[expose] public section

open Finset Interval MeasureTheory

/-- The periodized second Bernoulli polynomial divided by two. -/
noncomputable def bernoulli2PeriodizedHalf (x : ℝ) : ℂ :=
  (((Int.fract x : ℝ) : ℂ) ^ 2 - (((Int.fract x : ℝ) : ℂ)) + (1 / 6 : ℂ)) / 2

lemma abs_bernoulli2_periodized_le (x : ℝ) :
    |Int.fract x ^ 2 - Int.fract x + 1 / 6| ≤ (1 / 6 : ℝ) := by
  let u : ℝ := Int.fract x
  have hu0 : 0 ≤ u := Int.fract_nonneg x
  have hu1 : u ≤ 1 := (Int.fract_lt_one x).le
  have hsq : 0 ≤ (u - 1 / 2) ^ 2 := sq_nonneg (u - 1 / 2)
  have hprod : u * (u - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hu0 (sub_nonpos.mpr hu1)
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

lemma abs_bernoulli2_periodized_half_le (x : ℝ) :
    |(Int.fract x ^ 2 - Int.fract x + 1 / 6) / 2| ≤ (1 / 12 : ℝ) := by
  have h := abs_bernoulli2_periodized_le x
  calc
    |(Int.fract x ^ 2 - Int.fract x + 1 / 6) / 2|
        = |Int.fract x ^ 2 - Int.fract x + 1 / 6| / 2 := by
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (1 / 6 : ℝ) / 2 := div_le_div_of_nonneg_right h (by norm_num)
    _ = (1 / 12 : ℝ) := by norm_num

lemma norm_bernoulli2PeriodizedHalf_le (x : ℝ) :
    ‖bernoulli2PeriodizedHalf x‖ ≤ (1 / 12 : ℝ) := by
  have h := abs_bernoulli2_periodized_half_le x
  have hcast :
      bernoulli2PeriodizedHalf x =
        (((Int.fract x ^ 2 - Int.fract x + 1 / 6) / 2 : ℝ) : ℂ) := by
    simp [bernoulli2PeriodizedHalf]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  exact h

lemma fract_eq_sub_nat_of_mem_Ioo (m : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (m : ℝ) (m + 1 : ℝ)) :
    Int.fract x = x - m := by
  rw [← Int.self_sub_floor x]
  have hfloor : ((⌊x⌋ : ℤ) : ℝ) = (m : ℝ) := by
    simpa using
      (Int.floor_eq_on_Ico' (R := ℝ) (m : ℤ) x ⟨hx.1.le, by simpa using hx.2⟩)
  rw [hfloor]

lemma B1_eq_sub_nat_sub_half_of_mem_Ioo (m : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (m : ℝ) (m + 1 : ℝ)) :
    B1 x = x - m - 1 / 2 := by
  unfold B1
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg m) hx.1.le
  have hfloor : (⌊x⌋₊ : ℝ) = (m : ℝ) := by
    have hfloor_int : ((⌊x⌋ : ℤ) : ℝ) = (m : ℝ) := by
      simpa using
        (Int.floor_eq_on_Ico' (R := ℝ) (m : ℤ) x ⟨hx.1.le, by simpa using hx.2⟩)
    rw [natCast_floor_eq_intCast_floor hx0, hfloor_int]
  rw [hfloor]

lemma hasDerivAt_bernoulli2PeriodizedHalf_of_mem_Ioo (m : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (m : ℝ) (m + 1 : ℝ)) :
    HasDerivAt bernoulli2PeriodizedHalf (((B1 x : ℝ) : ℂ)) x := by
  have hnear : ∀ᶠ y in nhds x, y ∈ Set.Ioo (m : ℝ) (m + 1 : ℝ) :=
    isOpen_Ioo.mem_nhds hx
  have heq :
      bernoulli2PeriodizedHalf =ᶠ[nhds x]
        (fun y : ℝ ↦
          ((((y - (m : ℝ)) ^ 2 - (y - (m : ℝ)) + 1 / 6) / 2 : ℝ) : ℂ)) := by
    filter_upwards [hnear] with y hy
    rw [bernoulli2PeriodizedHalf, fract_eq_sub_nat_of_mem_Ioo m hy]
    norm_num
  have hbase : HasDerivAt (fun y : ℝ ↦ y - (m : ℝ)) 1 x := by
    simpa using (hasDerivAt_id x).sub_const (m : ℝ)
  have hreal :
      HasDerivAt
        (fun y : ℝ ↦ (((y - (m : ℝ)) ^ 2 - (y - (m : ℝ)) + 1 / 6) / 2))
        ((2 * (x - (m : ℝ)) - 1) / 2) x := by
    have hpoly := (((hbase.pow 2).sub hbase).add_const (1 / 6)).div_const 2
    convert hpoly using 2 <;>
      first
        | rfl
        | (push_cast; ring)
        | (simp only [Pi.pow_apply, Pi.sub_apply]; push_cast; ring)
  have htarget :
      ((((2 * (x - (m : ℝ)) - 1) / 2 : ℝ) : ℂ)) =
        (((B1 x : ℝ) : ℂ)) := by
    rw [B1_eq_sub_nat_sub_half_of_mem_Ioo m hx]
    norm_num
    ring_nf
  exact (hreal.ofReal_comp.congr_deriv htarget).congr_of_eventuallyEq heq

lemma continuous_bernoulli2PeriodizedHalf : Continuous bernoulli2PeriodizedHalf := by
  let p : ℝ → ℝ := fun x ↦ (x ^ 2 - x + 1 / 6) / 2
  have hp_cont : ContinuousOn p (Set.Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun x : ℝ ↦ (x ^ 2 - x + 1 / 6) / 2) (Set.Icc (0 : ℝ) 1)
    fun_prop
  have hp_end : p 0 = p 1 := by
    norm_num [p]
  have hreal : Continuous (p ∘ Int.fract) := hp_cont.comp_fract'' hp_end
  have hcomplex : Continuous (fun x : ℝ ↦ ((p (Int.fract x) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hreal
  convert hcomplex using 1
  ext x
  simp [p, bernoulli2PeriodizedHalf]

private lemma complex_deriv_ofReal (x : ℝ) : deriv Complex.ofReal x = 1 := by
  have h := (Complex.ofRealCLM.hasDerivAt (x := x)).deriv
  change deriv Complex.ofReal x = (1 : ℂ) at h
  exact h

lemma intervalIntegrable_B1_complex {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ ((B1 t : ℝ) : ℂ)) volume a b := by
  have h := intervalIntegrable_deriv_mul_B1 (𝕜 := ℂ)
    (f := Complex.ofReal) (a := a) (b := b) ha hab ?_
  · refine h.congr ?_
    intro t _ht
    change deriv Complex.ofReal t * ↑(B1 t) = ↑(B1 t)
    rw [complex_deriv_ofReal]
    simp
  · exact (continuousOn_const : ContinuousOn (fun _ : ℝ ↦ (1 : ℂ)) [[a, b]]).congr
      (fun x _hx ↦ complex_deriv_ofReal x)

noncomputable def secondOrderIBPExpr (g g' : ℝ → ℂ) (u v : ℝ) : ℂ :=
  g v * bernoulli2PeriodizedHalf v -
    g u * bernoulli2PeriodizedHalf u -
    ∫ y in u..v, g' y * bernoulli2PeriodizedHalf y

noncomputable def B1IntegralExpr (g : ℝ → ℂ) (u v : ℝ) : ℂ :=
  ∫ y in u..v, g y * ((B1 y : ℝ) : ℂ)

lemma secondOrderIBPExpr_eq_B1_on_unit {g g' : ℝ → ℂ} {u v : ℝ}
    (huv : u ≤ v) (hu_nonneg : 0 ≤ u) (m : ℕ)
    (hmu : (m : ℝ) ≤ u) (hvm : v ≤ (m + 1 : ℝ))
    (hg_cont : ContinuousOn g [[u, v]])
    (hg_deriv : ∀ x ∈ Set.Ioo u v, HasDerivAt g (g' x) x)
    (hg'_cont : ContinuousOn g' [[u, v]]) :
    secondOrderIBPExpr g g' u v = B1IntegralExpr g u v := by
  let W' : ℝ → ℂ := fun y ↦ ((B1 y : ℝ) : ℂ)
  have hIoo_to_unit :
      ∀ {x : ℝ}, x ∈ Set.Ioo (min u v) (max u v) →
        x ∈ Set.Ioo (m : ℝ) (m + 1 : ℝ) := by
    intro x hx
    rw [min_eq_left huv, max_eq_right huv] at hx
    exact ⟨lt_of_le_of_lt hmu hx.1, lt_of_lt_of_le hx.2 hvm⟩
  have h_ibp :
      ∫ y in u..v, g y * W' y =
        g v * bernoulli2PeriodizedHalf v -
          g u * bernoulli2PeriodizedHalf u -
          ∫ y in u..v, g' y * bernoulli2PeriodizedHalf y := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (by simpa [Set.uIcc_of_le huv] using hg_cont)
      continuous_bernoulli2PeriodizedHalf.continuousOn
      (by
        intro x hx
        rw [min_eq_left huv, max_eq_right huv] at hx
        exact hg_deriv x hx)
      (by
        intro x hx
        simpa [W'] using hasDerivAt_bernoulli2PeriodizedHalf_of_mem_Ioo m
          (hIoo_to_unit hx))
      hg'_cont.intervalIntegrable
      (by
        have hB1 := intervalIntegrable_B1_complex hu_nonneg huv
        simpa [W'] using hB1)
  calc
    secondOrderIBPExpr g g' u v
        = g v * bernoulli2PeriodizedHalf v -
          g u * bernoulli2PeriodizedHalf u -
          ∫ y in u..v, g' y * bernoulli2PeriodizedHalf y := rfl
    _ = ∫ y in u..v, g y * W' y := h_ibp.symm
    _ = B1IntegralExpr g u v := by rfl

lemma intervalIntegrable_second_order_integrand {g' : ℝ → ℂ} {u v : ℝ}
    (hg'_cont : ContinuousOn g' [[u, v]]) :
    IntervalIntegrable (fun y : ℝ ↦ g' y * bernoulli2PeriodizedHalf y) volume u v := by
  exact (hg'_cont.mul continuous_bernoulli2PeriodizedHalf.continuousOn).intervalIntegrable

lemma secondOrderIBPExpr_add_adjacent {g g' : ℝ → ℂ} {a c b : ℝ}
    (hInt_ac : IntervalIntegrable (fun y : ℝ ↦ g' y * bernoulli2PeriodizedHalf y) volume a c)
    (hInt_cb : IntervalIntegrable (fun y : ℝ ↦ g' y * bernoulli2PeriodizedHalf y) volume c b) :
    secondOrderIBPExpr g g' a c + secondOrderIBPExpr g g' c b =
      secondOrderIBPExpr g g' a b := by
  unfold secondOrderIBPExpr
  rw [← intervalIntegral.integral_add_adjacent_intervals hInt_ac hInt_cb]
  ring

lemma B1IntegralExpr_add_adjacent {g : ℝ → ℂ} {a c b : ℝ}
    (hInt_ac : IntervalIntegrable (fun y : ℝ ↦ g y * ((B1 y : ℝ) : ℂ)) volume a c)
    (hInt_cb : IntervalIntegrable (fun y : ℝ ↦ g y * ((B1 y : ℝ) : ℂ)) volume c b) :
  B1IntegralExpr g a c + B1IntegralExpr g c b = B1IntegralExpr g a b := by
  unfold B1IntegralExpr
  rw [← intervalIntegral.integral_add_adjacent_intervals hInt_ac hInt_cb]

theorem secondOrderIBPExpr_eq_B1IntegralExpr {g g' : ℝ → ℂ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hg_cont : ContinuousOn g [[a, b]])
    (hg_deriv : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x)
    (hg'_cont : ContinuousOn g' [[a, b]])
    (hGB1_int :
      ∀ {u v : ℝ}, a ≤ u → v ≤ b → 0 ≤ u → u ≤ v →
        IntervalIntegrable (fun y : ℝ ↦ g y * ((B1 y : ℝ) : ℂ)) volume u v) :
    secondOrderIBPExpr g g' a b = B1IntegralExpr g a b := by
  let P : ℕ → Prop := fun d ↦
    ∀ {u v : ℝ}, a ≤ u → v ≤ b → 0 ≤ u → u ≤ v → ⌊v⌋₊ - ⌊u⌋₊ = d →
      secondOrderIBPExpr g g' u v = B1IntegralExpr g u v
  have restrict_cont :
      ∀ {u v : ℝ}, a ≤ u → v ≤ b → u ≤ v →
        ContinuousOn g [[u, v]] := by
    intro u v hau hvb huv
    refine hg_cont.mono ?_
    rw [Set.uIcc_of_le huv, Set.uIcc_of_le hab]
    intro x hx
    exact ⟨le_trans hau hx.1, le_trans hx.2 hvb⟩
  have restrict_deriv :
      ∀ {u v x : ℝ}, a ≤ u → v ≤ b → u ≤ v →
        x ∈ Set.Ioo u v → HasDerivAt g (g' x) x := by
    intro u v x hau hvb _huv hx
    exact hg_deriv x ⟨lt_of_le_of_lt hau hx.1, lt_of_lt_of_le hx.2 hvb⟩
  have restrict_second_cont :
      ∀ {u v : ℝ}, a ≤ u → v ≤ b → u ≤ v →
        ContinuousOn g' [[u, v]] := by
    intro u v hau hvb huv
    refine hg'_cont.mono ?_
    rw [Set.uIcc_of_le huv, Set.uIcc_of_le hab]
    intro x hx
    exact ⟨le_trans hau hx.1, le_trans hx.2 hvb⟩
  have hP : ∀ d, P d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro u v hau hvb hu_nonneg huv hd
        by_cases hfloor_eq : ⌊v⌋₊ = ⌊u⌋₊
        · let m : ℕ := ⌊u⌋₊
          have hmu : (m : ℝ) ≤ u := by
            simpa [m] using Nat.floor_le hu_nonneg
          have hv_nonneg : 0 ≤ v := le_trans hu_nonneg huv
          have hvm : v ≤ (m + 1 : ℝ) := by
            have hv_lt : v < (⌊v⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one v
            have hcast : (⌊v⌋₊ : ℝ) = (m : ℝ) := by
              simp [m, hfloor_eq]
            linarith
          exact secondOrderIBPExpr_eq_B1_on_unit huv hu_nonneg m hmu hvm
            (restrict_cont hau hvb huv)
            (fun x hx ↦ restrict_deriv hau hvb huv hx)
            (restrict_second_cont hau hvb huv)
        · have hfloor_le : ⌊u⌋₊ ≤ ⌊v⌋₊ := Nat.floor_mono huv
          have hfloor_lt : ⌊u⌋₊ < ⌊v⌋₊ := by
            exact lt_of_le_of_ne hfloor_le (fun h ↦ hfloor_eq h.symm)
          let c : ℝ := ((⌊u⌋₊ + 1 : ℕ) : ℝ)
          have hac : u ≤ c := by
            exact le_of_lt (by simpa [c] using Nat.lt_floor_add_one u)
          have hcb : c ≤ v := by
            have hv_nonneg : 0 ≤ v := le_trans hu_nonneg huv
            have hfloor_v_le : (⌊v⌋₊ : ℝ) ≤ v := Nat.floor_le hv_nonneg
            have hsucc_le_nat : ⌊u⌋₊ + 1 ≤ ⌊v⌋₊ := Nat.succ_le_iff.mpr hfloor_lt
            have hsucc_le : (((⌊u⌋₊ + 1 : ℕ) : ℝ)) ≤ (⌊v⌋₊ : ℝ) := by
              exact_mod_cast hsucc_le_nat
            exact le_trans (by simpa [c] using hsucc_le) hfloor_v_le
          have hau_c : a ≤ c := le_trans hau hac
          have hcb_b : c ≤ b := le_trans hcb hvb
          have hc_nonneg : 0 ≤ c := le_trans hu_nonneg hac
          have hlocal : secondOrderIBPExpr g g' u c = B1IntegralExpr g u c := by
            refine secondOrderIBPExpr_eq_B1_on_unit hac hu_nonneg ⌊u⌋₊ ?_ ?_
              (restrict_cont hau hcb_b hac)
              (fun x hx ↦ restrict_deriv hau hcb_b hac hx)
              (restrict_second_cont hau hcb_b hac)
            · exact Nat.floor_le hu_nonneg
            · simp [c]
          have hfloor_c : ⌊c⌋₊ = ⌊u⌋₊ + 1 := by
            simpa [c] using (Nat.floor_natCast (⌊u⌋₊ + 1))
          have hsmaller : ⌊v⌋₊ - ⌊c⌋₊ < d := by
            rw [hfloor_c]
            omega
          have hrec : secondOrderIBPExpr g g' c v = B1IntegralExpr g c v := by
            exact ih (⌊v⌋₊ - ⌊c⌋₊) hsmaller hau_c hvb hc_nonneg hcb rfl
          have hInt2_uc :
              IntervalIntegrable
                (fun y : ℝ ↦ g' y * bernoulli2PeriodizedHalf y) volume u c :=
            intervalIntegrable_second_order_integrand (restrict_second_cont hau hcb_b hac)
          have hInt2_cv :
              IntervalIntegrable
                (fun y : ℝ ↦ g' y * bernoulli2PeriodizedHalf y) volume c v :=
            intervalIntegrable_second_order_integrand (restrict_second_cont hau_c hvb hcb)
          have hIntB1_uc :
              IntervalIntegrable
                (fun y : ℝ ↦ g y * ((B1 y : ℝ) : ℂ)) volume u c :=
            hGB1_int hau hcb_b hu_nonneg hac
          have hIntB1_cv :
              IntervalIntegrable
                (fun y : ℝ ↦ g y * ((B1 y : ℝ) : ℂ)) volume c v :=
            hGB1_int hau_c hvb hc_nonneg hcb
          calc
            secondOrderIBPExpr g g' u v
                = secondOrderIBPExpr g g' u c + secondOrderIBPExpr g g' c v := by
                    exact (secondOrderIBPExpr_add_adjacent hInt2_uc hInt2_cv).symm
            _ = B1IntegralExpr g u c + B1IntegralExpr g c v := by rw [hlocal, hrec]
            _ = B1IntegralExpr g u v := B1IntegralExpr_add_adjacent hIntB1_uc hIntB1_cv
  exact hP (⌊b⌋₊ - ⌊a⌋₊) (le_rfl : a ≤ a) (le_rfl : b ≤ b) ha hab rfl

theorem sum_eq_integral_add_boundary_deriv_bernoulli2 {f : ℝ → ℂ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_deriv_cont : ContinuousOn (deriv f) [[a, b]])
    (h_second_deriv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun y : ℝ ↦ deriv f y) (deriv (deriv f) t) t)
    (h_second_cont : ContinuousOn (deriv (deriv f)) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) +
        (deriv f b * bernoulli2PeriodizedHalf b -
          deriv f a * bernoulli2PeriodizedHalf a -
          ∫ t in a..b, deriv (deriv f) t * bernoulli2PeriodizedHalf t) := by
  have hfirst := sum_eq_integral_add_integral_deriv (𝕜 := ℂ)
    (a := a) (b := b) (f := f) ha hab hf_diff h_deriv_cont
  have hsecond :
      secondOrderIBPExpr (fun t : ℝ ↦ deriv f t) (fun t : ℝ ↦ deriv (deriv f) t) a b =
        B1IntegralExpr (fun t : ℝ ↦ deriv f t) a b := by
    refine secondOrderIBPExpr_eq_B1IntegralExpr (a := a) (b := b) ha hab
      h_deriv_cont h_second_deriv h_second_cont ?_
    intro u v hau hvb hu_nonneg huv
    have hsub : [[u, v]] ⊆ [[a, b]] := by
      rw [Set.uIcc_of_le huv, Set.uIcc_of_le hab]
      intro x hx
      exact ⟨le_trans hau hx.1, le_trans hx.2 hvb⟩
    exact intervalIntegrable_deriv_mul_B1 (𝕜 := ℂ)
      (f := f) (a := u) (b := v) hu_nonneg huv (h_deriv_cont.mono hsub)
  calc
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k
        = f a * B1 a - f b * B1 b + (∫ t in a..b, f t) +
          B1IntegralExpr (fun t : ℝ ↦ deriv f t) a b := by
            simpa [B1IntegralExpr] using hfirst
    _ = f a * B1 a - f b * B1 b + (∫ t in a..b, f t) +
        secondOrderIBPExpr (fun t : ℝ ↦ deriv f t) (fun t : ℝ ↦ deriv (deriv f) t) a b := by
          rw [hsecond]
    _ = f a * B1 a - f b * B1 b + (∫ t in a..b, f t) +
        (deriv f b * bernoulli2PeriodizedHalf b -
          deriv f a * bernoulli2PeriodizedHalf a -
          ∫ t in a..b, deriv (deriv f) t * bernoulli2PeriodizedHalf t) := by
          rfl

end
