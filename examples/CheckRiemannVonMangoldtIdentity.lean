import PrimeNumberTheoremAnd.RiemannVonMangoldtIdentity

noncomputable section

open Complex

#check riemannXi_meromorphicOn
#check riemannXi_logDeriv_meromorphicOn
#check riemannXi_meromorphicOrderAt_ne_top
#check riemannXi_no_boundary_divisor_support
#check riemannXi_rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt
#check riemannXi_rectangle_argumentChange_eq_two_pi_sum_meromorphicOrderAt
#check riemannVonMangoldtGammaPoint
#check riemannVonMangoldtGammaStirlingMain
#check riemannVonMangoldtLogGammaBranch
#check riemannVonMangoldtGammaPhase
#check riemannVonMangoldtGammaStirlingMain_im
#check im_logGamma_quarter_stirling_of_logGammaSeq_stirling_remainder
#check logGammaBranch
#check exp_logGammaBranch
#check riemannVonMangoldtMainTerm
#check riemannVonMangoldtS
#check riemannZeta_N_eq_toFinset_sum_order
#check riemannXi_eq_zeta_mul_gamma_factor_of_im_ne_zero
#check riemannXi_eq_zero_iff_riemannZeta_eq_zero_of_im_ne_zero
#check meromorphicOrderAt_riemannXi_eq_riemannZeta_of_im_ne_zero
#check riemannXi_rectangle_divisor_sum_eq_riemannZeta_N

example (z : ℂ) (hz : 0 < z.re) :
    Complex.exp (logGammaBranch z) = Complex.Gamma z :=
  exp_logGammaBranch hz

example (T : ℝ) (hT : 1 ≤ T)
    (hstirling :
      |(riemannVonMangoldtLogGammaBranch (riemannVonMangoldtGammaPoint T) -
          riemannVonMangoldtGammaStirlingMain (riemannVonMangoldtGammaPoint T)).im|
        ≤ 1 / (3 * T)) :
    |(riemannVonMangoldtLogGammaBranch ((1 / 4 : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im -
        ((T / 2) * Real.log (T / 2) - T / 2 - Real.pi / 8
          + (T / 4) * Real.log (1 + 1 / (4 * T ^ 2))
          + (1 / 4) * Real.arctan (1 / (2 * T)))| ≤ 1 / (3 * T) :=
  im_logGamma_quarter_stirling_of_logGammaSeq_stirling_remainder T hT hstirling

#print axioms riemannXi_rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt
#print axioms riemannXi_rectangle_argumentChange_eq_two_pi_sum_meromorphicOrderAt
#print axioms riemannVonMangoldtGammaStirlingMain_im
#print axioms im_logGamma_quarter_stirling_of_logGammaSeq_stirling_remainder
#print axioms exp_logGammaBranch
#print axioms riemannVonMangoldtMainTerm
#print axioms riemannVonMangoldtS
#print axioms riemannZeta_N_eq_toFinset_sum_order
#print axioms riemannXi_eq_zeta_mul_gamma_factor_of_im_ne_zero
#print axioms riemannXi_eq_zero_iff_riemannZeta_eq_zero_of_im_ne_zero
#print axioms meromorphicOrderAt_riemannXi_eq_riemannZeta_of_im_ne_zero
#print axioms riemannXi_rectangle_divisor_sum_eq_riemannZeta_N
