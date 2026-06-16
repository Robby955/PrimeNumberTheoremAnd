import PrimeNumberTheoremAnd.IEANTN.CH2.CH2
import PrimeNumberTheoremAnd.IEANTN.KadiriHadamardPVBridge

/-!
# Downstream Kadiri Theorem 3.1 assembly

This file keeps the final Kadiri Theorem 3.1 assembly downstream of
`Kadiri.lean`, so it can import the axiom-clean horizontal and Hadamard/PV
wrappers without creating an import cycle.
-/

namespace Kadiri

open Complex Filter MeasureTheory
open Asymptotics
open scoped Topology Interval

noncomputable section

/--
At a nontrivial zero `rho`, the negative logarithmic derivative has principal
part `-ord(rho)/(s-rho)` and bounded remainder on the punctured neighborhood.
-/
theorem kadiri_neg_zeta_logDeriv_principal_part_at_nontrivialZero
    (rho : NontrivialZeros) :
    ((fun s : ℂ => -deriv riemannZeta s / riemannZeta s)
        - fun s => -((riemannZeta.order (rho : ℂ) : ℂ)) / (s - (rho : ℂ)))
      =O[𝓝[≠] (rho : ℂ)] (1 : ℂ → ℂ) := by
  have h := (kadiri_logDeriv_zeta_hadamard_pv_remainder_bound rho).neg_left
  refine h.congr ?_ (fun _ => rfl)
  intro s
  simp [Pi.sub_apply, Pi.div_apply, neg_div]
  ring

end

end Kadiri
