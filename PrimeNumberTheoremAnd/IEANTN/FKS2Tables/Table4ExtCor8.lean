import PrimeNumberTheoremAnd.IEANTN.FKS2
import PrimeNumberTheoremAnd.IEANTN.FKS2Tables.Table4ExtCore

/-!
# Extended Table 4 certificates from FKS2 Corollary 8

This file isolates the proof-producing boundary needed to replace the trusted
extended Table 4 row data.  Generated data should provide a `Cor8CellCert` for
each `Cell`; this module proves that such a certificate implies the row bound
currently supplied by `Table4Ext.allCells_trusted`.
-/

namespace FKS2
namespace Table4Ext

open Real

/-- A numerical theta bound at an earlier start point can be reused at a later
start point if the step function value has not decreased. -/
theorem etheta_numericalBound_mono_start {x₀ x₁ : ℝ} {epsTheta : ℝ → ℝ}
    (h : Eθ.numericalBound x₀ epsTheta) (hx₀x₁ : x₀ ≤ x₁)
    (heps : epsTheta x₀ ≤ epsTheta x₁) :
    Eθ.numericalBound x₁ epsTheta := by
  intro x hx
  exact le_trans (h x (le_trans hx₀x₁ hx)) heps

/-- Data needed to derive one extended Table 4 row from `FKS2.corollary_8`.

The remaining generator work is to fill these fields from the fine theta
subdivision used in the FKS2 ancillary computation and to prove `hPiNum_le`
by decidable interval arithmetic. -/
structure Cor8CellCert (c : Cell) where
  M : ℕ
  nodes : Fin (M + 1) → EReal
  hx₁ : (14 : ℝ) ≤ exp (c.b : ℝ)
  hmono : Monotone nodes
  h_start : nodes 0 = (log (exp (c.b : ℝ)) : EReal)
  h_end : nodes (Fin.last M) = ⊤
  h_finite : ∀ j : Fin (M + 1), nodes j = ⊤ → j = Fin.last M
  epsTheta : ℝ → ℝ
  hTheta : ∀ i : Fin (M + 1),
    Eθ.numericalBound (exp (nodes i).toReal) epsTheta
  hPiNum_le :
    (⨆ i : Finset.Iio (Fin.last M),
      επ_num
        (fun j : Fin (i.val.val + 1) => (nodes ⟨j.val, by grind⟩).toReal)
        epsTheta
        (exp (c.b : ℝ))
        (exp (nodes i.val).toReal)
        (if (i + 1) = Fin.last M then ⊤ else exp (nodes (i + 1)).toReal))
      ≤ (c.eps : ℝ)

/-- A generated Corollary 8 certificate for one cell gives the row bound used
by the extended Table 4 interpolation layer. -/
theorem cell_bound_from_cor8 (c : Cell) (cert : Cor8CellCert c) :
    Eπ.bound (c.eps : ℝ) (exp (c.b : ℝ)) := by
  intro x hx
  exact le_trans
    (corollary_8 cert.hx₁ cert.nodes cert.hmono cert.h_start cert.h_end
      cert.h_finite cert.epsTheta cert.hTheta x hx)
    cert.hPiNum_le

end Table4Ext
end FKS2
