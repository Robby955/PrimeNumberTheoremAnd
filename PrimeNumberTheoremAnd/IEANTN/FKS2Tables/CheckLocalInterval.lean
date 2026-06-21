import PrimeNumberTheoremAnd.IEANTN.FKS2

namespace FKS2

open Real

example {x₁ : ℝ} (hx₁ : x₁ ≥ 14)
    {M : ℕ} (b' : Fin (M + 1) → EReal) (hmono : Monotone b')
    (h_b_start : b' 0 = log x₁)
    (h_b_end : b' (Fin.last M) = ⊤)
    (h_finite : ∀ j : Fin (M+1), b' j = ⊤ → j = Fin.last M)
    (εθ_num : ℝ → ℝ)
    (h_εθ_cell :
      ∀ i : Fin M,
        Eθ.intervalBound (exp (b' i.castSucc).toReal)
          (if i.succ = Fin.last M then ⊤
           else ↑(exp (b' i.succ).toReal)) εθ_num)
    (h_εθ_pos :
      ∀ i : Fin M, 0 < εθ_num (exp (b' i.castSucc).toReal))
    (x : ℝ) (hx : x ≥ x₁) :
    Eπ x ≤ iSup (fun i : Finset.Iio (Fin.last M) ↦
      επ_num (fun j : Fin (i.val.val+1) ↦ (b' ⟨ j.val, by grind ⟩).toReal)
        εθ_num x₁ (exp (b' i.val).toReal)
        (if (i+1) = Fin.last M then ⊤ else exp (b' (i+1)).toReal)) := by
  exact corollary_8_interval hx₁ b' hmono h_b_start h_b_end h_finite
    εθ_num h_εθ_cell h_εθ_pos x hx

end FKS2
