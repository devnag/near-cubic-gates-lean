import Proof.Gates.OuterM.ARunD

set_option autoImplicit false

namespace NearCubicGates.Close.OuterM

/-- The A-run's total step count (`L = ν^{G+2}`, `W` the walk's end, `nbits = |T_G(L).bits|`,
`nb = natBitLength T_G(L)`). -/
def costT (G et ct coeff cE ν L W nbits nb : ℕ) : ℕ :=
  costA G ν L W + 1 + (costB ν (2 * (ct * (ν + 1) ^ et) + 2) + 1 + (costC et ct ν + 1 +
    costD L nbits (2 * (coeff * (L + nb + 1) ^ cE) + 2)))

/-- The degree. -/
def aE (G et cE : ℕ) : ℕ := (G + 3 + et) * (cE + 2)

/-- The coefficient. -/
def aK (G et ct coeff cE : ℕ) : ℕ :=
  2000 * ((G + 2) + et * 2 ^ et + ct + coeff * 3 ^ cE + 1) * (2 * ct + 9) ^ (cE + 2)

theorem pow_le_pow_of (V a b : ℕ) (hV : 1 ≤ V) (h : a ≤ b) : V ^ a ≤ V ^ b := Nat.pow_le_pow_right hV h

/-- **The A-run's cost bound.** -/
theorem costT_le (G et ct coeff cE ν L W nbits nb : ℕ) (hL : L ≤ (ν + 1) ^ (G + 2)) (hW : W ≤ 2 * L + 3)
    (hb : nbits ≤ bmax et ct ν) (hnb : nb ≤ nbits + 1) :
    2 * costT G et ct coeff cE ν L W nbits nb + 2 ≤ aK G et ct coeff cE * (ν + 1) ^ aE G et cE := by
  have hV1 : 1 ≤ ν + 1 := by omega
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (ν + 1) ^ (G + 3 + et) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = (2 * ct + 9) * Q := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = M ^ (cE + 2) := ⟨_, rfl⟩
  obtain ⟨Kc, hKc⟩ : ∃ Kc, Kc = (G + 2) + et * 2 ^ et + ct + coeff * 3 ^ cE + 1 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Kc * P := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact Nat.one_le_pow _ _ hV1
  have hVQ : ν + 1 ≤ Q := by
    rw [hQ]
    calc ν + 1 = (ν + 1) ^ 1 := (pow_one _).symm
      _ ≤ (ν + 1) ^ (G + 3 + et) := pow_le_pow_of _ 1 _ hV1 (by omega)
  have hQM : Q ≤ M := by rw [hM]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hM9 : 9 * Q ≤ M := by rw [hM]; exact Nat.mul_le_mul_right _ (by omega)
  have hM1 : 1 ≤ M := by omega
  have hMP : M ≤ P := by
    rw [hP]
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ (cE + 2) := pow_le_pow_of M 1 (cE + 2) hM1 (by omega)
  have hM2P : M * M ≤ P := by
    rw [hP]
    calc M * M = M ^ 2 := (sq M).symm
      _ ≤ M ^ (cE + 2) := pow_le_pow_of M 2 (cE + 2) hM1 (by omega)
  have hMcP : M ^ cE ≤ P := by rw [hP]; exact pow_le_pow_of M cE (cE + 2) hM1 (by omega)
  have hKc1 : 1 ≤ Kc := by omega
  have hPY : P ≤ Y := by rw [hY]; exact Nat.le_mul_of_pos_left _ (by omega)
  -- primitive quantities
  have f3 : (ν + 1) ^ (G + 2) ≤ Q := by rw [hQ]; exact pow_le_pow_of _ _ _ hV1 (by omega)
  have f4 : (ν + 1) ^ et ≤ Q := by rw [hQ]; exact pow_le_pow_of _ _ _ hV1 (by omega)
  have f5 : bmax et ct ν ≤ M := by
    unfold bmax
    have h1 : (ν + 1) ^ et * (2 * ct) ≤ Q * (2 * ct) := Nat.mul_le_mul_right _ f4
    have h2 : (2 * ct + 9) * Q = Q * (2 * ct) + 9 * Q := by ring
    rw [hM, h2]
    omega
  have f6 : (ν + 1 + 1) ^ et ≤ 2 ^ et * Q := by
    calc (ν + 1 + 1) ^ et ≤ (2 * (ν + 1)) ^ et := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ et * (ν + 1) ^ et := mul_pow 2 _ et
      _ ≤ 2 ^ et * Q := Nat.mul_le_mul_left _ f4
  have f7 : nbits ≤ M := hb.trans f5
  have f8 : L + nb + 1 ≤ 3 * M := by omega
  -- the nonlinear terms, each against Y
  have tA : (G + 2) * (61 * (ν + 1) ^ (G + 2)) ≤ 61 * Y := by
    have h1 : (G + 2) * (61 * (ν + 1) ^ (G + 2)) ≤ (G + 2) * (61 * P) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ((f3.trans hQM).trans hMP))
    have h2 : (G + 2) * P ≤ Y := by rw [hY]; exact Nat.mul_le_mul_right _ (by omega)
    have h3 : (G + 2) * (61 * P) = 61 * ((G + 2) * P) := by ring
    omega
  have tC1 : et * (61 * (ν + 1 + 1) ^ et) ≤ 61 * Y := by
    have h1 : et * (61 * (ν + 1 + 1) ^ et) ≤ et * (61 * (2 ^ et * P)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (f6.trans (Nat.mul_le_mul_left _ (hQM.trans hMP))))
    have h2 : et * 2 ^ et * P ≤ Y := by rw [hY]; exact Nat.mul_le_mul_right _ (by omega)
    have h3 : et * (61 * (2 ^ et * P)) = 61 * (et * 2 ^ et * P) := by ring
    omega
  have tC2 : (ν + 1) ^ et * (4 * (2 * ct) + 4) ≤ 12 * Y := by
    have h1 : (ν + 1) ^ et * (4 * (2 * ct) + 4) ≤ P * (4 * (2 * ct) + 4) :=
      Nat.mul_le_mul_right _ ((f4.trans hQM).trans hMP)
    have h2 : ct * P ≤ Y := by rw [hY]; exact Nat.mul_le_mul_right _ (by omega)
    have h3 : P * (4 * (2 * ct) + 4) = 8 * (ct * P) + 4 * P := by ring
    omega
  have tC3 : bmax et ct ν * (3 * (0 + bmax et ct ν) + 15) ≤ 18 * Y := by
    have h1 : bmax et ct ν * bmax et ct ν ≤ M * M := Nat.mul_le_mul f5 f5
    have h2 : bmax et ct ν * (3 * (0 + bmax et ct ν) + 15) = 3 * (bmax et ct ν * bmax et ct ν) +
      15 * bmax et ct ν := by ring
    omega
  have tB : ct * (ν + 1) ^ et ≤ Y := by
    have h1 : ct * (ν + 1) ^ et ≤ ct * P := Nat.mul_le_mul_left _ ((f4.trans hQM).trans hMP)
    have h2 : ct * P ≤ Y := by rw [hY]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  have tD : coeff * (L + nb + 1) ^ cE ≤ Y := by
    have h1 : (L + nb + 1) ^ cE ≤ 3 ^ cE * M ^ cE := by
      calc (L + nb + 1) ^ cE ≤ (3 * M) ^ cE := Nat.pow_le_pow_left f8 _
        _ = 3 ^ cE * M ^ cE := mul_pow 3 M cE
    have h2 : coeff * (L + nb + 1) ^ cE ≤ coeff * 3 ^ cE * P := by
      calc coeff * (L + nb + 1) ^ cE ≤ coeff * (3 ^ cE * M ^ cE) := Nat.mul_le_mul_left _ h1
        _ ≤ coeff * (3 ^ cE * P) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hMcP)
        _ = coeff * 3 ^ cE * P := by ring
    have h3 : coeff * 3 ^ cE * P ≤ Y := by rw [hY]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  have hfin : aK G et ct coeff cE * (ν + 1) ^ aE G et cE = 2000 * Y := by
    rw [hY, hP, hM, hQ, hKc, mul_pow, ← pow_mul]
    unfold aK aE
    ring
  rw [hfin]
  have hMY : M ≤ Y := hMP.trans hPY
  have hLY : L ≤ Y := by omega
  have hνY : ν ≤ Y := by omega
  unfold costT costA costB costC costD
  omega

end NearCubicGates.Close.OuterM
