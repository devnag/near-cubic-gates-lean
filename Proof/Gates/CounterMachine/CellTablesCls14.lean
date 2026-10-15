import Proof.Gates.CounterMachine.CellTablesCls13

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

attribute [local irreducible] zeta KN Kwb Kwv Kbkc Kbody Kbk Klb Kpr Kst b0Of dN dE dB dP

def Kf (B1 B2 C0 e0 cT tsk : ℕ) : ℕ :=
  16000 * Kwv B1 B2 C0 e0 cT + KN B1 B2 C0 e0 cT * (500 * (Kwb B1 B2 C0 e0 + 1) ^ 2 + 100 * (tsk + 3)) +
    (5 + 640 * (2 * Kwb B1 B2 C0 e0 + 1)) * KN B1 B2 C0 e0 cT + 10 * zeta + 40 * Kwv B1 B2 C0 e0 cT +
    Kbkc C0 e0 cT + 400

theorem budget_le (RK : TabCallMachine B1 B2 cT PolyTab) (r : CellReq B1 B2 cT) (C0 e0 : ℕ) :
    langBudget (tabCallCallee RK) (zK (zOf B1 B2 C0 e0) cT r.c.n (leadOnes (cellInput r))) VV MM (cellInput r)
        (mainCost ((zOf B1 B2 C0 e0).Lk (leadOnes (cellInput r)))
          ((zK (zOf B1 B2 C0 e0) cT r.c.n (leadOnes (cellInput r))).Bk (leadOnes (cellInput r)))
          (C0 * (r.c.n + 1) ^ e0) r) +
      bkCost (zOf B1 B2 C0 e0) cT r.c.n (leadOnes (cellInput r)) ≤
      Kf B1 B2 C0 e0 cT RK.wf.program.tapeCount * 2 ^ (r.c.n - r.p.k) *
        (r.c.n + 1) ^ (2 * Jmax r.c.n + dE B1 B2 e0) := by
  rw [leadOnes_cellInput]
  have sz := sizes r
  have hN := main_le r C0 e0
  have hbk := bk_le r C0 e0
  have hV := V_le r C0 e0
  have hW := W_le r C0 e0
  have hZ := Z_le r
  set L := natBitLength r.c.n with hL
  set T := r.c.n + 1 with hT
  have hT1 : 1 ≤ T := by omega
  set z := zK (zOf B1 B2 C0 e0) cT r.c.n L with hz
  set N := mainCost ((zOf B1 B2 C0 e0).Lk L) (z.Bk L) (C0 * T ^ e0) r with hNd
  set V := z.W L + z.Lk L + z.Bk L + z.a1 + z.a2 + z.a3 + z.c1 + z.c2 + z.c3 + 1 with hVd
  set G := GT r (dE B1 B2 e0) with hG
  set tsk := RK.wf.program.tapeCount with htsk
  set c1 := e0 + 2 * b0Of B1 B2 with hc1
  have hG1 : 1 ≤ G := one_GT r _
  have hzW : z.W L = (zOf B1 B2 C0 e0).W L := rfl
  -- the set-up and the small terms
  have s1 := setup_le z L V le_rfl
  have hVG : (L + 1) * V ≤ 2 * Kwv B1 B2 C0 e0 cT * G := by
    calc (L + 1) * V ≤ (2 * T) * (Kwv B1 B2 C0 e0 cT * 2 ^ (r.c.n - r.p.k) * T ^ (c1 + 6)) :=
          Nat.mul_le_mul (by have := sz.L3; omega) hV
      _ = 2 * Kwv B1 B2 C0 e0 cT * (2 ^ (r.c.n - r.p.k) * T ^ (c1 + 7)) := by rw [pow_succ T (c1 + 6)]; ring
      _ ≤ 2 * Kwv B1 B2 C0 e0 cT * GT r (c1 + 7) := Nat.mul_le_mul_left _ (S_GT r _)
      _ ≤ _ := Nat.mul_le_mul_left _ (GT_mono r (by unfold dE; omega))
  have hV1 : V ≤ (L + 1) * V := Nat.le_mul_of_pos_left _ (by omega)
  have hX : (cellInput r).length ≤ zeta * G := by
    have h1 := T_GT r (b0Of B1 B2)
    have h2 : T ^ b0Of B1 B2 ≤ G := h1.trans (GT_mono r (by unfold dE; omega))
    have h3 : (cellInput r).length ≤ zeta * T ^ b0Of B1 B2 := by omega
    exact h3.trans (Nat.mul_le_mul_left _ h2)
  -- the run
  have hNG : N ≤ KN B1 B2 C0 e0 cT * GT r (dN B1 B2 e0) := hN
  have hWb : z.W L ≤ Kwb B1 B2 C0 e0 * T ^ c1 := hW
  have hW2 : 500 * (z.W L + 1) ^ 2 + 100 * (tsk + 3) ≤ (500 * (Kwb B1 B2 C0 e0 + 1) ^ 2 + 100 * (tsk + 3)) * T ^ (2 * c1) := by
    have h1 : z.W L + 1 ≤ (Kwb B1 B2 C0 e0 + 1) * T ^ c1 := by
      have := Nat.one_le_pow c1 T hT1
      have e : (Kwb B1 B2 C0 e0 + 1) * T ^ c1 = Kwb B1 B2 C0 e0 * T ^ c1 + T ^ c1 := by ring
      omega
    have h2 : (z.W L + 1) ^ 2 ≤ (Kwb B1 B2 C0 e0 + 1) ^ 2 * T ^ (2 * c1) := by
      calc (z.W L + 1) ^ 2 ≤ ((Kwb B1 B2 C0 e0 + 1) * T ^ c1) ^ 2 := Nat.pow_le_pow_left h1 2
        _ = _ := by rw [mul_pow, ← pow_mul, mul_comm c1 2]
    have h3 : 1 ≤ T ^ (2 * c1) := Nat.one_le_pow _ _ hT1
    have h4 : 100 * (tsk + 3) ≤ 100 * (tsk + 3) * T ^ (2 * c1) := Nat.le_mul_of_pos_right _ h3
    calc 500 * (z.W L + 1) ^ 2 + 100 * (tsk + 3) ≤ 500 * ((Kwb B1 B2 C0 e0 + 1) ^ 2 * T ^ (2 * c1)) +
          100 * (tsk + 3) * T ^ (2 * c1) := Nat.add_le_add (Nat.mul_le_mul_left _ h2) h4
      _ = _ := by ring
  have hP1 : N * (500 * (z.W L + 1) ^ 2 + 100 * (tsk + 3)) ≤
      KN B1 B2 C0 e0 cT * (500 * (Kwb B1 B2 C0 e0 + 1) ^ 2 + 100 * (tsk + 3)) * G := by
    calc N * (500 * (z.W L + 1) ^ 2 + 100 * (tsk + 3)) ≤ (KN B1 B2 C0 e0 cT * GT r (dN B1 B2 e0)) *
          ((500 * (Kwb B1 B2 C0 e0 + 1) ^ 2 + 100 * (tsk + 3)) * T ^ (2 * c1)) := Nat.mul_le_mul hNG hW2
      _ = KN B1 B2 C0 e0 cT * (500 * (Kwb B1 B2 C0 e0 + 1) ^ 2 + 100 * (tsk + 3)) * GT r (dN B1 B2 e0 + 2 * c1) := by
          unfold GT; rw [← hT, pow_add T (dN B1 B2 e0)]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ (GT_mono r (by unfold dE dN; omega))
  have hP2 : (2 * z.W L + 1) * N ≤ (2 * Kwb B1 B2 C0 e0 + 1) * KN B1 B2 C0 e0 cT * G := by
    have h1 : 2 * z.W L + 1 ≤ (2 * Kwb B1 B2 C0 e0 + 1) * T ^ c1 := by
      have := Nat.one_le_pow c1 T hT1
      have e : (2 * Kwb B1 B2 C0 e0 + 1) * T ^ c1 = 2 * (Kwb B1 B2 C0 e0 * T ^ c1) + T ^ c1 := by ring
      omega
    calc (2 * z.W L + 1) * N ≤ ((2 * Kwb B1 B2 C0 e0 + 1) * T ^ c1) * (KN B1 B2 C0 e0 cT * GT r (dN B1 B2 e0)) :=
          Nat.mul_le_mul h1 hNG
      _ = (2 * Kwb B1 B2 C0 e0 + 1) * KN B1 B2 C0 e0 cT * GT r (dN B1 B2 e0 + c1) := by
          unfold GT; rw [← hT, pow_add T (dN B1 B2 e0)]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ (GT_mono r (by unfold dE dN; omega))
  have hNG' : N ≤ KN B1 B2 C0 e0 cT * G := hNG.trans (Nat.mul_le_mul_left _ (GT_mono r (by unfold dE dN; omega)))
  have hbk' : bkCost (zOf B1 B2 C0 e0) cT r.c.n L ≤ Kbkc C0 e0 cT * G :=
    hbk.trans (Nat.mul_le_mul_left _ (GT_mono r (by unfold dE; omega)))
  have hfin : Kf B1 B2 C0 e0 cT tsk * 2 ^ (r.c.n - r.p.k) * T ^ (2 * Jmax r.c.n + dE B1 B2 e0) =
      Kf B1 B2 C0 e0 cT tsk * G := by
    rw [hG]; unfold GT Gc; rw [← hT, pow_add]; ring
  rw [hfin]
  unfold langBudget
  simp only []
  rw [leadOnes_cellInput]
  have e : Kf B1 B2 C0 e0 cT tsk * G = 16000 * (Kwv B1 B2 C0 e0 cT * G) +
      KN B1 B2 C0 e0 cT * (500 * (Kwb B1 B2 C0 e0 + 1) ^ 2 + 100 * (tsk + 3)) * G +
      5 * (KN B1 B2 C0 e0 cT * G) + 640 * ((2 * Kwb B1 B2 C0 e0 + 1) * KN B1 B2 C0 e0 cT * G) +
      10 * (zeta * G) + 40 * (Kwv B1 B2 C0 e0 cT * G) + Kbkc C0 e0 cT * G + 400 * G := by
    unfold Kf; ring
  rw [e]
  have hL' : leadOnes (cellInput r) = L := leadOnes_cellInput r
  have s2 : 8000 * (L + 1) * V ≤ 16000 * (Kwv B1 B2 C0 e0 cT * G) := by
    calc 8000 * (L + 1) * V = 8000 * ((L + 1) * V) := by ring
      _ ≤ 8000 * (2 * Kwv B1 B2 C0 e0 cT * G) := Nat.mul_le_mul_left _ hVG
      _ = _ := by ring
  have hVG2 : V ≤ 2 * (Kwv B1 B2 C0 e0 cT * G) := (hV1.trans hVG).trans_eq (by ring)
  have hP2' : 5 * ((2 * z.W L + 1) * N) ≤ 5 * ((2 * Kwb B1 B2 C0 e0 + 1) * KN B1 B2 C0 e0 cT * G) :=
    Nat.mul_le_mul_left _ hP2
  have htk : TSK (tabCallCallee RK) = tsk := rfl
  rw [← hL, htk]
  simp only [VV, MM] at *
  clear_value z N V G tsk c1 L T
  have hLkV : z.Lk L ≤ V := by rw [hVd]; omega
  have hBkV : z.Bk L ≤ V := by rw [hVd]; omega
  omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
