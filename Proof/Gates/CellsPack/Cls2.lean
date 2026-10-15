import Proof.Gates.CellsPack.Cls

set_option autoImplicit false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.CellsPack

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Counter
open NearCubicGates.Close.Cells.SystemsPhase

noncomputable def d2Of (S : SolveMachine) (B1 B2 : ℕ) : ℕ := dOf S B1 B2 + B1 + B2 + 8
noncomputable def AqOf (S : SolveMachine) (B1 B2 : ℕ) : ℕ := 2 ^ 10 + wSof S B1 B2 + 3
noncomputable def AnOf (S : SolveMachine) (K e B1 B2 : ℕ) : ℕ := K * AqOf S B1 B2 ^ e + 200 * AgOf S B1 B2 + 202

theorem q_le (S : SolveMachine) (B1 B2 n : ℕ) :
    n + bigOf B1 B2 n + (zOf S B1 B2).W (natBitLength n) + (zOf S B1 B2).Lk (natBitLength n) +
      (zOf S B1 B2).Bk (natBitLength n) + 2 ≤ AqOf S B1 B2 * (n + 1) ^ d2Of S B1 B2 := by
  have h := sizes_le S B1 B2 n
  have hY : 1 ≤ n + 1 := by omega
  have m1 : (n + 1) ^ (B1 + B2 + 8) ≤ (n + 1) ^ d2Of S B1 B2 := Nat.pow_le_pow_right hY (by unfold d2Of; omega)
  have m2 : (n + 1) ^ dOf S B1 B2 ≤ (n + 1) ^ d2Of S B1 B2 := Nat.pow_le_pow_right hY (by unfold d2Of; omega)
  have m3 : n + 1 ≤ (n + 1) ^ d2Of S B1 B2 := by
    simpa using Nat.pow_le_pow_right hY (show 1 ≤ d2Of S B1 B2 by unfold d2Of; omega)
  have hB : bigOf B1 B2 n = 2 ^ 10 * (n + 1) ^ (B1 + B2 + 8) := rfl
  have k1 := Nat.mul_le_mul_left (2 ^ 10) m1
  have k2 := Nat.mul_le_mul_left (wSof S B1 B2) m2
  have e : AqOf S B1 B2 * (n + 1) ^ d2Of S B1 B2 = 2 ^ 10 * (n + 1) ^ d2Of S B1 B2 +
      wSof S B1 B2 * (n + 1) ^ d2Of S B1 B2 + 3 * (n + 1) ^ d2Of S B1 B2 := by unfold AqOf; ring
  rw [e, hB]
  generalize (n + 1) ^ d2Of S B1 B2 = V2 at *
  generalize (n + 1) ^ dOf S B1 B2 = V1 at *
  generalize (n + 1) ^ (B1 + B2 + 8) = V0 at *
  omega

theorem N_le (S : SolveMachine) (K e : ℕ) {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) :
    NOf S K e (bigOf B1 B2) (zOf S B1 B2) r + 1 ≤ AnOf S K e B1 B2 *
      (2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n)) * (r.c.n + 1) ^ (d2Of S B1 B2 * e + dOf S B1 B2) := by
  have hL := leadOnes_pkIn r
  have hq := q_le S B1 B2 r.c.n
  have hG := gof_le S B1 B2 r.c.n
  have hY : 1 ≤ r.c.n + 1 := by omega
  have hX1 : 1 ≤ 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hWG : (zOf S B1 B2).W (natBitLength r.c.n) ≤ AgOf S B1 B2 * (r.c.n + 1) ^ dOf S B1 B2 := by
    unfold Gof at hG; omega
  unfold NOf loopCost outCost
  simp only [ctxOf, hL]
  have h1 : (r.c.n + bigOf B1 B2 r.c.n + (zOf S B1 B2).W (natBitLength r.c.n) + (zOf S B1 B2).Lk (natBitLength r.c.n) +
      (zOf S B1 B2).Bk (natBitLength r.c.n) + 2) ^ e ≤ AqOf S B1 B2 ^ e * (r.c.n + 1) ^ (d2Of S B1 B2 * e) := by
    calc _ ≤ (AqOf S B1 B2 * (r.c.n + 1) ^ d2Of S B1 B2) ^ e := Nat.pow_le_pow_left hq e
      _ = _ := by rw [mul_pow, ← pow_mul]
  have m1 : (r.c.n + 1) ^ (d2Of S B1 B2 * e) ≤ (r.c.n + 1) ^ (d2Of S B1 B2 * e + dOf S B1 B2) :=
    Nat.pow_le_pow_right hY (by omega)
  have m2 : (r.c.n + 1) ^ dOf S B1 B2 ≤ (r.c.n + 1) ^ (d2Of S B1 B2 * e + dOf S B1 B2) :=
    Nat.pow_le_pow_right hY (by omega)
  have hV1 : 1 ≤ (r.c.n + 1) ^ (d2Of S B1 B2 * e + dOf S B1 B2) := Nat.one_le_pow _ _ hY
  generalize hXd : 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n) = X at hX1
  have hlc : K * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n) *
      (r.c.n + bigOf B1 B2 r.c.n + (zOf S B1 B2).W (natBitLength r.c.n) + (zOf S B1 B2).Lk (natBitLength r.c.n) +
        (zOf S B1 B2).Bk (natBitLength r.c.n) + 2) ^ e ≤
      K * AqOf S B1 B2 ^ e * X * (r.c.n + 1) ^ (d2Of S B1 B2 * e + dOf S B1 B2) := by
    calc _ = K * X * (r.c.n + bigOf B1 B2 r.c.n + (zOf S B1 B2).W (natBitLength r.c.n) +
          (zOf S B1 B2).Lk (natBitLength r.c.n) + (zOf S B1 B2).Bk (natBitLength r.c.n) + 2) ^ e := by
          rw [← hXd]; ring
      _ ≤ K * X * (AqOf S B1 B2 ^ e * (r.c.n + 1) ^ (d2Of S B1 B2 * e + dOf S B1 B2)) :=
          Nat.mul_le_mul_left _ (h1.trans (Nat.mul_le_mul_left _ m1))
      _ = _ := by ring
  have hout : 200 * (zOf S B1 B2).W (natBitLength r.c.n) + 200 + 1 + 1 ≤
      (200 * AgOf S B1 B2 + 202) * X * (r.c.n + 1) ^ (d2Of S B1 B2 * e + dOf S B1 B2) := by
    have a1 : AgOf S B1 B2 * (r.c.n + 1) ^ dOf S B1 B2 ≤
        AgOf S B1 B2 * (X * (r.c.n + 1) ^ (d2Of S B1 B2 * e + dOf S B1 B2)) :=
      Nat.mul_le_mul_left _ (m2.trans (Nat.le_mul_of_pos_left _ hX1))
    have a2 : 1 ≤ X * (r.c.n + 1) ^ (d2Of S B1 B2 * e + dOf S B1 B2) := Nat.mul_le_mul hX1 hV1
    have e : (200 * AgOf S B1 B2 + 202) * X * (r.c.n + 1) ^ (d2Of S B1 B2 * e + dOf S B1 B2) =
        200 * (AgOf S B1 B2 * (X * (r.c.n + 1) ^ (d2Of S B1 B2 * e + dOf S B1 B2))) +
        202 * (X * (r.c.n + 1) ^ (d2Of S B1 B2 * e + dOf S B1 B2)) := by ring
    omega
  have e2 : AnOf S K e B1 B2 * X * (r.c.n + 1) ^ (d2Of S B1 B2 * e + dOf S B1 B2) =
      K * AqOf S B1 B2 ^ e * X * (r.c.n + 1) ^ (d2Of S B1 B2 * e + dOf S B1 B2) +
      (200 * AgOf S B1 B2 + 202) * X * (r.c.n + 1) ^ (d2Of S B1 B2 * e + dOf S B1 B2) := by unfold AnOf; ring
  rw [e2]
  omega

theorem in_le {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) :
    (pkIn r).length ≤ 2 ^ 24 * (2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n)) * (r.c.n + 1) ^ (B1 + B2 + 14) := by
  have hs := spec_r r
  have hY : 1 ≤ r.c.n + 1 := by omega
  have hX1 : 1 ≤ 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold pkIn
  rw [List.length_append, cellWord_len]
  have h1 := CounterMachine.PrefixProg.cellInput_len_explicit r
  have hRq : (reqIds r.c r.p).length ≤ (r.c.n + 1) ^ (2 * Jmax r.c.n + 4) := by
    rw [reqIds_length]
    have hP := P_le_n r.c r.p hs
    have hJ := J_le_Jmax r.c r.p hs
    calc requestCount r.c r.p ≤ r.p.P ^ (2 * r.p.J + 4) := requestCount_le r.c r.p hs
      _ ≤ (r.c.n + 1) ^ (2 * r.p.J + 4) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (r.c.n + 1) ^ (2 * Jmax r.c.n + 4) := Nat.pow_le_pow_right hY (by omega)
  have hRW : 2 * recWidth r.c r.p r.wt + 1 ≤ 2 ^ 23 * (r.c.n + 1) ^ (B1 + B2 + 10) := by
    have h := wdNeed_le r
    unfold wdNeed at h
    have := Nat.one_le_pow (B1 + B2 + 10) (r.c.n + 1) hY
    have : 2 ^ 23 * (r.c.n + 1) ^ (B1 + B2 + 10) = 2 * (2 ^ 22 * (r.c.n + 1) ^ (B1 + B2 + 10)) := by ring
    omega
  have h2 : 2 ^ (r.c.n - r.p.k) * (reqIds r.c r.p).length * (2 * recWidth r.c r.p r.wt + 1) ≤
      2 ^ 23 * (2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n)) * (r.c.n + 1) ^ (B1 + B2 + 14) := by
    calc _ ≤ 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n + 4) * (2 ^ 23 * (r.c.n + 1) ^ (B1 + B2 + 10)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hRq) hRW
      _ = _ := by rw [show B1 + B2 + 14 = 4 + (B1 + B2 + 10) by ring, pow_add, pow_add]; ring
  have m : (r.c.n + 1) ^ (B1 + B2 + 13) ≤ (r.c.n + 1) ^ (B1 + B2 + 14) := Nat.pow_le_pow_right hY (by omega)
  have hV : 1 ≤ (r.c.n + 1) ^ (B1 + B2 + 14) := Nat.one_le_pow _ _ hY
  generalize 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n) = X at *
  generalize (r.c.n + 1) ^ (B1 + B2 + 14) = V at *
  generalize (r.c.n + 1) ^ (B1 + B2 + 13) = U at *
  have a1 : U ≤ X * V := m.trans (Nat.le_mul_of_pos_left _ hX1)
  have a2 : 1 ≤ X * V := Nat.mul_le_mul hX1 hV
  have e1 : 2 ^ 24 * X * V = 2 ^ 24 * (X * V) := by ring
  have e2 : 2 ^ 23 * X * V = 2 ^ 23 * (X * V) := by ring
  rw [e1]; rw [e2] at h2
  omega

theorem budget_class (S : SolveMachine) (K e B1 B2 : ℕ) : ∃ Cc E : ℕ, ∀ (cT : ℕ) (r : CellReq B1 B2 cT),
    langBudget (Callee.ofSolve S) (zOf S B1 B2) VV MM (pkIn r) (NOf S K e (bigOf B1 B2) (zOf S B1 B2) r) ≤
      Cc * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n + E) := by
  refine ⟨10 ^ 6 * AnOf S K e B1 B2 * AgOf S B1 B2 ^ 2 + 10 * 2 ^ 24,
    d2Of S B1 B2 * e + 3 * dOf S B1 B2 + B1 + B2 + 14, fun cT r => ?_⟩
  have hlang := lang_le2 (Callee.ofSolve S) (zOf S B1 B2) (pkIn r) (NOf S K e (bigOf B1 B2) (zOf S B1 B2) r)
  rw [leadOnes_pkIn] at hlang
  have hN := N_le S K e r
  have hG := gof_le S B1 B2 r.c.n
  have hin := in_le r
  have hY : 1 ≤ r.c.n + 1 := by omega
  set E := d2Of S B1 B2 * e + 3 * dOf S B1 B2 + B1 + B2 + 14 with hE
  have m1 : (r.c.n + 1) ^ (d2Of S B1 B2 * e + 3 * dOf S B1 B2) ≤ (r.c.n + 1) ^ E := Nat.pow_le_pow_right hY (by omega)
  have m2 : (r.c.n + 1) ^ (B1 + B2 + 14) ≤ (r.c.n + 1) ^ E := Nat.pow_le_pow_right hY (by omega)
  have hf1 : (NOf S K e (bigOf B1 B2) (zOf S B1 B2) r + 1) * Gof (Callee.ofSolve S) (zOf S B1 B2) (natBitLength r.c.n) ^ 2
      ≤ AnOf S K e B1 B2 * AgOf S B1 B2 ^ 2 * (2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n)) * (r.c.n + 1) ^ E := by
    calc _ ≤ (AnOf S K e B1 B2 * (2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n)) *
          (r.c.n + 1) ^ (d2Of S B1 B2 * e + dOf S B1 B2)) * (AgOf S B1 B2 * (r.c.n + 1) ^ dOf S B1 B2) ^ 2 :=
          Nat.mul_le_mul hN (Nat.pow_le_pow_left hG 2)
      _ = AnOf S K e B1 B2 * AgOf S B1 B2 ^ 2 * (2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n)) *
          (r.c.n + 1) ^ (d2Of S B1 B2 * e + 3 * dOf S B1 B2) := by
          rw [mul_pow, ← pow_mul, show d2Of S B1 B2 * e + 3 * dOf S B1 B2 =
            (d2Of S B1 B2 * e + dOf S B1 B2) + dOf S B1 B2 * 2 by ring, pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ m1
  have hf2 : (pkIn r).length ≤ 2 ^ 24 * (2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n)) * (r.c.n + 1) ^ E :=
    hin.trans (Nat.mul_le_mul_left _ m2)
  have hgoal : (10 ^ 6 * AnOf S K e B1 B2 * AgOf S B1 B2 ^ 2 + 10 * 2 ^ 24) * 2 ^ (r.c.n - r.p.k) *
      (r.c.n + 1) ^ (2 * Jmax r.c.n + E) =
      10 ^ 6 * (AnOf S K e B1 B2 * AgOf S B1 B2 ^ 2 * (2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n)) *
        (r.c.n + 1) ^ E) + 10 * (2 ^ 24 * (2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n)) * (r.c.n + 1) ^ E) := by
    rw [pow_add]; ring
  rw [hgoal]
  have := Nat.mul_le_mul_left (10 ^ 6) hf1
  have := Nat.mul_le_mul_left 10 hf2
  generalize (NOf S K e (bigOf B1 B2) (zOf S B1 B2) r + 1) * Gof (Callee.ofSolve S) (zOf S B1 B2) (natBitLength r.c.n) ^ 2
    = A at *
  omega

end NearCubicGates.Close.CellsPack
