import Proof.Gates.CounterMachine.TabCallSetF
import Proof.Gates.Interfaces.WordFn

/-! # RK, part 7: stage A — measure, descriptor, the prefix machine's input

From the cold start on `frame (tabCallInput x)`: `LEN := 2|tabCallInput x|` (a bound on every stream RK fills from its
input), the descriptor's header in `Td 0 … Td 2`, its residue vector on `Y 6`, and `frame cellInput` on `PIN`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.CounterMachine.TabCallProg

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Counter

variable (tP tK : ℕ) {B1 B2 cT : ℕ}

theorem marks_app (u v : List Bool) : marks (u ++ v) = marks u ++ marks v := by simp [marks]

theorem tabCallInput_frame (x : TabCallReq B1 B2 cT) :
    RepairOrdinary.frame (tabCallInput x) = encN (descN x.id ++ cellN x.r.c x.r.p x.r.wt) ++ [false] := by
  rw [Codec.frame_eq_marks, encN_eq_marks, tabCallInput, cellInput, List.flatMap_append, cellN_word]

theorem tabCallInput_frame' (x : TabCallReq B1 B2 cT) :
    RepairOrdinary.frame (tabCallInput x) = encN (descN x.id) ++ RepairOrdinary.frame (cellInput x.r) := by
  rw [Codec.frame_eq_marks, Codec.frame_eq_marks, encN_eq_marks, tabCallInput, marks_app, List.append_assoc]

def stA1 : WM (NS tP tK) NR :=
  .seq (measP (sIN tP tK) (E 19) (E 20) (E 22)) (.seq (rdDesc (sIN tP tK) (Y tP tK 6) Q Td)
    (cpIn (sIN tP tK) (sPIN tP tK) (E 10) (E 11) (E 12)))

structure A1 (x : TabCallReq B1 B2 cT) (τ : WState (NS tP tK) NR) : Prop where
  nat : NatAt (sIN tP tK) (descN x.id ++ cellN x.r.c x.r.p x.r.wt) [false] τ (descN x.id).length
  qz : QZero Q τ
  len : τ.val (E 19) = 2 * (tabCallInput x).length
  t0 : τ.val (Td 0) = dTag x.id
  t1 : τ.val (Td 1) = dF1 x.id
  t2 : τ.val (Td 2) = dF2 x.id
  q15 : τ.val (Q 15) = (encN (dRho x.id)).length
  regs : ∀ r, r ≠ E 19 → (∀ i, r ≠ Td i ∨ i = 3) → r ≠ Q 15 → τ.val r = 0
  kv : τ.st (Y tP tK 6) = encN (dRho x.id)
  kvh : τ.sh (Y tP tK 6) = (τ.st (Y tP tK 6)).length
  pin : τ.st (sPIN tP tK) = RepairOrdinary.frame (cellInput x.r)
  pinh : τ.sh (sPIN tP tK) = 0
  other : ∀ i, i ≠ sIN tP tK → i ≠ Y tP tK 6 → i ≠ sPIN tP tK → τ.st i = [] ∧ τ.sh i = 0

theorem stA1_spec (x : TabCallReq B1 B2 cT) (Λ cap : ℕ)
    (hbits : ∀ v ∈ descN x.id, natBitLength v + 2 ≤ Λ ∧ 2 ^ (natBitLength v + 1) ≤ Λ) (hlen : (descN x.id).length ≤ Λ)
    (hcap : Λ + 4 * (encN (descN x.id ++ cellN x.r.c x.r.p x.r.wt)).length + 4 * (tabCallInput x).length + 10 ≤ cap) :
    ∃ τ, WExec cap (stA1 tP tK) (startState (NS tP tK) NR (tabCallInput x)) τ
        (60 * (tabCallInput x).length + 10 + 1 + (400 * (Λ + 1) ^ 3 + 1 + (100 * (cellInput x.r).length + 30))) ∧
      A1 tP tK x τ := by
  set w := tabCallInput x with hw
  set σ0 := startState (NS tP tK) NR w with hσ0
  have st0 : ∀ i, σ0.st i = if i.val = 0 then RepairOrdinary.frame w else [] := fun i => rfl
  have sh0 : ∀ i, σ0.sh i = 0 := fun i => rfl
  have v0 : ∀ r, σ0.val r = 0 := fun r => rfl
  have e1 := measP_spec cap (sIN tP tK) (E 19) (E 20) (E 22) (by lne) (by lne) (by lne) w σ0 (by rw [st0]; rfl)
    (sh0 _) (v0 _) (v0 _) (v0 _) (by omega)
  set σ1 := σ0.setv (E 19) (2 * w.length) with hσ1
  have hTQ : ∀ i j, Td i ≠ Q j := fun i j => by lne
  obtain ⟨τ2, e2, n2, z2, t02, t12, t22, t32, kv2, kvh2, q2, os2, or2⟩ :=
    rdDesc_spec cap (sIN tP tK) (Y tP tK 6) Q Td hTQ (by lne) x.id (cellN x.r.c x.r.p x.r.wt) [false] σ1
      ⟨by simp [hσ1, st0, hw, tabCallInput_frame], by simp [hσ1, sh0, encN]⟩
      (fun i _ => by simp [hσ1, v0, Function.update_of_ne (show Q i ≠ E 19 by lne)])
      (fun i => by simp [hσ1, v0, Function.update_of_ne (show Td i ≠ E 19 by lne)])
      (by simp [hσ1, sh0, st0]) Λ hbits hlen
      (by simp [hσ1, v0, Function.update_of_ne (show Q 15 ≠ E 19 by lne)]; omega)
  have hτ2IN : τ2.st (sIN tP tK) = encN (descN x.id) ++ RepairOrdinary.frame (cellInput x.r) ++ [] := by
    rw [n2.1, ← tabCallInput_frame, tabCallInput_frame']; simp
  have hτ2INh : τ2.sh (sIN tP tK) = (encN (descN x.id)).length := by rw [n2.2]; simp
  have pin2 := os2 (sPIN tP tK) (by lne) (by lne)
  have rz : ∀ r, r ≠ E 19 → (∀ i, r ≠ Td i) → r ≠ Q 15 → τ2.val r = 0 := fun r h1 h2 h3 => by
    rw [or2 r h2 h3]; simp [hσ1, v0, Function.update_of_ne h1]
  have e3 := cpIn_spec cap (sIN tP tK) (sPIN tP tK) (by lne) (E 10) (E 11) (E 12) (by lne) (by lne) (by lne)
    (encN (descN x.id)) (cellInput x.r) [] τ2 hτ2IN hτ2INh (by rw [pin2.1]; simp [hσ1, st0])
    (by rw [pin2.2]; simp [hσ1, sh0]) (rz _ (by lne) (fun i => by lne) (by lne))
    (rz _ (by lne) (fun i => by lne) (by lne)) (rz _ (by lne) (fun i => by lne) (by lne))
    (by have : w.length = ((descN x.id).flatMap natWord).length + (cellInput x.r).length := by
          simp [hw, tabCallInput]
        omega)
  refine ⟨_, WExec.seq e1 (WExec.seq e2 e3), ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_of_ne (show sIN tP tK ≠ sPIN tP tK by lne), n2.1]
  · simp [Function.update_of_ne (show sIN tP tK ≠ sPIN tP tK by lne), n2.2]
  · exact z2
  · rw [WState.sets_val, or2 _ (fun i => by lne) (by lne)]; simp [hσ1, hw]
  · simp [t02]
  · simp [t12]
  · simp [t22]
  · simp [q2, hσ1, v0, Function.update_of_ne (show Q 15 ≠ E 19 by lne)]
  · intro r h1 h2 h3
    rw [WState.sets_val]
    by_cases h4 : r = Td 3
    · subst h4; exact t32
    · exact rz r h1 (fun i => by
        rcases h2 i with h | h
        · exact h
        · subst h; exact h4) h3
  · simp [Function.update_of_ne (show Y tP tK 6 ≠ sPIN tP tK by lne), kv2, hσ1, st0]
  · simp [Function.update_of_ne (show Y tP tK 6 ≠ sPIN tP tK by lne), kvh2]
  · simp
  · simp [pin2.2, hσ1, sh0]
  · intro i h1 h2 h3
    have := os2 i h1 h2
    simp [Function.update_of_ne h3, this.1, this.2, hσ1, st0, sh0]
    intro h; exact absurd (Fin.ext (by simp [h])) h1

def stA2 : WM (NS tP tK) NR :=
  .seq (unCP Q (uS tP tK) uR) (.seq (pidxP (Td 0) (Td 1) (E 1) (E 21) (E 20) (E 22)) (unFW Q (uS tP tK) uR))

structure A2 (x : TabCallReq B1 B2 cT) (τ : WState (NS tP tK) NR) : Prop where
  nat : NatAt (sIN tP tK) (descN x.id ++ cellN x.r.c x.r.p x.r.wt) [false] τ
    (descN x.id ++ cellN x.r.c x.r.p x.r.wt).length
  qz : QZero Q τ
  y1 : τ.st (Y tP tK 1) = encN (W0 x.r.c x.r.wt x.r.p.J)
  y2 : τ.st (Y tP tK 2) = encN (x.r.c.first.coeffs.flatMap intN)
  y3 : τ.st (Y tP tK 3) = encN (W1 x.r.c x.r.wt x.r.p.J)
  y4 : τ.st (Y tP tK 4) = encN (x.r.c.second.coeffs.flatMap intN)
  y5 : τ.st (Y tP tK 5) = encN (x.r.p.factors ++ [x.r.p.M1, x.r.p.A])
  y6 : τ.st (Y tP tK 6) = encN (dRho x.id)
  yh : ∀ j : Fin 8, j ≠ 0 → j ≠ 7 → τ.sh (Y tP tK j) = (τ.st (Y tP tK j)).length
  pr : τ.st (sPR tP tK) = encN (x.r.p.primes.sort (· ≤ ·))
  prh : τ.sh (sPR tP tK) = (τ.st (sPR tP tK)).length
  gj : τ.st (sGJ tP tK) = encN (x.r.c.first.gates.flatMap gateN) ++ encN (x.r.c.second.gates.flatMap gateN)
  gjh : τ.sh (sGJ tP tK) = (τ.st (sGJ tP tK)).length
  tmph : τ.sh (sTMP tP tK) = (encN [x.r.p.M1]).length
  pin : τ.st (sPIN tP tK) = RepairOrdinary.frame (cellInput x.r)
  pinh : τ.sh (sPIN tP tK) = 0
  other : ∀ i, i ∉ [sIN tP tK, sGJ tP tK, Y tP tK 1, Y tP tK 2, Y tP tK 3, Y tP tK 4, sPR tP tK, sTMP tP tK,
    Y tP tK 5, Y tP tK 6, sPIN tP tK] → τ.st i = [] ∧ τ.sh i = 0
  len : τ.val (E 19) = 2 * (tabCallInput x).length
  t0 : τ.val (Td 0) = dTag x.id
  t1 : τ.val (Td 1) = dF1 x.id
  t2 : τ.val (Td 2) = dF2 x.id
  flag : τ.val (X 0) = if x.r.c.kind = .pair then 1 else 0
  vJ : τ.val (X 1) = x.r.p.J
  vE : τ.val (X 8) = x.r.p.e
  vG0 : τ.val (X 14) = x.r.c.first.gates.length
  vG1 : τ.val (X 18) = x.r.c.second.gates.length
  vn : τ.val (E 0) = x.r.c.n
  vk : τ.val (E 3) = x.r.p.k
  pix : τ.val (E 21) = pidx (dTag x.id) (dF1 x.id) (kindTag x.r.c.kind)
  regs : ∀ r, r ∉ [X 0, X 1, X 8, X 14, X 18, E 0, E 1, E 2, E 3, E 4, E 19, E 21, Td 0, Td 1, Td 2, Q 15] →
    τ.val r = 0

theorem uRv_far (j : Fin 11) : 64 ≤ uRv j ∨ uRv j < 48 := by revert j; decide

theorem uRv_lt70 : ∀ j : Fin 11, uRv j < 70 := by decide

theorem uSv_lt7 : ∀ i : Fin 9, i.val < 7 → uSv i ≠ 2 ∧ uSv i ≠ 4 := by decide

theorem uSv_fresh : ∀ j : Fin 9, j ≠ 0 → uSv j ≠ 0 ∧ uSv j ≠ 7 ∧ uSv j < 12 := by decide

theorem encN_single_le {x : ℕ} {L : List ℕ} (h : x ∈ L) : (encN [x]).length ≤ (encN L).length := by
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem h
  rw [show l1 ++ x :: l2 = l1 ++ [x] ++ l2 by simp]
  exact encN_le_mid l1 [x] l2

theorem uR_ne_Q (i : Fin 16) (j : Fin 11) : Q i ≠ uR j := by
  intro e; have h := congrArg Fin.val e; simp at h; have := uRv_far j; have := i.isLt; omega

theorem uR_lt9 : ∀ j : Fin 11, j.val < 9 → uR j ∈ [E 0, E 1, E 2, X 14, X 18, E 3, E 4, X 8, X 1] := by
  intro j hj; fin_cases j <;> simp at hj <;> simp [uR_0, uR_1, uR_2, uR_3, uR_4, uR_5, uR_6, uR_7, uR_8]

theorem uS_lt7 : ∀ j : Fin 9, j.val < 7 →
    uS tP tK j ∈ [sIN tP tK, sGJ tP tK, Y tP tK 2, Y tP tK 4, sPR tP tK, sTMP tP tK, Y tP tK 5] := by
  intro j hj; fin_cases j <;> simp at hj <;> simp [uS_0, uS_1, uS_2, uS_3, uS_4, uS_5, uS_6]

/-- The call/parameter unpack's facts, named. -/
structure UCP (x : TabCallReq B1 B2 cT) (σ τ : WState (NS tP tK) NR) : Prop where
  nat : NatAt (sIN tP tK) (descN x.id ++ callN x.r.c ++ paramsN x.r.p ++ witN x.r.c x.r.p x.r.wt ++ []) [false] τ
    (descN x.id ++ callN x.r.c ++ paramsN x.r.p).length
  qz : QZero Q τ
  y2 : τ.st (Y tP tK 2) = σ.st (Y tP tK 2) ++ encN (x.r.c.first.coeffs.flatMap intN)
  y2h : τ.sh (Y tP tK 2) = (τ.st (Y tP tK 2)).length
  y4 : τ.st (Y tP tK 4) = σ.st (Y tP tK 4) ++ encN (x.r.c.second.coeffs.flatMap intN)
  y4h : τ.sh (Y tP tK 4) = (τ.st (Y tP tK 4)).length
  y5 : τ.st (Y tP tK 5) = σ.st (Y tP tK 5) ++ encN (x.r.p.factors ++ [x.r.p.M1, x.r.p.A])
  y5h : τ.sh (Y tP tK 5) = (τ.st (Y tP tK 5)).length
  pr : τ.st (sPR tP tK) = σ.st (sPR tP tK) ++ encN (x.r.p.primes.sort (· ≤ ·))
  prh : τ.sh (sPR tP tK) = (τ.st (sPR tP tK)).length
  gj : τ.st (sGJ tP tK) = σ.st (sGJ tP tK) ++ encN (x.r.c.first.gates.flatMap gateN) ++
    encN (x.r.c.second.gates.flatMap gateN)
  gjh : τ.sh (sGJ tP tK) = (τ.st (sGJ tP tK)).length
  tmph : τ.sh (sTMP tP tK) = (encN [x.r.p.M1]).length
  rn : τ.val (E 0) = x.r.c.n
  rt : τ.val (E 1) = kindTag x.r.c.kind
  g0 : τ.val (X 14) = x.r.c.first.gates.length
  g1 : τ.val (X 18) = x.r.c.second.gates.length
  rk : τ.val (E 3) = x.r.p.k
  rE : τ.val (X 8) = x.r.p.e
  rJ : τ.val (X 1) = x.r.p.J
  q15 : τ.val (Q 15) ≤ σ.val (Q 15) + 3 * (encN (descN x.id ++ cellN x.r.c x.r.p x.r.wt ++ [])).length
  os : ∀ X, X ∉ [sIN tP tK, sGJ tP tK, Y tP tK 2, Y tP tK 4, sPR tP tK, sTMP tP tK, Y tP tK 5] →
    τ.st X = σ.st X ∧ τ.sh X = σ.sh X
  or : ∀ r, r ∉ [E 0, E 1, E 2, X 14, X 18, E 3, E 4, X 8, X 1] → r ≠ Q 15 → τ.val r = σ.val r

theorem ucp_spec (x : TabCallReq B1 B2 cT) (Λ cap : ℕ) (σ : WState (NS tP tK) NR) (hA : A1 tP tK x σ)
    (hbits : ∀ y ∈ descN x.id ++ cellN x.r.c x.r.p x.r.wt, natBitLength y + 2 ≤ Λ)
    (hlen : (descN x.id ++ cellN x.r.c x.r.p x.r.wt).length ≤ Λ)
    (hRd1 : ∀ v ∈ [x.r.c.n, kindTag x.r.c.kind, x.r.c.first.gates.length, x.r.c.first.coeffs.length,
      x.r.c.first.table.length, x.r.c.second.gates.length, x.r.c.second.coeffs.length, x.r.c.second.table.length,
      x.r.c.parity.length], 2 ^ (natBitLength v + 1) ≤ Λ) (hn : 2 * x.r.c.n + 3 ≤ Λ)
    (hRd2 : ∀ v ∈ [x.r.p.k, x.r.p.P, x.r.p.e, x.r.p.J, (x.r.p.primes.sort (· ≤ ·)).length, x.r.p.factors.length],
      2 ^ (natBitLength v + 1) ≤ Λ)
    (hcap : 40 * (Λ + 1) ^ 2 + 20 * (encN (descN x.id ++ cellN x.r.c x.r.p x.r.wt)).length +
      (encN (dRho x.id)).length ≤ cap) :
    ∃ τ, WExec cap (unCP Q (uS tP tK) uR) σ τ (30000 * (Λ + 1) ^ 2 + 23 * (σ.val (Q 15) +
      (encN (descN x.id ++ cellN x.r.c x.r.p x.r.wt ++ [])).length)) ∧ UCP tP tK x σ τ := by
  have hL : descN x.id ++ cellN x.r.c x.r.p x.r.wt ++ [] = descN x.id ++ cellN x.r.c x.r.p x.r.wt := by simp
  have z0 : ∀ j, σ.val (uR j) = 0 := fun j => hA.regs _
    (by intro e; have := congrArg Fin.val e; simp at this; revert j; decide)
    (fun i => Or.inl (by intro e; have := congrArg Fin.val e; simp at this; have := uRv_lt70 j; omega))
    (fun e => uR_ne_Q 15 j e.symm)
  have hend : ∀ j : Fin 9, j ≠ 0 → j ≠ 5 → σ.sh (uS tP tK j) = (σ.st (uS tP tK j)).length := fun j h0 _ => by
    have hf := uSv_fresh j h0
    have := hA.other (uS tP tK j) (by intro e; have := congrArg Fin.val e; simp at this; omega)
      (by intro e; have := congrArg Fin.val e; simp at this; omega)
      (by intro e; have := congrArg Fin.val e; simp at this; omega)
    rw [this.1, this.2]; rfl
  have hTMP := hA.other (uS tP tK 5) (by rw [uS_5]; lne) (by rw [uS_5]; lne) (by rw [uS_5]; lne)
  obtain ⟨τ2, e2, n2, z2, s22, h22, s32, h32, s62, h62, s42, h42, sG2, hG2, hT2, rn2, rt2, rg02, rg12, rk2, rP2,
      rE2, rJ2, q2l, q2u, os2, or2⟩ :=
    unCP_spec cap Q (uS tP tK) uR uR_ne_Q x.r.c x.r.p x.r.wt (descN x.id) [] [false] σ (natAt_congr _ _ hL.symm hA.nat)
      hA.qz z0 hend hTMP Λ (by rw [hL]; exact hbits) (by rw [hL]; exact hlen) hRd1 hn hRd2
      (by rw [hL, hA.q15]; omega)
  rw [uS_2] at s22 h22; rw [uS_3] at s32 h32; rw [uS_6] at s62 h62; rw [uS_4] at s42 h42; rw [uS_1] at sG2 hG2
  rw [uS_5] at hT2; rw [uR_0] at rn2; rw [uR_1] at rt2; rw [uR_3] at rg02; rw [uR_4] at rg12; rw [uR_5] at rk2
  rw [uR_7] at rE2; rw [uR_8] at rJ2
  exact ⟨τ2, e2, ⟨n2, z2, s22, h22, s32, h32, s62, h62, s42, h42, sG2, hG2, hT2, rn2, rt2, rg02, rg12, rk2, rE2, rJ2,
    q2u, fun X hX => os2 X (fun j hj e => hX (e ▸ uS_lt7 tP tK j hj)),
    fun r hr h15 => or2 r (fun j hj e => hr (e ▸ uR_lt9 j hj)) h15⟩⟩

/-- The state after the call/parameter unpack and the prefix index. -/
structure A2a (x : TabCallReq B1 B2 cT) (τ : WState (NS tP tK) NR) : Prop where
  nat : NatAt (sIN tP tK) (descN x.id ++ callN x.r.c ++ paramsN x.r.p ++ witN x.r.c x.r.p x.r.wt ++ []) [false] τ
    (descN x.id ++ callN x.r.c ++ paramsN x.r.p).length
  qz : QZero Q τ
  y13 : ∀ j : Fin 8, (j = 1 ∨ j = 3) → τ.st (Y tP tK j) = [] ∧ τ.sh (Y tP tK j) = 0
  y2 : τ.st (Y tP tK 2) = encN (x.r.c.first.coeffs.flatMap intN)
  y2h : τ.sh (Y tP tK 2) = (τ.st (Y tP tK 2)).length
  y4 : τ.st (Y tP tK 4) = encN (x.r.c.second.coeffs.flatMap intN)
  y4h : τ.sh (Y tP tK 4) = (τ.st (Y tP tK 4)).length
  y5 : τ.st (Y tP tK 5) = encN (x.r.p.factors ++ [x.r.p.M1, x.r.p.A])
  y5h : τ.sh (Y tP tK 5) = (τ.st (Y tP tK 5)).length
  y6 : τ.st (Y tP tK 6) = encN (dRho x.id)
  y6h : τ.sh (Y tP tK 6) = (τ.st (Y tP tK 6)).length
  pr : τ.st (sPR tP tK) = encN (x.r.p.primes.sort (· ≤ ·))
  prh : τ.sh (sPR tP tK) = (τ.st (sPR tP tK)).length
  gj : τ.st (sGJ tP tK) = encN (x.r.c.first.gates.flatMap gateN) ++ encN (x.r.c.second.gates.flatMap gateN)
  gjh : τ.sh (sGJ tP tK) = (τ.st (sGJ tP tK)).length
  tmph : τ.sh (sTMP tP tK) = (encN [x.r.p.M1]).length
  pin : τ.st (sPIN tP tK) = RepairOrdinary.frame (cellInput x.r)
  pinh : τ.sh (sPIN tP tK) = 0
  other : ∀ i, i ∉ [sIN tP tK, sGJ tP tK, Y tP tK 2, Y tP tK 4, sPR tP tK, sTMP tP tK, Y tP tK 5, Y tP tK 6,
    sPIN tP tK] → τ.st i = [] ∧ τ.sh i = 0
  len : τ.val (E 19) = 2 * (tabCallInput x).length
  t0 : τ.val (Td 0) = dTag x.id
  t1 : τ.val (Td 1) = dF1 x.id
  t2 : τ.val (Td 2) = dF2 x.id
  tg : τ.val (E 1) = kindTag x.r.c.kind
  vJ : τ.val (X 1) = x.r.p.J
  vE : τ.val (X 8) = x.r.p.e
  vG0 : τ.val (X 14) = x.r.c.first.gates.length
  vG1 : τ.val (X 18) = x.r.c.second.gates.length
  vn : τ.val (E 0) = x.r.c.n
  vk : τ.val (E 3) = x.r.p.k
  pix : τ.val (E 21) = pidx (dTag x.id) (dF1 x.id) (kindTag x.r.c.kind)
  q15 : τ.val (Q 15) ≤ (encN (dRho x.id)).length + 3 * (encN (descN x.id ++ cellN x.r.c x.r.p x.r.wt)).length
  regs : ∀ r, r ∉ [X 1, X 8, X 14, X 18, E 0, E 1, E 2, E 3, E 4, E 19, E 21, Td 0, Td 1, Td 2, Q 15] → τ.val r = 0

theorem a2a_spec (x : TabCallReq B1 B2 cT) (cap : ℕ) (σ τ2 : WState (NS tP tK) NR) (hA : A1 tP tK x σ)
    (hU : UCP tP tK x σ τ2) (hsm : dF1 x.id + kindTag x.r.c.kind + 3 ≤ cap) :
    ∃ τ, WExec cap (pidxP (Td 0) (Td 1) (E 1) (E 21) (E 20) (E 22)) τ2 τ
      (40 * (dF1 x.id + kindTag x.r.c.kind + 1) + 20) ∧ A2a tP tK x τ := by
  have rTd : ∀ i : Fin 4, τ2.val (Td i) = σ.val (Td i) := fun i => hU.or _ (by
    apply fin_nmem; simp; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega) (by lne)
  have rz : ∀ r, r ∉ [E 0, E 1, E 2, X 14, X 18, E 3, E 4, X 8, X 1] → r ≠ Q 15 → r ≠ E 19 →
      (∀ i, r ≠ Td i ∨ i = 3) → τ2.val r = 0 := fun r h1 h2 h3 h4 => by rw [hU.or r h1 h2]; exact hA.regs r h3 h4 h2
  have e3 := pidxP_spec cap (Td 0) (Td 1) (E 1) (E 21) (E 20) (E 22) (by simp [List.nodup_cons]; decide) τ2
    (dTag x.id) (dF1 x.id) (kindTag x.r.c.kind) (by rw [rTd, hA.t0]) (by rw [rTd, hA.t1]) hU.rt
    (rz _ (by lnm) (by lne) (by lne) (fun i => Or.inl (by lne)))
    (rz _ (by lnm) (by lne) (by lne) (fun i => Or.inl (by lne)))
    (rz _ (by lnm) (by lne) (by lne) (fun i => Or.inl (by lne))) hsm
  set τ3 := τ2.setv (E 21) (pidx (dTag x.id) (dF1 x.id) (kindTag x.r.c.kind)) with hτ3
  have v3 : ∀ r, r ≠ E 21 → τ3.val r = τ2.val r := fun r h => by simp [hτ3, Function.update_of_ne h]
  have s3 : τ3.st = τ2.st := by simp [hτ3]
  have h3 : τ3.sh = τ2.sh := by simp [hτ3]
  have oA : ∀ i, i ≠ sIN tP tK → i ≠ Y tP tK 6 → i ≠ sPIN tP tK → σ.st i = [] ∧ σ.sh i = 0 := hA.other
  refine ⟨τ3, e3, ⟨by rw [s3]; exact hU.nat.1, by rw [h3]; exact hU.nat.2⟩,
    fun i hi => by rw [v3 _ (by lne)]; exact hU.qz i hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [s3, h3, (hU.os _ (by rcases hj with rfl | rfl <;> lnm)).1, (hU.os _ (by rcases hj with rfl | rfl <;> lnm)).2]
    exact oA _ (by rcases hj with rfl | rfl <;> lne) (by rcases hj with rfl | rfl <;> lne)
      (by rcases hj with rfl | rfl <;> lne)
  · rw [s3, hU.y2, (oA _ (by lne) (by lne) (by lne)).1]; rfl
  · rw [s3, h3]; exact hU.y2h
  · rw [s3, hU.y4, (oA _ (by lne) (by lne) (by lne)).1]; rfl
  · rw [s3, h3]; exact hU.y4h
  · rw [s3, hU.y5, (oA _ (by lne) (by lne) (by lne)).1]; rfl
  · rw [s3, h3]; exact hU.y5h
  · rw [s3, (hU.os _ (by lnm)).1]; exact hA.kv
  · rw [s3, h3, (hU.os _ (by lnm)).1, (hU.os _ (by lnm)).2]; exact hA.kvh
  · rw [s3, hU.pr, (oA _ (by lne) (by lne) (by lne)).1]; rfl
  · rw [s3, h3]; exact hU.prh
  · rw [s3, hU.gj, (oA _ (by lne) (by lne) (by lne)).1]; simp
  · rw [s3, h3]; exact hU.gjh
  · rw [h3]; exact hU.tmph
  · rw [s3, (hU.os _ (by lnm)).1]; exact hA.pin
  · rw [h3, (hU.os _ (by lnm)).2]; exact hA.pinh
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hi
    have hm : i ∉ [sIN tP tK, sGJ tP tK, Y tP tK 2, Y tP tK 4, sPR tP tK, sTMP tP tK, Y tP tK 5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨a1, a2, a3, a4, a5, a6, a7⟩
    rw [s3, h3, (hU.os i hm).1, (hU.os i hm).2]
    exact oA i a1 a8 a9
  · rw [v3 _ (by lne), hU.or _ (by lnm) (by lne)]; exact hA.len
  · rw [v3 _ (by lne), rTd]; exact hA.t0
  · rw [v3 _ (by lne), rTd]; exact hA.t1
  · rw [v3 _ (by lne), rTd]; exact hA.t2
  · rw [v3 _ (by lne)]; exact hU.rt
  · rw [v3 _ (by lne)]; exact hU.rJ
  · rw [v3 _ (by lne)]; exact hU.rE
  · rw [v3 _ (by lne)]; exact hU.g0
  · rw [v3 _ (by lne)]; exact hU.g1
  · rw [v3 _ (by lne)]; exact hU.rn
  · rw [v3 _ (by lne)]; exact hU.rk
  · simp [hτ3]
  · rw [v3 _ (by lne)]; have := hU.q15; rw [hA.q15] at this; simp only [List.append_nil] at this; omega
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h8, h14, h18, e0, e1, e2', e3', e4', e19, e21, d0, d1, d2, q15⟩ := hr
    rw [v3 r e21]
    exact rz r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨e0, e1, e2', h14, h18,
      e3', e4', h8, h1⟩) q15 e19 (fun i => by
      fin_cases i
      · exact Or.inl d0
      · exact Or.inl d1
      · exact Or.inl d2
      · exact Or.inr rfl)

theorem a2_spec (x : TabCallReq B1 B2 cT) (Λ cap : ℕ) (σ : WState (NS tP tK) NR) (hB : A2a tP tK x σ)
    (hbits : ∀ y ∈ descN x.id ++ cellN x.r.c x.r.p x.r.wt, natBitLength y + 2 ≤ Λ)
    (hlen : (descN x.id ++ cellN x.r.c x.r.p x.r.wt).length ≤ Λ)
    (hRd3 : 2 ^ (natBitLength (coordsOf x.r.wt.I).length + 1) ≤ Λ ∧ ∀ s < x.r.p.J,
      2 ^ (natBitLength (x.r.wt.coef s 0).length + 1) ≤ Λ ∧ 2 ^ (natBitLength (x.r.wt.coef s 1).length + 1) ≤ Λ)
    (hcap : 40 * (Λ + 1) ^ 2 + 20 * (encN (descN x.id ++ cellN x.r.c x.r.p x.r.wt)).length +
      (encN (dRho x.id)).length ≤ cap) :
    ∃ τ, WExec cap (unFW Q (uS tP tK) uR) σ τ (2100 * (Λ + 1) ^ 3) ∧ A2 tP tK x τ := by
  have hL3 : descN x.id ++ callN x.r.c ++ paramsN x.r.p ++ witN x.r.c x.r.p x.r.wt ++ [] =
      descN x.id ++ cellN x.r.c x.r.p x.r.wt := by simp [cellN, List.append_assoc]
  have rX0 : σ.val (X 0) = 0 := hB.regs _ (by lnm)
  have rE5 : σ.val (E 5) = 0 := hB.regs _ (by lnm)
  obtain ⟨τ4, e4, n4, z4, s74, h74, s84, h84, rP4, rJ4, rK4, q4, os4, or4⟩ :=
    unFW_spec cap Q (uS tP tK) uR uR_ne_Q x.r.c x.r.p x.r.wt (descN x.id ++ callN x.r.c ++ paramsN x.r.p) [] [false]
      σ hB.nat hB.qz (by rw [uR_1]; exact hB.tg) (by rw [uR_9]; exact rX0) (by rw [uR_8]; exact hB.vJ)
      (by rw [uR_10]; exact rE5) (by rw [uS_7, (hB.y13 1 (by simp)).1, (hB.y13 1 (by simp)).2]; rfl)
      (by rw [uS_8, (hB.y13 3 (by simp)).1, (hB.y13 3 (by simp)).2]; rfl) Λ (by rw [hL3]; exact hbits)
      (by rw [hL3]; exact hlen) hRd3 (by rw [hL3]; have := hB.q15; omega)
  rw [uS_7] at s74 h74; rw [uS_8] at s84 h84; rw [uR_9] at rP4; rw [uR_8] at rJ4
  have ost : ∀ X, X ≠ sIN tP tK → X ≠ Y tP tK 1 → X ≠ Y tP tK 3 → τ4.st X = σ.st X ∧ τ4.sh X = σ.sh X :=
    fun X a b c => os4 X (by rw [uS_0]; exact a) (by rw [uS_7]; exact b) (by rw [uS_8]; exact c)
  have orv : ∀ r, r ≠ E 1 → r ≠ X 0 → r ≠ Q 15 → τ4.val r = σ.val r := fun r a b c =>
    or4 r (by rw [uR_1]; exact a) (by rw [uR_9]; exact b) c
  refine ⟨τ4, e4, natAt_congr _ _ hL3 (by
      have := n4; rw [show (descN x.id ++ callN x.r.c ++ paramsN x.r.p ++ witN x.r.c x.r.p x.r.wt).length =
        (descN x.id ++ cellN x.r.c x.r.p x.r.wt ++ []).length by simp [cellN]] at this
      rw [uS_0] at this; simpa using this), z4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [s74, (hB.y13 1 (by simp)).1]; rfl
  · rw [(ost _ (by lne) (by lne) (by lne)).1]; exact hB.y2
  · rw [s84, (hB.y13 3 (by simp)).1]; rfl
  · rw [(ost _ (by lne) (by lne) (by lne)).1]; exact hB.y4
  · rw [(ost _ (by lne) (by lne) (by lne)).1]; exact hB.y5
  · rw [(ost _ (by lne) (by lne) (by lne)).1]; exact hB.y6
  · intro j h0 h7
    fin_cases j
    · exact absurd rfl h0
    · exact h74
    · rw [(ost _ (by lne) (by lne) (by lne)).1, (ost _ (by lne) (by lne) (by lne)).2]; exact hB.y2h
    · exact h84
    · rw [(ost _ (by lne) (by lne) (by lne)).1, (ost _ (by lne) (by lne) (by lne)).2]; exact hB.y4h
    · rw [(ost _ (by lne) (by lne) (by lne)).1, (ost _ (by lne) (by lne) (by lne)).2]; exact hB.y5h
    · rw [(ost _ (by lne) (by lne) (by lne)).1, (ost _ (by lne) (by lne) (by lne)).2]; exact hB.y6h
    · exact absurd rfl h7
  · rw [(ost _ (by lne) (by lne) (by lne)).1]; exact hB.pr
  · rw [(ost _ (by lne) (by lne) (by lne)).1, (ost _ (by lne) (by lne) (by lne)).2]; exact hB.prh
  · rw [(ost _ (by lne) (by lne) (by lne)).1]; exact hB.gj
  · rw [(ost _ (by lne) (by lne) (by lne)).1, (ost _ (by lne) (by lne) (by lne)).2]; exact hB.gjh
  · rw [(ost _ (by lne) (by lne) (by lne)).2]; exact hB.tmph
  · rw [(ost _ (by lne) (by lne) (by lne)).1]; exact hB.pin
  · rw [(ost _ (by lne) (by lne) (by lne)).2]; exact hB.pinh
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hi
    have hm : i ∉ [sIN tP tK, sGJ tP tK, Y tP tK 2, Y tP tK 4, sPR tP tK, sTMP tP tK, Y tP tK 5, Y tP tK 6,
        sPIN tP tK] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨a1, a2, a4, a6, a7, a8, a9, a10, a11⟩
    rw [(ost i a1 a3 a5).1, (ost i a1 a3 a5).2]; exact hB.other i hm
  · rw [orv _ (by lne) (by lne) (by lne)]; exact hB.len
  · rw [orv _ (by lne) (by lne) (by lne)]; exact hB.t0
  · rw [orv _ (by lne) (by lne) (by lne)]; exact hB.t1
  · rw [orv _ (by lne) (by lne) (by lne)]; exact hB.t2
  · exact rP4
  · exact rJ4
  · rw [orv _ (by lne) (by lne) (by lne)]; exact hB.vE
  · rw [orv _ (by lne) (by lne) (by lne)]; exact hB.vG0
  · rw [orv _ (by lne) (by lne) (by lne)]; exact hB.vG1
  · rw [orv _ (by lne) (by lne) (by lne)]; exact hB.vn
  · rw [orv _ (by lne) (by lne) (by lne)]; exact hB.vk
  · rw [orv _ (by lne) (by lne) (by lne)]; exact hB.pix
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h8, h14, h18, e0, e1, e2', e3', e4', e19, e21, d0, d1, d2, q15⟩ := hr
    rw [orv r e1 h0 q15]
    exact hB.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                        exact ⟨h1, h8, h14, h18, e0, e1, e2', e3', e4', e19, e21, d0, d1, d2, q15⟩)

end NearCubicGates.Close.CounterMachine.TabCallProg
