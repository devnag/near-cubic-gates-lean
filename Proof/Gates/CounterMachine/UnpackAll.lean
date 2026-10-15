import Proof.Gates.CounterMachine.UnpackWit

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_append)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec NearCubicGates.Close.Counter NearCubicGates.Close.Interfaces

variable {ns nr : ℕ} (cap : ℕ)

section Call
variable (IN : Fin (ns + 1)) (Q : Fin 16 ↪ Fin nr)

/-- **The call unpacker, field by field.** -/
theorem unCall_facts (GJ S0 S1 : Fin (ns + 1)) (hd5 : [IN, GJ, S0, S1].Nodup) (Rn Rk N3 G0 G1 : Fin nr)
    (hdr : [Rn, Rk, N3, G0, G1].Nodup) (hQ' : ∀ i, Q i ∉ [Rn, Rk, N3, G0, G1]) (c : Call) (A B : List ℕ)
    (rest : List Bool) (σ : WState ns nr) (hσ : NatAt IN (A ++ callN c ++ B) rest σ A.length) (hz : QZero Q σ)
    (hGJ : σ.sh GJ = (σ.st GJ).length) (hS0 : σ.sh S0 = (σ.st S0).length) (hS1 : σ.sh S1 = (σ.st S1).length) :
    let τ := unCallFinal IN Q GJ S0 S1 Rn Rk N3 G0 G1 c A σ
    NatAt IN (A ++ callN c ++ B) rest τ (A ++ callN c).length ∧ QZero Q τ ∧
      τ.val Rn = c.n ∧ τ.val Rk = kindTag c.kind ∧ τ.val G0 = c.first.gates.length ∧
      τ.val G1 = c.second.gates.length ∧
      τ.st S0 = σ.st S0 ++ encN (c.first.coeffs.flatMap intN) ∧ τ.sh S0 = (τ.st S0).length ∧
      τ.st S1 = σ.st S1 ++ encN (c.second.coeffs.flatMap intN) ∧ τ.sh S1 = (τ.st S1).length ∧
      τ.sh GJ = (τ.st GJ).length ∧
      τ.st GJ = σ.st GJ ++ encN (c.first.gates.flatMap gateN) ++ encN (c.second.gates.flatMap gateN) ∧
      τ.val (Q 15) = σ.val (Q 15) + (encN (c.first.gates.flatMap gateN)).length +
        (encN (c.first.coeffs.flatMap intN)).length + (encN (c.second.gates.flatMap gateN)).length +
        (encN (c.second.coeffs.flatMap intN)).length ∧
      (∀ X, X ∉ [IN, GJ, S0, S1] → τ.st X = σ.st X ∧ τ.sh X = σ.sh X) ∧
      (∀ r, r ∉ [Rn, Rk, N3, G0, G1, Q 15] → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  intro τ
  have hQ : ∀ {a b : Fin 16}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hd5 hdr
  obtain ⟨⟨iG, i0, i1⟩, ⟨g0, g1⟩, s01⟩ := hd5
  obtain ⟨⟨nk, nN, nG0, nG1⟩, ⟨kN, kG0, kG1⟩, ⟨NG0, NG1⟩, G01⟩ := hdr
  have qr : ∀ i r, r ∈ [Rn, Rk, N3, G0, G1] → Q i ≠ r := fun i r hr h => hQ' i (h ▸ hr)
  have q15 : ∀ r, r ∈ [Rn, Rk, N3, G0, G1] → r ≠ Q 15 := fun r hr h => qr 15 r hr h.symm
  have q15' : ∀ r, r ∈ [Rn, Rk, N3, G0, G1] → Q 15 ≠ r := fun r hr => qr 15 r hr
  have a1 := q15 Rn (by simp); have a2 := q15 Rk (by simp); have a3 := q15 N3 (by simp)
  have a4 := q15 G0 (by simp); have a5 := q15 G1 (by simp)
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [τ, unCallFinal, appendO, Function.update_apply, iG, i0, i1, Ne.symm iG, Ne.symm i0, Ne.symm i1, hσ.1]
  · simp only [τ, unCallFinal, WState.seth_sh, Function.update_self]
    rw [show A ++ callN c ++ B = (A ++ callN c) ++ B from rfl, List.take_left', callN_split]
    · simp [List.append_assoc]
    · rfl
  · intro i hi
    have h15 : Q i ≠ Q 15 := fun h => hi (Q.injective h)
    simp [τ, unCallFinal, appendO, Function.update_apply, qr i G1 (by simp), qr i G0 (by simp), qr i N3 (by simp),
      qr i Rk (by simp), qr i Rn (by simp), h15]
    exact hz i hi
  all_goals try (simp [τ, unCallFinal, appendO, Function.update_apply, iG, i0, i1, g0, g1, s01, Ne.symm iG,
    Ne.symm i0, Ne.symm i1, Ne.symm g0, Ne.symm g1, Ne.symm s01, nk, nN, nG0, nG1, kN, kG0, kG1, NG0, NG1, G01,
    Ne.symm nk, Ne.symm nN, Ne.symm nG0, Ne.symm nG1, Ne.symm kN, Ne.symm kG0, Ne.symm kG1, Ne.symm NG0,
    Ne.symm NG1, Ne.symm G01, a1, a2, a3, a4, a5, Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4, Ne.symm a5,
    hS0, hS1, hGJ, List.append_assoc]; done)
  all_goals try (simp [τ, unCallFinal, appendO, Function.update_apply, iG, i0, i1, g0, g1, s01, Ne.symm iG,
    Ne.symm i0, Ne.symm i1, Ne.symm g0, Ne.symm g1, Ne.symm s01, nk, nN, nG0, nG1, kN, kG0, kG1, NG0, NG1, G01,
    Ne.symm nk, Ne.symm nN, Ne.symm nG0, Ne.symm nG1, Ne.symm kN, Ne.symm kG0, Ne.symm kG1, Ne.symm NG0,
    Ne.symm NG1, Ne.symm G01, a1, a2, a3, a4, a5, Ne.symm a1, Ne.symm a2, Ne.symm a3, Ne.symm a4, Ne.symm a5,
    hS0, hS1, hGJ, List.append_assoc]; ring; done)
  · intro X hX
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hX
    simp [τ, unCallFinal, appendO, Function.update_apply, hX.1, hX.2.1, hX.2.2.1, hX.2.2.2]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [τ, unCallFinal, appendO, Function.update_apply, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2]

/-- The pair flag from the kind tag (`pair` is tag `1`): `Pr := [Tg = 1]` (`Tg` is spent). -/
def pairFlagP (Tg Pr : Fin nr) : WM ns nr := .ifr Tg (.seq (.dec Tg) (.ifr Tg .skip (.inc Pr))) .skip

theorem pairFlag_spec (Tg Pr : Fin nr) (hTP : Tg ≠ Pr) (c : Call) (σ : WState ns nr)
    (hT : σ.val Tg = kindTag c.kind) (hP : σ.val Pr = 0) (hc : 2 ≤ cap) :
    ∃ v, WExec cap (pairFlagP Tg Pr) σ ((σ.setv Tg v).setv Pr (if c.kind = .pair then 1 else 0)) 10 := by
  cases hk : c.kind with
  | single =>
    rw [hk] at hT
    refine ⟨σ.val Tg, WExec.cast cap (WExec.ifrF (by rw [hT]; rfl) (WExec.skip σ)) ?_ (by omega)⟩
    apply WState.eq <;> simp
    exact hP
  | pair =>
    rw [hk] at hT
    have e1 := WExec.dec (cap := cap) Tg σ (by rw [hT]; simp [kindTag]; omega)
    have h0 : (σ.setv Tg (σ.val Tg - 1)).val Tg = 0 := by simp [hT, kindTag]
    have e2 := WExec.inc (cap := cap) Pr (σ.setv Tg (σ.val Tg - 1)) (by simp [Function.update_of_ne (Ne.symm hTP), hP]; omega)
    refine ⟨0, WExec.cast cap (WExec.ifrT (by rw [hT]; simp [kindTag]) (WExec.seq e1 (WExec.ifrF h0 e2))) ?_ (by omega)⟩
    simp [Function.update_of_ne (Ne.symm hTP), hP, hT, kindTag]
  | parity =>
    rw [hk] at hT
    have e1 := WExec.dec (cap := cap) Tg σ (by rw [hT]; simp [kindTag]; omega)
    have h1 : (σ.setv Tg (σ.val Tg - 1)).val Tg ≠ 0 := by simp [hT, kindTag]
    refine ⟨σ.val Tg - 1, WExec.cast cap (WExec.ifrT (by rw [hT]; simp [kindTag])
      (WExec.seq e1 (WExec.ifrT h1 (WExec.skip _)))) ?_ (by omega)⟩
    apply WState.eq <;> simp
    rw [Function.update_of_ne (Ne.symm hTP), hP]

theorem callN_parts (c : Call) : (encN (c.first.gates.flatMap gateN)).length +
    (encN (c.first.coeffs.flatMap intN)).length + (encN (c.second.gates.flatMap gateN)).length +
    (encN (c.second.coeffs.flatMap intN)).length ≤ (encN (callN c)).length := by
  simp only [callN, circN_split, encN_append, List.length_append]; omega

/-- Call and parameters (streams `S`: `0` input, `1` gates, `2`/`3` top coefficients, `4` primes, `5` scratch,
`6` rates; registers `R`: `0` n, `1` kind tag, `2` 2n+3, `3`/`4` gate counts, `5` k, `6` P, `7` e, `8` J). -/
def unCP (S : Fin 9 ↪ Fin (ns + 1)) (R : Fin 11 ↪ Fin nr) : WM ns nr :=
  .seq (unCall (S 0) Q (S 1) (S 2) (S 3) (R 0) (R 1) (R 2) (R 3) (R 4))
    (unPar (S 0) Q (R 5) (R 6) (R 7) (R 8) (S 4) (S 5) (S 6))

theorem unCP_spec (S : Fin 9 ↪ Fin (ns + 1)) (R : Fin 11 ↪ Fin nr) (hQR : ∀ i j, Q i ≠ R j) (c : Call) (p : Params)
    (wt : Wit c.n) (A B : List ℕ) (rest : List Bool) (σ : WState ns nr)
    (hσ : NatAt (S 0) (A ++ cellN c p wt ++ B) rest σ A.length) (hz : QZero Q σ) (h0 : ∀ j, σ.val (R j) = 0)
    (hend : ∀ j : Fin 9, j ≠ 0 → j ≠ 5 → σ.sh (S j) = (σ.st (S j)).length) (hTMP : σ.st (S 5) = [] ∧ σ.sh (S 5) = 0)
    (Λ : ℕ) (hbits : ∀ y ∈ A ++ cellN c p wt ++ B, natBitLength y + 2 ≤ Λ) (hlen : (A ++ cellN c p wt ++ B).length ≤ Λ)
    (hRd1 : ∀ v ∈ [c.n, kindTag c.kind, c.first.gates.length, c.first.coeffs.length, c.first.table.length,
      c.second.gates.length, c.second.coeffs.length, c.second.table.length, c.parity.length],
      2 ^ (natBitLength v + 1) ≤ Λ) (hn : 2 * c.n + 3 ≤ Λ)
    (hRd2 : ∀ v ∈ [p.k, p.P, p.e, p.J, (p.primes.sort (· ≤ ·)).length, p.factors.length], 2 ^ (natBitLength v + 1) ≤ Λ)
    (hcap : 40 * (Λ + 1) ^ 2 + 20 * (encN (A ++ cellN c p wt ++ B)).length + σ.val (Q 15) ≤ cap) :
    ∃ τ, WExec cap (unCP Q S R) σ τ (30000 * (Λ + 1) ^ 2 + 23 * (σ.val (Q 15) + (encN (A ++ cellN c p wt ++ B)).length)) ∧
      NatAt (S 0) (A ++ callN c ++ paramsN p ++ witN c p wt ++ B) rest τ (A ++ callN c ++ paramsN p).length ∧
      QZero Q τ ∧
      τ.st (S 2) = σ.st (S 2) ++ encN (c.first.coeffs.flatMap intN) ∧ τ.sh (S 2) = (τ.st (S 2)).length ∧
      τ.st (S 3) = σ.st (S 3) ++ encN (c.second.coeffs.flatMap intN) ∧ τ.sh (S 3) = (τ.st (S 3)).length ∧
      τ.st (S 6) = σ.st (S 6) ++ encN (p.factors ++ [p.M1, p.A]) ∧ τ.sh (S 6) = (τ.st (S 6)).length ∧
      τ.st (S 4) = σ.st (S 4) ++ encN (p.primes.sort (· ≤ ·)) ∧ τ.sh (S 4) = (τ.st (S 4)).length ∧
      τ.st (S 1) = σ.st (S 1) ++ encN (c.first.gates.flatMap gateN) ++ encN (c.second.gates.flatMap gateN) ∧
      τ.sh (S 1) = (τ.st (S 1)).length ∧ τ.sh (S 5) = (encN [p.M1]).length ∧
      τ.val (R 0) = c.n ∧ τ.val (R 1) = kindTag c.kind ∧ τ.val (R 3) = c.first.gates.length ∧
      τ.val (R 4) = c.second.gates.length ∧ τ.val (R 5) = p.k ∧ τ.val (R 6) = p.P ∧ τ.val (R 7) = p.e ∧
      τ.val (R 8) = p.J ∧
      σ.val (Q 15) + (encN (c.first.coeffs.flatMap intN)).length + (encN (c.second.coeffs.flatMap intN)).length +
        (encN (p.factors ++ [p.M1, p.A])).length ≤ τ.val (Q 15) ∧
      τ.val (Q 15) ≤ σ.val (Q 15) + 3 * (encN (A ++ cellN c p wt ++ B)).length ∧
      (∀ X, (∀ j : Fin 9, j.val < 7 → X ≠ S j) → τ.st X = σ.st X ∧ τ.sh X = σ.sh X) ∧
      (∀ r, (∀ j : Fin 11, j.val < 9 → r ≠ R j) → r ≠ Q 15 → τ.val r = σ.val r) := by
  have hS : ∀ {a b : Fin 9}, a ≠ b → S a ≠ S b := fun h => S.injective.ne h
  have hR : ∀ {a b : Fin 11}, a ≠ b → R a ≠ R b := fun h => R.injective.ne h
  have hL : A ++ cellN c p wt ++ B = A ++ callN c ++ (paramsN p ++ witN c p wt ++ B) := by
    simp [cellN, List.append_assoc]
  have hcp := callN_parts c
  have hmid := encN_le_mid A (callN c) (paramsN p ++ witN c p wt ++ B)
  rw [← hL] at hmid
  have hQ5 : ∀ i, Q i ∉ [R 0, R 1, R 2, R 3, R 4] := fun i h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h <;> exact hQR i _ h
  have hd5 : [S 0, S 1, S 2, S 3].Nodup := by simp [hS, S.injective.eq_iff]
  have hdr : [R 0, R 1, R 2, R 3, R 4].Nodup := by simp [R.injective.eq_iff]
  have hb1 : ∀ x ∈ A ++ callN c ++ (paramsN p ++ witN c p wt ++ B), natBitLength x + 2 ≤ Λ := by
    rw [← hL]; exact hbits
  have hl1 : (A ++ callN c ++ (paramsN p ++ witN c p wt ++ B)).length ≤ Λ := by rw [← hL]; exact hlen
  have hc1 : 20 * (Λ + 1) ^ 2 + 4 * (encN (A ++ callN c ++ (paramsN p ++ witN c p wt ++ B))).length +
      σ.val (Q 15) ≤ cap := by
    rw [← hL]; omega
  have hσ1 := natAt_congr (S 0) rest hL hσ
  have e1 := unCall_run cap (S 0) Q (S 1) (S 2) (S 3) hd5 (R 0) (R 1) (R 2) (R 3) (R 4) hdr hQ5 c A
    (paramsN p ++ witN c p wt ++ B) rest σ hσ1 hz (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact h0 _)
    (hend 1 (by decide) (by decide)) (hend 2 (by decide) (by decide)) (hend 3 (by decide) (by decide)) Λ hb1 hRd1
    hl1 hn hc1
  have f1 := unCall_facts (S 0) Q (S 1) (S 2) (S 3) hd5 (R 0) (R 1) (R 2) (R 3) (R 4) hdr hQ5 c A
    (paramsN p ++ witN c p wt ++ B) rest σ hσ1 hz (hend 1 (by decide) (by decide)) (hend 2 (by decide) (by decide))
    (hend 3 (by decide) (by decide))
  set τ1 := unCallFinal (S 0) Q (S 1) (S 2) (S 3) (R 0) (R 1) (R 2) (R 3) (R 4) c A σ with hτ1
  obtain ⟨n1, z1, vn1, vT1, vG01, vG11, st01, sh01, st11, sh11, shG1, stG1, q1, os1, or1, ce1⟩ := f1
  have os1' : ∀ j : Fin 9, 4 ≤ j.val → τ1.st (S j) = σ.st (S j) ∧ τ1.sh (S j) = σ.sh (S j) := fun j hj =>
    os1 (S j) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨hS ?_, hS ?_, hS ?_, hS ?_⟩ <;> (intro h; rw [h] at hj; simp at hj))
  have or1' : ∀ j : Fin 11, 5 ≤ j.val → τ1.val (R j) = σ.val (R j) := fun j hj =>
    or1 (R j) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨hR ?_, hR ?_, hR ?_, hR ?_, hR ?_, fun h => hQR 15 j h.symm⟩ <;> (intro h; rw [h] at hj; simp at hj))
  -- 2. the parameters
  have hL2 : A ++ callN c ++ (paramsN p ++ witN c p wt ++ B) = (A ++ callN c) ++ paramsN p ++ (witN c p wt ++ B) := by
    simp [List.append_assoc]
  have hL3 : A ++ cellN c p wt ++ B = (A ++ callN c) ++ paramsN p ++ (witN c p wt ++ B) := by
    simp [cellN, List.append_assoc]
  have hq1 : τ1.val (Q 15) ≤ σ.val (Q 15) + (encN (A ++ cellN c p wt ++ B)).length := by rw [q1]; omega
  have hQ4 : ∀ i, Q i ∉ [R 5, R 6, R 7, R 8] := fun i h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;> exact hQR i _ h
  obtain ⟨τ2, e2, n2, z2, vk2, vP2, vE2, vJ2, stP2, shP2, stF2, shF2, shT2, q2u, q2l, os2, or2⟩ :=
    unPar_spec cap (S 0) Q (R 5) (R 6) (R 7) (R 8) (S 4) (S 5) (S 6) (by simp [hS, S.injective.eq_iff])
      (by simp [R.injective.eq_iff]) hQ4 p (A ++ callN c) (witN c p wt ++ B) rest τ1 (natAt_congr (S 0) rest hL2 n1) z1
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> (rw [or1' _ (by decide)]; exact h0 _))
      (by rw [(os1' 4 (by decide)).1, (os1' 4 (by decide)).2]; exact hend 4 (by decide) (by decide))
      (by rw [(os1' 6 (by decide)).1, (os1' 6 (by decide)).2]; exact hend 6 (by decide) (by decide))
      (by rw [(os1' 5 (by decide)).1, (os1' 5 (by decide)).2]; exact hTMP) Λ
      (by rw [← hL3]; exact hbits) (by rw [← hL3]; exact hlen) hRd2 (by rw [← hL3]; omega)
  have os2' : ∀ j : Fin 9, j.val < 4 → j ≠ 0 → τ2.st (S j) = τ1.st (S j) ∧ τ2.sh (S j) = τ1.sh (S j) := fun j hj h0' =>
    os2 (S j) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨hS h0', hS ?_, hS ?_, hS ?_⟩ <;> (intro h; rw [h] at hj; simp at hj))
  have or2' : ∀ j : Fin 11, j.val < 5 → τ2.val (R j) = τ1.val (R j) := fun j hj =>
    or2 (R j) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨hR ?_, hR ?_, hR ?_, hR ?_, fun h => hQR 15 j h.symm⟩ <;> (intro h; rw [h] at hj; simp at hj))
  refine ⟨τ2, WExec.mono (WExec.seq e1 e2) ?_, natAt_congr (S 0) rest
    (L := (A ++ callN c) ++ paramsN p ++ (witN c p wt ++ B)) (by simp [List.append_assoc]) n2, z2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, shT2, ?_, ?_, ?_, ?_, vk2, vP2, vE2, vJ2, ?_, ?_, ?_, ?_⟩
  · have : 23 * τ1.val (Q 15) ≤ 23 * (σ.val (Q 15) + (encN (A ++ cellN c p wt ++ B)).length) := by omega
    nlinarith
  · rw [(os2' 2 (by decide) (by decide)).1, st01]
  · rw [(os2' 2 (by decide) (by decide)).1, (os2' 2 (by decide) (by decide)).2, sh01]
  · rw [(os2' 3 (by decide) (by decide)).1, st11]
  · rw [(os2' 3 (by decide) (by decide)).1, (os2' 3 (by decide) (by decide)).2, sh11]
  · rw [stF2, (os1' 6 (by decide)).1]
  · exact shF2
  · rw [stP2, (os1' 4 (by decide)).1]
  · exact shP2
  · rw [(os2' 1 (by decide) (by decide)).1, stG1]
  · rw [(os2' 1 (by decide) (by decide)).1, (os2' 1 (by decide) (by decide)).2]; exact shG1
  · rw [or2' 0 (by decide)]; exact vn1
  · rw [or2' 1 (by decide)]; exact vT1
  · rw [or2' 3 (by decide)]; exact vG01
  · rw [or2' 4 (by decide)]; exact vG11
  · rw [q1] at q2l; omega
  · rw [← hL3] at q2u; omega
  · intro X hX
    have h1 := os1 X (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hX 0 (by decide), hX 1 (by decide), hX 2 (by decide), hX 3 (by decide)⟩)
    have h2 := os2 X (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hX 0 (by decide), hX 4 (by decide), hX 5 (by decide), hX 6 (by decide)⟩)
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
  · intro r hr h15
    rw [or2 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hr 5 (by decide), hr 6 (by decide), hr 7 (by decide), hr 8 (by decide), h15⟩)]
    exact or1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hr 0 (by decide), hr 1 (by decide), hr 2 (by decide), hr 3 (by decide), hr 4 (by decide), h15⟩)

/-- The pair flag and the witness (`R 9` the flag, `R 10` the stage counter; streams `S 7`, `S 8`). -/
def unFW (S : Fin 9 ↪ Fin (ns + 1)) (R : Fin 11 ↪ Fin nr) : WM ns nr :=
  .seq (pairFlagP (R 1) (R 9)) (unWit (S 0) Q (S 7) (S 8) (R 9) (R 8) (R 10))

theorem unFW_spec (S : Fin 9 ↪ Fin (ns + 1)) (R : Fin 11 ↪ Fin nr) (hQR : ∀ i j, Q i ≠ R j) (c : Call) (p : Params)
    (wt : Wit c.n) (A B : List ℕ) (rest : List Bool) (σ : WState ns nr)
    (hσ : NatAt (S 0) (A ++ witN c p wt ++ B) rest σ A.length) (hz : QZero Q σ)
    (hT : σ.val (R 1) = kindTag c.kind) (hP : σ.val (R 9) = 0) (hJ : σ.val (R 8) = p.J) (hK : σ.val (R 10) = 0)
    (hY1 : σ.sh (S 7) = (σ.st (S 7)).length) (hY3 : σ.sh (S 8) = (σ.st (S 8)).length) (Λ : ℕ)
    (hbits : ∀ y ∈ A ++ witN c p wt ++ B, natBitLength y + 2 ≤ Λ) (hlen : (A ++ witN c p wt ++ B).length ≤ Λ)
    (hrd : 2 ^ (natBitLength (coordsOf wt.I).length + 1) ≤ Λ ∧
      ∀ s < p.J, 2 ^ (natBitLength (wt.coef s 0).length + 1) ≤ Λ ∧ 2 ^ (natBitLength (wt.coef s 1).length + 1) ≤ Λ)
    (hcap : 40 * (Λ + 1) ^ 2 + 10 * (encN (A ++ witN c p wt ++ B)).length + σ.val (Q 15) ≤ cap) :
    ∃ τ, WExec cap (unFW Q S R) σ τ (2100 * (Λ + 1) ^ 3) ∧
      NatAt (S 0) (A ++ witN c p wt ++ B) rest τ (A ++ witN c p wt).length ∧ QZero Q τ ∧
      τ.st (S 7) = σ.st (S 7) ++ encN (W0 c wt p.J) ∧ τ.sh (S 7) = (τ.st (S 7)).length ∧
      τ.st (S 8) = σ.st (S 8) ++ encN (W1 c wt p.J) ∧ τ.sh (S 8) = (τ.st (S 8)).length ∧
      τ.val (R 9) = (if c.kind = .pair then 1 else 0) ∧ τ.val (R 8) = p.J ∧ τ.val (R 10) = 0 ∧
      τ.val (Q 15) = σ.val (Q 15) + (encN (W0 c wt p.J)).length + (encN (W1 c wt p.J)).length ∧
      (∀ X, X ≠ S 0 → X ≠ S 7 → X ≠ S 8 → τ.st X = σ.st X ∧ τ.sh X = σ.sh X) ∧
      (∀ r, r ≠ R 1 → r ≠ R 9 → r ≠ Q 15 → τ.val r = σ.val r) := by
  have hS : ∀ {a b : Fin 9}, a ≠ b → S a ≠ S b := fun h => S.injective.ne h
  have hR : ∀ {a b : Fin 11}, a ≠ b → R a ≠ R b := fun h => R.injective.ne h
  have hc2 : 2 ≤ cap := by have : 1 ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega); omega
  obtain ⟨v, e1⟩ := pairFlag_spec cap (R 1) (R 9) (hR (by decide)) c σ hT hP hc2
  set σ1 := (σ.setv (R 1) v).setv (R 9) (if c.kind = .pair then 1 else 0) with hσ1
  have z1 : QZero Q σ1 := fun i hi => by
    simp [hσ1, Function.update_of_ne (hQR i 9), Function.update_of_ne (hQR i 1)]; exact hz i hi
  have e2 := unWit_spec cap (S 0) Q (S 7) (S 8) (hS (by decide)) (hS (by decide)) (hS (by decide)) (R 9) (R 8) (R 10)
    (by simp [R.injective.eq_iff]) (fun i h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h <;> exact hQR i _ h) c p wt A B rest σ1 hσ z1 (by simp [hσ1])
    (by simp [hσ1, Function.update_of_ne (hR (show (8 : Fin 11) ≠ 9 by decide)),
      Function.update_of_ne (hR (show (8 : Fin 11) ≠ 1 by decide)), hJ])
    (by simp [hσ1, Function.update_of_ne (hR (show (10 : Fin 11) ≠ 9 by decide)),
      Function.update_of_ne (hR (show (10 : Fin 11) ≠ 1 by decide)), hK]) hY1 hY3 Λ hbits hlen hrd
    (by simp only [hσ1, WState.setv_val]
        rw [Function.update_of_ne (hQR 15 9), Function.update_of_ne (hQR 15 1)]; exact hcap)
  refine ⟨_, WExec.mono (WExec.seq e1 e2) ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (Λ + 1) ^ 3 ≥ 1 := Nat.one_le_pow _ _ (by omega)
    omega
  · refine ⟨?_, ?_⟩
    · simp [hσ1, appendO, Function.update_of_ne (hS (show (0 : Fin 9) ≠ 7 by decide)),
        Function.update_of_ne (hS (show (0 : Fin 9) ≠ 8 by decide)), hσ.1]
    · simp only [WState.seth_sh, Function.update_self]
      rw [show A ++ witN c p wt ++ B = (A ++ witN c p wt) ++ B from rfl, List.take_left']
      rfl
  · intro i hi
    simp [hσ1, appendO, Function.update_of_ne (fun h => hi (Q.injective h)), Function.update_of_ne (hQR i 9),
      Function.update_of_ne (hQR i 1)]
    exact hz i hi
  · simp [hσ1, appendO, Function.update_of_ne (hS (show (7 : Fin 9) ≠ 8 by decide))]
  · simp [hσ1, appendO, Function.update_of_ne (hS (show (7 : Fin 9) ≠ 8 by decide)),
      Function.update_of_ne (hS (show (7 : Fin 9) ≠ 0 by decide)), hY1]
  · simp [hσ1, appendO]
  · simp [hσ1, appendO, Function.update_of_ne (hS (show (8 : Fin 9) ≠ 0 by decide)),
      Function.update_of_ne (hS (show (8 : Fin 9) ≠ 7 by decide)), hY3]
  · simp [hσ1, appendO, Function.update_of_ne (hQR 15 9).symm]
  · simp [hσ1, appendO, Function.update_of_ne (hQR 15 8).symm,
      Function.update_of_ne (hR (show (8 : Fin 11) ≠ 9 by decide)),
      Function.update_of_ne (hR (show (8 : Fin 11) ≠ 1 by decide)), hJ]
  · simp [hσ1, appendO, Function.update_of_ne (hQR 15 10).symm,
      Function.update_of_ne (hR (show (10 : Fin 11) ≠ 9 by decide)),
      Function.update_of_ne (hR (show (10 : Fin 11) ≠ 1 by decide)), hK]
  · simp [hσ1, appendO, Function.update_of_ne (hQR 15 9), Function.update_of_ne (hQR 15 1)]
  · intro X h0 h7 h8
    simp [hσ1, appendO, Function.update_of_ne h0, Function.update_of_ne h7, Function.update_of_ne h8]
  · intro r h1 h9 h15
    simp [hσ1, appendO, Function.update_of_ne h1, Function.update_of_ne h9, Function.update_of_ne h15]

end Call

end NearCubicGates.Close.CounterMachine
