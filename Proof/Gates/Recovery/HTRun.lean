import Proof.Gates.Recovery.HTMain
import Proof.Gates.Recovery.HTCore

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.HT

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CheckedPCPP.ClauseFront (named)
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicGates.Close NearCubicGates.Close.Gadget
open NearCubicGates.PublishedSources.PCPP NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.OuterPCPRecovery (canonicalBoundedCircuitDescription)
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)

/-- The point splits into the table address `(x, a, j)` and the padding. -/
theorem ofFn_split {n : ℕ} (point : BitInput n) (R cl pl : ℕ) (h : R + cl + pl ≤ n) :
    List.ofFn point = List.ofFn (fun i : Fin R => point ⟨i.val, by omega⟩) ++
      List.ofFn (fun i : Fin cl => point ⟨R + i.val, by omega⟩) ++
      List.ofFn (fun i : Fin pl => point ⟨R + cl + i.val, by omega⟩) ++ (List.ofFn point).drop (R + cl + pl) := by
  apply List.ext_getElem
  · simp only [List.length_append, List.length_ofFn, List.length_drop] <;> omega
  · intro i h1 h2
    simp only [List.getElem_append, List.getElem_ofFn, List.length_append, List.length_ofFn, List.getElem_drop]
    split_ifs <;> (congr 1 <;> (apply Fin.ext; simp only [Fin.val_mk]; omega))

section Bounds
variable {s : GateSources} {P : ThreeQueryPCPP} {g : Transfer.GateParams}

/-- The cap the main branch needs (`main_exec`'s `hcap`, with `|a| = cl`). -/
noncomputable def mainReq {N : ℕ} (x : BitInput N) (Bs c : BooleanCircuit (Outer.width s.mw (g.sv s) N))
    (cl pl : ℕ) : ℕ :=
  2 * (PCPPNative.descriptor c).length + 8 * Outer.width s.mw (g.sv s) N + 8 +
      (8 * (Outer.width s.mw (g.sv s) N + P.code.length (Outer.width s.mw (g.sv s) N)) +
        4 * (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩)).word.length +
        2 * (P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩))).proofBits + 16) +
      (2 * 2 ^ cl + 2 * 2 ^ pl + 4 * (Outer.width s.mw (g.sv s) N + cl + pl) + 4 +
        16 * ((P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩))).word.length + 2 ^ cl +
          (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩)).n +
          (P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩))).proofBits + 2) +
        4 * ((checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩)).n +
          (P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩))).proofBits +
          3 * ((checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩)).n +
            (P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩))).proofBits)) + 2 ^ pl + 20)

noncomputable def mainBound (cx : Setup.CompFull s P g) (Ke ee Kh eh cap Bv : ℕ) {N : ℕ} (x : BitInput N)
    (Bs c : BooleanCircuit (Outer.width s.mw (g.sv s) N)) : ℕ :=
  CloseoutCaseTwo.Cold.budget Bv c +
    cx.C * ((mwWord s g N Bs).length + (PCPPNative.descriptor c).length + Outer.width s.mw (g.sv s) N + 1) ^ cx.e +
    Ke * (2 * (Outer.width s.mw (g.sv s) N).bits.length +
      2 * Outer.width s.mw (g.sv s) N + 3) ^ ee +
    Kh * ((checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩)).word.length +
      (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩)).n + 1) ^ eh
    + 30000 * (cap + 1) ^ 2

end Bounds

theorem messageWord_len (q : ℕ) (xp : BitInput q) (hq : 2 ≤ q) :
    (messageWord ⟨q, ⟨xp, hq⟩⟩).length = 2 * q.bits.length + 2 * q + 2 := by
  simp only [messageWord, List.length_append, frame_length, List.length_ofFn]; ring

theorem acceptedWord_len (E : LinearCodeFamily) (D : Circuit) (xp : BitInput D.n) (h : D.D.eval xp = true) :
    (acceptedCircuitInputWord (acceptedInput E D xp h)).length = (checkedCircuit E D).word.length +
      (checkedCircuit E D).n := by
  simp only [acceptedCircuitInputWord, acceptedInput, List.length_append, List.length_ofFn]

/-- The composite's `D_B` at source length `2^ν` is `gateCore`'s `D_B` (`Nat.log 2 (2^ν) = ν`). -/
theorem substitutedAt_pow (s : GateSources) (g : Transfer.GateParams) (ν : ℕ) (z : BitInput (2 ^ ν))
    (B : Outer.OuterGuess (g.width s ν)) : substitutedAt s g z B = g.D s ν B := by
  unfold substitutedAt Transfer.GateParams.D Outer.D
  rw [Nat.log_pow (by norm_num)]

/-- The hard-table bit read from the honest assignment depends on the outer verifier only. -/
theorem tableBit_subst (P : ThreeQueryPCPP) {S D : Circuit} (h : S = D) (xS : BitInput S.n) (xD : BitInput D.n)
    (hx : HEq xS xD) (hS : S.D.eval xS = true) (hD : D.D.eval xD = true) (a j : ℕ) :
    TableSem.tableBit (P.output (checkedCircuit P.code S))
        (List.ofFn (sysEnc P.code S.n xS) ++ List.ofFn (P.honest (acceptedInput P.code S xS hS))) a j =
      TableSem.tableBit (P.output (checkedCircuit P.code D))
        (List.ofFn (sysEnc P.code D.n xD) ++ List.ofFn (P.honest (acceptedInput P.code D xD hD))) a j := by
  subst h
  cases hx
  rfl

/-- Acceptance transported along an equality of outer verifiers. -/
theorem eval_subst {S D : Circuit} (h : S = D) (xS : BitInput S.n) (xD : BitInput D.n) (hx : HEq xS xD)
    (hD : D.D.eval xD = true) : S.D.eval xS = true := by
  subst h
  cases hx
  exact hD

/-- **The producer's whole word program** (`sec:gadget-extract`, `sec:all-lengths`): on the five Case 2 ports
(`initHT`: the word of
`C_{⟨B*_src⟩_ν}`, the canonical description of `B*_pf`, `frame point`, `1^q`, `1^B`) the program `htW` ends with
`OUT = frame (gateCore … n point).toNat.bits`. -/
theorem ht_exec {s : GateSources} {P : ThreeQueryPCPP} {g : Transfer.GateParams}
    (cx : Setup.CompFull s P g) (pe ph : Program) (Ke ee Kh eh : ℕ)
    (hpe : ∀ m : MessageRequest, ∃ out, ClockJoin.ReadyRun pe.machine (Ke * ((messageWord m).length + 1) ^ ee)
      (pe.inputTapes (messageWord m)) out ∧ out pe.outputTape = FramedSim.pairs (List.ofFn (P.code.enc m.1 m.2.val)))
    (hph : ∀ a : AcceptedCircuitInput, ∃ out, ClockJoin.ReadyRun ph.machine
      (Kh * ((acceptedCircuitInputWord a).length + 1) ^ eh) (ph.inputTapes (acceptedCircuitInputWord a)) out ∧
      out ph.outputTape = FramedSim.pairs (List.ofFn (P.honest a)))
    (cd pl cap : ℕ) (ν : ℕ) (z : BitInput (2 ^ ν)) (h : g.IsCaseTwo s ν z)
    (hq : 2 ≤ Outer.width s.mw (g.sv s) (2 ^ ν))
    (n : ℕ) (point : BitInput n)
    (hcapF : ((Outer.width s.mw (g.sv s) (2 ^ ν) + 2) ^ cd + Outer.width s.mw (g.sv s) (2 ^ ν) +
      2 * n + pl + 4) ^ 2 ≤ cap)
    (hcapM : mainReq (P := P) z (g.selectedPair s ν z h).src (g.selectedPair s ν z h).pf
      (((Outer.width s.mw (g.sv s) (2 ^ ν)) + 2) ^ cd - 1).size pl ≤ cap) :
    ∃ τ n', WXExec cap (htW cx pe ph cd pl)
      (initHT cx.t pe.tapeCount ph.tapeCount (mwWord s g (2 ^ ν) (g.selectedPair s ν z h).src)
        (RepairOrdinary.frame (canonicalBoundedCircuitDescription (g.bound s ν) (g.selectedPair s ν z h).pf))
        (RepairOrdinary.frame (List.ofFn point)) (Outer.width s.mw (g.sv s) (2 ^ ν)) (g.bound s ν)) τ n' ∧
      n' ≤ 200 * (cd + pl + 1) * (cap + 1) ^ 2 + 10 +
        mainBound cx Ke ee Kh eh cap (g.bound s ν) z (g.selectedPair s ν z h).src (g.selectedPair s ν z h).pf ∧
      τ.st (OUT cx.t pe.tapeCount ph.tapeCount) = RepairOrdinary.frame (g.gateCore s P
        (selectedAmplifier s.amplification g.degree) ν z
        (((Outer.width s.mw (g.sv s) (2 ^ ν)) + 2) ^ cd - 1).size pl n point).toNat.bits := by
  set W := Outer.width s.mw (g.sv s) (2 ^ ν) with hW
  set Bv := g.bound s ν with hBv
  set Bs := (g.selectedPair s ν z h).src with hBs
  set c := (g.selectedPair s ν z h).pf with hc
  have hcB : c.size ≤ Bv := (RecoveryChoice.oracleSelector _ g.degree z h.2.2.2).sizeBounded
  set cl := ((W + 2) ^ cd - 1).size with hcl
  set σ0 := initHT cx.t pe.tapeCount ph.tapeCount (mwWord s g (2 ^ ν) Bs)
    (RepairOrdinary.frame (canonicalBoundedCircuitDescription Bv c)) (RepairOrdinary.frame (List.ofFn point)) W Bv
    with hσ0
  -- the fit test
  have eF := fit_exec cx.t pe.tapeCount ph.tapeCount cd pl cap σ0 W (List.ofFn point)
    (by simp [hσ0, initHT, fiveWords]) (by simp [hσ0, initHT])
    (by simp [hσ0, initHT, fiveWords]) (by simp [hσ0, initHT])
    (by simp [hσ0, initHT]) (by simp [hσ0, initHT]) (fun r _ => by simp [hσ0, initHT])
    (by simp only [List.length_ofFn]; exact hcapF)
  have hcap16 : 16 ≤ cap := by
    have h4 : 4 ≤ ((W + 2) ^ cd + W + 2 * n + pl + 4) := by omega
    have := Nat.pow_le_pow_left h4 2
    omega
  have hSD : substitutedAt s g z ⟨Bs, c⟩ = g.D s ν (g.selectedPair s ν z h) :=
    substitutedAt_pow s g ν z (g.selectedPair s ν z h)
  by_cases hfit : W + cl + pl ≤ n
  · -- the main branch
    set xp : BitInput W := fun i => point ⟨i.val, by have := i.isLt; omega⟩ with hxp
    set wa := List.ofFn (fun i : Fin cl => point ⟨W + i.val, by omega⟩) with hwa
    set wj := List.ofFn (fun i : Fin pl => point ⟨W + cl + i.val, by omega⟩) with hwj
    set r := (List.ofFn point).drop (W + cl + pl) with hr
    have hsplit : List.ofFn point = List.ofFn xp ++ wa ++ wj ++ r := ofFn_split point W cl pl hfit
    have hacc : (substitutedAt s g z ⟨Bs, c⟩).D.eval xp = true :=
      eval_subst hSD xp xp HEq.rfl (g.selected_taut s ν z h xp)
    have hwal : wa.length = cl := List.length_ofFn
    have hwjl : wj.length = pl := List.length_ofFn
    obtain ⟨τ, n', eM, hn', hT⟩ := main_exec cx pe ph Ke ee Kh eh hpe hph cd pl cap z Bs c hq Bv hcB xp hacc wa wj r
      hwal hwjl _ (by rw [← hsplit]) (by have := hcapM; unfold mainReq at this; rw [hwal]; exact this)
    have hF1 : (fitState σ0 W (List.ofFn point).length cd pl).val rF ≠ 0 := by
      simp (config := { decide := true }) [fitState, Function.update_apply, List.length_ofFn]; omega
    refine ⟨τ, _, WXExec.seq eF (WXExec.ifrT hF1 eM), ?_, ?_⟩
    · have hm : n' ≤ mainBound cx Ke ee Kh eh cap Bv z Bs c := by
        unfold mainBound
        rw [messageWord_len, acceptedWord_len] at hn'
        exact hn'
      omega
    · have hfit' : g.width s ν + cl + pl ≤ n := hfit
      rw [hT, outWord_eq, HTCore.gateCore_two_point s g P _ ν z cl pl n point h, dif_pos hfit']
      dsimp only
      rw [ofFn_addCases]
      congr 3
      exact tableBit_subst P hSD xp _ HEq.rfl hacc _ _ _
  · -- no fit: `OUT := [false]`
    have hF0 : (fitState σ0 W (List.ofFn point).length cd pl).val rF = 0 := by
      simp (config := { decide := true }) [fitState, Function.update_apply, List.length_ofFn]; omega
    have eE := emits_raw (cap := cap) (dst := OUT cx.t pe.tapeCount ph.tapeCount) (OP := opOUT) false
      (fitState σ0 W (List.ofFn point).length cd pl)
      (by simp (config := { decide := true }) [fitState, hσ0, initHT])
      (by simp (config := { decide := true }) [fitState, Function.update_apply, hσ0, initHT]; omega)
    refine ⟨_, _, WXExec.seq eF (WXExec.ifrF (P := .seq (headW cx pe ph) (tailW cx.t pe.tapeCount ph.tapeCount pl
      cx.wOut)) hF0 (WXExec.wm eE)), ?_, ?_⟩
    · omega
    · have hfit' : ¬g.width s ν + cl + pl ≤ n := hfit
      rw [HTCore.gateCore_two_point s g P _ ν z cl pl n point h, dif_neg hfit']
      simp (config := { decide := true }) [appendO, fitState, hσ0, initHT]

end NearCubicGates.Close.Recovery.HT
