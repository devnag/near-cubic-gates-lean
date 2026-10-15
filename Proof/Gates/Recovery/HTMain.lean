import Proof.Gates.Recovery.HTHead
import Proof.Gates.Recovery.HardTableRuns
import Proof.CaseAnalysis.CaseTwoSelectedDescription

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

section Program
variable {s : GateSources} {P : ThreeQueryPCPP} {g : Transfer.GateParams}
  (cx : Setup.CompFull s P g) (pe ph : Program)

/-- The head: converter, descriptor, composite, encoder input, encoder, `AS`, `HI`, honest prover. -/
noncomputable def headW : WMX (NS cx.t pe.tapeCount ph.tapeCount) 64 :=
  .seq (.seq (convW cx.t pe.tapeCount ph.tapeCount) (.seq (.mach cx.M (compMap cx.t pe.tapeCount ph.tapeCount cx.cIn
    cx.dIn)) (eiW cx.t pe.tapeCount ph.tapeCount)))
  (.seq (.seq (.mach pe.machine (encMap cx.t pe.tapeCount ph.tapeCount))
      (asW cx.t pe.tapeCount ph.tapeCount (encMap cx.t pe.tapeCount ph.tapeCount pe.outputTape)))
    (.seq (hiW cx.t pe.tapeCount ph.tapeCount (bK cx.t pe.tapeCount ph.tapeCount cx.cOut))
      (.seq (.mach ph.machine (honMap cx.t pe.tapeCount ph.tapeCount))
        (as2W cx.t pe.tapeCount ph.tapeCount (honMap cx.t pe.tapeCount ph.tapeCount ph.outputTape)))))

/-- **The producer's word program.** -/
noncomputable def htW (cd pl : ℕ) : WMX (NS cx.t pe.tapeCount ph.tapeCount) 64 :=
  .seq (fitW cx.t pe.tapeCount ph.tapeCount cd pl)
    (.ifr rF (.seq (headW cx pe ph) (tailW cx.t pe.tapeCount ph.tapeCount pl cx.wOut))
      (.wm (emitC (OUT cx.t pe.tapeCount ph.tapeCount) opOUT false)))

end Program

/-- The entry state: the five ports, every other stream empty, heads and registers `0`. -/
def initHT (tK tE tH : ℕ) (h desc addr : List Bool) (Rv Bv : ℕ) : WState (NS tK tE tH) 64 :=
  ⟨fun _ => 0, fun i => if hi : i.val < 5 then fiveWords h desc addr Rv Bv ⟨i.val, hi⟩ else [], fun _ => 0, false⟩

theorem initHT_conv (tK tE tH : ℕ) (h desc addr : List Bool) (Rv Bv : ℕ) (j : Fin 135) :
    (initHT tK tE tH h desc addr Rv Bv).st (convMap tK tE tH j) = CloseoutCaseTwo.Cold.input h desc addr Rv Bv j := by
  unfold initHT CloseoutCaseTwo.Cold.input
  simp only [convMap_val]
  by_cases hj : j.val < 5
  · simp only [hj, if_true, dif_pos hj]
    have : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 := by omega
    rcases this with e | e | e | e | e <;>
      simp [e, fiveWords, Fin.ext_iff]
  · simp only [hj, if_false]
    rw [dif_neg (by omega)]
    have h0 : j ≠ 0 := fun e => hj (by rw [e]; decide)
    have h1 : j ≠ 1 := fun e => hj (by rw [e]; decide)
    have h2 : j ≠ 2 := fun e => hj (by rw [e]; decide)
    have h3 : j ≠ 3 := fun e => hj (by rw [e]; decide)
    have h4 : j ≠ 4 := fun e => hj (by rw [e]; decide)
    simp [h0, h1, h2, h3, h4]

open NearCubicWires.OuterPCPRecovery (canonicalBoundedCircuitDescription)
open NearCubicWires.RepairOrdinary.RadixSemantics (value)

theorem binKCost_le' (L c : ℕ) (h : 2 ^ L ≤ c) : LitDecode.binKCost L ≤ 100 * (c + 1) ^ 2 := by
  have hL : L < 2 ^ L := Nat.lt_two_pow_self
  unfold LitDecode.binKCost
  have h1 : L * (50 * 2 ^ L + 32) ≤ c * (50 * c + 32) := Nat.mul_le_mul (by omega) (by omega)
  nlinarith

theorem frontCost_le' (S c : ℕ) (h : S ≤ c) : ClauseFront.frontCost S ≤ 10000 * (c + 1) ^ 2 := by
  unfold ClauseFront.frontCost
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

/-- **The main branch.** -/
theorem main_exec {s : GateSources} {P : ThreeQueryPCPP} {g : Transfer.GateParams}
    (cx : Setup.CompFull s P g) (pe ph : Program) (Ke ee Kh eh : ℕ)
    (hpe : ∀ m : MessageRequest, ∃ out, ClockJoin.ReadyRun pe.machine (Ke * ((messageWord m).length + 1) ^ ee)
      (pe.inputTapes (messageWord m)) out ∧ out pe.outputTape = FramedSim.pairs (List.ofFn (P.code.enc m.1 m.2.val)))
    (hph : ∀ a : AcceptedCircuitInput, ∃ out, ClockJoin.ReadyRun ph.machine
      (Kh * ((acceptedCircuitInputWord a).length + 1) ^ eh) (ph.inputTapes (acceptedCircuitInputWord a)) out ∧
      out ph.outputTape = FramedSim.pairs (List.ofFn (P.honest a)))
    (cd pl cap : ℕ) {N : ℕ} (x : BitInput N)
    (Bs c : BooleanCircuit (Outer.width s.mw (g.sv s) N)) (hq : 2 ≤ Outer.width s.mw (g.sv s) N)
    (Bv : ℕ) (hc : c.size ≤ Bv) (xp : BitInput (Outer.width s.mw (g.sv s) N))
    (hacc : (substitutedAt s g x ⟨Bs, c⟩).D.eval xp = true) (wa wj r : List Bool)
    (ha : wa.length = (((Outer.width s.mw (g.sv s) N) + 2) ^ cd - 1).size) (hj : wj.length = pl)
    (σ : WState (NS cx.t pe.tapeCount ph.tapeCount) 64)
    (hσ : σ = fitState (initHT cx.t pe.tapeCount ph.tapeCount (mwWord s g N Bs)
      (RepairOrdinary.frame (canonicalBoundedCircuitDescription Bv c))
      (RepairOrdinary.frame (List.ofFn xp ++ wa ++ wj ++ r)) (Outer.width s.mw (g.sv s) N) Bv)
      (Outer.width s.mw (g.sv s) N) (List.ofFn xp ++ wa ++ wj ++ r).length cd pl)
    (hcap : 2 * (PCPPNative.descriptor c).length + 8 * Outer.width s.mw (g.sv s) N + 8 +
      (8 * (Outer.width s.mw (g.sv s) N + P.code.length (Outer.width s.mw (g.sv s) N)) +
        4 * (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩)).word.length +
        2 * (P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩))).proofBits + 16) +
      (2 * 2 ^ wa.length + 2 * 2 ^ pl + 4 * (Outer.width s.mw (g.sv s) N + wa.length + pl) + 4 +
        16 * ((P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩))).word.length + 2 ^ wa.length +
          (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩)).n +
          (P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩))).proofBits + 2) +
        4 * ((checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩)).n +
          (P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩))).proofBits +
          3 * ((checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩)).n +
            (P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩))).proofBits)) + 2 ^ pl + 20) ≤ cap) :
    ∃ τ n', WXExec cap (.seq (headW cx pe ph) (tailW cx.t pe.tapeCount ph.tapeCount pl cx.wOut)) σ τ n' ∧
      n' ≤ CloseoutCaseTwo.Cold.budget Bv c +
        cx.C * ((mwWord s g N Bs).length + (PCPPNative.descriptor c).length + Outer.width s.mw (g.sv s) N + 1) ^ cx.e +
        Ke * ((messageWord ⟨(substitutedAt s g x ⟨Bs, c⟩).n, ⟨xp, hq⟩⟩).length + 1) ^ ee +
        Kh * ((acceptedCircuitInputWord (acceptedInput P.code (substitutedAt s g x ⟨Bs, c⟩) xp hacc)).length + 1) ^ eh
        + 30000 * (cap + 1) ^ 2 ∧
      τ.st (OUT cx.t pe.tapeCount ph.tapeCount) = outWord (TableSem.tableBit
        (P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩)))
        (List.ofFn (sysEnc P.code (substitutedAt s g x ⟨Bs, c⟩).n xp) ++
          List.ofFn (P.honest (acceptedInput P.code (substitutedAt s g x ⟨Bs, c⟩) xp hacc))) (value wa) (value wj)) := by
  set σ0 := initHT cx.t pe.tapeCount ph.tapeCount (mwWord s g N Bs)
    (RepairOrdinary.frame (canonicalBoundedCircuitDescription Bv c))
    (RepairOrdinary.frame (List.ofFn xp ++ wa ++ wj ++ r)) (Outer.width s.mw (g.sv s) N) Bv with hσ0
  have hst : ∀ y, σ.st y = σ0.st y := fun y => by rw [hσ]; simp [fitState]
  have hsh : ∀ y, σ.sh y = 0 := fun y => by rw [hσ]; simp [fitState, hσ0, initHT]
  have hlo : ∀ y : Fin (NS cx.t pe.tapeCount ph.tapeCount + 1), 5 ≤ y.val → σ.st y = [] := by
    intro y hy; rw [hst, hσ0]; simp [initHT]; omega
  have hval : ∀ q : Fin 64, q ∉ [rR, rC2, pX, rCL, rS, rS2, rF] → σ.val q = 0 := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
    rw [hσ]; simp [fitState, Function.update_apply, q1, q2, q3, q4, q5, q6, q7, hσ0, initHT]
  have hRσ : σ.val rR = Outer.width s.mw (g.sv s) N := by rw [hσ]; simp (config := { decide := true }) [fitState, Function.update_apply]
  have hCLσ : σ.val rCL = wa.length := by
    rw [hσ, ha]; simp (config := { decide := true }) [fitState, Function.update_apply]
  have hxl : (List.ofFn xp).length = Outer.width s.mw (g.sv s) N := List.length_ofFn
  -- head A
  obtain ⟨τA, eA, hcA, hchA, hwA, hwhA, hEIA, hEIhA, hP2A, hP2hA, hvA, hclA, hkA⟩ :=
    headA_exec cx pe.tapeCount ph.tapeCount cap x Bs c hq Bv hc (List.ofFn xp) (wa ++ wj ++ r) hxl σ
      (fun j => by rw [hst, hσ0, initHT_conv]; simp [List.append_assoc])
      (fun j => hsh _) (hlo _ (by simp only [DS_val, EI_val, AS_val, HI_val, OUT_val, bK_val, bE_val, bH_val]; omega)) (hsh _)
      (fun j => ⟨hlo _ (by simp only [bK_val]; omega), hsh _⟩) (hlo _ (by simp only [DS_val, EI_val, AS_val, HI_val, OUT_val, bK_val, bE_val, bH_val]; omega)) (hsh _) hRσ
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact hval _ (by decide))
      (by omega)
  have nd := cx.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at nd
  obtain ⟨_, _, ⟨hcw, _, _, _⟩, -, -, -⟩ := nd
  have keepA : ∀ y : Fin (NS cx.t pe.tapeCount ph.tapeCount + 1), 145 + cx.t ≤ y.val → τA.st y = [] ∧ τA.sh y = 0 := by
    intro y hy
    have h1 : ∀ j, convMap cx.t pe.tapeCount ph.tapeCount j ≠ y := by
      intro j e; have := congrArg Fin.val e; rw [convMap_val] at this; split_ifs at this <;> omega
    have h2 : ∀ j, compMap cx.t pe.tapeCount ph.tapeCount cx.cIn cx.dIn j ≠ y := by
      intro j e; have hv := congrArg Fin.val e; rw [compMap_val] at hv; have hj := j.isLt
      split_ifs at hv <;> omega
    have h3 : y ≠ DS cx.t pe.tapeCount ph.tapeCount := fin_ne (by simp; omega)
    have h4 : y ≠ EI cx.t pe.tapeCount ph.tapeCount := fin_ne (by simp; omega)
    rw [(hkA y h1 h2 h3 h4).1, (hkA y h1 h2 h3 h4).2]; exact ⟨hlo _ (by omega), hsh _⟩
  have keepA' : ∀ y : Fin (NS cx.t pe.tapeCount ph.tapeCount + 1), y.val = 7 ∨ y.val = 8 ∨ y.val = 9 →
      τA.st y = [] ∧ τA.sh y = 0 := by
    intro y hy
    have h1 : ∀ j, convMap cx.t pe.tapeCount ph.tapeCount j ≠ y := by
      intro j e; have := congrArg Fin.val e; rw [convMap_val] at this; split_ifs at this <;> omega
    have h2 : ∀ j, compMap cx.t pe.tapeCount ph.tapeCount cx.cIn cx.dIn j ≠ y := by
      intro j e; have hv := congrArg Fin.val e; rw [compMap_val] at hv
      split_ifs at hv <;> omega
    have h3 : y ≠ DS cx.t pe.tapeCount ph.tapeCount := fin_ne (by simp; omega)
    have h4 : y ≠ EI cx.t pe.tapeCount ph.tapeCount := fin_ne (by simp; omega)
    rw [(hkA y h1 h2 h3 h4).1, (hkA y h1 h2 h3 h4).2]; exact ⟨hlo _ (by omega), hsh _⟩
  have hvA' : ∀ q : Fin 64, q ≠ scC → τA.val q = σ.val q := fun q hq => by rw [hvA]; simp [Function.update_apply, hq]
  -- head B
  have hDn : (substitutedAt s g x ⟨Bs, c⟩).n = Outer.width s.mw (g.sv s) N := rfl
  obtain ⟨τB, eB, hASB, hAShB, hOPB, hWB, hWhB, hP2B, hP2hB, hOB, hOhB, hvB⟩ :=
    headB_exec cx.t cap P pe ph Ke ee Kh eh hpe hph (substitutedAt s g x ⟨Bs, c⟩) hq xp hacc (wa ++ wj ++ r) cx.cOut
      cx.wOut hcw τA (by rw [hvA' _ (by decide), hRσ]; rfl) hEIA hEIhA
      (fun j => keepA _ (by simp only [bE_val]; omega)) (fun j => keepA _ (by simp only [bH_val]; omega))
      hP2A hP2hA (keepA' _ (by simp)).1 (keepA' _ (by simp)).2 (keepA' _ (by simp)).1 (keepA' _ (by simp)).2 hcA hchA
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hvA' _ (by decide)] <;> exact hval _ (by decide))
      (by rw [hDn]; omega)
  -- tail
  have hvB' : ∀ q : Fin 64, q ∉ [opAS, scE, scK, scAS, scH, scC] → τB.val q = σ.val q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [hvB q (by simp [hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1]), hvA' q hq.2.2.2.2.2]
  obtain ⟨τ, eT, hT⟩ := tail_exec cx.t pe.tapeCount ph.tapeCount pl cap τB cx.wOut
    (P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩)))
    (List.ofFn (sysEnc P.code (substitutedAt s g x ⟨Bs, c⟩).n xp) ++
      List.ofFn (P.honest (acceptedInput P.code (substitutedAt s g x ⟨Bs, c⟩) xp hacc)))
    (List.ofFn xp) wa wj r (Outer.width s.mw (g.sv s) N) wa.length hxl rfl hj
    (by rw [hP2B, hP2A]; simp [List.append_assoc]) hP2hB
    (by rw [hvB' _ (by decide), hRσ]) (by rw [hvB' _ (by decide), hCLσ])
    (by rw [hWB, hwA]) (by rw [hWhB, hwhA]) hASB hAShB hOPB
    (by rw [hOB]; exact (keepA' _ (by simp)).1) (by rw [hOhB]; exact (keepA' _ (by simp)).2)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hvB' _ (by decide)] <;>
        exact hval _ (by decide))
    (fun i => by
      have hi := i.isLt
      rw [hvB' _ (by simp; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (apply fin_ne; simp; omega))]
      exact hval _ (by simp; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (apply fin_ne; simp; omega)))
    (fun cc t => ClauseFront.litVar_lt _)
    (by have hal : (List.ofFn (sysEnc P.code (substitutedAt s g x ⟨Bs, c⟩).n xp) ++
          List.ofFn (P.honest (acceptedInput P.code (substitutedAt s g x ⟨Bs, c⟩) xp hacc))).length =
          (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩)).n +
          (P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩))).proofBits := by
          simp only [List.length_append, List.length_ofFn]; rfl
        rw [hal]; omega)
  refine ⟨τ, _, WXExec.seq (WXExec.seq eA eB) eT, ?_, hT⟩
  have hva : value wa < 2 ^ wa.length := RadixSemantics.value_lt wa
  have hvj : value wj < 2 ^ pl := hj ▸ RadixSemantics.value_lt wj
  have hc1 := binKCost_le' wa.length cap (by omega)
  have hc2 := binKCost_le' pl cap (by omega)
  have hc3 := frontCost_le' ((P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩))).word.length + value wa +
    (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩)).n +
    (P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩))).proofBits) cap (by omega)
  have hR1 : (Outer.width s.mw (g.sv s) N + 1) * (Outer.width s.mw (g.sv s) N + 1) ≤
      (cap + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have hq1 : cap + 1 ≤ (cap + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hR2 : 100 * (Outer.width s.mw (g.sv s) N + 1) * (Outer.width s.mw (g.sv s) N + 1)
      ≤ 100 * (cap + 1) ^ 2 := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hR1
  have hal : (List.ofFn (sysEnc P.code (substitutedAt s g x ⟨Bs, c⟩).n xp) ++
      List.ofFn (P.honest (acceptedInput P.code (substitutedAt s g x ⟨Bs, c⟩) xp hacc))).length =
      (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩)).n +
      (P.output (checkedCircuit P.code (substitutedAt s g x ⟨Bs, c⟩))).proofBits := by
    simp only [List.length_append, List.length_ofFn]; rfl
  have hD2 : P.code.length (substitutedAt s g x ⟨Bs, c⟩).n =
      P.code.length (Outer.width s.mw (g.sv s) N) := rfl
  omega

end NearCubicGates.Close.Recovery.HT
