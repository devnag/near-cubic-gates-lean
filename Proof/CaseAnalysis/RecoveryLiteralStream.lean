import Proof.CaseAnalysis.RecoveryLiteralPipeline

/-! One complete original streaming literal: paid scratch/operand reset,
actual source-field read and decode, then the original graph operation.
Every source cursor, scratch output and physical handoff is retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralStream
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition
open RecoveryBoundedLiteralPrepared (decoded)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def prepare (second : Bool):=RecoveryBoundedLiteralPipeline.prepare
  (RecoveryBoundedLiteralReset.machine second) RecoveryBoundedLiteralLoad.machine
noncomputable def machine (second : Bool):=RecoveryBoundedLiteralPipeline.machine
  (RecoveryBoundedLiteralReset.machine second) RecoveryBoundedLiteralLoad.machine (RecoveryBoundedLiteralDock.machine second)
def budget (second neg : Bool) (before : List ℕ) (ref node C : ℕ):=
  (2*C+4)+1+RecoveryBoundedLiteralLoad.budget before.length neg+1+
    RecoveryBoundedLiteral.budget second before ref node C

theorem stream_run (second neg : Bool) (H : Fin 71→ℕ) (A : Fin 71→List Bool)
    (before : List ℕ) (ref node W C L : ℕ) (out pre sourceTail refTail : List Bool)
    (hReset : ∀ j,H (RecoveryBoundedLiteralReset.slots second j)=0)
    (hBacking : A 22=List.replicate C true) (hClearLog : A 23=List.replicate (C+1) false)
    (hWork : ∀ j,(A (RecoveryBoundedLiteralReset.workSlots second j)).length ≤ C)
    (hCursor : H 70=pre.length)
    (hSource : A 70=pre++frame (RecoveryBoundedLiteralDriver.code before.length neg)++sourceTail)
    (hQuery : A 59=RecoveryBoundedClauseLookup.source before ref refTail)
    (hLog : A 43=List.replicate L false)
    (hLookup : ∀ j,H (RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseSelect.lookupSlots j))=0)
    (hGate : ∀ j,H (RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseGate.slots (RecoveryBoundedLiteral.kind second) j))=PCPPNativeClauseBank.heads out j)
    (aGate : ∀ j,RecoveryBoundedLiteralReset.output A second C
      (RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseGate.slots (RecoveryBoundedLiteral.kind second) j))=RecoveryBoundedUniversalGates.data 0 0 C out j)
    (hReplace : ∀ j,H (RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseReplace.slots second j))=0)
    (aReplace : ∀ j,RecoveryBoundedLiteralReset.output A second C
      (RecoveryBoundedLiteralDock.slots (RecoveryBoundedClauseReplace.slots second j))=RecoveryBoundedClauseReplace.data node 0 C 0 j)
    (hL : RecoveryBoundedClauseLookup.rawBudget before ref ≤ L)
    (hb : before.length ≤ W) (href : ref ≤ W) (hC : 16384*(W+1)^2 ≤ C) (hn : node+1 ≤ C) :
    let bits:=RecoveryBoundedLiteralDriver.code before.length neg
    let nextH:=RecoveryBoundedLiteralLoad.heads H (pre.length+2*bits.length+1)
    ∃ work r,runFrom (machine second) (budget second neg before ref node C)
      ⟨(machine second).start,H,A⟩=some r ∧
      r.steps ≤ budget second neg before ref node C ∧
      r.final.heads=RecoveryBoundedLiteralDock.heads second neg nextH ref out ∧
      r.final.tapes=RecoveryBoundedLiteralDock.output second neg
        (decoded (RecoveryBoundedLiteralReset.output A second C) bits C work) before ref node C out ∧
      work 6=ZeroPadding.pad C [neg] ∧
      work 9=ZeroPadding.pad C (RepairSource.VerifierDecoding.CompareMachine.word before.length) ∧
      (∀ j,(work j).length ≤ C) := by
  let bits:=RecoveryBoundedLiteralDriver.code before.length neg
  let clean:=RecoveryBoundedLiteralReset.output A second C
  let nextH:=RecoveryBoundedLiteralLoad.heads H (pre.length+2*bits.length+1)
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedLiteralReset.reset_run second H A C hReset hBacking hClearLog hWork
  have hDriver : ∀ j,H (RecoveryBoundedLiteralLoad.driverSlots j)=0 := by
    intro j
    have h:=hReset (((j.castAdd 3).castAdd 1).castAdd 1)
    fin_cases j <;> cases second <;> exact h
  obtain ⟨work,q,qr,qs,qh,qt,qflag,qindex,qwork⟩:=RecoveryBoundedLiteralLoad.decode_run H clean before.length W C neg pre sourceTail
    (by intro j;fin_cases j
        · exact hCursor
        · exact hDriver 0
        · exact hReset 15)
    (by intro j;fin_cases j
        · change RecoveryBoundedLiteralReset.output A second C 70=_
          rw [RecoveryBoundedLiteralPrepared.clean_other A second C 70 (by cases second <;> decide)]
          exact hSource
        · exact RecoveryBoundedLiteralPrepared.clean_driver A second C 0
        · change RecoveryBoundedLiteralReset.output A second C 23=_
          rw [RecoveryBoundedLiteralPrepared.clean_other A second C 23 (by cases second <;> decide)]
          exact hClearLog)
    hDriver (RecoveryBoundedLiteralPrepared.clean_driver A second C) hb hC
  have qr' : runFrom RecoveryBoundedLiteralLoad.machine (RecoveryBoundedLiteralLoad.budget before.length neg)
      (restart p.final RecoveryBoundedLiteralLoad.machine.start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  obtain ⟨s,sr,ss,sh,st⟩:=RecoveryBoundedLiteralDock.literal_run second neg nextH (decoded clean bits C work)
    before ref node W C L out refTail
    (by intro j
        dsimp only [nextH]
        rw [RecoveryBoundedLiteralPrepared.head_old _ _ _ (by fin_cases j <;> decide)]
        exact hLookup j)
    (RecoveryBoundedLiteralPrepared.lookup A second C L before ref refTail bits work hQuery hLog qindex)
    (by intro j
        dsimp only [nextH]
        rw [RecoveryBoundedLiteralPrepared.head_old _ _ _ (by cases second <;> fin_cases j <;> decide)]
        exact hGate j)
    (by intro j
        rw [RecoveryBoundedLiteralPrepared.gate_unchanged]
        exact aGate j)
    (by intro j
        dsimp only [nextH]
        rw [RecoveryBoundedLiteralPrepared.head_old _ _ _ (by cases second <;> fin_cases j <;> decide)]
        exact hReplace j)
    (by intro j
        rw [RecoveryBoundedLiteralPrepared.replace_unchanged]
        exact aReplace j)
    (by
      have h48 : H 48=0:=hDriver 6
      change readTapeBit (decoded clean bits C work (RecoveryBoundedLiteralLoad.driverSlots 6))
        (RecoveryBoundedLiteralLoad.heads H (pre.length+2*bits.length+1) 48)=neg
      rw [RecoveryBoundedLiteralPrepared.decoded_driver,qflag,
        RecoveryBoundedLiteralPrepared.head_old _ _ _ (by decide),h48,ZeroPadding.read_pad]
      rfl)
    hL href hC hn
  have sr' : runFrom (RecoveryBoundedLiteralDock.machine second) (RecoveryBoundedLiteral.budget second before ref node C)
      (restart (joinedReceipt p q).final (RecoveryBoundedLiteralDock.machine second).start)=some s := by
    change runFrom _ _ ⟨_,q.final.heads,q.final.tapes⟩=some s
    rw [qh,qt]
    exact sr
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedLiteralPipeline.pipeline_run
    (RecoveryBoundedLiteralReset.machine second) RecoveryBoundedLiteralLoad.machine (RecoveryBoundedLiteralDock.machine second)
    H A (2*C+4) (RecoveryBoundedLiteralLoad.budget before.length neg)
    (RecoveryBoundedLiteral.budget second before ref node C) p q s pr qr' sr'
  refine ⟨work,r,rr,?_,rh.trans sh,rt.trans st,qflag,qindex,qwork⟩
  rw [rs]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralStream
