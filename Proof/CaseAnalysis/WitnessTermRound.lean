import Proof.CaseAnalysis.WitnessTermCircuitDock

/-! One literal term round. A failed coefficient never enters the circuit
worker, mass update or retained-record emission. A successful commit alone
enters the private circuit-bank reset. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
open LocalBitMultitape RecoveryRootRound RecoveryExecution CanonicalWitnessCodec RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def begin := TapeEmbedding.machine 1705 TermBegin.machine
noncomputable def ending := TapeEmbedding.machine 1705 TermExit.machine
def flagSlots : Fin 2 → Fin 2532 := ![2527,719]
noncomputable def foldFlag := RecoveryFocus.machine flagSlots CloseoutRowsIntegerRound.flagMachine
private def stateCount {s : ℕ} (_ : Machine 2532 s) := s
noncomputable def sizes (s : ℕ) : Fin 5 → ℕ := ![stateCount begin,s,2,stateCount ending,4]
noncomputable def programs {s : ℕ} (circuit : Machine 1703 s) : (j : Fin 5) → Machine 2532 (sizes s j)
  | 0 => begin
  | 1 => RecoveryFocus.machine TermCircuitDock.slots circuit
  | 2 => foldFlag
  | 3 => ending
  | 4 => TermCircuitReset.machine
def next {s : ℕ} (j : Fin 5) (_ : Fin (sizes s j)) (bits : Fin 2532 → Bool) : Option (Fin 5) :=
  if j.val=0 then if bits 719 then some 1 else some 3
  else if j.val=1 then some 2 else if j.val=2 then some 3
  else if j.val=3 then if bits 724 then some 4 else none else none
noncomputable def machine {s : ℕ} (circuit : Machine 1703 s) :=
  RecoveryCalls.machine (sizes s) (programs circuit) 0 next

def heads (position : ℕ) (out : List Bool) (extra : Fin 1705 → ℕ) : Fin 2532 → ℕ :=
  Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>ℕ) (TermCommit.heads position out) extra
def data (P : ℕ) (terms : Fin 725 → List Bool) (ambient : Fin 94 → List Bool)
    (out : List Bool) (extra : Fin 1705 → List Bool) : Fin 2532 → List Bool :=
  Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>List Bool) (TermCommit.data P terms ambient out) extra

theorem coefficient_reject_run {s : ℕ} (circuit : Machine 1703 s)
    (P C : ℕ) (bits pre tail out : List Bool) (ambient : Fin 94 → List Bool)
    (extraHeads : Fin 1705 → ℕ) (extraTapes : Fin 1705 → List Bool)
    (hC : 0 < C) (hbudget : TermCoefficient.budget C bits+1 ≤ P)
    (hraw : 2*bits.length+1 ≤ P) (hb : natBitLength C ≤ P)
    (hbad : ¬(PairHeader.valid bits ∧ ∃ q,
      decodeCanonicalRational (value (TermCoefficient.coefficientCode bits))=some q ∧
        natBitLength q.num.natAbs ≤ natBitLength C ∧ natBitLength q.den ≤ natBitLength C)) :
    ∃ result,runFrom (machine circuit) (TermRead.budget C bits+2*P+9)
      ⟨(machine circuit).start,heads pre.length out extraHeads,
        data P (TermRead.data P (natBitLength C) [] (pre++frame bits++tail) true) ambient out extraTapes⟩
      =some result ∧ result.steps ≤ TermRead.budget C bits+2*P+9 ∧
      result.final.heads 724=0 ∧ result.final.tapes 724=[false] := by
  let source := pre++frame bits++tail
  let position := pre.length+2*bits.length+1
  obtain ⟨terms,base,hr,rs,rh,rt,hbound,hwidth,hextra,_hcir,hflag,_hvalues,_hsign⟩ :=
    TermBegin.read_run P C bits pre tail out true ambient hC hbudget hraw hb
  have hf : readTapeBit (terms 719) 0=false := by
    cases he : readTapeBit (terms 719) 0
    · rfl
    · exact (hbad (hflag.mp he)).elim
  let first := TapeEmbedding.receipt extraHeads extraTapes base
  have firstRun := TapeEmbedding.run_embed TermBegin.machine extraHeads extraTapes _ _ base hr
  have firstHeads : first.final.heads=heads position out extraHeads := by
    change Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>ℕ) base.final.heads extraHeads=_
    rw [rh];rfl
  have firstTapes : first.final.tapes=data P terms ambient out extraTapes := by
    change Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>List Bool) base.final.tapes extraTapes=_
    rw [rt];rfl
  have firstFlag : first.final.scanned 719=false := by
    change readTapeBit (first.final.tapes 719) (first.final.heads 719)=false
    rw [firstHeads,firstTapes]
    exact hf
  obtain ⟨u,hu,initial⟩ := call_receipt (sizes s) (programs circuit) 0 next 0 3
    (TermRead.budget C bits) _ first firstRun (by
      change (if first.final.scanned 719 then some (1 : Fin 5) else some 3)=some 3
      rw [firstFlag];rfl)
  obtain ⟨last,hl,ls,lh,lt⟩ := TermExit.reject_run P (natBitLength C) position source out true terms ambient
    (by omega) hf hbound hwidth hextra
  let final := TapeEmbedding.receipt extraHeads extraTapes last
  have finalRun := TapeEmbedding.run_embed TermExit.machine extraHeads extraTapes _ _ last hl
  have finalHeads : final.final.heads=heads position out extraHeads := by
    change Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>ℕ) last.final.heads extraHeads=_
    rw [lh];rfl
  have finalTapes : final.final.tapes=data P (TermRead.data P (natBitLength C) [] source false) ambient out extraTapes := by
    change Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>List Bool) last.final.tapes extraTapes=_
    rw [lt];rfl
  have finalFlag : final.final.scanned 724=false := by
    change readTapeBit (final.final.tapes 724) (final.final.heads 724)=false
    rw [finalHeads,finalTapes]
    rfl
  rw [firstHeads,firstTapes] at initial
  obtain ⟨v,hv,terminal⟩ := stop_receipt (sizes s) (programs circuit) 0 next 3 (2*P+7)
    _ final finalRun (by
      change (if final.final.scanned 724 then some (4 : Fin 5) else none)=none
      rw [finalFlag];rfl)
  obtain ⟨result,run,rfinal,steps⟩ := (initial.trans terminal).run (by
    simp only [RecoveryCalls.machine,RecoveryCalls.stopped,Equiv.symm_apply_apply,Option.isNone_none])
  have bound : u+v ≤ TermRead.budget C bits+2*P+9 := by omega
  have more := runFrom_moreFuel (machine circuit) (u+v) (TermRead.budget C bits+2*P+9-(u+v)) _ result run
  rw [Nat.add_sub_of_le bound] at more
  refine ⟨result,more,steps.le.trans bound,?_,?_⟩
  · rw [rfinal]
    change final.final.heads 724=0
    rw [finalHeads];rfl
  · rw [rfinal]
    change final.final.tapes 724=[false]
    rw [finalTapes];rfl

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
