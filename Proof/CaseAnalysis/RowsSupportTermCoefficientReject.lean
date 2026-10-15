import Proof.CaseAnalysis.RowsSupportTermReject
import Proof.CaseAnalysis.RowsSupportTermRun

/-! The rejected coefficient takes the original reader-to-exit path in the
strengthened controller. Its new support tape stays outside both calls. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
open LocalBitMultitape RecoveryRootRound RecoveryExecution CanonicalWitnessCodec RadixSemantics
open CloseoutWitness
open CloseoutWitness.TermRound (heads data)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem coefficient_reject_run {s : ℕ} (circuit : Machine 1704 s)
    (P C : ℕ) (bits pre tail out : List Bool) (ambient : Fin 94 → List Bool)
    (extraHeads : Fin 1705 → ℕ) (extraTapes : Fin 1705 → List Bool)
    (supports : List Bool)
    (hC : 0 < C) (hbudget : TermCoefficient.budget C bits+1 ≤ P)
    (hraw : 2*bits.length+1 ≤ P) (hb : natBitLength C ≤ P)
    (hbad : ¬(PairHeader.valid bits ∧ ∃ q,
      decodeCanonicalRational (value (TermCoefficient.coefficientCode bits))=some q ∧
        natBitLength q.num.natAbs ≤ natBitLength C ∧ natBitLength q.den ≤ natBitLength C)) :
    ∃ result,runFrom (machine circuit) (TermRead.budget C bits+2*P+9)
      ⟨(machine circuit).start,lift (heads pre.length out extraHeads) supports.length,
        lift (data P (TermRead.data P (natBitLength C) [] (pre++frame bits++tail) true) ambient out extraTapes) supports⟩
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
  let oldFirst := TapeEmbedding.receipt extraHeads extraTapes base
  let first := TapeEmbedding.receipt (fun _ : Fin 1=>supports.length) (fun _=>supports) oldFirst
  have oldFirstRun := TapeEmbedding.run_embed TermBegin.machine extraHeads extraTapes _ _ base hr
  have firstRun := TapeEmbedding.run_embed TermRound.begin (fun _ : Fin 1=>supports.length) (fun _=>supports) _ _ oldFirst oldFirstRun
  have firstHeads : first.final.heads=lift (heads position out extraHeads) supports.length := by
    change lift (Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>ℕ) base.final.heads extraHeads) supports.length=_
    rw [rh];rfl
  have firstTapes : first.final.tapes=lift (data P terms ambient out extraTapes) supports := by
    change lift (Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>List Bool) base.final.tapes extraTapes) supports=_
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
  let oldFinal := TapeEmbedding.receipt extraHeads extraTapes last
  let final := TapeEmbedding.receipt (fun _ : Fin 1=>supports.length) (fun _=>supports) oldFinal
  have oldFinalRun := TapeEmbedding.run_embed TermExit.machine extraHeads extraTapes _ _ last hl
  have finalRun := TapeEmbedding.run_embed TermRound.ending (fun _ : Fin 1=>supports.length) (fun _=>supports) _ _ oldFinal oldFinalRun
  have finalHeads : final.final.heads=lift (heads position out extraHeads) supports.length := by
    change lift (Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>ℕ) last.final.heads extraHeads) supports.length=_
    rw [lh];rfl
  have finalTapes : final.final.tapes=lift (data P (TermRead.data P (natBitLength C) [] source false) ambient out extraTapes) supports := by
    change lift (Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>List Bool) last.final.tapes extraTapes) supports=_
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

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
