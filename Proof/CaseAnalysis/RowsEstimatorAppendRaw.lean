import Proof.CaseAnalysis.RowsEstimatorWhole
import Proof.PCP.ProjectionNormalizationClauseCopy

/-! Append the existing six-field scalar record using two existing fixed
three-field copies. The number of fields is in the finite control; there is
no supplied count stream or runtime record-length prepass. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.AppendRaw
open LocalBitMultitape RepairSource.ProjectionNormalization SignedSortKey
open CloseoutRowsEstimatorCoefficients CompetitorMonomialStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine := Composition.machine ClauseCopy.machine ClauseCopy.machine
def cfg {s : ℕ} (q : Fin s) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 s :=
  ClauseCopy.cfg q source pos out
def finalCode : Fin 18 := ClauseCopy.finalCode.natAdd 9
def leftFields (b : ℕ) (q : CompetitorValidity.Estimate) : SuffixScan.Clause :=
  ![binary (CompetitorRationalDecision.width b) q.positive,
    binary (CompetitorRationalDecision.width b) q.negative,
    binary (CompetitorRationalDecision.width b) q.denominator]
def rightFields (b count denominator : ℕ) : SuffixScan.Clause :=
  ![binary (CompetitorRationalDecision.width b) 0,binary b denominator,binary b count]

theorem source_eq (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) :
    Stream.recordWord b q count denominator=
      ClauseEquality.stream (leftFields b q)++ClauseEquality.stream (rightFields b count denominator):=by
  simp [Stream.recordWord,fieldStream,allFields,Stream.recordFields,
    leftFields,rightFields,ClauseEquality.stream,List.append_assoc]

theorem run (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) (pre suffix out : List Bool) :
    ∃ r,runFrom machine (20*b+27)
      (cfg machine.start (pre++Stream.recordWord b q count denominator++suffix) pre.length out)=some r ∧
      r.final=cfg finalCode (pre++Stream.recordWord b q count denominator++suffix)
        (pre.length+(Stream.recordWord b q count denominator).length)
        (out++Stream.recordWord b q count denominator) ∧ r.steps=20*b+27:=by
  let l:=ClauseEquality.stream (leftFields b q)
  let r:=ClauseEquality.stream (rightFields b count denominator)
  have hw:Stream.recordWord b q count denominator=l++r:=source_eq b q count denominator
  obtain ⟨first,hf,ff,fs⟩:=ClauseCopy.copy_run pre (leftFields b q) (r++suffix) out
  obtain ⟨last,hl,lf,ls⟩:=ClauseCopy.copy_run (pre++l) (rightFields b count denominator) suffix (out++l)
  have hi:Composition.restart first.final ClauseCopy.machine.start=
      ClauseCopy.cfg ClauseCopy.machine.start ((pre++l)++r++suffix) (pre++l).length (out++l):=by
    rw [ff]
    simp only [Composition.restart,ClauseCopy.cfg,List.append_assoc,List.length_append]
    rfl
  have hl':runFrom ClauseCopy.machine (r.length+2)
      (Composition.restart first.final ClauseCopy.machine.start)=some last:=by rw [hi];exact hl
  have whole:=Composition.run_join ClauseCopy.machine ClauseCopy.machine _ _ _ first last hf hl'
  have hlen:l.length+r.length=20*b+22:=by
    simpa only [hw,List.length_append] using Stream.record_length b q count denominator
  have ht:l.length+2+1+(r.length+2)=20*b+27:=by omega
  change runFrom machine (l.length+2+1+(r.length+2))
    (cfg machine.start (pre++l++(r++suffix)) pre.length out)=some _ at whole
  rw [ht] at whole
  refine ⟨Composition.joinedReceipt first last,?_,?_,?_⟩
  · simpa only [hw,List.append_assoc] using whole
  · change Composition.rightConfig 9 last.final=_
    rw [lf]
    simp only [cfg,ClauseCopy.cfg,Composition.rightConfig,finalCode,hw,List.append_assoc,List.length_append,Nat.add_assoc]
    rfl
  · change first.steps+1+last.steps=_
    rw [fs,ls]
    exact ht

theorem forward (i : Fin 2) : CursorRestore.NoLeft machine i :=
  CursorRestore.composition_forward _ _ _ (ClauseCopy.forward i) (ClauseCopy.forward i)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.AppendRaw
