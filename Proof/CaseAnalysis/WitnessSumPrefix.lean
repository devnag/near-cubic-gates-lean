import Proof.CaseAnalysis.WitnessSumHeader
import Proof.CaseAnalysis.WitnessSumControl

/-! One raw sum header produces its actual native term-count record.
Rejected headers stop before the record append; the ordered term stream
and actual repeat driver come from the same canonical traversal. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumPrefix
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def first := TapeEmbedding.machine 18 SumGuard.machine
def machine := RecoveryGatedSequence.machine first SumCountStream.machine 499
def budget (bits arityBits : List Bool) (T : ℕ) :=
  SumGuard.budget bits arityBits T+CloseoutRowsCircuitCountHeader.budget (SumFields.count bits)+2

theorem prefix_run (H T : ℕ) (bits arityBits out : List Bool)
    (hraw : 2*bits.length+1 ≤ H) (hbudget : SumGuard.budget bits arityBits T+1 ≤ H)
    (happend : SumHeader.flag bits arityBits T=true → EquationHeaderAppend.budget (SumFields.count bits)+1 ≤ H) :
    ∃ r,runFrom machine (budget bits arityBits T)
      (SumControl.start first SumCountStream.machine
        ⟨first.start,SumCountStream.heads out,
          SumCountStream.input H (SumHeader.input H bits arityBits T) out⟩)=some r ∧
      r.steps ≤ budget bits arityBits T ∧ r.final.heads 499=0 ∧
      r.final.tapes 499=[SumHeader.flag bits arityBits T] ∧
      (SumHeader.flag bits arityBits T=true →
        r.final.heads=SumCountStream.heads (out++RepairRepresentation.natWord (SumFields.count bits)) ∧
        r.final.tapes 501=frame arityBits ∧ r.final.tapes 502=List.replicate T true ∧
        r.final.tapes 357=(SumHeader.words bits).flatMap frame++SumHeader.tail H bits ∧
        r.final.tapes 368=ZeroPadding.pad H (CompareMachine.word (SumFields.count bits)) ∧
        r.final.tapes 526=out++RepairRepresentation.natWord (SumFields.count bits) ∧
        (∀ i : Fin 528,i≠501 → i≠502 → i≠526 → (r.final.tapes i).length ≤ H)) := by
  obtain ⟨bank,⟨base,hbase,bt,bh,bs⟩,arity,cap,stream,count,rawCount,flag,support⟩ :=
    SumHeader.header_run H T bits arityBits hraw hbudget
  let reader := TapeEmbedding.receipt (SumCountStream.extraHeads out) (SumCountStream.extra H out) base
  have readRun := TapeEmbedding.run_embed SumGuard.machine
    (SumCountStream.extraHeads out) (SumCountStream.extra H out) _ _ base hbase
  have readHeads : reader.final.heads=SumCountStream.heads out := by
    change Fin.addCases (m:=510) (n:=18) (motive:=fun _=>ℕ) base.final.heads (SumCountStream.extraHeads out)=_
    rw [funext bh];rfl
  have readTapes : reader.final.tapes=SumCountStream.input H bank out := by
    change Fin.addCases (m:=510) (n:=18) (motive:=fun _=>List Bool) base.final.tapes (SumCountStream.extra H out)=_
    rw [bt];rfl
  have headFlag : reader.final.heads 499=0 := by rw [readHeads];rfl
  have tapeFlag : reader.final.tapes 499=[SumHeader.flag bits arityBits T] := by rw [readTapes];exact flag
  cases hp : SumHeader.flag bits arityBits T with
  | false =>
    obtain ⟨r,run,rs,rh,rt⟩ := SumControl.reject_run first SumCountStream.machine 499
      (SumGuard.budget bits arityBits T) _ reader readRun headFlag (by rw [tapeFlag,hp])
    have bound : SumGuard.budget bits arityBits T+1 ≤ budget bits arityBits T := by unfold budget;omega
    have more := runFrom_moreFuel machine _ (budget bits arityBits T-(SumGuard.budget bits arityBits T+1)) _ r run
    rw [Nat.add_sub_of_le bound] at more
    refine ⟨r,more,rs.trans bound,(by rw [rh];exact headFlag),(by rw [rt,tapeFlag,hp]),?_⟩
    intro impossible;cases impossible
  | true =>
    have hcount : SumFields.count bits ≤ H := by
      have h := support 504 (by decide) (by decide)
      rw [rawCount,ZeroPadding.pad_length,List.length_replicate] at h
      exact (Nat.le_max_right H _).trans h
    obtain ⟨last,lastRun,lastSteps,lastHeads,lastWord,_copy,_log,lastFlag,old,localBound⟩ :=
      SumCountStream.append_run H bits out bank rawCount (by rw [flag,hp]) hcount (happend hp)
    have tailRun : runFrom SumCountStream.machine (CloseoutRowsCircuitCountHeader.budget (SumFields.count bits))
        (RecoveryCalls.restarted SumCountStream.machine reader.final.heads reader.final.tapes)=some last := by
      rw [readHeads,readTapes];exact lastRun
    obtain ⟨r,run,rs,rh,rt⟩ := SumControl.accept_run first SumCountStream.machine 499
      (SumGuard.budget bits arityBits T) (CloseoutRowsCircuitCountHeader.budget (SumFields.count bits))
      _ reader last readRun headFlag (by rw [tapeFlag,hp]) tailRun
    refine ⟨r,run,rs,?_,?_,?_⟩
    · rw [rh,lastHeads];rfl
    · rw [rt,lastFlag]
    · intro _
      refine ⟨rh.trans lastHeads,?_,?_,?_,?_,by rw [rt];exact lastWord,?_⟩
      · rw [rt];exact (old 501 (by decide)).trans arity
      · rw [rt];exact (old 502 (by decide)).trans cap
      · rw [rt];exact (old 357 (by decide)).trans stream
      · rw [rt];exact (old 368 (by decide)).trans count
      · intro i
        rw [rt]
        refine Fin.addCases (m:=510) (n:=18) ?_ ?_ i
        · intro j h501 h502 _
          by_cases hj : j=504
          · subst j;exact localBound 0 (by decide)
          · rw [old j hj]
            exact support j (by intro h;subst j;exact h501 rfl) (by intro h;subst j;exact h502 rfl)
        · intro j _ _ h526
          have hn : j.val≠16 := by intro h;apply h526;exact Fin.ext (by change 510+j.val=526;omega)
          let k : Fin 19:=⟨j.val+1,by omega⟩
          have hk : k≠17 := by intro h;apply hn;have hv:=congrArg Fin.val h;dsimp only [k] at hv;omega
          have he : SumCountStream.slots k=j.natAdd 510 := by
            fin_cases j <;> rfl
          rw [←he]
          exact localBound k hk

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SumPrefix
