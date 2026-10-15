import Proof.CaseAnalysis.RecoveryFixedRowsPadded
import Proof.CaseAnalysis.RecoveryGrammarAfter

/-! Reuse the checked save/count/erase/reload continuation under the
original projector and full randomness driver. Their actual tapes and
heads are retained; stack padding is carried through the same worker. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedFixedContinue
open LocalBitMultitape Composition RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (P : ℕ) (i : Fin 78):=if i=74 then P else 0
def padded (P : ℕ) (A : Fin 78→List Bool) (i : Fin 78):=ZeroPadding.pad (capacity P i) (A i)
def data (P : ℕ) (A : Fin 78→List Bool) (extra : Fin 38→List Bool) : Fin 116→List Bool:=
  Fin.addCases (m:=78) (n:=38) (motive:=fun _=>List Bool) (padded P A) extra
def heads (out stack : List Bool) (extra : Fin 38→ℕ) : Fin 116→ℕ:=
  Fin.addCases (m:=78) (n:=38) (motive:=fun _=>ℕ) (RecoveryBoundedGrammarWorker.heads out stack) extra
noncomputable def machine:=TapeEmbedding.machine 38 RecoveryBoundedGrammarAfter.machine

theorem run (out stack tail : List Bool) (A fields : Fin 78→List Bool) (ref B P : ℕ)
    (extraH : Fin 38→ℕ) (extraA : Fin 38→List Bool)
    (ha : A 25=List.replicate ref true) (hs : A 74=stack) (hw : A 73=List.replicate B false)
    (hp : A 75=RecoveryBoundedRowReload.word fields++tail)
    (hd : A 76=List.replicate B true) (hl : A 77=List.replicate (B+1) false)
    (hB : 2*ref+2≤B) (hA : ∀ i,(A (RecoveryBoundedRowErase.work i)).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields j).length≤B)
    (hpB : (RecoveryBoundedRowReload.word fields).length≤B) :
    ∃ r,runFrom machine (RecoveryBoundedGrammarAfter.budget ref B fields)
      ⟨machine.start,heads out stack extraH,data P A extraA⟩=some r ∧
      r.steps≤RecoveryBoundedGrammarAfter.budget ref B fields ∧
      r.final.heads=heads out (RecoveryBoundedAddress.pushed ref stack) extraH ∧
      r.final.tapes=data P (RecoveryBoundedGrammarAfter.output fields A ref B stack) extraA := by
  obtain ⟨base,br,bs,bh,bt⟩:=RecoveryBoundedGrammarAfter.after_run out stack tail A fields ref B ha hs hw hp hd hl hB hA hf hpB
  obtain ⟨paddedReceipt,pr,pf,ps,_⟩:=ZeroPadding.run_config RecoveryBoundedGrammarAfter.machine (capacity P) _ _ base br
  have full:=TapeEmbedding.run_embed RecoveryBoundedGrammarAfter.machine extraH extraA _ _ paddedReceipt pr
  refine ⟨TapeEmbedding.receipt extraH extraA paddedReceipt,full,ps.le.trans bs,?_,?_⟩
  · change (TapeEmbedding.config extraH extraA paddedReceipt.final).heads=_
    simp only [TapeEmbedding.config,pf,ZeroPadding.config,bh]
    rfl
  · change (TapeEmbedding.config extraH extraA paddedReceipt.final).tapes=_
    simp only [TapeEmbedding.config,pf,ZeroPadding.config,bt]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedFixedContinue
