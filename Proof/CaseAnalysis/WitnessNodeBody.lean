import Proof.CaseAnalysis.WitnessNativeTriple

/-! The complete raw node body validates its canonical code and appends its
three already-produced native words. Invalid nodes also take this bounded
binary-copy path; the retained validity bit controls the enclosing DAG's
single acceptance decision before any native source execution. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeBody
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlot (j : Fin 3) : Fin 748:=(NodeGuard.fieldSlots (NodeFields.slots j 180)).castAdd 2
def appendSlots : Fin 5 → Fin 748:=![nativeSlot 0,nativeSlot 1,nativeSlot 2,746,747]
theorem append_injective : Function.Injective appendSlots:=by decide
noncomputable def guard:=TapeEmbedding.machine 2 NodeGuard.machine
noncomputable def append:=RecoveryFocus.machine appendSlots NativeTriple.machine
noncomputable def machine:=Composition.machine guard append
def extraHeads (out : List Bool) : Fin 2 → ℕ:=![0,out.length]
def extraTapes (old out : List Bool) : Fin 2 → List Bool:=![old,out]
noncomputable def entry (w : ℕ) (left right bits old out : List Bool):=
  Composition.leftConfig 12 (TapeEmbedding.config (extraHeads out) (extraTapes old out)
    (initialConfiguration NodeGuard.machine (NodeGuard.input w left right bits)))
def payloads (bits : List Bool) (j : Fin 3):=BitFields.payload (NodeMeaning.codeWord bits j)
def appended (bits out : List Bool):=out++(List.ofFn (fun j=>NativeWord.word (payloads bits j))).flatten
def budget (w : ℕ) (bits : List Bool):=NodeGuard.budget w bits+6*bits.length+24

theorem append_time (bits : List Bool) : NativeTriple.budget (payloads bits) ≤ 6*bits.length+23:=by
  have h0:=NodeGuard.payload_bound bits 0
  have h1:=NodeGuard.payload_bound bits 1
  have h2:=NodeGuard.payload_bound bits 2
  unfold NativeTriple.budget payloads
  omega

theorem entry_heads (w : ℕ) (left right bits old out : List Bool) (i : Fin 748) (hi : i≠747) :
    (entry w left right bits old out).heads i=0:=by
  revert hi
  refine Fin.addCases (m:=746) (n:=2) ?_ ?_ i
  · intro j _
    simp only [entry,Composition.leftConfig,TapeEmbedding.config,Fin.addCases_left,initialConfiguration]
  · intro j hi
    fin_cases j
    · rfl
    · exact False.elim (hi rfl)

theorem raw_run (w : ℕ) (left right bits old out : List Bool)
    (hl : left.length=w) (hr : right.length=w) (hw : bits.length+1 ≤ w) : ∃ result,
    runFrom machine (budget w bits) (entry w left right bits old out)=some result ∧
      result.steps ≤ budget w bits ∧
      result.final.tapes 747=appended bits out ∧ result.final.heads 747=(appended bits out).length ∧
      (readTapeBit (result.final.tapes 745) 0=true ↔ NodeMeaning.valid (value left) (value right) bits) ∧
      (∀ i,result.final.heads ((NodeGuard.common i).castAdd 2)=0 ∧
        result.final.tapes ((NodeGuard.common i).castAdd 2)=NodeGuard.shared w left right i):=by
  obtain ⟨fields,⟨g,hg,gt,gh,gs⟩,gflag,gwords,_,gcommon⟩:=NodeGuard.node_run w left right bits hl hr hw
  let a:=TapeEmbedding.receipt (extraHeads out) (extraTapes old out) g
  have ha:=TapeEmbedding.run_embed NodeGuard.machine (extraHeads out) (extraTapes old out) _ _ g hg
  obtain ⟨r,hrun,rs,rheads,rtapes⟩:=NativeTriple.triple_run (payloads bits) old out
  obtain ⟨b,hb,_,bsteps,bheads,btapes,bkeep⟩:=RecoveryFocus.dock appendSlots append_injective NativeTriple.machine
    _ a.final.heads a.final.tapes (NativeTriple.entry (payloads bits) old out)
    (by
      intro i
      fin_cases i
      · exact (TapeEmbedding.receipt_heads_old _ _ g _).trans (gh _)
      · exact (TapeEmbedding.receipt_heads_old _ _ g _).trans (gh _)
      · exact (TapeEmbedding.receipt_heads_old _ _ g _).trans (gh _)
      · exact TapeEmbedding.receipt_heads_new _ _ g 0
      · exact TapeEmbedding.receipt_heads_new _ _ g 1)
    (by
      intro i
      fin_cases i
      · exact (TapeEmbedding.receipt_tapes_old _ _ g _).trans ((congrFun gt _).trans (gwords 0))
      · exact (TapeEmbedding.receipt_tapes_old _ _ g _).trans ((congrFun gt _).trans (gwords 1))
      · exact (TapeEmbedding.receipt_tapes_old _ _ g _).trans ((congrFun gt _).trans (gwords 2))
      · exact TapeEmbedding.receipt_tapes_new _ _ g 0
      · exact TapeEmbedding.receipt_tapes_new _ _ g 1) r hrun
  have hj:=Composition.run_join guard append _ _ _ a b ha hb
  have htime:NodeGuard.budget w bits+1+NativeTriple.budget (payloads bits) ≤ budget w bits:=by
    have h:=append_time bits
    unfold budget;omega
  have more:=runFrom_moreFuel machine _ (budget w bits-(NodeGuard.budget w bits+1+NativeTriple.budget (payloads bits)))
    (entry w left right bits old out) (Composition.joinedReceipt a b) hj
  rw [Nat.add_sub_of_le htime] at more
  refine ⟨_,more,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ _
    rw [bsteps]
    change g.steps+1+r.steps ≤ _
    omega
  · change b.final.tapes (appendSlots 4)=_
    rw [btapes,rtapes]
    exact NativeTriple.prefix_three (payloads bits) out
  · change b.final.heads (appendSlots 4)=_
    rw [bheads,rheads]
    exact congrArg List.length (NativeTriple.prefix_three (payloads bits) out)
  · change readTapeBit (b.final.tapes 745) 0=true ↔ _
    rw [(bkeep 745 (by decide)).2]
    change readTapeBit ((TapeEmbedding.receipt _ _ g).final.tapes ((745 : Fin 746).castAdd 2)) 0=true ↔ _
    rw [TapeEmbedding.receipt_tapes_old,gt]
    exact gflag
  · intro i
    change b.final.heads _=0 ∧ b.final.tapes _=_
    have hkeep:=bkeep ((NodeGuard.common i).castAdd 2) (by fin_cases i <;> decide)
    exact ⟨hkeep.1.trans ((TapeEmbedding.receipt_heads_old _ _ g _).trans (gh _)),
      hkeep.2.trans ((TapeEmbedding.receipt_tapes_old _ _ g _).trans ((congrFun gt _).trans (gcommon i)))⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeBody
