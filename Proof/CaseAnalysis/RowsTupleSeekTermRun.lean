import Proof.CaseAnalysis.RowsTupleSeekTermLayout

/-! A single actual parser and tail consume all three slices of one same
original term. The emitted count comes from that parser, before cleanup. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sources (t : TermSlices) (pre tail : Fin 3→List Bool) := fun i=>pre i++t.words (i.castAdd 1)++tail i

theorem term_run (keep : Bool) (t : TermSlices) (pre tail : Fin 3→List Bool) (out : Fin 4→List Bool) :
    ∃ r,runFrom (rawMachine keep) t.cost
      (rawEntry keep (sources t pre tail) (fun i=>(pre i).length) out)=some r ∧
      (∀ i,r.final.tapes (rawSourceSlots i)=sources t pre tail i ∧
        r.final.heads (rawSourceSlots i)=(pre i).length+(t.words (i.castAdd 1)).length) ∧
      (∀ i,r.final.tapes (rawOutputSlots i)=appended keep t out i ∧
        r.final.heads (rawOutputSlots i)=(appended keep t out i).length) ∧ r.steps ≤ t.cost := by
  let src := sources t pre tail
  let pos := fun i : Fin 3=>(pre i).length
  obtain ⟨a,ha,at0,ah0,at10,ah10,at14,ah14,as⟩ := header_run keep (pre 0)
    (frame t.top++nativeWord t.gates++tail 0) (out 0) t.gates.length
  have hs : pre 0++natWord t.gates.length++(frame t.top++nativeWord t.gates++tail 0)=src 0 := by
    simp [src,sources,TermSlices.words,List.append_assoc]
  rw [hs] at ha at0
  let a' := TapeEmbedding.receipt (rawExtraHeads pos out) (rawExtraData src out) a
  have firstRun := TapeEmbedding.run_embed (headerMachine keep) (rawExtraHeads pos out)
    (rawExtraData src out) _ _ a ha
  have first : Step (rawFirst keep) (headerCost t.gates.length)
      (rawInput keep src pos out).heads (rawInput keep src pos out).tapes a'.final.heads a'.final.tapes :=
    ⟨a',firstRun,rfl,rfl,as⟩
  let out1 := withHeader keep t.gates.length out
  have rawTail := tail_run keep (pre 0++natWord t.gates.length) t.top (tail 0) (pre 1) (tail 1)
    (pre 2) (t.coefficient 0) (t.coefficient 1) (t.coefficient 2) (tail 2) t.gates out1
  have tailSource : (![ (pre 0++natWord t.gates.length)++frame t.top++nativeWord t.gates++tail 0,
      pre 1++supportWord t.gates++tail 1,pre 2++record (t.coefficient 0) (t.coefficient 1) (t.coefficient 2)++tail 2] : Fin 3→List Bool)=src := by
    funext i;fin_cases i <;> simp [src,sources,TermSlices.words,List.append_assoc]
  rw [tailSource,tail_appended] at rawTail
  have last := rawTail.dock rawSlots (by decide) a'.final.heads a'.final.tapes
    (by intro i;fin_cases i
        · change a.final.heads 0=(pre 0++natWord t.gates.length).length
          rw [List.length_append];exact ah0
        · exact ah14
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact ah10)
    (by intro i;fin_cases i
        · exact at0
        · exact at14
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact at10)
  obtain ⟨r,hr,rh,rt,rs⟩ := first.seq last
  refine ⟨r,hr,?_,?_,rs⟩
  · intro i;fin_cases i
    · constructor
      · change r.final.tapes (rawSlots 0)=_
        rw [rt,install_slot rawSlots (by decide)];rfl
      · change r.final.heads (rawSlots 0)=_
        rw [rh,dockH_slot rawSlots (by decide)]
        simp [tailHeads,TermSlices.words,List.length_append,Nat.add_assoc]
    · constructor
      · change r.final.tapes (rawSlots 2)=_
        rw [rt,install_slot rawSlots (by decide)];rfl
      · change r.final.heads (rawSlots 2)=_
        rw [rh,dockH_slot rawSlots (by decide)];rfl
    · constructor
      · change r.final.tapes (rawSlots 4)=_
        rw [rt,install_slot rawSlots (by decide)];rfl
      · change r.final.heads (rawSlots 4)=_
        rw [rh,dockH_slot rawSlots (by decide)];rfl
  · intro i
    have slot : rawOutputSlots i=rawSlots (![1,3,5,6] i) := by fin_cases i <;> rfl
    rw [slot,rt,rh,install_slot rawSlots (by decide),dockH_slot rawSlots (by decide)]
    fin_cases i <;> exact ⟨rfl,rfl⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
