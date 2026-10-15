import Proof.Amplification.RecoveryRawLiteralState

/-! Actual cell and tag/index calls retain the independent presence flag.
Every entry and return has literal tape/head equalities. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawLiteral
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem data_ready {s n : Nat} (p : Machine 28 s) (x y : State)
    (h : ReadyRun p n x.data.tapes y.data.tapes) (hp : y.present=x.present) :
    ∃ r,runFrom (TapeEmbedding.machine 1 p) n (x.cfg (TapeEmbedding.machine 1 p).start)=some r ∧
      r.final=y.cfg r.final.control ∧ r.steps=n := by
  obtain ⟨base,hr,ht,hh,hs⟩ := h
  have he := TapeEmbedding.run_embed p (fun _ : Fin 1=>0) (fun _ : Fin 1=>[x.present]) n _ base hr
  have hi : TapeEmbedding.config (fun _ : Fin 1=>0) (fun _ : Fin 1=>[x.present])
      (initialConfiguration p x.data.tapes)=x.cfg (TapeEmbedding.machine 1 p).start := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at he
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _ : Fin 1=>[x.present]) base,he,?_,hs⟩
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=28) (n:=1) (fun j=>?_) (fun j=>?_) i
    · simpa only [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left,State.cfg] using hh j
    · simp only [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right,State.cfg]
  · change Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool) base.final.tapes (fun _=>[x.present])=y.tapes
    rw [ht,←hp]
    rfl

theorem cell_run (x : State) (hx : x.data.Valid) :
    ∃ r,runFrom cellMachine (RecoveryStoredListCell.time x.data.bits) (x.cfg cellMachine.start)=some r ∧
      r.final=(stepped x).cfg r.final.control ∧ r.steps=RecoveryStoredListCell.time x.data.bits :=
  data_ready (RecoveryClauseState.machine 0) x (stepped x) (RecoveryClauseState.cell_ready x.data 0 hx) rfl

theorem decode_run (x : State) (hx : x.data.Valid) (hp : (marked x).present=true) :
    ∃ r,runFrom decodeMachine (RecoveryCheckedLiteral.time (literal x)) ((marked x).cfg decodeMachine.start)=some r ∧
      r.final=(decoded x).cfg r.final.control ∧ r.steps=RecoveryCheckedLiteral.time (literal x) :=
  data_ready (RecoveryCheckedLiteral.machine 0) (marked x) (decoded x)
    (RecoveryCheckedLiteral.state_ready (stepped x).data 0 (literal x)
      (RecoveryClauseState.after_valid x.data 0 hx) (literal_length x) (literal_field x hp)) rfl

theorem marked_tapes (x : State) :
    (marked x).tapes=Function.update (stepped x).tapes 28 [(stepped x).data.flag] := by
  funext i
  fin_cases i <;> rfl

theorem flag_run (x : State) :
    ∃ r,runFrom flagMachine 1 ((stepped x).cfg flagMachine.start)=some r ∧
      r.final=(marked x).cfg r.final.control ∧ r.steps=1 := by
  obtain ⟨r,hr,hs,hh,ht⟩ := RecoveryBankPair.flag_run (28 : Fin 29) 23 (fun _=>0) (stepped x).tapes
    x.present (stepped x).data.flag rfl rfl rfl rfl
  refine ⟨r,hr,?_,hs⟩
  apply configuration_ext
  · rfl
  · exact hh
  · exact ht.trans (marked_tapes x).symm

theorem first_run (x : State) (hx : x.data.Valid) :
    ∃ r,runFrom firstMachine (firstCost x) (x.cfg firstMachine.start)=some r ∧
      r.final=(marked x).cfg r.final.control ∧ r.steps=firstCost x := by
  obtain ⟨first,hr0,hf0,hs0⟩ := cell_run x hx
  obtain ⟨last,hr1,hf1,hs1⟩ := flag_run x
  have he : Composition.restart first.final flagMachine.start=(stepped x).cfg flagMachine.start := by rw [hf0]; rfl
  rw [←he] at hr1
  have hrun := Composition.run_join cellMachine flagMachine (RecoveryStoredListCell.time x.data.bits) 1 _ first last hr0 hr1
  refine ⟨Composition.joinedReceipt first last,hrun,?_,?_⟩
  · apply configuration_ext
    · rfl
    · change last.final.heads=_; rw [hf1]; rfl
    · change last.final.tapes=_; rw [hf1]; rfl
  · change first.steps+1+last.steps=firstCost x
    rw [hs0,hs1]; rfl

end NearCubicWires.RepairOrdinary.RecoveryRawLiteral
