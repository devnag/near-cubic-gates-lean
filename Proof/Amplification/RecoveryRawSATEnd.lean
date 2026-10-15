import Proof.Amplification.RecoveryRawSATLoop

/-! The raw-SAT tail is checked by an actual outer-list cell operation.
Its presence bit is negated into the final result cell. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawSATEnd
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawSAT
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def negateMachine : Machine 70 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then
    some ⟨1,fun i=>if i=27 then some (!scanned 65) else none,fun _=>.stay⟩ else none
def negateOutput (input : Fin 70→List Bool) :=
  Function.update input 27 [!readTapeBit (input 65) 0]
noncomputable def localMachine := Composition.machine RecoveryRawSAT.outerMachine negateMachine
noncomputable def machine := TapeEmbedding.machine 1 localMachine
def output (x : State) := negateOutput (outerStep x).tapes
def budget (x : State) := RecoveryStoredListCell.time x.outer.bits+2
def cfg {s : Nat} (input : Fin 70→List Bool) (total : Nat) (q : Fin s) : Configuration 71 s :=
  TapeEmbedding.config (fun _ : Fin 1=>1) (fun _=>CompareMachine.word total) ⟨q,fun _=>0,input⟩

theorem negate_ready (input : Fin 70→List Bool) (bit : Bool) (hi : input 27=[bit]) :
    ReadyRun negateMachine 1 input (negateOutput input) := by
  have h : step negateMachine (initialConfiguration negateMachine input)=
      some (⟨1,fun _=>0,negateOutput input⟩ : Configuration 70 2) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases he : i=27
      · subst i
        simp only [applyAction,if_true,negateOutput,Function.update_self]
        change writeTapeBit (input 27) 0 (!readTapeBit (input 65) 0)=_
        rw [hi]
        rfl
      · simp only [applyAction,if_neg he,negateOutput,Function.update_of_ne he]
        rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  refine ⟨r,hr,?_,?_,hs⟩
  · rw [hf]
  · intro i; rw [hf]

theorem local_ready (x : State) (hx : x.outer.Valid) :
    ReadyRun localMachine (budget x) x.tapes (output x) := by
  obtain ⟨first,hr0,ht0,hh0,hs0⟩ := RecoveryRawSAT.outer_ready x hx
  obtain ⟨last,hr1,ht1,hh1,hs1⟩ := negate_ready (outerStep x).tapes x.clause.result rfl
  have hi : Composition.restart first.final negateMachine.start=
      initialConfiguration negateMachine (outerStep x).tapes := by
    apply configuration_ext
    · rfl
    · exact funext hh0
    · exact ht0
  unfold run at hr1
  rw [←hi] at hr1
  have h := Composition.run_join RecoveryRawSAT.outerMachine negateMachine
    (RecoveryStoredListCell.time x.outer.bits) 1 _ first last hr0 hr1
  have hb : RecoveryStoredListCell.time x.outer.bits+1+1=budget x := by unfold budget; omega
  rw [hb] at h
  refine ⟨Composition.joinedReceipt first last,h,ht1,hh1,?_⟩
  change first.steps+1+last.steps=budget x
  rw [hs0,hs1,hb]

theorem test_run (x : State) (total : Nat) (hx : x.outer.Valid) :
    ∃ r,runFrom machine (budget x) (cfg x.tapes total machine.start)=some r ∧
      r.final=cfg (output x) total r.final.control ∧ r.steps=budget x := by
  obtain ⟨base,hr,ht,hh,hs⟩ := local_ready x hx
  have h := TapeEmbedding.run_embed localMachine (fun _ : Fin 1=>1)
    (fun _=>CompareMachine.word total) (budget x) _ base hr
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1=>1) (fun _=>CompareMachine.word total) base,h,?_,hs⟩
  apply configuration_ext
  · rfl
  · change Fin.addCases (m:=70) (n:=1) (motive:=fun _=>Nat) base.final.heads (fun _=>1)=_
    rw [show base.final.heads=(fun _=>0) from funext hh]
    rfl
  · change Fin.addCases (m:=70) (n:=1) (motive:=fun _=>List Bool) base.final.tapes (fun _=>CompareMachine.word total)=_
    rw [ht]
    rfl

theorem output_answer (x : State) : output x 27=[decide (x.code=0)] := by
  change [!readTapeBit [(x.outer.after 0).flag] 0]=_
  change [!(x.outer.after 0).flag]=_
  rw [RecoveryThreeCellReader.after_flag]
  change [!(decide (x.code≠0))]=_
  by_cases hz : x.code=0 <;> simp [hz]

end NearCubicWires.RepairOrdinary.RecoveryRawSATEnd
