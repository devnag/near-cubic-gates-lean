import Proof.Amplification.RecoveryRawViewLoop

/-! After the outer iteration, one actual outer-list cell test checks
that no clause code remains. A physical negation writes the final result. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewEnd
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : Nat} (x : State) (total : Nat) (q : Fin s) : Configuration 66 s :=
  TapeEmbedding.config (fun _ : Fin 1=>1) (fun _=>CompareMachine.word total) (x.cfg q)
def negated (x : State) := flagged x (!x.outer.flag)
def tested (x : State) := negated (outerStep x)
def negateMachine : Machine 66 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then
    some ⟨1,fun i=>if i=28 then some (!scanned 59) else none,fun _=>.stay⟩ else none
noncomputable def outerMachine := TapeEmbedding.machine 1 RecoveryRawView.outerMachine
noncomputable def machine := Composition.machine outerMachine negateMachine
def budget (x : State) := RecoveryStoredListCell.time x.outer.bits+2

theorem negate_run (x : State) (total : Nat) :
    ∃ r,runFrom negateMachine 1 (cfg x total 0)=some r ∧
      r.final=cfg (negated x) total 1 ∧ r.steps=1 := by
  have h : step negateMachine (cfg x total 0)=some (cfg (negated x) total 1) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · change Fin.addCases (m:=65) (n:=1) (motive:=fun _=>Nat) (x.cfg 0).heads (fun _=>1)=
        Fin.addCases (m:=65) (n:=1) (motive:=fun _=>Nat) ((flagged x (!x.outer.flag)).cfg 1).heads (fun _=>1)
      rw [flagged_heads]
      rfl
    · have ht := flagged_tapes x (!x.outer.flag) (1 : Fin 2)
      change _=Fin.addCases (m:=65) (n:=1) (motive:=fun _=>List Bool)
        ((flagged x (!x.outer.flag)).cfg 1).tapes (fun _=>CompareMachine.word total)
      rw [ht,RecoveryRowStructure.bank_update_left]
      change _=Function.update (cfg x total 1).tapes (28 : Fin 66) [!x.outer.flag]
      funext i
      by_cases hi : i=28
      · subst i
        change writeTapeBit [x.inner.stream.data.present] 0 (!readTapeBit [x.outer.flag] 0)=[!x.outer.flag]
        rfl
      · simp only [applyAction,if_neg hi,Function.update_of_ne hi]
        rfl
  exact (Timed.single (by rfl) h).run (by rfl)

theorem outer_run (x : State) (total : Nat) (hx : x.outer.Valid) :
    ∃ r,runFrom outerMachine (RecoveryStoredListCell.time x.outer.bits) (cfg x total outerMachine.start)=some r ∧
      r.final=cfg (outerStep x) total r.final.control ∧ r.steps=RecoveryStoredListCell.time x.outer.bits := by
  obtain ⟨base,hr,hf,hs⟩ := RecoveryRawView.outer_run x hx
  have h := TapeEmbedding.run_embed RecoveryRawView.outerMachine (fun _ : Fin 1=>1)
    (fun _=>CompareMachine.word total) (RecoveryStoredListCell.time x.outer.bits) _ base hr
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1=>1) (fun _=>CompareMachine.word total) base,h,?_,hs⟩
  change TapeEmbedding.config _ _ base.final=_
  rw [hf]
  rfl

theorem test_run (x : State) (total : Nat) (hx : x.outer.Valid) :
    ∃ r,runFrom machine (budget x) (cfg x total machine.start)=some r ∧
      r.final=cfg (tested x) total r.final.control ∧ r.steps=budget x := by
  obtain ⟨first,hr0,hf0,hs0⟩ := outer_run x total hx
  obtain ⟨last,hr1,hf1,hs1⟩ := negate_run (outerStep x) total
  have hi : Composition.restart first.final negateMachine.start=cfg (outerStep x) total 0 := by
    rw [hf0]; rfl
  rw [←hi] at hr1
  have h := Composition.run_join outerMachine negateMachine (RecoveryStoredListCell.time x.outer.bits) 1 _ first last hr0 hr1
  have hb : RecoveryStoredListCell.time x.outer.bits+1+1=budget x := by unfold budget; omega
  rw [hb] at h
  refine ⟨Composition.joinedReceipt first last,h,?_,?_⟩
  · apply configuration_ext
    · rfl
    · change last.final.heads=_
      rw [hf1]; rfl
    · change last.final.tapes=_
      rw [hf1]; rfl
  · change first.steps+1+last.steps=_
    rw [hs0,hs1]
    exact hb

theorem tested_answer (x : State) :
    (tested x).inner.stream.data.present=decide (RecoveryRawViewBody.code x=0) := by
  change (!(x.outer.after 0).flag)=_
  rw [RecoveryThreeCellReader.after_flag]
  by_cases hz : RecoveryRawViewBody.code x=0
  · change (!(decide (RecoveryRawViewBody.code x≠0)))=_
    simp [hz]
  · change (!(decide (RecoveryRawViewBody.code x≠0)))=_
    simp [hz]

end NearCubicWires.RepairOrdinary.RecoveryRawViewEnd
