import Proof.Circuits.DecompositionSourceRecords
import Proof.Amplification.RecoveryFocusDock

/-! Position the same native decomposition cache at a selected child.
The existing counted native scan pays for preceding fields; the consumer
reads the selected weight/target block directly, without a second encoding. -/
namespace NearCubicWires.RepairOrdinary.DecompositionCachedChild
open LocalBitMultitape RepairRepresentation DecompositionSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def header := TapeEmbedding.machine 2 (PCPPQueryField.machine false)
noncomputable def machine := Composition.machine header Records.machine
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (index : ℕ) :=
  (⟨machine.start,![0,0,0,1,1],
    ![exactListWord gs,[],[],UnaryTemplate.tape n,UnaryTemplate.tape index]⟩ :
    Configuration 5 (4+Fintype.card (RepairSource.VerifierDecoding.RepeatMachine.Control (Records.innerStates+6))))
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (index : ℕ) :=
  2*natBitLength gs.length+((gs.take index).flatMap exactWord).length+(6*n+10)*index+7

theorem position_run {n : ℕ} (gs : List (ExactThresholdGate n)) (index : ℕ) (hi : index ≤ gs.length) :
    ∃ r,runFrom machine (budget gs index) (entry gs index)=some r ∧
      r.final.tapes 0=exactListWord gs ∧
      r.final.heads 0=(natWord gs.length).length+((gs.take index).flatMap exactWord).length ∧
      r.final.tapes 3=UnaryTemplate.tape n ∧ r.final.heads 3=1 ∧
      r.final.tapes 4=UnaryTemplate.tape index ∧ r.final.heads 4=1 ∧
      r.steps=budget gs index := by
  let priorChildren := gs.take index
  let tail := (gs.drop index).flatMap exactWord
  have hlen : priorChildren.length=index := by simp only [priorChildren,List.length_take,Nat.min_eq_left hi]
  have hword : natWord gs.length++priorChildren.flatMap exactWord++tail=exactListWord gs := by
    rw [List.append_assoc,←List.flatMap_append]
    simp only [priorChildren,List.take_append_drop,exactListWord]
  obtain ⟨base,hb,bf,bs⟩ := PCPPQueryField.nat_run false [] (gs.flatMap exactWord) [] [] gs.length
  simp only [List.nil_append,List.length_nil] at hb
  let eh : Fin 2 → ℕ := fun _ => 1
  let et : Fin 2 → List Bool := ![UnaryTemplate.tape n,UnaryTemplate.tape index]
  let prep := TapeEmbedding.receipt eh et base
  have hp := TapeEmbedding.run_embed (PCPPQueryField.machine false) eh et _ _ base hb
  obtain ⟨last,hl,lt,lh,ls⟩ := Records.padded_run priorChildren (natWord gs.length) tail
    (PCPPQueryField.saved gs.length []) []
  rw [hword,hlen] at hl lt
  rw [hlen] at ls
  simp only [List.nil_append,List.length_nil] at hl lt lh
  have hc : (⟨Records.machine.start,
      ![(natWord gs.length).length,0,0,1,1],
      ![exactListWord gs,PCPPQueryField.saved gs.length [],[],UnaryTemplate.tape n,UnaryTemplate.tape index]⟩ :
      Configuration 5 (Fintype.card (RepairSource.VerifierDecoding.RepeatMachine.Control (Records.innerStates+6))))=
      Composition.restart prep.final Records.machine.start := by
    dsimp only [prep,TapeEmbedding.receipt]
    rw [bf]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart,TapeEmbedding.config,PCPPQueryField.payload,
        PCPPQueryField.cfg,PCPPQueryField.selected,eh,DecompositionSource.natWord_length] <;> rfl
    · funext i
      fin_cases i <;> simp [Composition.restart,TapeEmbedding.config,PCPPQueryField.payload,
        PCPPQueryField.cfg,PCPPQueryField.selected,et,exactListWord,PCPPQueryField.saved] <;> rfl
  rw [hc] at hl
  have whole := Composition.run_join header Records.machine _ _ _ prep last hp hl
  have he : Composition.leftConfig _ (TapeEmbedding.config eh et
      (PCPPQueryField.cfg 0 (natWord gs.length++gs.flatMap exactWord) 0 [] 0 []))=entry gs index := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [he] at whole
  have time : (2*natBitLength gs.length+3)+1+
      ((priorChildren.flatMap exactWord).length+(6*n+10)*index+3)=budget gs index := by dsimp only [budget,priorChildren]; omega
  rw [time] at whole
  refine ⟨Composition.joinedReceipt prep last,whole,congrFun lt 0,congrFun lh 0,
    congrFun lt 3,congrFun lh 3,congrFun lt 4,congrFun lh 4,?_⟩
  change base.steps+1+last.steps=_
  rw [bs,ls,time]

end NearCubicWires.RepairOrdinary.DecompositionCachedChild
