import Proof.Amplification.RecoveryBoundedNativeLiteralLayout

/-! Execute the grammar literal controller with the runtime polarity cell.
Both paths emit exactly the original compiler's input/optional-NOT bytes,
and retain the actual addresses and reusable printing workspace. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteral
open LocalBitMultitape RepairRepresentation RecoveryExecution PCPPNativeClauseBank
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem first_run (index position C : ℕ) (negative : Bool) (out : List Bool)
    (hi : PCPPNativeSumAppend.budget 0 index+1≤C) (hz : PCPPNativeSumAppend.budget 0 0+1≤C) :
    ∃ r,runFrom first (firstBudget index position C) ⟨first.start,heads out,data index position C negative out⟩=some r ∧
      r.steps≤firstBudget index position C ∧ r.final.heads=heads (out++inputBits index) ∧
      r.final.tapes=data index position C negative (out++inputBits index) := by
  obtain ⟨a,ha,as,ah,atapes⟩:=node_run 1 0 1 0 2 (by decide) (by decide) (values index position) C out hi hz
  have hb : nodeBits 1 0 1 0 2 (values index position)=inputBits index := by simp [nodeBits,values,inputBits]
  rw [hb] at ah atapes
  have runLift:=TapeEmbedding.run_embed (nodeMachine 1 0 1 0 2) (fun _ : Fin 1=>0) (fun _=>[negative]) _ _ a ha
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _=>[negative]) a,runLift,as,?_,?_⟩
  · change (Fin.addCases (m:=29) (n:=1) (motive:=fun _=>ℕ) a.final.heads (fun _=>0))=_
    rw [ah]; rfl
  · change (Fin.addCases (m:=29) (n:=1) (motive:=fun _=>List Bool) a.final.tapes (fun _=>[negative]))=_
    rw [atapes]; rfl

theorem second_run (index position C : ℕ) (negative : Bool) (out : List Bool)
    (hp : PCPPNativeSumAppend.budget 0 position+1≤C) (hz : PCPPNativeSumAppend.budget 0 0+1≤C) :
    ∃ r,runFrom second (secondBudget index position C) ⟨second.start,heads out,data index position C negative out⟩=some r ∧
      r.steps ≤ secondBudget index position C ∧ r.final.heads=heads (out++notBits position) ∧
      r.final.tapes=data index position C negative (out++notBits position) := by
  obtain ⟨a,ha,as,ah,atapes⟩:=node_run 2 0 3 0 2 (by decide) (by decide) (values index position) C out hp hz
  have hb : nodeBits 2 0 3 0 2 (values index position)=notBits position := by simp [nodeBits,values,notBits]
  rw [hb] at ah atapes
  have runLift:=TapeEmbedding.run_embed (nodeMachine 2 0 3 0 2) (fun _ : Fin 1=>0) (fun _=>[negative]) _ _ a ha
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _=>[negative]) a,runLift,as,?_,?_⟩
  · change (Fin.addCases (m:=29) (n:=1) (motive:=fun _=>ℕ) a.final.heads (fun _=>0))=_
    rw [ah]; rfl
  · change (Fin.addCases (m:=29) (n:=1) (motive:=fun _=>List Bool) a.final.tapes (fun _=>[negative]))=_
    rw [atapes]; rfl

theorem literal_run (index position C : ℕ) (negative : Bool) (out : List Bool)
    (hi : PCPPNativeSumAppend.budget 0 index+1≤C) (hp : PCPPNativeSumAppend.budget 0 position+1≤C)
    (hz : PCPPNativeSumAppend.budget 0 0+1≤C) :
    ∃ r,runFrom machine (budget index position C) (entry index position C negative out)=some r ∧
      r.steps≤budget index position C ∧ r.final.heads=heads (out++emitted index position negative) ∧
      r.final.tapes=data index position C negative (out++emitted index position negative) := by
  obtain ⟨a,ha,as,ah,atapes⟩:=first_run index position C negative out hi hz
  have flag : a.final.scanned 29=negative := by
    change readTapeBit (a.final.tapes 29) (a.final.heads 29)=negative
    rw [atapes,ah]
    rfl
  cases negative with
  | false=>
    have full:=stop_run 0 _ _ _ a ha (by
      change (if a.final.scanned 29 then some (1 : Fin 2) else none)=none
      rw [flag]; rfl)
    obtain ⟨r,hr,rf,rs⟩:=full.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
    have hbudget : a.steps+1≤budget index position C := by unfold budget; omega
    have more:=runFrom_moreFuel machine _ (budget index position C-(a.steps+1)) _ r hr
    rw [Nat.add_sub_of_le hbudget] at more
    refine ⟨r,more,by omega,?_,?_⟩
    · rw [rf]
      simpa only [RecoveryCalls.stopped,emitted,Bool.false_eq_true,ite_false,List.append_nil] using ah
    · rw [rf]
      simpa only [RecoveryCalls.stopped,emitted,Bool.false_eq_true,ite_false,List.append_nil] using atapes
  | true=>
    have initial:=call_run 0 1 _ _ _ a ha (by
      change (if a.final.scanned 29 then some (1 : Fin 2) else none)=some 1
      rw [flag]; rfl)
    rw [ah,atapes] at initial
    obtain ⟨b,hb,bs,bh,bt⟩:=second_run index position C true (out++inputBits index) hp hz
    have terminal:=stop_run 1 _ _ _ b hb (by simp [next])
    have full:=initial.trans terminal
    obtain ⟨r,hr,rf,rs⟩:=full.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
    have hbudget : (a.steps+1)+(b.steps+1)≤budget index position C := by unfold budget; omega
    have more:=runFrom_moreFuel machine _ (budget index position C-((a.steps+1)+(b.steps+1))) _ r hr
    rw [Nat.add_sub_of_le hbudget] at more
    refine ⟨r,more,by omega,?_,?_⟩
    · rw [rf]
      simpa only [RecoveryCalls.stopped,emitted,ite_true,List.append_assoc] using bh
    · rw [rf]
      simpa only [RecoveryCalls.stopped,emitted,ite_true,List.append_assoc] using bt

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteral
