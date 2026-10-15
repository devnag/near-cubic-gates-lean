import Proof.PCP.PCPPRequestNodeFields
import Proof.PCP.PCPPRequestTagPadded
import Proof.PCP.PCPPRequestNodeSchema

/-! The finite tag classifier is docked to the actual three-field producer.
The producer state space stays abstract while its physical tapes are retained. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodePrepare
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 406) : Fin 408 := i.castAdd 2
def tagSlots : Fin 3 → Fin 408 := ![85,406,407]
theorem tagSlots_injective : Function.Injective tagSlots := by decide
noncomputable def classify := RecoveryFocus.machine tagSlots PCPPRequestTagArity.machine
noncomputable def dock {s : ℕ} (producer : Machine 406 s) :=
  Composition.machine (TapeEmbedding.machine 2 producer) classify
def extended {s : ℕ} (c : Configuration 406 s) :=
  TapeEmbedding.config (fun _ : Fin 2 => 0) (fun _ => []) c

theorem dock_run {s : ℕ} (producer : Machine 406 s) (fuel : ℕ)
    (initial : Configuration 406 s) (first : ExecutionReceipt 406 s)
    (hfirst : runFrom producer fuel initial=some first)
    (tag : Fin 5) (padding : ℕ)
    (ht : first.final.tapes 85=frame (PCPPRequestTagArity.code tag)++List.replicate padding false)
    (hh : first.final.heads 85=0) :
    ∃ r,runFrom (dock producer) (fuel+37)
      (Composition.leftConfig _ (extended initial))=some r ∧
      r.steps≤first.steps+37 ∧
      (∀ i,r.final.tapes (old i)=first.final.tapes i) ∧
      (∀ i,r.final.heads (old i)=first.final.heads i) ∧
      r.final.tapes 406=[PCPPRequestTagArity.outputFlag tag] ∧ r.final.heads 406=0 := by
  let lifted := TapeEmbedding.receipt (fun _ : Fin 2 => 0) (fun _ => []) first
  have hlift := TapeEmbedding.run_embed producer (fun _ : Fin 2 => 0) (fun _ => [])
    fuel initial first hfirst
  have hin (i : Fin 3) : lifted.final.tapes (tagSlots i)=
      PCPPRequestTagArity.paddedInput tag padding i := by
    fin_cases i
    · exact ht
    · rfl
    · rfl
  have hheads (i : Fin 3) : lifted.final.heads (tagSlots i)=0 := by
    fin_cases i
    · exact hh
    · rfl
    · rfl
  obtain ⟨last,hlast,lh,lt,ls⟩ := (PCPPRequestTagArity.padded_run tag padding).focus_at
    tagSlots tagSlots_injective lifted.final.heads lifted.final.tapes hin hheads
  have hjoin := Composition.run_join (TapeEmbedding.machine 2 producer) classify fuel 36
    (extended initial) lifted last hlift hlast
  refine ⟨Composition.joinedReceipt lifted last,by simpa only [dock,Nat.add_assoc] using hjoin,?_,?_,?_,?_,?_⟩
  · change lifted.steps+1+last.steps≤first.steps+37
    change first.steps+1+last.steps≤first.steps+37
    omega
  · intro i
    change last.final.tapes (old i)=first.final.tapes i
    rw [lt]
    by_cases hi : i=85
    · subst i
      have ho := install_slot tagSlots tagSlots_injective lifted.final.tapes
        (PCPPRequestTagArity.paddedOutput tag padding) 0
      exact ho.trans ht.symm
    · rw [install_other tagSlots _ _ (old i) (by
        intro j he
        have hv := congrArg Fin.val he
        have hi' : i.val≠85 := fun h => hi (Fin.ext h)
        have hib := i.isLt
        fin_cases j <;> dsimp [tagSlots,old] at hv <;> omega)]
      simp only [lifted,TapeEmbedding.receipt,TapeEmbedding.config,old,Fin.addCases_left]
  · intro i
    change last.final.heads (old i)=first.final.heads i
    rw [lh]
    simp only [lifted,TapeEmbedding.receipt,TapeEmbedding.config,old,Fin.addCases_left]
  · change last.final.tapes 406=_
    rw [lt]
    exact install_slot tagSlots tagSlots_injective lifted.final.tapes
      (PCPPRequestTagArity.paddedOutput tag padding) 1
  · change last.final.heads 406=0
    rw [lh]
    rfl

end NearCubicWires.RepairOrdinary.PCPPRequestNodePrepare
