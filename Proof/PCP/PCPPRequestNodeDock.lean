import Proof.PCP.PCPPRequestNodeDispatch
import Proof.PCP.PCPPRequestNodePrepare

/-! The canonical-node dispatcher consumes the actual prepared fields. The
producer state space stays abstract through the physical 642-tape join. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeDock
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old (i : Fin 408) : Fin 642 := i.castAdd 234
def slots (j : Fin 234) : Fin 642 :=
  if j=0 then 85 else if j=1 then 220 else if j=2 then 355 else if j=5 then 406
  else j.natAdd 408
theorem slots_val (j : Fin 234) : (slots j).val=
    if j=0 then 85 else if j=1 then 220 else if j=2 then 355 else if j=5 then 406 else 408+j.val := by
  unfold slots
  split_ifs <;> rfl
theorem slots_injective : Function.Injective slots := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  rw [slots_val,slots_val] at hv
  split_ifs at hv <;> omega
theorem source_outside (j : Fin 234) : slots j≠0 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [slots] at hv
  split_ifs at hv <;> simp_all

def extended {s : ℕ} (c : Configuration 408 s) :=
  TapeEmbedding.config (fun _ : Fin 234 => 0) (fun _ => []) c
def dock {s t : ℕ} (producer : Machine 408 s) (callee : Machine 234 t) :=
  Composition.machine (TapeEmbedding.machine 234 producer) (RecoveryFocus.machine slots callee)

theorem dock_run {s t : ℕ} (producer : Machine 408 s) (callee : Machine 234 t)
    (fuel localFuel : ℕ) (initial : Configuration 408 s) (first : ExecutionReceipt 408 s)
    (hfirst : runFrom producer fuel initial=some first)
    (a b c pa pb pc : ℕ) (flag : Bool)
    (ha : first.final.tapes 85=frame a.bits++List.replicate pa false)
    (hb : first.final.tapes 220=frame b.bits++List.replicate pb false)
    (hc : first.final.tapes 355=frame c.bits++List.replicate pc false)
    (hflag : first.final.tapes 406=[flag])
    (hheads : ∀ i : Fin 4,first.final.heads (![85,220,355,406] i)=0)
    (out : Fin 234 → List Bool)
    (ready : ClockJoin.ReadyRun callee localFuel (PCPPRequestNodeCode.input a b c flag pa pb pc) out) :
    ∃ r,runFrom (dock producer callee) (fuel+1+localFuel)
      (Composition.leftConfig _ (extended initial))=some r ∧
      r.steps≤first.steps+1+localFuel ∧
      r.final.tapes 0=first.final.tapes 0 ∧ r.final.heads 0=first.final.heads 0 ∧
      (∀ j,r.final.tapes (slots j)=out j) ∧
      (∀ j,r.final.heads (slots j)=0) := by
  let lifted := TapeEmbedding.receipt (fun _ : Fin 234 => 0) (fun _ => []) first
  have hlift := TapeEmbedding.run_embed producer (fun _ : Fin 234 => 0) (fun _ => [])
    fuel initial first hfirst
  have newT (j : Fin 234) : lifted.final.tapes (j.natAdd 408)=[] := by
    simp only [lifted,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right]
  have newH (j : Fin 234) : lifted.final.heads (j.natAdd 408)=0 := by
    simp only [lifted,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right]
  have hin (j : Fin 234) : lifted.final.tapes (slots j)=PCPPRequestNodeCode.input a b c flag pa pb pc j := by
    by_cases h0 : j=0
    · subst j; exact ha
    by_cases h1 : j=1
    · subst j; exact hb
    by_cases h2 : j=2
    · subst j; exact hc
    by_cases h5 : j=5
    · subst j; exact hflag
    simp only [slots,PCPPRequestNodeCode.input,h0,h1,h2,h5,ite_false]
    exact newT j
  have hinH (j : Fin 234) : lifted.final.heads (slots j)=0 := by
    by_cases h0 : j=0
    · subst j; exact hheads 0
    by_cases h1 : j=1
    · subst j; exact hheads 1
    by_cases h2 : j=2
    · subst j; exact hheads 2
    by_cases h5 : j=5
    · subst j; exact hheads 3
    simp only [slots,h0,h1,h2,h5,ite_false]
    exact newH j
  obtain ⟨last,hlast,lh,lt,ls⟩ := ready.focus_at slots slots_injective
    lifted.final.heads lifted.final.tapes hin hinH
  have joined := Composition.run_join (TapeEmbedding.machine 234 producer)
    (RecoveryFocus.machine slots callee) fuel localFuel (extended initial) lifted last hlift hlast
  refine ⟨Composition.joinedReceipt lifted last,joined,?_,?_,?_,?_,?_⟩
  · change first.steps+1+last.steps≤first.steps+1+localFuel
    omega
  · change last.final.tapes 0=first.final.tapes 0
    rw [lt,install_other slots _ _ 0 source_outside]
    rfl
  · change last.final.heads 0=first.final.heads 0
    rw [lh]; rfl
  · intro j
    change last.final.tapes (slots j)=out j
    rw [lt]
    exact install_slot slots slots_injective _ _ j
  · intro j
    change last.final.heads (slots j)=0
    rw [lh]
    exact hinH j

end
end NearCubicWires.RepairOrdinary.PCPPRequestNodeDock
