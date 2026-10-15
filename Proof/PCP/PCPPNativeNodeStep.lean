import Proof.PCP.PCPPNativePositionAdvance

/-! One reusable iteration of the oracle-node loop: substitute the node,
clear its local workspace, and advance the actual current position by2. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeStep
open LocalBitMultitape SourceInterfaces PCPPNativeNodeMachine PCPPNativeNodeReusable RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def advanceSlots : Fin 2 → Fin 122 := ![3,6]
theorem advance_injective : Function.Injective advanceSlots := by decide
noncomputable def advance := RecoveryFocus.machine advanceSlots PCPPNativePositionAdvance.machine
noncomputable def machine := Composition.machine PCPPNativeNodeReusable.machine advance
noncomputable def entry (source queries : List Bool) (pos base position C F : ℕ) (out : List Bool) :=
  (⟨machine.start,PCPPNativeNodeReusable.heads pos out,
    PCPPNativeNodeReusable.data source queries base position C F out⟩ : Configuration 122 _)

theorem advance_install (source queries : List Bool) (base position C F : ℕ) (out : List Bool) :
    install advanceSlots (data source queries base position C F out)
      ![List.replicate (position+2) true,List.replicate F false]=data source queries base (position+2) C F out := by
  funext i
  by_cases h3 : i=3
  · subst i
    change install advanceSlots _ _ (advanceSlots 0)=_
    rw [install_slot advanceSlots advance_injective]
    rfl
  · by_cases h6 : i=6
    · subst i
      change install advanceSlots _ _ (advanceSlots 1)=_
      rw [install_slot advanceSlots advance_injective]
      rfl
    · rw [install_other advanceSlots _ _ i (by
        intro j; fin_cases j
        · exact Ne.symm h3
        · exact Ne.symm h6)]
      simp only [data,h3,ite_false]

theorem advance_run (source queries : List Bool) (pos base position C F : ℕ) (out : List Bool)
    (hF : position+2 ≤ F) :
    ∃ result,runFrom advance (2*position+6)
      (RecoveryCalls.restarted advance (heads pos out) (data source queries base position C F out))=some result ∧
      result.steps=2*position+6 ∧ result.final.heads=heads pos out ∧
      result.final.tapes=data source queries base (position+2) C F out := by
  have ready := PCPPNativePositionAdvance.advance_ready position F hF
  obtain ⟨result,hr,rh,rt,rs⟩ := ready.focus_at advanceSlots advance_injective
    (heads pos out) (data source queries base position C F out)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  exact ⟨result,hr,rs,rh,rt.trans (advance_install source queries base position C F out)⟩

def budget {n r : ℕ} (base index C F : ℕ) (projection : Fin n → ProjectedRandomBit r) (node : BooleanNode n) :=
  PCPPNativeNodeReusable.budget base index C F projection node+1+(2*(base+2*index)+6)

theorem step_run {n r : ℕ} (pre tail : List Bool) (base index C F : ℕ)
    (projection : Fin n → ProjectedRandomBit r) (node : BooleanNode n) (out : List Bool)
    (hC : nodeCapacity base index C projection node)
    (hF : nodeBudget base index C projection node+1 ≤ F) (hCF : C+1 ≤ F)
    (hposition : base+2*index+2 ≤ F) :
    ∃ result,runFrom machine (budget base index C F projection node)
      (entry (originalSource pre tail node) (rowCache projection) pre.length base (base+2*index) C F out)=some result ∧
      result.steps ≤ budget base index C F projection node ∧
      result.final.heads=heads (pre.length+(PCPPRequestNodeSchema.native node).length) (out++emittedNode base index projection node) ∧
      result.final.tapes=data (originalSource pre tail node) (rowCache projection) base (base+2*(index+1)) C F
        (out++emittedNode base index projection node) := by
  obtain ⟨a,ha,as,ah,atapes⟩ := PCPPNativeNodeReusable.node_run pre tail base index C F projection node out hC hF hCF
  obtain ⟨b,hb,bs,bh,bt⟩ := advance_run (originalSource pre tail node) (rowCache projection)
    (pre.length+(PCPPRequestNodeSchema.native node).length) base (base+2*index) C F
    (out++emittedNode base index projection node) hposition
  have hmid : Composition.restart a.final advance.start=
      RecoveryCalls.restarted advance
        (heads (pre.length+(PCPPRequestNodeSchema.native node).length) (out++emittedNode base index projection node))
        (data (originalSource pre tail node) (rowCache projection) base (base+2*index) C F
          (out++emittedNode base index projection node)) := by
    apply configuration_ext
    · rfl
    · exact ah
    · exact atapes
  rw [←hmid] at hb
  let result := Composition.joinedReceipt a b
  have hr := Composition.run_join PCPPNativeNodeReusable.machine advance _ _ _ a b ha hb
  refine ⟨result,hr,?_,bh,?_⟩
  · change a.steps+1+b.steps ≤ _
    unfold budget; omega
  · change b.final.tapes=_
    rw [bt,show base+2*index+2=base+2*(index+1) by omega]

end NearCubicWires.RepairOrdinary.PCPPNativeNodeStep
