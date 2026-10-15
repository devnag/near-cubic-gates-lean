import Proof.Amplification.RecoveryAssignmentLayout

/-! Reusable full scalar return from the executed prefix selector. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAssignment
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics RecoveryValuationStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem selector_return (d : Data) (count cap : Nat) (binaryCount committed : List Bool) (guard : Bool)
    (hw : binaryCount.length=d.index.length) (hsmall : 2*binaryCount.length+3≤d.capacity)
    (hcap : RecoveryCommittedBit.rawCost d.index committed≤d.capacity) :
    ∃ r,runFrom selectorMachine (RecoveryPrefixAssignment.cost (prefixData d binaryCount committed guard))
      (cfg d count cap binaryCount committed guard selectorMachine.start)=some r ∧
      r.steps≤RecoveryPrefixAssignment.cost (prefixData d binaryCount committed guard) ∧
      ∃ out guard',out.width=d.width ∧ out.index.length=d.index.length ∧ out.source=d.source ∧
        out.pos=d.pos ∧ out.row=d.row ∧ out.capacity=d.capacity ∧ out.valid=d.valid ∧
        out.value=(if value d.index<value binaryCount then (value committed).testBit (value d.index) else d.value) ∧
        r.final=cfg out count cap binaryCount committed guard'
          (RecoveryCalls.controlCode RecoveryPrefixAssignment.sizes none) := by
  obtain ⟨base,hr,hs,out,hcount,hcommitted,hindex,hcapacity,hvalue,hf⟩ := RecoveryPrefixAssignment.assignment_run
    (prefixData d binaryCount committed guard) hw hsmall hcap
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config selectorSlots selectorSlots_injective
    RecoveryPrefixAssignment.machine
    (cfg d count cap binaryCount committed guard selectorMachine.start).heads
    (cfg d count cap binaryCount committed guard selectorMachine.start).tapes _ _ base hr
  rw [selector_input] at hrun
  rw [hf] at hfinal
  change r.final=RecoveryFocus.config selectorSlots
    (cfg d count cap binaryCount committed guard selectorMachine.start).heads
    (cfg d count cap binaryCount committed guard selectorMachine.start).tapes (selectorResult out) at hfinal
  rw [selector_output d out count cap binaryCount committed guard hcount hcommitted hcapacity] at hfinal
  exact ⟨r,hrun,by rw [hsteps]; exact hs,selectedData d out,out.guard,rfl,hindex,rfl,rfl,rfl,rfl,rfl,hvalue,hfinal⟩

end NearCubicWires.RepairOrdinary.RecoveryAssignment
