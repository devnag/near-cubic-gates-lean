import Proof.Amplification.RecoveryOuterRowTime

/-! The outer table increments only its physical prior-row driver. Its
independent inner-table count and all retained inputs remain available. -/
namespace NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def advanceMachine := onOuter priorAdvanceMachine
def advanced (x : State) := withOuter x (priorSuccessor x.outer)

theorem advance_run (x : State) :
    ∃ r,runFrom advanceMachine (2*x.outer.total+6) (x.cfg advanceMachine.start)=some r ∧
      r.final=(advanced x).cfg r.final.control ∧ r.steps=2*x.outer.total+6 := by
  obtain ⟨base,hr,hf,hs⟩ := prior_advance_run x.outer
  obtain ⟨r,hrun,hfinal,hsteps⟩ := outer_run priorAdvanceMachine x (priorSuccessor x.outer) (2*x.outer.total+6) base hr hf
  exact ⟨r,hrun,hfinal,hsteps.trans hs⟩

theorem advanced_valid (x : State) (word outerBits innerBits : List Bool) (hx : x.Valid word outerBits innerBits)
    (hc : (x.outer.total+1)*(RecoveryRowLookupStream.budget x.outer.bank.row.width+3)+5 ≤ x.outer.lookupCapacity) :
    (advanced x).Valid word outerBits innerBits :=
  withOuter_valid x _ word outerBits innerBits hx (priorSuccessor_valid x.outer word outerBits hx.1 hc) rfl rfl

def rowAdvanced (x : State) (outerBits innerBits input : List Bool) := advanced (readRowOutput x outerBits innerBits input)

theorem row_advanced_valid (x : State) (word outerBits innerBits input : List Bool)
    (hx : x.Valid word outerBits innerBits)
    (ho : (readRowOutput x outerBits innerBits input).Valid word outerBits innerBits)
    (hi : 4*x.outer.base.state.bits.length ≤ input.length)
    (hc : (x.outer.total+1)*(RecoveryRowLookupStream.budget x.outer.bank.row.width+3)+5 ≤ x.outer.lookupCapacity) :
    (rowAdvanced x outerBits innerBits input).Valid word outerBits innerBits := by
  apply advanced_valid _ word outerBits innerBits ho
  have h := read_output_retained x outerBits innerBits input hi
  have hw : (readRowOutput x outerBits innerBits input).outer.bank.row.width=x.outer.bank.row.width :=
    ho.1.2.1.2.1.trans (h.2.2.2.2.2.1.trans hx.1.2.1.2.1.symm)
  rw [h.2.2.1,h.2.2.2.2.1,hw]
  exact hc

end NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
