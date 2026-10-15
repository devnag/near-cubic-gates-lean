import Proof.Amplification.RecoveryOuterLeaf

namespace NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def withOuter (x : State) (data : Children) : State := {x with outer:=data}
noncomputable def onOuter {s : Nat} (p : Machine 68 s) := TapeEmbedding.machine 16 p

theorem withOuter_valid (x : State) (data : Children) (word outerBits innerBits : List Bool)
    (hx : x.Valid word outerBits innerBits) (hd : data.Valid word outerBits)
    (hw : data.base.state.bits.length=x.outer.base.state.bits.length)
    (hc : data.copyCapacity=x.outer.copyCapacity) : (withOuter x data).Valid word outerBits innerBits := by
  refine ⟨hd,hd.1,?_,hx.2.2.2.1,hx.2.2.2.2.1,?_,hx.2.2.2.2.2.2⟩
  · change RecoveryRowLookupTable.Inv data.base.state.bits.length ⟨x.inner,innerBits⟩
    rw [hw]
    exact hx.2.2.1
  · change 2*data.base.state.bits.length+1 ≤ data.copyCapacity
    rw [hw,hc]
    exact hx.2.2.2.2.2.1

theorem outer_run {s : Nat} (p : Machine 68 s) (x : State) (data : Children) (fuel : Nat)
    (base : ExecutionReceipt 68 s)
    (hr : runFrom p fuel (x.outer.cfg p.start)=some base)
    (hf : base.final=data.cfg base.final.control) :
    ∃ r,runFrom (onOuter p) fuel (x.cfg p.start)=some r ∧
      r.final=(withOuter x data).cfg r.final.control ∧ r.steps=base.steps := by
  let r := TapeEmbedding.receipt (fun _ : Fin 16=>0) x.extra base
  have h := TapeEmbedding.run_embed p (fun _ : Fin 16=>0) x.extra fuel _ base hr
  refine ⟨r,h,?_,rfl⟩
  change TapeEmbedding.config (fun _ : Fin 16=>0) x.extra base.final=_
  rw [hf]
  rfl

noncomputable def structuralMachine := onOuter structureMachine
def structured (x : State) (bits : List Bool) := withOuter x (structureOutput x.outer bits)

theorem structural_run (x : State) (word outerBits innerBits : List Bool) (prior : List Row) (rest : List Bool)
    (hx : x.Valid word outerBits innerBits)
    (hw : x.outer.base.code.length=x.outer.base.state.bits.length)
    (hk : x.outer.base.kind.length=x.outer.base.state.bits.length)
    (hc : x.outer.base.count.length=x.outer.base.state.bits.length)
    (hp : readMany (readRow x.outer.bank.row.width) x.outer.total outerBits=some (prior,rest))
    (hprior : checkFrom [] prior=true) :
    ∃ r,runFrom structuralMachine (structureTime x.outer) (x.cfg structuralMachine.start)=some r ∧
      r.final=(structured x outerBits).cfg r.final.control ∧ r.steps ≤ structureTime x.outer ∧
      (structured x outerBits).Valid word outerBits innerBits ∧
      (structured x outerBits).outer.base.valid=unpairCheck prior (dataRow x.outer.base) := by
  obtain ⟨base,hr,hf,hb,hv,ha⟩ := structure_run_checked x.outer word outerBits prior rest hx.1 hw hk hc hp hprior
  obtain ⟨r,hrun,hfinal,hsteps⟩ := outer_run structureMachine x (structureOutput x.outer outerBits)
    (structureTime x.outer) base hr hf
  have hret := structure_retained x.outer outerBits
  exact ⟨r,hrun,hfinal,hsteps.le.trans hb,
    withOuter_valid x _ word outerBits innerBits hx hv (congrArg List.length hret.1) hret.2.2.2.2.2.2.1,ha⟩

end NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
