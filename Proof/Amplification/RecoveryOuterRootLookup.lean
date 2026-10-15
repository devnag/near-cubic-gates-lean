import Proof.Amplification.RecoveryOuterRootLayout

namespace NearCubicWires.RepairOrdinary.RecoveryOuterRoot
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem root_run (x : State) (word outerBits innerBits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word outerBits innerBits)
    (hp : readMany (readRow x.data.outer.bank.row.width) x.data.outer.total outerBits=some (rows,rest)) :
    ∃ r,runFrom rootMachine (RecoveryRowRoot.checkTime x.root) (x.cfg rootMachine.start)=some r ∧
      r.final=(output x outerBits).cfg r.final.control ∧ r.steps ≤ RecoveryRowRoot.checkTime x.root ∧
      (output x outerBits).Valid word outerBits innerBits ∧
      (output x outerBits).data.outer.base.valid=rows.any (fun row=>decide (RadixSemantics.value x.key=row.code)) := by
  obtain ⟨base,hr,hf,hb,hv,ha⟩ := RecoveryRowRoot.root_check_run x.root word outerBits rows rest ⟨hx.1.1,hx.2⟩ hp
  let embedded := TapeEmbedding.receipt (fun _ : Fin 16=>0) x.data.extra base
  have he := TapeEmbedding.run_embed RecoveryRowRoot.checkMachine (fun _ : Fin 16=>0) x.data.extra
    (RecoveryRowRoot.checkTime x.root) _ base hr
  let r := TapeRenaming.receipt layout embedded
  have h := TapeRenaming.run_rename layout (TapeEmbedding.machine 16 RecoveryRowRoot.checkMachine)
    (RecoveryRowRoot.checkTime x.root) _ embedded he
  rw [layout_config] at h
  refine ⟨r,h,?_,hb,?_,ha⟩
  · change TapeRenaming.config layout (TapeEmbedding.config (fun _ : Fin 16=>0) x.data.extra base.final)=_
    rw [hf]
    exact layout_config (output x outerBits) base.final.control
  · refine ⟨RecoveryOuterLeaf.withOuter_valid x.data _ word outerBits innerBits hx.1 hv.1 rfl rfl,hx.2⟩

end NearCubicWires.RepairOrdinary.RecoveryOuterRoot
