import Proof.MachineModel.LoopState

/-! The actual cleaned occurrence returns exactly the next reusable state. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a : DecompositionAlgorithm)

theorem round_run (C q : ℕ) (g : SupportedNormalizedGate q) (pre rest c1 c2 c3 : List Bool)
    (hC : bodyCost a q g<C) :
    Step (cleanRound a) (roundCost a C g)
      (loopInH a pre.length c1 c2 c3)
      (loopInA a C q (pre++frame (nativeWord g)++rest) c1 c2 c3)
      (loopInH a (pre.length+(frame (nativeWord g)).length)
        (c1++natWord (children a g).length) (c2++(children a g).flatMap exactWord)
        (c3++List.replicate (children a g).length true))
      (loopInA a C q (pre++frame (nativeWord g)++rest)
        (c1++natWord (children a g).length) (c2++(children a g).flatMap exactWord)
        (c3++List.replicate (children a g).length true)) := by
  obtain ⟨K,KH,run⟩:=cleaned_body a C q g pre rest c1 c2 c3
    (loopHeads a pre.length c1 c2 c3)
    (loopTapes a C q (pre++frame (nativeWord g)++rest) c1 c2 c3)
    (by intro i;simp [loopTapes,bk]) (by intro i;simp [loopHeads,bk])
    (by simp [loopTapes,str,ex]) (by simp [loopHeads,str,ex])
    (by simp [loopTapes,fcp,ex]) (by simp [loopHeads,fcp,ex])
    (by simp [loopTapes,cnt,ex]) (by simp [loopHeads,cnt,ex])
    (by simp [loopTapes,bod,ex]) (by simp [loopHeads,bod,ex])
    (by simp [loopTapes,tot,ex]) (by simp [loopHeads,tot,ex])
    (by simp [loopTapes,dom,ex]) (by simp [loopHeads,dom,ex])
    (by simp [loopTapes,drv,ex]) (by simp [loopHeads,drv,ex])
    (by simp [loopTapes,wsp,ex]) (by simp [loopHeads,wsp,ex])
    hC
  have result:=body_state a C q g pre rest c1 c2 c3 K KH
  exact run.congr result.1 result.2

end NearCubicWires.ExtDecompositionBatch
