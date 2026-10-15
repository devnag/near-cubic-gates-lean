import Proof.MachineModel.OccurrenceLoop

/-! A run receipt for the whole original occurrence stream, including the
terminal driver test and the paid return to its sentinel. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom RepairOrdinary.RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a : DecompositionAlgorithm)

def loopCost {q : ℕ} (C : ℕ) (occ : List (SupportedNormalizedGate q)):=roundSum a C occ+occ.length+3

theorem occurrence_run (C q : ℕ) (occ : List (SupportedNormalizedGate q))
    (pre rest c1 c2 c3 : List Bool) (hC : ∀ g∈occ,bodyCost a q g<C) :
    ∃ r,runFrom (occurrenceLoop a) (loopCost a C occ)
      (loopCfg a 0 C q pre.length (pre++requestStream occ++rest) c1 c2 c3 occ.length 1)=some r ∧
      r.final=loopCfg a 3 C q (pre.length+(requestStream occ).length) (pre++requestStream occ++rest)
        (c1++(counts a occ).flatMap natWord) (c2++(GS a occ).flatMap exactWord)
        (c3++List.replicate (B a occ) true) occ.length 1 ∧ r.steps≤loopCost a C occ := by
  obtain ⟨n,hn,path⟩:=remaining a C q occ pre rest c1 c2 c3 occ.length 0 (by omega) hC
  obtain ⟨r,hr,hf,hs⟩:=path.run (by
    simp [occurrenceLoop,loopCfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  change n≤loopCost a C occ at hn
  have more:=runFrom_moreFuel (occurrenceLoop a) n (loopCost a C occ-n) _ r hr
  rw [Nat.add_sub_of_le hn] at more
  exact ⟨r,more,hf,by omega⟩

end NearCubicWires.ExtDecompositionBatch
