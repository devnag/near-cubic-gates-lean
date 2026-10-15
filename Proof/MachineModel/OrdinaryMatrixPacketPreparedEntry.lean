import Proof.MachineModel.OrdinaryMatrixPacketRestoreDock

/-! Exact restored-array correspondence for the next paid packet call. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketPreparedEntry
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
open MatrixPacketRestoreDock (slots)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem tapes (a : WilliamsAlgorithm) (E cap log left right : ℕ) (r : Request) (bit : ℕ) (out : List Bool)
    (ambient : Fin (MatrixPacketWorkClear.tapes a E) → List Bool)
    (hpdata : ∀ i,¬MatrixVariablePacketWorkspace.working a i →
      ambient (MatrixPacketBootstrapErase.old a E i)=(MatrixVariablePacketReset.input a r bit out).tapes i)
    (i : Fin (MatrixVariablePacketWorkspace.tapes a)) :
    MatrixPacketRestore.output a E cap log left right (word r) ambient (slots a E i)=
      (ZeroPadding.config (MatrixVariablePacketWorkspace.caps a cap) (MatrixVariablePacketReset.input a r bit out)).tapes i := by
  have ho := MatrixPacketRestoreDock.output_tapes a E cap log left right (word r) ambient i
  have ci := MatrixPacketEntryForm.input_tapes a r bit out i
  change MatrixPacketRestore.output a E cap log left right (word r) ambient (slots a E i)=
    ZeroPadding.pad (MatrixVariablePacketWorkspace.caps a cap i) ((MatrixVariablePacketReset.input a r bit out).tapes i)
  by_cases h0 : i.val=0
  · have hw : MatrixVariablePacketWorkspace.working a i := by
      unfold MatrixVariablePacketWorkspace.working
      have hK : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
      omega
    rw [if_pos h0] at ho ci
    have hc : MatrixVariablePacketWorkspace.caps a cap i=cap := if_pos hw
    rw [hc]
    exact ho.trans (congrArg (ZeroPadding.pad cap) ci).symm
  rw [if_neg h0] at ho ci
  by_cases hw : MatrixVariablePacketWorkspace.working a i
  · rw [if_pos hw] at ho
    rw [if_neg hw.1,if_neg hw.2] at ci
    have hp : ZeroPadding.pad (MatrixVariablePacketWorkspace.caps a cap i)
        ((MatrixVariablePacketReset.input a r bit out).tapes i)=List.replicate cap false := by
      rw [ci]
      simp [MatrixVariablePacketWorkspace.caps,hw,ZeroPadding.pad]
    exact ho.trans hp.symm
  · rw [if_neg hw] at ho
    have hp : ZeroPadding.pad (MatrixVariablePacketWorkspace.caps a cap i)
        ((MatrixVariablePacketReset.input a r bit out).tapes i)=ambient (MatrixPacketBootstrapErase.old a E i) := by
      simp only [MatrixVariablePacketWorkspace.caps,if_neg hw,ZeroPadding.pad_zero]
      exact (hpdata i hw).symm
    exact ho.trans hp.symm

end NearCubicWires.RepairOrdinary.MatrixPacketPreparedEntry
