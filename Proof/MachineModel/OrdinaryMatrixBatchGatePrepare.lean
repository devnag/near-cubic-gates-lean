import Proof.MachineModel.OrdinaryMatrixBatchGateBank

/-! The repeated gate body's executed clear/reset/cut-load prefix. The only
new gate data are read from the original source at its retained cursor. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchGatePrepare
open LocalBitMultitape MatrixScoreBatch
open MatrixScoreReusableRanks (D)
open MatrixBatchGateClear (tapes heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine MatrixBatchGateReset.machine MatrixBatchGateBank.bank
def budget (r : Request) := MatrixBatchGateReset.budget r+1+MatrixScoreBankReady.budget r.width r.p
noncomputable def input (r : Request) (gate : Fin r.Gates) (assignment id cap : ℕ)
    (pre suffix out : List Bool) (backing : Fin 30 → List Bool) :=
  RecoveryCalls.restarted machine (heads pre.length out.length)
    (tapes r assignment id cap (pre++cutWord r.p (r.cuts.get gate)++suffix) out backing)

theorem prepare_run (r : Request) (gate : Fin r.Gates) (assignment id cap : ℕ)
    (pre suffix out : List Bool) (backing : Fin 30 → List Bool) (hb : ∀ i,(backing i).length≤D r) :
    ∃ actual,runFrom machine (budget r) (input r gate assignment id cap pre suffix out backing)=some actual ∧
      actual.final.heads=heads (pre.length+(cutWord r.p (r.cuts.get gate)).length) out.length ∧
      actual.final.tapes=tapes r 0 0 (max cap (D r+1))
        (pre++cutWord r.p (r.cuts.get gate)++suffix) out (MatrixBatchGateBank.loaded r gate) ∧
      actual.steps≤budget r := by
  obtain ⟨prepared,hp,ph,pt,ps⟩ := MatrixBatchGateReset.prepare_run r assignment id cap pre.length
    (pre++cutWord r.p (r.cuts.get gate)++suffix) out backing hb
  obtain ⟨banked,hb,bh,bt,bs⟩ := MatrixBatchGateBank.bank_run r gate (max cap (D r+1)) pre suffix out
  have hi : Composition.restart prepared.final MatrixBatchGateBank.bank.start=
      MatrixBatchGateBank.input r gate (max cap (D r+1)) pre suffix out := by
    apply configuration_ext
    · rfl
    · exact ph
    · exact pt
  rw [←hi] at hb
  have joined := Composition.run_join MatrixBatchGateReset.machine MatrixBatchGateBank.bank _ _ _ prepared banked hp hb
  refine ⟨Composition.joinedReceipt prepared banked,joined,bh,bt,?_⟩
  change prepared.steps+1+banked.steps≤_
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.MatrixBatchGatePrepare
