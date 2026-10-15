import Proof.CaseAnalysis.WitnessFamilyWork

/-! Keep the complete family controller's state type named at its
consumer boundary, as for the existing complete circuit controllers. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyRun
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def workerProgram {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ) : Σ z,Machine 3241 z:=
  ⟨_,FamilyWork.machine (FamilyRound.machine circuit k q)⟩
def worker {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ) : Machine 3241 (workerProgram circuit k q).1:=
  (workerProgram circuit k q).2
def program {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ) : Σ z,Machine 3241 z:=
  ⟨_,RecoveryGatedSequence.machine FamilyDock.reader (worker circuit k q) 724⟩
def machine {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ) : Machine 3241 (program circuit k q).1:=
  (program circuit k q).2

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyRun
