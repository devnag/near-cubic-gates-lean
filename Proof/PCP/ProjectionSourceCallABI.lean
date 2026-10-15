import Proof.PCP.ProjectionSourceCall

namespace NearCubicWires.RepairSource.ProjectionNormalization.SourceCall
open RepairOrdinary LocalBitMultitape SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem input_eq {v : OrdinaryVerifier} {T : ℕ → ℕ} (source : ProjectionSourceAlgorithm v T)
    (r : InputRequest) : input source r=fun i => if i.val=0 then frame (List.ofFn r.2)
      else if i.val=1 then frame (T r.1).bits else [] := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;> rfl
  · simp only [input,Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega),if_neg (by omega)]

end NearCubicWires.RepairSource.ProjectionNormalization.SourceCall
