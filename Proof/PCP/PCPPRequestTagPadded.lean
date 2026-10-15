import Proof.PCP.PCPPRequestTagArity

/-! The finite classifier accepts the actual zero-padded natural-code field
left by the shared serializer and preserves that allocated source field. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestTagArity
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def paddedInput (tag : Fin 5) (padding : ℕ) : Fin 3 → List Bool :=
  fun j => if j=0 then frame (code tag)++List.replicate padding false else []
def paddedOutput (tag : Fin 5) (padding : ℕ) : Fin 3 → List Bool :=
  ![frame (code tag)++List.replicate padding false,[outputFlag tag],List.replicate (steps tag) false]

theorem padded_run (tag : Fin 5) (padding : ℕ) :
    ClockJoin.ReadyRun machine 36 (paddedInput tag padding) (paddedOutput tag padding) := by
  let caps : Fin 3 → ℕ := fun j => if j=0 then (frame (code tag)).length+padding else 0
  have h := PCPPairReusable.padded_ready _ _ _ (tag_run tag) caps
  have hin : (fun j => ZeroPadding.pad (caps j) (if j=0 then frame (code tag) else []))=
      paddedInput tag padding := by
    funext j
    fin_cases j <;> simp [caps,ZeroPadding.pad,paddedInput]
  have hout : (fun j => ZeroPadding.pad (caps j) (output tag j))=paddedOutput tag padding := by
    funext j
    fin_cases j <;> simp [caps,ZeroPadding.pad,output,paddedOutput]
  rw [hin,hout] at h
  exact h

end NearCubicWires.RepairOrdinary.PCPPRequestTagArity
