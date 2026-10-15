import Proof.PCP.PCPPRequestCircuitCode

/-! Pay one selective rewind of the original native source, retaining the
literal canonical circuit field for the exact arity-prefixed source request. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestCircuitReady
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes := PCPPRequestCircuitCode.tapes+1
noncomputable def machine := SelectiveReset.machine PCPPRequestCircuitCode.machine PCPPRequestCircuitCode.nativeSource
def nativeSource := PCPPRequestCircuitCode.nativeSource.castAdd 1
def framedSlot := PCPPRequestCircuitCode.framedSlot.castAdd 1
def rawSlot := PCPPRequestCircuitCode.rawSlot.castAdd 1
def input {n : ℕ} (c : BooleanCircuit n) : Fin tapes → List Bool :=
  Fin.addCases (m:=PCPPRequestCircuitCode.tapes) (n:=1) (PCPPRequestCircuitCode.input c) (fun _ => [])
def budget {n : ℕ} (c : BooleanCircuit n) := 2*PCPPRequestCircuitCode.budget c+2

theorem ready_run {n : ℕ} (c : BooleanCircuit n) :
    ∃ r,run machine (budget c) (input c)=some r ∧
      (∃ padding,r.final.tapes framedSlot=frame
        (ExecutableInterfaces.encodeBooleanCircuit c).bits++List.replicate padding false) ∧
      r.final.heads framedSlot=0 ∧
      r.final.tapes rawSlot=(ExecutableInterfaces.encodeBooleanCircuit c).bits ∧
      r.final.heads rawSlot=0 ∧
      r.final.tapes nativeSource=PCPPRequestNodeGlobal.payload c.nodes (natWord c.output.val) ∧
      r.final.heads nativeSource=0 ∧ r.steps ≤ budget c := by
  obtain ⟨base,hb,⟨padding,bf⟩,bhf,br,bhr,bn,_,_⟩ := PCPPRequestCircuitCode.code_run c
  obtain ⟨r,hr,rt,rh,rs⟩ := DecompositionStreamReset.reset_output_run PCPPRequestCircuitCode.machine
    PCPPRequestCircuitCode.nativeSource _ _ base hb (by rfl)
  have hi : Rewind.recording (initialConfiguration PCPPRequestCircuitCode.machine
      (PCPPRequestCircuitCode.input c)) 0=initialConfiguration machine (input c) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=PCPPRequestCircuitCode.tapes) (n:=1) (fun j => ?_) (fun j => ?_) i
      · simp only [Rewind.recording,Rewind.config,initialConfiguration,PCPPRequestCircuitCode.tapes,
          PCPPRequestCircuitIndex.tapes,PCPPRequestCircuitNodes.tapes,PCPPRequestCircuitNodes.prefixTapes,
          PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_left]
      · simp only [Rewind.recording,Rewind.config,initialConfiguration,PCPPRequestCircuitCode.tapes,
          PCPPRequestCircuitIndex.tapes,PCPPRequestCircuitNodes.tapes,PCPPRequestCircuitNodes.prefixTapes,
          PCPPRequestNodeGlobal.tapes,DecompositionColdPrepare.tapes,Fin.addCases_right]
    · rfl
  rw [hi] at hr
  exact ⟨r,hr,⟨padding,(rt _).trans bf⟩,
    (rh _).trans ((if_neg (PCPPRequestCircuitCode.slots_ne_native 222)).trans bhf),
    (rt _).trans br,(rh _).trans ((if_neg (PCPPRequestCircuitCode.slots_ne_native 232)).trans bhr),
    (rt _).trans bn,by
      change r.final.heads (PCPPRequestCircuitCode.nativeSource.castAdd 1)=0
      exact rh PCPPRequestCircuitCode.nativeSource,rs⟩

end NearCubicWires.RepairOrdinary.PCPPRequestCircuitReady
