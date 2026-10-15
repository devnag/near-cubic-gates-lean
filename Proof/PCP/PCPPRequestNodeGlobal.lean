import Proof.PCP.PCPPRequestNodeGlobalRun
import Proof.Circuits.DecompositionStreamReset

/-! The fixed circuit-node serializer executes from the actual original
framed input. No caller-supplied capacity or count remains. Its one output
rewind prepares the same balanced-list serializer's source tape. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeGlobal
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def payload {n : ℕ} (nodes : List (BooleanNode n)) (suffix : List Bool) :=
  DecompositionInputCounts.word n nodes.length (PCPPRequestNodeLoop.stream nodes++suffix)
def coldBudget {n : ℕ} (nodes : List (BooleanNode n)) (suffix : List Bool) :=
  budget 12 capacityCoefficient (capacity (payload nodes suffix)) n nodes suffix
noncomputable def coldMachine := machine 12 capacityCoefficient
noncomputable def readyMachine := SelectiveReset.machine coldMachine (outputSlot 12)
def readyInput {n : ℕ} (nodes : List (BooleanNode n)) (suffix : List Bool) : Fin (tapes 12+1) → List Bool :=
  Fin.addCases (m:=tapes 12) (n:=1) (input 12 (payload nodes suffix)) (fun _ => [])

theorem cold_run {n : ℕ} (nodes : List (BooleanNode n)) (suffix : List Bool) :
    ∃ r,run coldMachine (coldBudget nodes suffix) (input 12 (payload nodes suffix))=some r ∧
      r.final.tapes (outputSlot 12)=PCPPRequestNodeLoop.encoded nodes ∧
      r.final.heads (outputSlot 12)=(PCPPRequestNodeLoop.encoded nodes).length ∧
      r.final.tapes (slots 12 0)=payload nodes suffix ∧
      r.final.heads (slots 12 0)=(natWord n++natWord nodes.length).length+
        (PCPPRequestNodeLoop.stream nodes).length ∧
      r.final.tapes (slots 12 644)=List.replicate (capacity (payload nodes suffix)) true ∧
      r.final.heads (slots 12 644)=0 ∧
      r.final.tapes (slots 12 646)=RepairSource.VerifierDecoding.CompareMachine.word nodes.length ∧
      r.final.heads (slots 12 646)=1 ∧ r.steps ≤ coldBudget nodes suffix := by
  apply global_run 12 capacityCoefficient (capacity (payload nodes suffix)) n nodes suffix rfl
  have hc := node_capacity (natWord n++natWord nodes.length) suffix nodes
  simpa only [payload,DecompositionInputCounts.word,List.append_assoc] using hc

theorem ready_run {n : ℕ} (nodes : List (BooleanNode n)) (suffix : List Bool) :
    ∃ r,run readyMachine (2*coldBudget nodes suffix+2) (readyInput nodes suffix)=some r ∧
      r.final.tapes ((outputSlot 12).castAdd 1)=PCPPRequestNodeLoop.encoded nodes ∧
      r.final.heads ((outputSlot 12).castAdd 1)=0 ∧
      r.final.tapes ((slots 12 646).castAdd 1)=RepairSource.VerifierDecoding.CompareMachine.word nodes.length ∧
      r.final.heads ((slots 12 646).castAdd 1)=1 ∧
      r.final.tapes ((slots 12 0).castAdd 1)=payload nodes suffix ∧
      r.final.heads ((slots 12 0).castAdd 1)=(natWord n++natWord nodes.length).length+
        (PCPPRequestNodeLoop.stream nodes).length ∧
      r.steps ≤ 2*coldBudget nodes suffix+2 := by
  obtain ⟨p,hp,po,_,p0,ph0,_,_,pn,phn,_⟩ := cold_run nodes suffix
  obtain ⟨r,hr,rt,rh,rs⟩ := DecompositionStreamReset.reset_output_run coldMachine
    (outputSlot 12) _ _ p hp (by rfl)
  have hn : slots 12 646≠outputSlot 12 := fun h =>
    (by decide : (646 : Fin 647)≠643) (slots_injective 12 h)
  have h0 : slots 12 0≠outputSlot 12 := fun h =>
    (by decide : (0 : Fin 647)≠643) (slots_injective 12 h)
  have hi : Rewind.recording (initialConfiguration coldMachine (input 12 (payload nodes suffix))) 0=
      initialConfiguration readyMachine (readyInput nodes suffix) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=tapes 12) (n:=1) (fun j => ?_) (fun j => ?_) i
      · simp only [Rewind.recording,Rewind.config,initialConfiguration,tapes,DecompositionColdPrepare.tapes,Fin.addCases_left]
      · simp only [Rewind.recording,Rewind.config,initialConfiguration,tapes,DecompositionColdPrepare.tapes,Fin.addCases_right]
    · rfl
  rw [hi] at hr
  refine ⟨r,hr,(rt _).trans po,rh _,(rt _).trans pn,?_,(rt _).trans p0,?_,rs⟩
  · exact (rh _).trans ((if_neg hn).trans phn)
  · exact (rh _).trans ((if_neg h0).trans ph0)

end NearCubicWires.RepairOrdinary.PCPPRequestNodeGlobal
