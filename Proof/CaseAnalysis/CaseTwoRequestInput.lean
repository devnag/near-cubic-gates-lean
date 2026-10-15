import Proof.PCP.PCPPRequestSourceInput
import Proof.PCP.PCPPNativeRequestSchema
import Proof.Hierarchy.HierarchyBinaryPower

/-! The original native request descriptor is serialized to the exact
faithful input. One paid rewind restores all heads for the following copy
and source/honest calls. Every non-input cell starts empty. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.RequestInput
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Rewind.machine PCPPRequestInput.machine
def tapes:=PCPPRequestInput.tapes+1
def outputSlot : Fin tapes:=PCPPRequestInput.outputSlot.castAdd 1
def input (word : List Bool) : Fin tapes→List Bool:=SourceHandoff.sourceTapes (frame word)
def budget {n : ℕ} (c : BooleanCircuit n):=2*PCPPRequestInput.budget c+2

theorem input_literal {n : ℕ} (c : BooleanCircuit n) :
    PCPPRequestInput.input c=SourceHandoff.sourceTapes (frame (PCPPNative.descriptor c)):=by
  have five (bits : List Bool) : (![bits,[],[],[],[]] : Fin 5→List Bool)=
      (fun j=>if j.val=0 then bits else []):=by funext j;fin_cases j <;>rfl
  unfold PCPPRequestInput.input PCPPRequestCircuitReady.input PCPPRequestCircuitCode.input
    PCPPRequestCircuitIndex.input PCPPRequestCircuitNodes.input PCPPRequestNodeGlobal.readyInput
    PCPPRequestNodeGlobal.input DecompositionColdPrepare.input DecompositionCapacity.input
  repeat' apply PCPPRequestSource.single_input_from (by decide)
  exact five _

theorem request_run {n0 : ℕ} (request : PCPPRequest n0) : ∃ out,
    ClockJoin.ReadyRun machine (budget request.circuit) (input (PCPPNative.descriptor request.circuit)) out ∧
      out outputSlot=frame (pcppInput request):=by
  obtain ⟨base,hb,bt,_bh,bs⟩:=PCPPRequestInput.request_run request
  obtain ⟨r,hr,ht,hh,hs,_⟩:=Rewind.reset_run PCPPRequestInput.machine _ _ base hb
  have hi : Fin.addCases (PCPPRequestInput.input request.circuit) (fun _ : Fin 1=>[])=
      input (PCPPNative.descriptor request.circuit):=by
    rw [input_literal]
    exact PCPPRequestSource.single_input_extend (by decide) _
  change run machine (2*base.steps+2)
    (Fin.addCases (m:=PCPPRequestInput.tapes) (n:=1) (PCPPRequestInput.input request.circuit) (fun _=>[]))=some r at hr
  rw [hi] at hr
  have ready : ClockJoin.ReadyRun machine (2*base.steps+2) (input (PCPPNative.descriptor request.circuit)) r.final.tapes:=
    ⟨r,hr,rfl,hh,hs.le⟩
  exact ⟨_,ClockJoin.enlarge _ _ _ _ _ ready (by unfold budget;omega),(ht _).trans bt⟩

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.RequestInput
