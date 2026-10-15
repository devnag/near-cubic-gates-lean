import Proof.PCP.PCPPRequestSource

/-! Expose the complete source caller's literal cold input, so the native
emitter supplies one framed descriptor and no hidden prepared work. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestSource
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem single_input_extend {t e : ℕ} (ht : 0 < t) (bits : List Bool) :
    Fin.addCases (m:=t) (n:=e) (fun j => if j.val=0 then bits else []) (fun _ => [])=
      (fun i : Fin (t+e) => if i.val=0 then bits else []) := by
  funext i
  refine Fin.addCases (m:=t) (n:=e) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left,Fin.val_castAdd]
    by_cases hj : j.val=0 <;> simp only [hj,ite_true,ite_false]
  · have hn : t+j.val≠0 := by omega
    simp only [Fin.addCases_right,Fin.val_natAdd,hn,ite_false]

theorem single_input_from {t e : ℕ} (ht : 0 < t) (bits : List Bool)
    (data : Fin t → List Bool) (h : data=(fun j => if j.val=0 then bits else [])) :
    Fin.addCases (m:=t) (n:=e) data (fun _ => [])=
      (fun i : Fin (t+e) => if i.val=0 then bits else []) := by
  exact (congrArg (fun f : Fin t → List Bool =>
    Fin.addCases (m:=t) (n:=e) (motive:=fun _ => List Bool) f (fun _ => [])) h).trans
    (single_input_extend ht bits)

theorem input_literal (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) :
    input a request=(fun i => if i.val=0 then frame
      (PCPPRequestNodeGlobal.payload request.circuit.nodes (natWord request.circuit.output.val)) else []) := by
  have five (bits : List Bool) : (![bits,[],[],[],[]] : Fin 5 → List Bool)=
      (fun j => if j.val=0 then bits else []) := by
    funext j
    fin_cases j <;> rfl
  unfold input PCPPRequestInput.input PCPPRequestCircuitReady.input PCPPRequestCircuitCode.input
    PCPPRequestCircuitIndex.input PCPPRequestCircuitNodes.input PCPPRequestNodeGlobal.readyInput
    PCPPRequestNodeGlobal.input DecompositionColdPrepare.input DecompositionCapacity.input
  repeat' apply single_input_from (by decide)
  exact five _

theorem cold_run (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) :
    ∃ r,run (machine a) (budget a request)
      (fun i => if i.val=0 then frame
        (PCPPRequestNodeGlobal.payload request.circuit.nodes (natWord request.circuit.output.val)) else [])=some r ∧
      r.final.tapes (outputSlot a)=pcppOutput request (a.output request) ∧
      r.final.heads (outputSlot a)=0 ∧ r.steps ≤ budget a request := by
  obtain ⟨r,hr,ho,hh,hs⟩ := source_run a request
  refine ⟨r,?_,ho,hh,hs⟩
  exact (congrArg (fun data : Fin (tapes a) → List Bool => run (machine a) (budget a request) data)
    (input_literal a request)).symm.trans hr

end NearCubicWires.RepairOrdinary.PCPPRequestSource
