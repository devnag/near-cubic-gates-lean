import Proof.CaseAnalysis.RecoverySourceGraphJoin

/-! One ordinary worker produces the original balanced CNF from only the
SAME raw hierarchy request and paid W, preserving both outside graph work. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSourceGraph
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization SourceInterfaces
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryScheduleEnvelope BalancedCNFSATEncoding
open CloseoutRecoveryWorkspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def graphMachine (k d : ℕ):=RecoveryFocus.machine (graphSlots source k d) RecoveryBoundedColdGraph.machine
def machine (k d CH Cpad : ℕ) (code : List Bool):=
  Join.machine source k d (supplierMachine source k d CH Cpad code) RecoveryBoundedColdGraph.machine
def budget (k d CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n) (W : ℕ) (hpad : k+3 ≤ Cpad):=
  RecoveryBoundedColdSuppliers.budget source k d CH Cpad code (List.ofFn x) W+1+
    RecoveryBoundedColdGraph.budget (RecoveryBoundedGraphBudget.scalarBacking W) W
      (PCPPNativeHierarchyNodes.width source k CH Cpad code x)
      (oracleSizeBound d (PCPPNativeHierarchyNodes.width source k CH Cpad code x))
      (circuit source k d CH Cpad code x hpad)

private theorem input_transport {s : ℕ} (m : Machine 1664 s) (fuel : ℕ)
    (A B : Fin 158→List Bool) (P : ExecutionReceipt 1664 s→Prop) (he : A=B)
    (h : ∃ r,run m fuel (RecoveryBoundedColdGraph.insert [] B)=some r ∧ P r) :
    ∃ r,run m fuel (RecoveryBoundedColdGraph.insert [] A)=some r ∧ P r:=by
  rw [he]
  exact h

theorem cold_run (k d CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n)
    (clock : List Bool) (W : ℕ) (hpad : k+3 ≤ Cpad)
    (hb : 0 < oracleSizeBound d (PCPPNativeHierarchyNodes.width source k CH Cpad code x))
    (hW : originalWorkspace (PCPPNativeHierarchyNodes.width source k CH Cpad code x)
      (oracleSizeBound d (PCPPNativeHierarchyNodes.width source k CH Cpad code x))
      (PCPPNativeHierarchyNodes.queries source k CH Cpad code x)
      (Codec.clauses (PCPPNativeHierarchyNodes.pcp source k CH Cpad code x)).length ≤ W)
    (hsource : (DedupBytes.fields (PCPPNativeHierarchyNodes.pcp source k CH Cpad code x)).length ≤ W)
    (htwo : 2^(PCPPNativeHierarchyNodes.width source k CH Cpad code x) ≤ W) :
    ∃ r,run (machine source k d CH Cpad code) (budget source k d CH Cpad code x W hpad)
      (input source k d (frame (List.ofFn x)++frame clock) W)=some r ∧
      r.steps ≤ budget source k d CH Cpad code x W hpad ∧
      r.final.tapes (graphSlots source k d 1657)=
        frame (balancedCNFPayload (CircuitInputCNF.circuitInputFormula (circuit source k d CH Cpad code x hpad))).bits ∧
      r.final.heads (graphSlots source k d 1657)=0 ∧
      r.final.tapes (graphSlots source k d 144)=ZeroPadding.pad (RecoveryBoundedGraphBudget.scalarBacking W)
        (List.replicate (descriptionWidth (PCPPNativeHierarchyNodes.width source k CH Cpad code x)
          (oracleSizeBound d (PCPPNativeHierarchyNodes.width source k CH Cpad code x))) true) ∧
      r.final.heads (graphSlots source k d 144)=0 ∧
      (∀ j : Fin 5,r.final.tapes (graphSlots source k d (j.natAdd 1659))=
        RecoveryBoundedColdCompile.raw (PCPPNativeHierarchyNodes.width source k CH Cpad code x)
          (oracleSizeBound d (PCPPNativeHierarchyNodes.width source k CH Cpad code x))
          (RecoveryBoundedSelectorLoop.capacity W) (PCPPNativeHierarchyNodes.queries source k CH Cpad code x)
          (Codec.clauses (PCPPNativeHierarchyNodes.pcp source k CH Cpad code x)).length j ∧
        r.final.heads (graphSlots source k d (j.natAdd 1659))=0) ∧
      r.final.tapes (hierarchyPort source k d)=frame (List.ofFn x)++frame clock ∧
      r.final.heads (hierarchyPort source k d)=0 ∧
      r.final.tapes (wPort source k d)=List.replicate W true ∧
      r.final.heads (wPort source k d)=0:=by
  let p:=PCPPNativeHierarchyNodes.pcp source k CH Cpad code x
  let R:=PCPPNativeHierarchyNodes.width source k CH Cpad code x
  let Q:=PCPPNativeHierarchyNodes.queries source k CH Cpad code x
  let b:=oracleSizeBound d R
  let c:=circuit source k d CH Cpad code x hpad
  let B:=RecoveryBoundedGraphBudget.scalarBacking W
  apply Join.run source k d (supplierMachine source k d CH Cpad code) RecoveryBoundedColdGraph.machine
    (RecoveryBoundedColdSuppliers.budget source k d CH Cpad code (List.ofFn x) W)
    (RecoveryBoundedColdGraph.budget B W R b c) (frame (List.ofFn x)++frame clock) W
    (RecoveryBoundedColdSuppliers.output source k d CH Cpad code (List.ofFn x) W)
  · exact prefix_run source k d CH Cpad code (List.ofFn x) clock W hpad
  · refine input_transport RecoveryBoundedColdGraph.machine _ _ _ _
      (output_original source k d CH Cpad code x W) ?_
    exact RecoveryBoundedColdGraph.original_run p R Q
      (PCPPNativeHierarchyNodes.width_fits source k CH Cpad code x hpad)
      (PCPPNativeHierarchyNodes.queries_fit source k CH Cpad code x hpad) x W hb hW hsource htwo

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSourceGraph
