import Proof.CaseAnalysis.RecoverySelectorReuseBank

/-! The literal original selector runs with its reusable value/index/stack
backing physically present. Padding transports the same fixed machine. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorReuse
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
open RecoveryBoundedSelectorLoop RecoveryBoundedSelectorFinish
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem padded_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit W D : ℕ) (hblock : start+limit ≤ rowWidth n bound)
    (wires : List (LiveWire b)) (out tail : List Bool)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+wires.length*(3*limit+2)+3*limit ≤ W)
    (hf : b.nodes.length+RecoveryBoundedUniversal.prefixSize
      (fieldItems row start limit hblock 0 (wires.map (fun w=>w.output.val)))+wires.length ≤ W)
    (hc : wires.length ≤ W) (hD : 8388608*(W+1)^3 ≤ D) :
    let raw:=wires.map (fun w=>w.output.val)
    let source:=sourceWord raw++tail
    let a:=(initial b.nodes.length out [] []).iterate row start limit hblock raw
    let refs:=RecoveryBoundedUniversal.references b.nodes.length (fieldItems row start limit hblock 0 raw)
    let f:=folded a.position (a.out++falseBits) refs
    ∃ r,runFrom RecoveryBoundedSelectorFinish.machine (RecoveryBoundedSelectorFinish.budget wires.length W)
      (ZeroPadding.config (caps (capacity W))
        (RecoveryBoundedSelectorFinish.entry (n:=n) row start limit W D b.nodes.length wires.length out [] source []))=some r ∧
      r.steps ≤ RecoveryBoundedSelectorFinish.budget wires.length W ∧
      r.final.heads=heads f.out [] a.skipped.length ∧
      r.final.tapes=paddedData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        f.acc (capacity W) D wires.length limit wires.length f.out source := by
  let raw:=wires.map (fun w=>w.output.val)
  let source:=sourceWord raw++tail
  let a:=(initial b.nodes.length out [] []).iterate row start limit hblock raw
  let refs:=RecoveryBoundedUniversal.references b.nodes.length (fieldItems row start limit hblock 0 raw)
  have hs:=iterate_schedule row start limit hblock raw (initial b.nodes.length out [] [])
  have haPos : a.position=b.nodes.length+RecoveryBoundedUniversal.prefixSize (fieldItems row start limit hblock 0 raw) := hs.1
  have hrlen : refs.length=wires.length := by
    simp only [refs,RecoveryBoundedUniversal.references_length,fieldItems_length,raw,List.length_map]
  have hf' : a.position+wires.length ≤ W := by rw [haPos]; exact hf
  have href : ∀ ref∈refs,ref ≤ W := by
    intro ref hr
    have h:=saved_bound b.nodes.length (fieldItems row start limit hblock 0 raw) ref hr
    rw [←haPos] at h
    omega
  have hz:=erased_small a.position W (a.out++falseBits) refs (by rw [hrlen]; exact hc) href
  have hCap : 1 ≤ capacity W := by
    unfold capacity
    have h : 0 < (W+1)^2 := by positivity
    omega
  obtain ⟨r0,hr0,rs0,rh0,rt0⟩:=join_run b row start limit W D hblock wires out [] tail [] hi hp hf hc hD
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config RecoveryBoundedSelectorFinish.machine (caps (capacity W)) _ _ r0 hr0
  refine ⟨r,hr,rs.le.trans rs0,?_,?_⟩
  · rw [rf]
    change r0.final.heads=_
    rw [rh0,endBank_heads]
  · rw [rf]
    change (fun i=>ZeroPadding.pad (caps (capacity W) i) (r0.final.tapes i))=_
    rw [rt0,endBank_tapes _ _ _ _ _ _ _ _ _ _ _ _ hCap]
    exact padded_after _ _ _ _ _ _ _ _ _ _ hz

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorReuse
