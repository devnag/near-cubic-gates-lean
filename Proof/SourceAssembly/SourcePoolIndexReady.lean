import Proof.SourceAssembly.SourcePoolIndexRun
import Proof.SourceAssembly.SLoadSuffixFrame

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2000
set_option warningAsError true
set_option linter.unusedVariables false
namespace SourceAssemblyPoolIndexReady
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open FixedLivePackets PacketProduction
open MaskedFamilySource PoolColdSource
open SourceAssemblyPoolIndex
noncomputable section
attribute [local irreducible] SourceAssemblyPoolIndex.machine PoolCold.machine Cold.machine

/-- The actual paid index producer supplies precisely suffix port5, including
retained zero backing outside the frame. The other suffix fields remain the
separate producers' duties. No logical index word or count driver is assumed. -/
theorem request_run (a : DecompositionAlgorithm) (r : Request)
    (B w P : Nat) (top : List Bool)
    (R : Fin (baseTapes a+6)→Nat)
    (hw : 0<w) (hqw : r.q≤w)
    (hb : ∀ g∈(r.family a).occurrences,(CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : ∀ g∈(r.family a).occurrences,
      (g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w)
    (hqP : r.q≤P)
    (hi : (segment (CloseoutRowsUniversal.pool (Packets.live (r.family a))
      (r.family a).occurrences) top).length≤1000*(P+2)^2) :
    ∃ H A, Step (machine a) (budget a (Packets.live (r.family a)) (r.family a).occurrences B w P)
      (Fin.addCases (Fin.addCases (PoolCold.start (Packets.live (r.family a))
        (r.family a).occurrences B w top).heads (PoolCold.coldHeads a)) (fun _ : Fin 6=>0))
      (fun i=>ZeroPadding.pad (R i) (Fin.addCases (Fin.addCases
        (PoolCold.start (Packets.live (r.family a)) (r.family a).occurrences B w top).tapes
        (PoolCold.coldData a P r.q)) (fun _ : Fin 6=>[]) i)) H A ∧
      H (indexPorts a 7)=0 ∧
      A (indexPorts a 7)=SLoad.SuffixFrame.entry 0 0 (R (indexPorts a 7))
        (maskData a r).word r.nativeWord (r.supportWord a) (r.indexWord a) (r.topWord a) 5 := by
  obtain ⟨H,A,paid,head,word⟩:=run a (Packets.live (r.family a)) (r.family a).occurrences
    B w P top hw hqw hb hm hqP hi
  refine ⟨H,(fun i=>ZeroPadding.pad (R i) (A i)),paid.pad R,head,?_⟩
  change ZeroPadding.pad (R (indexPorts a 7)) (A (indexPorts a 7))=
    ZeroPadding.pad (R (indexPorts a 7)) (RepairOrdinary.frame (r.indexWord a))
  exact congrArg (ZeroPadding.pad (R (indexPorts a 7))) word

end
end SourceAssemblyPoolIndexReady
