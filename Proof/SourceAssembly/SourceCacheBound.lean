import Proof.SourceAssembly.SourceCacheReady
import Proof.MachineModel.ClosureLocalSupport

/- Actual cache-program support bounds, independent of retained zero reserve.
The bound excludes allocation and prior clearing; it is a maximum with the old
backing, so reuse does not create a reserve recurrence. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace SourceAssemblyCacheBound
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open FixedLivePackets PacketProduction
open MaskedFamilySource PoolColdSource
open SourceAssemblyCache
noncomputable section
attribute [local irreducible] SourceAssemblyCache.machine
  SourceAssemblyCache.readyMachine PoolCold.machine Cold.machine

def startHeads (a : DecompositionAlgorithm) (r : Request) (B w : Nat) (top : List Bool) :
    Fin (SourceAssemblyCache.tapes a+373) → Nat :=
  Fin.addCases (Fin.addCases
    (PoolCold.start (Packets.live (r.family a)) (r.family a).occurrences B w top).heads
    (PoolCold.coldHeads a)) (fun _ : Fin 373 => 0)

def startTapes (a : DecompositionAlgorithm) (r : Request) (B w P : Nat) (top : List Bool) :
    Fin (SourceAssemblyCache.tapes a+373) → List Bool :=
  Fin.addCases (Fin.addCases
    (PoolCold.start (Packets.live (r.family a)) (r.family a).occurrences B w top).tapes
    (PoolCold.coldData a P r.q))
    (fun j : Fin 373 => if j=225 then UnaryTemplate.tape (maskData a r).K else
      if j=226 then (maskData a r).word else [])

def dirtyBound (a : DecompositionAlgorithm) (r : Request) (B w P : Nat) (top : List Bool)
    (R : Fin (SourceAssemblyCache.tapes a+373) → Nat)
    (i : Fin (SourceAssemblyCache.tapes a+373)) : Nat :=
  max (R i) (max ((startTapes a r B w P top i).length)
    (startHeads a r B w top i + SourceAssemblyCache.budget a
      (r.family a).occurrences B w P + 1))

theorem paid_bounds (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (r : Request) (B w P : Nat) (top : List Bool)
    (R : Fin (SourceAssemblyCache.tapes a+373) → Nat)
    (hw : 0<w) (hqw : r.q≤w)
    (hb : ∀ g∈(r.family a).occurrences,(CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : ∀ g∈(r.family a).occurrences,
      (g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w)
    (hqP : r.q≤P)
    (hi : (segment (CloseoutRowsUniversal.pool (Packets.live (r.family a))
      (r.family a).occurrences) top).length≤1000*(P+2)^2) :
    ∃ H A,
      Step (SourceAssemblyCache.machine a)
        (SourceAssemblyCache.budget a (r.family a).occurrences B w P)
        (startHeads a r B w top)
        (fun i => ZeroPadding.pad (R i) (startTapes a r B w P top i))
        (dockH (poolSlots a) H (fun _=>0))
        (install (poolSlots a) A (fun j => ZeroPadding.pad (R (poolSlots a j))
          (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) j))) ∧
      (∀ i, dockH (poolSlots a) H (fun _=>0) i ≤ dirtyBound a r B w P top R i) ∧
      (∀ i, (install (poolSlots a) A (fun j => ZeroPadding.pad (R (poolSlots a j))
          (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) j)) i).length
          ≤ dirtyBound a r B w P top R i) := by
  obtain ⟨H,A,paid⟩ := SourceAssemblyCacheReady.request_pool_entry
    selector a r B w P top R hw hqw hb hm hqP hi
  refine ⟨H,A,paid,?_,?_⟩
  · intro i
    obtain ⟨rc,hr,rh,rt,rs⟩ := paid
    have bound := SelectiveReset.prefix_head (prefix_of_run _ _ _ _ hr).1 i
    rw [rh] at bound
    change dockH (poolSlots a) H (fun _=>0) i ≤ startHeads a r B w top i+rc.steps at bound
    unfold dirtyBound
    omega
  · intro i
    apply LocalSupport.step_fits paid i
    · simp only [ZeroPadding.pad,List.length_append,List.length_replicate]
      change (startTapes a r B w P top i).length+
        (R i-(startTapes a r B w P top i).length) ≤ _
      unfold dirtyBound
      omega
    · change startHeads a r B w top i+SourceAssemblyCache.budget a
        (r.family a).occurrences B w P+1 ≤ _
      unfold dirtyBound
      omega

end
end SourceAssemblyCacheBound
