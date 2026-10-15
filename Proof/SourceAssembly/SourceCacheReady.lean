import Proof.SourceAssembly.SourceCache

/- Retained-bank form of the paid cache join, specialized to the exact Request
and the same mask bitmap used by packet production. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace SourceAssemblyCacheReady
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open FixedLivePackets PacketProduction
open MaskedFamilySource PoolColdSource
open SourceAssemblyCache
noncomputable section
attribute [local irreducible] SourceAssemblyCache.machine
  SourceAssemblyCache.readyMachine PoolCold.machine Cold.machine

theorem request_members (a : DecompositionAlgorithm) (r : Request) :
    CloseoutRowsGateSupport.gateMembers (Packets.live (r.family a)) = (maskData a r).word := rfl

theorem request_extra (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (r : Request) (i : Fin 373) :
    extra (Packets.live (r.family a)) i =
      if i=225 then UnaryTemplate.tape (maskData a r).K else
      if i=226 then (maskData a r).word else [] := by
  have hc := (geometryOf selector a r).card
  simp only [extra,hc,request_members]
  rfl

/-- The same paid cache program and cost run on a retained physical bank.
The mask and K template must be resident from their earlier paid producers;
the original child cache, q template, and all consumer zero ports are proved. -/
theorem request_pool_entry (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (r : Request) (B w P : Nat) (top : List Bool)
    (R : Fin (SourceAssemblyCache.tapes a+373) → Nat)
    (hw : 0<w) (hqw : r.q≤w)
    (hb : ∀ g∈(r.family a).occurrences,(CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : ∀ g∈(r.family a).occurrences,
      (g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w)
    (hqP : r.q≤P)
    (hi : (segment (CloseoutRowsUniversal.pool (Packets.live (r.family a))
      (r.family a).occurrences) top).length≤1000*(P+2)^2) :
    ∃ (H : Fin (SourceAssemblyCache.tapes a+373) → Nat) (A : Fin (SourceAssemblyCache.tapes a+373) → List Bool),
      Step (SourceAssemblyCache.machine a) (SourceAssemblyCache.budget a (r.family a).occurrences B w P)
        (Fin.addCases
          (Fin.addCases (PoolCold.start (Packets.live (r.family a))
            (r.family a).occurrences B w top).heads (PoolCold.coldHeads a))
          (fun _ : Fin 373 => 0))
        (fun i => ZeroPadding.pad (R i) (Fin.addCases
          (Fin.addCases (PoolCold.start (Packets.live (r.family a))
            (r.family a).occurrences B w top).tapes (PoolCold.coldData a P r.q))
          (fun j : Fin 373 => if j=225 then UnaryTemplate.tape (maskData a r).K else
            if j=226 then (maskData a r).word else []) i))
        (dockH (SourceAssemblyCache.poolSlots a) H (fun _ => 0))
        (install (SourceAssemblyCache.poolSlots a) A (fun j => ZeroPadding.pad (R (SourceAssemblyCache.poolSlots a j))
          (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) j))) := by
  obtain ⟨H,A,run⟩ := SourceAssemblyCache.pool_entry a (Packets.live (r.family a)) (r.family a).occurrences
    B w P top hw hqw hb hm hqP hi
  have paid := run.pad R
  rw [SourceAssemblyReuse.pad_install] at paid
  have he : extra (Packets.live (r.family a)) =
      fun j : Fin 373 => if j=225 then UnaryTemplate.tape (maskData a r).K else
        if j=226 then (maskData a r).word else [] :=
    funext (request_extra selector a r)
  rw [he] at paid
  refine ⟨H,(fun i => ZeroPadding.pad (R i) (A i)),?_⟩
  simpa only [args,CachedFamilyLoader.cacheArgs] using paid

end
end SourceAssemblyCacheReady
