import Proof.SourceAssembly.SLoadGeometry

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.Pool
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open FixedLivePackets PacketProduction MaskedFamilySource
noncomputable section

/-! ### The four live cold-cache input tapes -/

theorem input_left {q : Nat} (c : BinaryCacheColdJoin.Args q) (j : Fin 372) :
    BinaryCacheColdRun.input c (Fin.castAdd 1 j) = BinaryCacheColdJoin.data0 c j := by
  simp only [BinaryCacheColdRun.input, Fin.addCases_left]

theorem input_right {q : Nat} (c : BinaryCacheColdJoin.Args q) (j : Fin 1) :
    BinaryCacheColdRun.input c (Fin.natAdd 372 j) = [] := by
  simp only [BinaryCacheColdRun.input, Fin.addCases_right]

theorem input_of_val {q : Nat} (c : BinaryCacheColdJoin.Args q) (i : Fin 373) (j : Fin 372)
    (h : i.val = j.val) : BinaryCacheColdRun.input c i = BinaryCacheColdJoin.data0 c j := by
  have he : i = Fin.castAdd 1 j := Fin.ext h
  rw [he, input_left]

theorem input_last {q : Nat} (c : BinaryCacheColdJoin.Args q) (i : Fin 373) (h : i.val = 372) :
    BinaryCacheColdRun.input c i = [] := by
  have he : i = Fin.natAdd 372 (0 : Fin 1) := by
    apply Fin.ext
    show i.val = 372 + (0 : Fin 1).val
    simp [h]
  rw [he, input_right]

theorem data0_blank {q : Nat} (c : BinaryCacheColdJoin.Args q) (j : Fin 372)
    (h98 : j.val ≠ 98) (h224 : j.val ≠ 224) (h225 : j.val ≠ 225) (h226 : j.val ≠ 226) :
    BinaryCacheColdJoin.data0 c j = [] := by
  have e98 : ¬ j = (98 : Fin 372) := fun h => h98 (by rw [h]; rfl)
  have e224 : ¬ j = (224 : Fin 372) := fun h => h224 (by rw [h]; rfl)
  have e225 : ¬ j = (225 : Fin 372) := fun h => h225 (by rw [h]; rfl)
  have e226 : ¬ j = (226 : Fin 372) := fun h => h226 (by rw [h]; rfl)
  simp only [BinaryCacheColdJoin.data0, if_neg e98, if_neg e224, if_neg e225, if_neg e226]

theorem input_blank {q : Nat} (c : BinaryCacheColdJoin.Args q) (i : Fin 373)
    (h98 : i.val ≠ 98) (h224 : i.val ≠ 224) (h225 : i.val ≠ 225) (h226 : i.val ≠ 226) :
    BinaryCacheColdRun.input c i = [] := by
  by_cases h : i.val = 372
  · exact input_last c i h
  · have hlt : i.val < 372 := by have := i.isLt; omega
    rw [input_of_val c i ⟨i.val, hlt⟩ rfl]
    exact data0_blank c ⟨i.val, hlt⟩ h98 h224 h225 h226

theorem input_98 {q : Nat} (c : BinaryCacheColdJoin.Args q) (i : Fin 373) (h : i.val = 98) :
    BinaryCacheColdRun.input c i = exactListWord c.gs := by
  rw [input_of_val c i (98 : Fin 372) h]
  rfl

theorem input_224 {q : Nat} (c : BinaryCacheColdJoin.Args q) (i : Fin 373) (h : i.val = 224) :
    BinaryCacheColdRun.input c i = UnaryTemplate.tape q := by
  rw [input_of_val c i (224 : Fin 372) h]
  rfl

theorem input_225 {q : Nat} (c : BinaryCacheColdJoin.Args q) (i : Fin 373) (h : i.val = 225) :
    BinaryCacheColdRun.input c i = UnaryTemplate.tape c.K := by
  rw [input_of_val c i (225 : Fin 372) h]
  rfl

theorem input_226 {q : Nat} (c : BinaryCacheColdJoin.Args q) (i : Fin 373) (h : i.val = 226) :
    BinaryCacheColdRun.input c i = c.members := by
  rw [input_of_val c i (226 : Fin 372) h]
  rfl

/-! ### Residency: four words and a zero backing -/

/-- The 373 pool-bank equations of `Prepared` reduce to four resident words
and a zero-backed ambient slot at every other index. -/
theorem residency {U q : Nat} (poolSlots : Fin 373 → Fin U)
    (c : BinaryCacheColdJoin.Args q) (A : Fin U → List Bool) (reserve : Fin 373 → Nat)
    (h98 : ∀ i : Fin 373, i.val = 98 →
      A (poolSlots i) = ZeroPadding.pad (reserve i) (exactListWord c.gs))
    (h224 : ∀ i : Fin 373, i.val = 224 →
      A (poolSlots i) = ZeroPadding.pad (reserve i) (UnaryTemplate.tape q))
    (h225 : ∀ i : Fin 373, i.val = 225 →
      A (poolSlots i) = ZeroPadding.pad (reserve i) (UnaryTemplate.tape c.K))
    (h226 : ∀ i : Fin 373, i.val = 226 →
      A (poolSlots i) = ZeroPadding.pad (reserve i) c.members)
    (hblank : ∀ i : Fin 373, i.val ≠ 98 → i.val ≠ 224 → i.val ≠ 225 → i.val ≠ 226 →
      A (poolSlots i) = List.replicate (reserve i) false) :
    ∀ i, A (poolSlots i) = ZeroPadding.pad (reserve i) (BinaryCacheColdRun.input c i) := by
  intro i
  by_cases e98 : i.val = 98
  · rw [h98 i e98, input_98 c i e98]
  by_cases e224 : i.val = 224
  · rw [h224 i e224, input_224 c i e224]
  by_cases e225 : i.val = 225
  · rw [h225 i e225, input_225 c i e225]
  by_cases e226 : i.val = 226
  · rw [h226 i e226, input_226 c i e226]
  rw [hblank i e98 e224 e225 e226, input_blank c i e98 e224 e225 e226, Words.pad_nil]

/-! ### The re-indexing -/

/-- A loader certificate already landing on a bank that is resident at the
pool slots IS a certificate at the consumer's pool-shaped exit. `poolSlots`
need not be injective. -/
theorem reindex {U : Nat} {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {packet : PacketWriter selector a}
    (code : MaskSeedCode mask packet U) (r : Request) (fuel : Nat)
    (H H' : Fin U → Nat) (A A' : Fin U → List Bool)
    (poolSlots : Fin 373 → Fin U) (poolReserve : Fin 373 → Nat)
    (hH : ∀ i, H' (poolSlots i) = 0)
    (hA : ∀ i, A' (poolSlots i) = ZeroPadding.pad (poolReserve i)
      (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) i))
    (h : code.Ready r fuel H H' A A') :
    code.Ready r fuel H (dockH poolSlots H' (fun _ => 0)) A
      (install poolSlots A' (fun i => ZeroPadding.pad (poolReserve i)
        (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) i))) := by
  rw [SLoad.dockH_existing poolSlots H' (fun _ => 0) hH, install_existing poolSlots A' _ hA]
  exact h

/-- The same at the accepted `SeedCode` interface. -/
theorem reindex_base {U : Nat} {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {packet : PacketWriter selector a}
    (code : MaskSeedCode mask packet U) (r : Request) (fuel : Nat)
    (H H' : Fin U → Nat) (A A' : Fin U → List Bool)
    (poolSlots : Fin 373 → Fin U) (poolReserve : Fin 373 → Nat)
    (hH : ∀ i, H' (poolSlots i) = 0)
    (hA : ∀ i, A' (poolSlots i) = ZeroPadding.pad (poolReserve i)
      (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) i))
    (h : code.Ready r fuel H H' A A') :
    code.base.Ready r fuel H (dockH poolSlots H' (fun _ => 0)) A
      (install poolSlots A' (fun i => ZeroPadding.pad (poolReserve i)
        (BinaryCacheColdRun.input (CachedFamilyLoader.cacheArgs a (r.family a)) i))) :=
  MaskSeedCode.project _ r _ _ _ _ _
    (reindex code r fuel H H' A A' poolSlots poolReserve hH hA h)

end
end SLoad.Pool
