import Proof.CaseAnalysis.FinalSupplierRowInput
import Proof.MachineModel.NativeFamily

/-! The A.12 hardwiring pool keeps the lowered monomials and changes each
absolute child index c to N*yi+c+1. This pins the exact bytes consumed by
NativeFamily.rawWord; no relabelled input tape is assumed. -/
namespace NearCubicWires.P1Closure.RawRelabelShape
open CanonicalFourfoldRowProgram RepairRepresentation SupplierPipeline RepairOrdinary
open RepairSource.CloseoutFinal
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def Valid (N : ℕ) (P : StructuralGF2Polynomial) := ∀ m∈P,∀ c∈m,c<N

theorem valid_mul {N : ℕ} {P Q : StructuralGF2Polynomial} (hp : Valid N P) (hq : Valid N Q) :
    Valid N (structuralGF2Mul P Q) := by
  intro m hm c hc
  obtain ⟨l,hl,hm⟩:=List.mem_flatMap.mp hm
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hm
  rcases List.mem_append.mp hc with hc|hc
  · exact hp l hl c hc
  · exact hq r hr c hc

theorem valid_product {N : ℕ} (ps : List StructuralGF2Polynomial) (h : ∀ p∈ps,Valid N p) :
    Valid N (structuralGF2Product ps) := by
  induction ps with
  | nil=>simp [Valid,structuralGF2Product,structuralGF2One]
  | cons p ps ih=>
    exact valid_mul (h p (by simp)) (ih (fun q hq=>h q (by simp [hq])))

theorem valid_substitute {N : ℕ} (atom : ℕ→StructuralGF2Polynomial)
    (h : ∀ c,Valid N (atom c)) (P : StructuralGF2Polynomial) :
    Valid N (structuralGF2Substitute atom P) := by
  induction P with
  | nil=>simp [Valid,structuralGF2Substitute,structuralGF2Zero]
  | cons m P ih=>
    have hp:=valid_product (m.map atom) (by intro p hp;obtain ⟨c,_,rfl⟩:=List.mem_map.mp hp;exact h c)
    intro l hl c hc
    rcases List.mem_append.mp hl with hl|hl
    · exact hp l hl c hc
    · exact ih l hl c hc

theorem cache_valid {q : ℕ} (a : DecompositionAlgorithm)
    (gs : List (SupportedNormalizedGate q)) (i : Fin gs.length) :
    Valid (ExtDecompositionBatch.GS a gs).length (RepairSource.CloseoutRowsUniversal.cacheAtom a gs i) := by
  unfold RepairSource.CloseoutRowsUniversal.cacheAtom
  rw [CloseoutRowsRawAtomCache.source_getElem]
  exact CloseoutRowsRawAtomMeaning.indices_valid a gs i

theorem lower_valid {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (P : StructuralGF2Polynomial) :
    Valid (C10SupplierRowInput.childList a live occ).length
      (RepairSource.CloseoutRowsUniversal.lower a live occ P) := by
  apply valid_substitute
  intro c
  unfold RepairSource.CloseoutRowsUniversal.atomOfCode
  split
  · intro m hm d hd
    rcases List.mem_append.mp hm with hm|hm
    · exact cache_valid a _ _ m hm d hd
    · exact cache_valid a _ _ m hm d hd
  · simp [Valid,structuralGF2Zero]

theorem raw_index_row {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (s : ℕ) (harity : (s+1)/2+s/2=liveᶜ.card)
    (P : StructuralGF2Polynomial) (yi : Fin (C10SupplierRowInput.liveList live).length) :
    ExtIncidence.NativeFamily.rawWord (C10SupplierRowInput.indexRow a live occ s harity P yi)=
      ExtIncidence.stream ((RepairSource.CloseoutRowsUniversal.lower a live occ P).map
        (List.map (fun c=>(C10SupplierRowInput.childList a live occ).length*yi.val+c+1))) := by
  unfold ExtIncidence.NativeFamily.rawWord ExtIncidence.rawIndices C10SupplierRowInput.indexRow
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro m hm
  dsimp only [Function.comp_def]
  rw [List.map_map]
  apply List.map_congr_left
  intro c hc
  have h:=lower_valid a live occ P m hm c hc
  simp [C10SupplierRowInput.poolIndex,h]

end
end NearCubicWires.P1Closure.RawRelabelShape
