import Proof.CaseAnalysis.RowsUniversalPool
import Proof.CaseAnalysis.RowsRawAtomCache

/-! One input-independent residual polynomial on the actual absolute child
cache. The physical paired reader emits these exact two adjacent cache bodies;
its meaning holds for every assignment/frozen column with the same syntax. -/
namespace NearCubicWires.RepairSource.CloseoutRowsUniversal
open SupplierPipeline RepairRepresentation CanonicalFourfoldRowProgram CloseoutRawRows
open RepairOrdinary ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable {q : ℕ}

def originalIndex (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q))
    (i : Fin occ.length) : Fin (pool live occ).length:=⟨2*i.val,by rw [pool_length];omega⟩
def constantIndex (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q))
    (i : Fin occ.length) : Fin (pool live occ).length:=⟨2*i.val+1,by rw [pool_length];omega⟩
def cacheAtom (a : DecompositionAlgorithm) (gs : List (SupportedNormalizedGate q)) (i : Fin gs.length) :=
  (CloseoutRowsRawAtomCache.sourceCache a gs)[i.val]'(by rw [CloseoutRowsRawAtomCache.source_length];exact i.isLt)
def assignment (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (x : BitInput q) :=
  encodedFiniteBooleanAssignment (fun j : Fin (GS a (pool live occ)).length=>(GS a (pool live occ)).get j |>.eval x)
def residualAtom (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (i : Fin occ.length) : StructuralGF2Polynomial :=
  structuralGF2Add (cacheAtom a (pool live occ) (originalIndex live occ i))
    (cacheAtom a (pool live occ) (constantIndex live occ i))

theorem original_value (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (i : Fin occ.length) (x : BitInput q) :
    evaluateStructuralGF2 (assignment a live occ x)
      (cacheAtom a (pool live occ) (originalIndex live occ i))=(occ.get i).eval x:=by
  have h:=CloseoutRowsRawAtomCache.source_value a (pool live occ) (originalIndex live occ i) x
  simpa only [cacheAtom,assignment,List.get_eq_getElem,originalIndex,
    pool_original live occ i.val i.isLt] using h

theorem constant_value (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (i : Fin occ.length) (x : BitInput q) :
    evaluateStructuralGF2 (assignment a live occ x)
      (cacheAtom a (pool live occ) (constantIndex live occ i))=residualConstant (occ.get i).gate live x:=by
  have h:=CloseoutRowsRawAtomCache.source_value a (pool live occ) (constantIndex live occ i) x
  simpa only [cacheAtom,assignment,List.get_eq_getElem,constantIndex,
    pool_constant live occ i.val i.isLt,constant_eval] using h

theorem residual_value (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (i : Fin occ.length) (x : BitInput q) :
    evaluateStructuralGF2 (assignment a live occ x) (residualAtom a live occ i)=
      residualVariable (occ.get i).gate live x:=by
  rw [residualAtom,evaluateStructuralGF2_add,original_value,constant_value]
  rfl

theorem cache_degree (a : DecompositionAlgorithm) (gs : List (SupportedNormalizedGate q))
    (i : Fin gs.length) : RawMonomialDegreeAtMost 1 (cacheAtom a gs i):=by
  unfold cacheAtom
  rw [CloseoutRowsRawAtomCache.source_getElem a gs i.val i.isLt]
  intro mon hm
  simp only [CloseoutRowsRawAtomLoop.indices,List.mem_map] at hm
  obtain ⟨j,_,rfl⟩:=hm
  simp

theorem residual_degree (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (i : Fin occ.length) :
    RawMonomialDegreeAtMost 1 (residualAtom a live occ i):=
  rawDegree_add (cache_degree a _ _) (cache_degree a _ _)

theorem cache_length (a : DecompositionAlgorithm) (gs : List (SupportedNormalizedGate q))
    (i : Fin gs.length) : (cacheAtom a gs i).length=(children a (gs.get i)).length:=by
  unfold cacheAtom
  rw [CloseoutRowsRawAtomCache.source_getElem a gs i.val i.isLt]
  simp only [CloseoutRowsRawAtomLoop.indices,List.length_map,List.length_range',List.get_eq_getElem]

end
end NearCubicWires.RepairSource.CloseoutRowsUniversal
