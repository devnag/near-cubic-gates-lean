import Proof.MachineModel.ClosureMaskDegree

/-! Discharge the compact writer's mask certificate for the literal C.10
pool and bank, using the original polynomial's degree. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.RepairOrdinary
open RepairRepresentation SupplierPipeline SupplierPrime SupplierEstimator ThresholdCompiler
open RepairSource CloseoutFinal C10SupplierRowInput CanonicalFourfoldRowProgram

theorem p1BankDegree_of_family {l r : Nat} (gs : List (ExactThresholdGate (l+r)))
    [P1Radix gs] (rowsBank : List (List (List Bool)))
    (hlen : ∀ rows∈rowsBank, ∀ bits∈rows, bits.length = gs.length)
    (hdeg : ∀ ms∈CloseoutRowsCacheInput.family gs rowsBank, ∀ m∈ms,
      m.length ≤ P1Radix.degree gs) : P1BankDegree gs rowsBank := by
  refine ⟨?_⟩
  intro rows hr
  refine ⟨?_⟩
  intro bits hb
  have hl := hlen rows hr bits hb
  have hm := hdeg (CloseoutRowsCacheInput.polynomial gs rows)
    (List.mem_map.mpr ⟨rows,hr,rfl⟩) (CloseoutRowsCacheInput.monomial gs bits)
    (List.mem_map.mpr ⟨bits,hb,rfl⟩)
  have he : (CloseoutRowsCacheInput.monomial gs bits).length = bits.count true := by
    simp only [CloseoutRowsCacheInput.monomial,RowCachedEquation.equations,List.length_map,
      RowTupleCommonEquation.one,dif_pos hl.le,RowMaskMeaning.typed_length]
  rw [he] at hm
  exact Nat.le_min.mpr ⟨hm, (List.count_le_length (a := true) (l := bits)).trans hl.le⟩

theorem p1ActualMaskDegree {q : Nat} (a : DecompositionAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (degree : Nat)
    (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost degree P) :
    letI := p1ActualRadix a live occ s harity degree
    P1BankDegree (pool a live occ s harity) (bank a live occ s harity P) := by
  letI := p1ActualRadix a live occ s harity degree
  exact p1BankDegree_of_family (pool a live occ s harity) (bank a live occ s harity P)
    (bank_row_length a live occ s harity P)
    (P1Closure.CompactBounds.actual_family_degree a live occ s harity P degree hdegree)

end NearCubicWires.RepairOrdinary
