import Proof.MachineModel.ClosureBinaryPool
import Proof.MachineModel.ClosureCompactNativeRequest

/-! A.12's compact request with the physical binary-order pool. The original
child-cache radix and original monomial degree are unchanged; the mask bank
is literally the existing C.10 bank. Its generic printer congruence lands on
the existing C.10 table. Physical source production remains separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryRequest
open RepairRepresentation RepairOrdinary SupplierPipeline SupplierPrime SupplierEstimator
open ThresholdCompiler CanonicalFourfoldRowProgram RepairSource CloseoutFinal C10SupplierRowInput

variable {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : Nat)
  (harity : (s+1)/2+s/2 = liveᶜ.card)

theorem pool_magnitude (g : ExactThresholdGate ((s+1)/2+s/2))
    (hg : g ∈ BinaryPool.pool a live occ s harity) :
    equationMagnitudeBound (RowCachedEquation.equation g) < 2^CompactBounds.radix a live occ := by
  have hone : 1 < 2^CompactBounds.radix a live occ := by
    apply Nat.one_lt_pow (by unfold CompactBounds.radix; omega) (by decide)
  have hget (i : Nat) :
      equationMagnitudeBound (RowCachedEquation.equation
        ((childList a live occ).getD i falseChild)) < 2^CompactBounds.radix a live occ := by
    by_cases hi : i < (childList a live occ).length
    · rw [List.getD_eq_getElem _ _ hi]
      exact RowCachedEquation.cache_radix_safe (childList a live occ) ⟨i,hi⟩
    · rw [List.getD_eq_default _ _ (by omega : (childList a live occ).length ≤ i)]
      simpa [falseChild,falseGate,RowCachedEquation.equation,equationMagnitudeBound] using hone
  rcases List.mem_cons.mp hg with h | h
  · subst g
    simpa [falseGate,RowCachedEquation.equation,equationMagnitudeBound] using hone
  · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp h
    unfold BinaryPool.poolFn
    rw [CompactBounds.cast_magnitude]
    exact (CompactBounds.hardwire_magnitude live _ _).trans_lt (hget _)

noncomputable abbrev radix (degree : Nat) : P1Radix (BinaryPool.pool a live occ s harity) where
  bits := CompactBounds.radix a live occ
  positive := by unfold CompactBounds.radix; omega
  safe := fun i => pool_magnitude a live occ s harity _ (List.getElem_mem i.isLt)
  degree := degree

attribute [local irreducible] pool BinaryPool.pool bank childList CompactBounds.radix
  CloseoutRowsUniversal.pool ExtDecompositionBatch.GS

theorem bankDegree (P : StructuralGF2Polynomial) (degree : Nat)
    (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost degree P) :
    letI := radix a live occ s harity degree
    P1BankDegree (BinaryPool.pool a live occ s harity) (bank a live occ s harity P) := by
  letI := radix a live occ s harity degree
  letI := p1ActualRadix a live occ s harity degree
  letI := p1ActualMaskDegree a live occ s harity P degree hdegree
  refine ⟨fun rows hr => ⟨fun row hm => ?_⟩⟩
  letI := P1BankDegree.bound (gs:=pool a live occ s harity) (bank:=bank a live occ s harity P) rows hr
  have h := P1MaskDegree.bound (gs:=pool a live occ s harity) row hm
  change row.count true ≤ min degree (BinaryPool.pool a live occ s harity).length
  rw [BinaryPool.pool_length]
  exact h

theorem gate (P : StructuralGF2Polynomial) (w : Nat)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w)
    (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s) :
    (RowBinLift.batch (live.card+1)
      (CloseoutRowsCacheInput.family (BinaryPool.pool a live occ s harity)
        (bank a live occ s harity P))).length^100 ≤ 2^s := by
  have hw := bank_rows_le a live occ s harity P w hmon
  rw [batch_length_eq (BinaryPool.pool a live occ s harity) (live.card+1) w
    (bank a live occ s harity P) hw]
  exact CloseoutRawRows.raw_cuts_gate (BinaryPool.pool a live occ s harity) live.card w s
    (bank a live occ s harity P) (le_of_eq (bank_length a live occ s harity P)) hw hpos hload

variable (P : StructuralGF2Polynomial) (w degree : Nat)
  (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w)
  (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)
  (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost degree P)

noncomputable def input : EquationRow.Input := by
  letI := radix a live occ s harity degree
  letI := bankDegree a live occ s harity P degree hdegree
  exact P1CompactInput.input s (live.card+1) w (BinaryPool.pool a live occ s harity)
    (bank a live occ s harity P) hs (gate a live occ s harity P w hmon hpos hload)
    (bank_rows_le a live occ s harity P w hmon)

theorem table_modEq (i j : Fin (2^((s+1)/2))) :
    let row := input a live occ s harity P w degree hs hmon hpos hload hdegree
    Int.ModEq ((2 : Int)^(live.card+1))
      (SupplierPrinter.weightedDominance
        (MatrixScoreBatch.leftScore (EquationRow.request row))
        (MatrixScoreBatch.rightScore (EquationRow.request row))
        (MatrixScoreBatch.weight (EquationRow.request row)) i j)
      (C10SupplierTable.table a live occ s harity P w hs hmon hpos hload i j) := by
  letI := radix a live occ s harity degree
  letI := bankDegree a live occ s harity P degree hdegree
  have h := P1CompactInput.count_modEq s (live.card+1) w (BinaryPool.pool a live occ s harity)
    (bank a live occ s harity P) hs (gate a live occ s harity P w hmon hpos hload)
    (bank_rows_le a live occ s harity P w hmon) i j
  simp only [CompetitorCountTable.rowValues,CompactNativeRequest.family_eq] at h
  rw [BinaryPool.count_eq_table a live occ s harity P w hs hmon hpos hload i j] at h
  exact h

end NearCubicWires.P1Closure.BinaryRequest
