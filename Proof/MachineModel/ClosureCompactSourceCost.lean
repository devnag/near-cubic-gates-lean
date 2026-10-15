import Proof.MachineModel.ClosureCompactModeCost

/-! Polynomial radix from original source descriptions and occurrence count.
The all-live-assignment cache is never used as the radix bound. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactSourceCost
open RepairRepresentation RepairOrdinary SupplierPipeline SupplierEstimator
open RepairSource CloseoutRawRows CloseoutRowsRawLogShape SupplierWalkBridge
open ExtDecompositionBatch DecompositionSource PolynomialSchedule SourceInterfaces

theorem radix_bound {q : Nat} (a : DecompositionAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (cap : Nat)
    (hc : ∀ i : Fin occ.length, (occ.get i).descriptionBits ≤ cap) :
    CompactBounds.radix a live occ ≤ 6*occ.length*sourceChildBound a ((cap+3)^2)+4 := by
  have hb : ∀ g∈CloseoutRowsUniversal.pool live occ,
      sourceBudget a (request g) ≤ sourceChildBound a ((cap+3)^2) := by
    intro g hg
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hg
    have hd := CloseoutRowsUniversal.pool_description live occ cap hc ⟨i,hi⟩
    simp only [List.get_eq_getElem] at hd
    have hs := strict_gate_bits ((CloseoutRowsUniversal.pool live occ)[i]).gate
    have hp : q+(request ((CloseoutRowsUniversal.pool live occ)[i])).gate.encodingBits+1
        ≤ (cap+3)^2+2 := by
      unfold SupportedNormalizedGate.descriptionBits at hd
      calc
        _ ≤ q+(((CloseoutRowsUniversal.pool live occ)[i]).gate.encodingBits+1)+1 :=
          Nat.add_le_add_right (Nat.add_le_add_left hs q) 1
        _ ≤ _ := by omega
    exact Nat.mul_le_mul_left a.coefficient (Nat.pow_le_pow_left hp a.degree)
  obtain ⟨hcount,hbody⟩ := SourceEnvelope.totals_le a (CloseoutRowsUniversal.pool live occ) _ hb
  rw [CloseoutRowsUniversal.pool_length] at hcount hbody
  have hlog : natBitLength (B a (CloseoutRowsUniversal.pool live occ)) ≤
      B a (CloseoutRowsUniversal.pool live occ)+1 := by
    unfold natBitLength
    have := Nat.log_le_self 2 (B a (CloseoutRowsUniversal.pool live occ))
    omega
  change (exactListWord (GS a (CloseoutRowsUniversal.pool live occ))).length+1 ≤ _
  rw [exactListWord,List.length_append,natWord_length]
  change 2*natBitLength (B a (CloseoutRowsUniversal.pool live occ))+1+
    (bodyWord a (CloseoutRowsUniversal.pool live occ)).length+1 ≤ _
  nlinarith

theorem radix_polynomial (a : DecompositionAlgorithm) {description count : Nat → Nat}
    (hdesc : PolynomiallyBounded description) (hcount : PolynomiallyBounded count) :
    ∃ c e : Nat, 0 < c ∧ ∀ q (live : Finset (Fin q))
      (occ : List (SupportedNormalizedGate q)),
      (∀ i : Fin occ.length, (occ.get i).descriptionBits ≤ description q) →
      occ.length ≤ count q → CompactBounds.radix a live occ ≤ c*(q+1)^e := by
  have hbase : PolynomiallyBounded (fun q => (description q+3)^2) :=
    polynomiallyBounded_pow (polynomiallyBounded_add hdesc (polynomiallyBounded_constant 3)) 2
  have hp : PolynomiallyBounded (fun q => 6*count q*sourceChildBound a ((description q+3)^2)+4) :=
    polynomiallyBounded_add
      (polynomiallyBounded_mul
        (polynomiallyBounded_mul (polynomiallyBounded_constant 6) hcount)
        (sourceChildBound_polynomial a hbase)) (polynomiallyBounded_constant 4)
  obtain ⟨c,e,hc,he⟩ := hp
  refine ⟨c,e,hc,?_⟩
  intro q live occ hd hn
  exact (radix_bound a live occ (description q) hd).trans
    ((by gcongr : 6*occ.length*sourceChildBound a ((description q+3)^2)+4 ≤
      6*count q*sourceChildBound a ((description q+3)^2)+4).trans (he q))

end NearCubicWires.P1Closure.CompactSourceCost
