import Proof.PCP.PCPTripleGlobal

/-! Whole repeated-clause resource ledger at the next nesting consumer.
The fixed three-field shape keeps the emitted clause-code stream linear in
the original field mass, while the actual repeated program has degree13. -/
namespace NearCubicWires.RepairOrdinary.PCPTripleGlobal
open CanonicalBinary PCPSerializerMass PCPSerializerReuse
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem triple_frame_bound (fields : List (List Bool)) (hthree : fields.length=3) :
    (frame (PCPTraversal.code fields).bits).length ≤ 512*(FieldList.stream fields).length := by
  have h := balancedListCodeBits_le (values fields)
  have hlen : (values fields).length=3 := by simp only [values,List.length_map,hthree]
  rw [hlen] at h
  change natBitLength (PCPTraversal.code fields) ≤ 1+2*3^4*balancedListAtomBits (values fields) at h
  obtain ⟨hc,hm⟩ := mass_bounds fields
  rw [hthree] at hc
  have hb := nat_bits_width (PCPTraversal.code fields)
  unfold balancedListAtomBits at h
  norm_num at h
  rw [frame_length,PCPTraversal.stream_mass]
  omega

theorem encoded_linear (groups : List (List (List Bool)))
    (hthree : ∀ fields∈groups,fields.length=3) :
    (PCPTripleLoop.encoded groups).length ≤ 512*(PCPTripleLoop.stream groups).length := by
  induction groups with
  | nil => simp
  | cons fields groups ih =>
    have hf := triple_frame_bound fields (hthree fields (by simp))
    have ht := ih (by intro g hg; exact hthree g (by simp [hg]))
    rw [PCPTripleLoop.encoded_cons,PCPTripleLoop.stream_cons,List.length_append,List.length_append]
    omega

theorem budget_bound (B M : ℕ) (hM : M ≤ B) : budget B M ≤ 2000000000000000000*(B+1)^13 := by
  have hp : (B+1)^13=(B+1)^12*(B+1) := by rw [pow_succ]
  have hp12 : (B+1)^12 ≤ (B+1)^13 := pow_le_pow_right₀ (by omega) (by omega)
  have hpos : 1 ≤ (B+1)^12 := Nat.one_le_pow 12 _ (by omega)
  have hb : B+1 ≤ (B+1)^13 := by
    calc
      _=(B+1)^1 := by simp
      _≤_ := pow_le_pow_right₀ (by omega) (by omega)
  have hterm := Nat.mul_le_mul_right (6*envelope B+11) hM
  unfold budget PCPTripleEnvelope.budget PCPTripleCold.budget PCPSerializerCapacity.coefficient envelope at *
  norm_num at hterm ⊢
  nlinarith

theorem group_count_le (groups : List (List (List Bool)))
    (hthree : ∀ fields∈groups,fields.length=3) : groups.length ≤ (PCPTripleLoop.stream groups).length := by
  have hc := PCPSerializerCapacity.MassReady.count_le_mass groups.flatten
  rw [flatten_length groups hthree,flatten_stream] at hc
  omega

end NearCubicWires.RepairOrdinary.PCPTripleGlobal
