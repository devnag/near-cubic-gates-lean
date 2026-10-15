import Proof.Amplification.RecoveryProjectionWidthBudget

namespace NearCubicWires.RepairSource.RecoveryProjectionRows
open LocalBitMultitape RepairOrdinary SourceInterfaces ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def addressFields (p : RawProjectionPCP) (R Q : Nat) (hr : p.width ≤ R) (hq : p.queries ≤ Q)
    {n : Nat} (x : BitInput n) (randomness : BitInput R) :=
  List.ofFn (fun j : Fin Q=>List.ofFn (fun i : Fin R=>
    ((p.normalized R Q hr hq).queryAddressBits x j i).eval randomness))

theorem normalized_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width ≤ R) (hq : p.queries ≤ Q)
    {n : Nat} (x : BitInput n) (randomness : BitInput R) (pre suffix tail out : List Bool) : ∃ r,
    runFrom machine (Q*(R*(4*capacity R+11)+8)+3)
      (cfg 0 (capacity R) R (pre++QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix)
        (List.ofFn randomness) tail out pre.length Q 1)=some r ∧
      r.final=cfg 3 (capacity R) R (pre++QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix)
        (List.ofFn randomness) tail (out++FieldList.stream (addressFields p R Q hr hq x randomness))
        (pre.length+(QueryBytes.framedCodes (normalizedRows p R Q).flatten).length) Q 1 ∧
      r.steps ≤ Q*(R*(4*capacity R+11)+8)+3 := by
  have hw : ∀ row∈QueryBytes.rowsBits (normalizedRows p R Q),row.length=R := by
    intro row hrow
    rw [normalized_fields p R Q hr hq x] at hrow
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hrow
    simp only [List.length_ofFn]
  have hc : ∀ row∈QueryBytes.rowsBits (normalizedRows p R Q),∀ bits∈row,
      RecoveryProjectionEval.budget bits (List.ofFn randomness)+1 ≤ capacity R := by
    intro row hrow bits hbits
    rw [normalized_fields p R Q hr hq x] at hrow
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hrow
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hbits
    exact capacity_covers _ randomness
  have hQ : (QueryBytes.rowsBits (normalizedRows p R Q)).length=Q := by
    rw [normalized_fields p R Q hr hq x]
    simp only [List.length_ofFn]
  obtain ⟨r,hrr,hf,hs⟩ := rows_run (capacity R) R pre (QueryBytes.rowsBits (normalizedRows p R Q))
    suffix (List.ofFn randomness) tail out hw hc
  rw [hQ] at hrr hf hs
  rw [code_stream] at hrr hf
  rw [normalized_output p R Q hr hq x randomness] at hf
  exact ⟨r,hrr,hf,hs⟩

end NearCubicWires.RepairSource.RecoveryProjectionRows
