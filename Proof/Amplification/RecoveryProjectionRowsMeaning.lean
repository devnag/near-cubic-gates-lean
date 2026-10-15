import Proof.Amplification.RecoveryProjectionRows
import Proof.PCP.ProjectionNormalizationQueryBytes

namespace NearCubicWires.RepairSource.RecoveryProjectionRows
open LocalBitMultitape RepairOrdinary SourceInterfaces ProjectionNormalization RecoveryProjectionField
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem emitted_codes {n : Nat} (projections : List (ProjectedRandomBit n)) (randomness : BitInput n) :
    emitted (projections.map (fun p=>(projectionCode p).bits)) (List.ofFn randomness)=
      Streaming.marks (projections.map (fun p=>p.eval randomness)) := by
  induction projections with
  | nil => rfl
  | cons p projections ih =>
    simp only [List.map_cons,emitted,List.flatMap_cons,RecoveryProjectionEval.projection_bit,
      Streaming.marks,List.flatMap_cons] at *
    rw [ih]

theorem emitted_ofFn {n width : Nat} (projections : Fin width→ProjectedRandomBit n) (randomness : BitInput n) :
    emitted (List.ofFn (fun i=>(projectionCode (projections i)).bits)) (List.ofFn randomness)=
      Streaming.marks (List.ofFn (fun i=>(projections i).eval randomness)) := by
  simpa only [List.map_ofFn,Function.comp_def] using emitted_codes (List.ofFn projections) randomness

theorem code_stream (codes : List (List Nat)) :
    stream (QueryBytes.rowsBits codes)=QueryBytes.framedCodes codes.flatten := by
  induction codes with
  | nil => rfl
  | cons row rows ih =>
    change QueryBytes.framedCodes row++stream (QueryBytes.rowsBits rows)=
      QueryBytes.framedCodes (row++rows.flatten)
    rw [QueryBytes.framed_append,ih]

theorem output_projections {n width queries : Nat}
    (projections : Fin queries→Fin width→ProjectedRandomBit n) (randomness : BitInput n) :
    output (List.ofFn (fun j=>List.ofFn (fun i=>(projectionCode (projections j i)).bits))) (List.ofFn randomness)=
      FieldList.stream (List.ofFn (fun j=>List.ofFn (fun i=>(projections j i).eval randomness))) := by
  have h (row : Fin width→ProjectedRandomBit n) :
      emitted (List.ofFn (fun i=>(projectionCode (row i)).bits)) (List.ofFn randomness)++[false]=
        RepairOrdinary.frame (List.ofFn (fun i=>(row i).eval randomness)) := by
    rw [emitted_ofFn]
    simpa only [List.append_nil,RepairOrdinary.frame] using (Streaming.frame_append (List.ofFn (fun i=>(row i).eval randomness)) []).symm
  simp only [output,FieldList.stream,List.flatMap,List.map_ofFn,Function.comp_def,h]

theorem normalized_fields (p : RawProjectionPCP) (R Q : Nat) (hr : p.width ≤ R) (hq : p.queries ≤ Q)
    {n : Nat} (x : BitInput n) :
    QueryBytes.rowsBits (normalizedRows p R Q)=
      List.ofFn (fun j : Fin Q=>List.ofFn (fun i : Fin R=>
        (projectionCode ((p.normalized R Q hr hq).queryAddressBits x j i)).bits)) := by
  rw [←normalized_rows p R Q hr hq x]
  simp only [QueryBytes.rowsBits,List.map_ofFn,Function.comp_def]

theorem normalized_output (p : RawProjectionPCP) (R Q : Nat) (hr : p.width ≤ R) (hq : p.queries ≤ Q)
    {n : Nat} (x : BitInput n) (randomness : BitInput R) :
    output (QueryBytes.rowsBits (normalizedRows p R Q)) (List.ofFn randomness)=
      FieldList.stream (List.ofFn (fun j : Fin Q=>List.ofFn (fun i : Fin R=>
        ((p.normalized R Q hr hq).queryAddressBits x j i).eval randomness))) := by
  rw [normalized_fields p R Q hr hq x]
  exact output_projections _ randomness

end NearCubicWires.RepairSource.RecoveryProjectionRows
