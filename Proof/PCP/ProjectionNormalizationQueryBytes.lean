import Proof.PCP.ProjectionNormalizationQueries

/-! The prepared query machine consumes the actual raw source suffix and
emits exactly the fields of the selected normalized PCP. Its literal entry
still names the four physical dimension drivers, produced by the caller. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.QueryBytes
open SourceInterfaces ExecutableInterfaces LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rowsBits (rows : List (List ℕ)) := rows.map (fun row => row.map Nat.bits)
def framedCodes (codes : List ℕ) := FieldList.stream (codes.map Nat.bits)
def header (p : RawProjectionPCP) := frame p.width.bits++frame p.queries.bits
def suffix (p : RawProjectionPCP) := frame p.decision.clauses.length.bits++
  (p.decision.clauses.map fun clause =>
    (List.ofFn fun i : Fin 3 => frame (literalCode (clause i)).bits).flatten).flatten

@[simp] theorem framed_append (xs ys : List ℕ) :
    framedCodes (xs++ys)=framedCodes xs++framedCodes ys := by
  simp [framedCodes,FieldList.stream]

theorem rows_stream (rows : List (List ℕ)) :
    Rows.stream (rowsBits rows)=framedCodes rows.flatten := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    change framedCodes row++Rows.stream (rowsBits rows)=framedCodes (row++rows.flatten)
    rw [ih,framed_append]

theorem padded_bits (rows : List (List ℕ)) (padding : ℕ) :
    Rows.padded (rowsBits rows) padding=
      rowsBits (rows.map (fun row => row++List.replicate padding zeroCode)) := by
  simp [Rows.padded,rowsBits,Row.paddedFields,List.map_map,Function.comp_def]

theorem normalized_output (p : RawProjectionPCP) (R Q : ℕ) :
    Queries.output (rowsBits (queryRows p)) (R-p.width) ((Q-p.queries)*R)=
      framedCodes (normalizedRows p R Q).flatten := by
  rw [Queries.output,padded_bits,rows_stream]
  simp only [normalizedRows,List.flatten_append,List.flatten_replicate_replicate,framed_append]
  congr 1
  simp only [framedCodes,FieldList.stream,List.map_replicate,Constants.zeroField]

theorem rowsBits_length (p : RawProjectionPCP) :
    (rowsBits (queryRows p)).length=p.queries := by simp [rowsBits,queryRows]

theorem row_length (p : RawProjectionPCP) (row : List (List Bool))
    (hrow : row∈rowsBits (queryRows p)) : row.length=p.width := by
  simp only [rowsBits,queryRows,List.map_ofFn,Function.comp_def,List.mem_ofFn] at hrow
  obtain ⟨j,rfl⟩ := hrow
  simp

theorem source_split (p : RawProjectionPCP) :
    p.word=header p++Rows.stream (rowsBits (queryRows p))++suffix p := by
  simp only [RawProjectionPCP.word,header,suffix,Rows.stream,rowsBits,queryRows,
    FieldList.stream,List.map_ofFn,Function.comp_def,List.append_assoc]

def budget (p : RawProjectionPCP) (R Q : ℕ) :=
  (Rows.stream (rowsBits (queryRows p))).length+
    p.queries*(3*p.width+10*(R-p.width)+10)+10*((Q-p.queries)*R)+7

theorem query_run (p : RawProjectionPCP) (R Q : ℕ) (out : List Bool) :
    ∃ r,runFrom Queries.machine (budget p R Q)
      (Queries.cfg Queries.machine.start p.word (header p).length out
        p.width (R-p.width) p.queries ((Q-p.queries)*R))=some r ∧
      r.final=Queries.cfg Queries.finalState p.word
        ((header p).length+(Rows.stream (rowsBits (queryRows p))).length)
        (out++framedCodes (normalizedRows p R Q).flatten)
        p.width (R-p.width) p.queries ((Q-p.queries)*R) ∧ r.steps≤budget p R Q := by
  obtain ⟨r,hr,hf,ht⟩ := Queries.queries_run (header p) (rowsBits (queryRows p)) (suffix p) out
    p.width (R-p.width) ((Q-p.queries)*R) (row_length p)
  rw [←source_split] at hr hf
  rw [rowsBits_length] at hr hf ht
  rw [normalized_output] at hf
  exact ⟨r,hr,hf,ht⟩

theorem normalized_query_run (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (out : List Bool) :
    ∃ r,runFrom Queries.machine (budget p R Q)
      (Queries.cfg Queries.machine.start p.word (header p).length out
        p.width (R-p.width) p.queries ((Q-p.queries)*R))=some r ∧
      r.final=Queries.cfg Queries.finalState p.word
        ((header p).length+(Rows.stream (rowsBits (queryRows p))).length)
        (out++framedCodes (List.ofFn fun j : Fin Q => List.ofFn fun i : Fin R =>
          projectionCode ((p.normalized R Q hr hq).queryAddressBits x j i)).flatten)
        p.width (R-p.width) p.queries ((Q-p.queries)*R) ∧ r.steps≤budget p R Q := by
  rw [normalized_rows]
  exact query_run p R Q out

end NearCubicWires.RepairSource.ProjectionNormalization.QueryBytes
