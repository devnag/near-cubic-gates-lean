import Proof.PCP.VerifierLookupRuntimeSelection

/-! These identities identify fields of the same literal code at the cursor
produced by navigation and selection. They do not install a tape or address. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem frame_split (word : List Bool) (offset : ℕ) :
    frame word=Streaming.marks (word.take offset)++frame (word.drop offset) := by
  rw [←Streaming.frame_append,List.take_append_drop]

theorem frame_slice (word : List Bool) (offset width : ℕ) :
    frame word=Streaming.marks (word.take offset)++Streaming.marks (slice word offset width)++
      frame (word.drop (offset+width)) := by
  rw [frame_split word offset,frame_split (word.drop offset) width]
  simp only [slice,List.drop_drop,List.append_assoc]

theorem scalar_source (word : List Bool) (offset : ℕ) (ho : offset<word.length) :
    frame word=Streaming.marks (word.take offset)++true::word.getD offset false::frame (word.drop (offset+1)) := by
  have h := frame_split word offset
  rw [List.drop_eq_getElem_cons ho] at h
  have hb : word.getD offset false=word[offset] := by simp [List.getD,List.getElem?_eq_getElem ho]
  rw [hb]
  exact h

theorem scalar_slice_run (i : Fin 3) (d : Store) (offset : ℕ)
    (hp : d.codePos=2*offset) (ho : offset<d.code.length) :
    ∃ r,runFrom (scalarProgram i) 2 (cfg (scalarProgram i).start d)=some r ∧
      r.final=cfg r.final.control (scalarOut d i (d.codePos+2) (d.code.getD offset false)) ∧ r.steps=2 := by
  apply scalar_run i d (Streaming.marks (d.code.take offset)) (frame (d.code.drop (offset+1)))
    (d.code.getD offset false) (scalar_source d.code offset ho)
  simpa only [Streaming.marks_length,List.length_take,Nat.min_eq_left ho.le] using hp

theorem field_slice_run (tags : Bool) (d : Store) (offset : ℕ)
    (hp : d.codePos=2*offset) (ho : offset+fieldWidth d tags≤d.code.length)
    (hb : (fieldBacking d tags).length≤2*(fieldWidth d tags)+1) :
    ∃ r,runFrom (fieldProgram tags) (4*(fieldWidth d tags)+2) (cfg (fieldProgram tags).start d)=some r ∧
      r.final=cfg r.final.control
        (fieldOut d tags (d.codePos+2*(fieldWidth d tags)) (frame (slice d.code offset (fieldWidth d tags)))) ∧
      r.steps=4*(fieldWidth d tags)+2 := by
  have hl := Sequential.slice_length d.code offset (fieldWidth d tags) ho
  obtain ⟨r,hr,hrf,hrs⟩ := field_run tags d (Streaming.marks (d.code.take offset))
    (slice d.code offset (fieldWidth d tags)) (frame (d.code.drop (offset+fieldWidth d tags)))
    (frame_slice d.code offset (fieldWidth d tags))
    (by simpa only [Streaming.marks_length,List.length_take,Nat.min_eq_left (by omega : offset≤d.code.length)] using hp)
    hl hb
  rw [hl] at hrf
  exact ⟨r,hr,hrf,hrs⟩

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
