import Proof.CaseAnalysis.RowsTupleSeekRecycle

/-! One original term is selected or skipped, then every private parser
field is ready for the next call. Live family cursors keep their advances. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reusable_run (keep : Bool) (t : TermSlices) (pre tail : Fin 3→List Bool)
    (out : Fin 4→List Bool) (C : ℕ) (hC : t.cost+1 ≤ C) :
    Step (reusableMachine keep) (4*C+7)
      (reuseHeads (localHeads (fun i=>(pre i).length) out))
      (reuseData C (localData (sources t pre tail) out))
      (reuseHeads (localHeads (fun i=>(pre i).length+(t.words (i.castAdd 1)).length) (appended keep t out)))
      (reuseData C (localData (sources t pre tail) (appended keep t out))) := by
  obtain ⟨r,hr,hs,ho,hn⟩ := term_run keep t pre tail out
  rw [raw_entry] at hr
  apply recycle_run (rawMachine keep) t.cost C _ _ _ _ r hr
  · intro i hi;fin_cases i <;> simp_all [privateTapes,localHeads]
  · intro i hi;fin_cases i <;> simp_all [privateTapes,localData]
  · intro i hi;fin_cases i <;> simp_all [privateTapes,localHeads]
  · intro i hi;fin_cases i
    · exact ⟨(hs 0).2,(hs 0).1⟩
    · simp [privateTapes] at hi
    · simp [privateTapes] at hi
    · simp [privateTapes] at hi
    · simp [privateTapes] at hi
    · simp [privateTapes] at hi
    · simp [privateTapes] at hi
    · simp [privateTapes] at hi
    · simp [privateTapes] at hi
    · simp [privateTapes] at hi
    · simp [privateTapes] at hi
    · simp [privateTapes] at hi
    · simp [privateTapes] at hi
    · simp [privateTapes] at hi
    · exact ⟨(ho 0).2,(ho 0).1⟩
    · exact ⟨(hs 1).2,(hs 1).1⟩
    · exact ⟨(ho 1).2,(ho 1).1⟩
    · exact ⟨(hs 2).2,(hs 2).1⟩
    · exact ⟨(ho 2).2,(ho 2).1⟩
    · exact ⟨(ho 3).2,(ho 3).1⟩
  · omega

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
