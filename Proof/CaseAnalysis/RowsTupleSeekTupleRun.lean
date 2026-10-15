import Proof.CaseAnalysis.RowsTupleSeekRepeat

/-! The single physical controller preserves arbitrary request order and
repeated original indices. Its only body supplier is the actual indexed run. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem tuple_fold (ts : List TermSlices) (js : List (Fin ts.length)) (out : Fin 4 → List Bool) :
    js.foldl (fun acc j=>appended true ts[j] acc) out=tupleOutput ts js out := by
  induction js generalizing out with
  | nil=>funext i;simp [tupleOutput]
  | cons j js ih=>
    rw [List.foldl_cons,ih]
    funext i;simp [tupleOutput,appended,selected,List.append_assoc]

theorem tuple_run (ts : List TermSlices) (js : List (Fin ts.length)) (C D : ℕ)
    (hC : ∀ t∈ts,t.cost+1 ≤ C) (hD : ∀ i,(familyWords ts i).length ≤ D)
    (pre tail : List Bool) (out : Fin 4 → List Bool) (hfour : js.length ≤ 4) :
    ∃ r,runFrom tupleMachine (tupleBudget C D ts.length 4)
      (RepeatMachine.cfg 0 (tupleEntry ts C D pre.length (pre++tupleWord js++tail) out) js.length 1)=some r ∧
      r.final=RepeatMachine.cfg 3 (tupleEntry ts C D (pre.length+(tupleWord js).length)
        (pre++tupleWord js++tail) (tupleOutput ts js out)) js.length 1 ∧
      r.steps ≤ tupleBudget C D ts.length 4 := by
  have run := RepeatList.run indexedMachine (indexedCost C D ts.length) (tupleEntry ts C D)
    (fun j : Fin ts.length=>ExtIncidence.block j.val) (fun acc j=>appended true ts[j] acc)
    (by intro ip index acc;rfl)
    (by intro j ip it acc
        obtain ⟨r,hr,rh,rt,rs⟩ := indexed_family_run ts j C D hC hD ip it acc
        exact ⟨r,hr,rh,rt,rs⟩) js pre tail out hfour
  rw [tuple_fold] at run
  exact run

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
