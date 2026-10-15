import Proof.CaseAnalysis.RowsTupleSeekTailLayout

/-! The original bottom-count driver first executes paired native/support
copies and then emits its own unary metadata before scratch is cleared. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def bottomStage (keep : Bool) := RecoveryFocus.machine bottomSlots (pairsMachine keep)
noncomputable def countStage (keep : Bool) := RecoveryFocus.machine countSlots (countMachine keep)

theorem bottom_dock (keep : Bool) (gs : List GatePair) (np nt sp st cs : List Bool)
    (cp : ℕ) (out : Fin 4→List Bool) :
    Step (bottomStage keep) (pairsCost gs) (tailHeads ![np.length,sp.length,cp] out 1)
      (tailData ![np++nativeWord gs++nt,sp++supportWord gs++st,cs] out gs.length)
      (tailHeads ![np.length+(nativeWord gs).length,sp.length+(supportWord gs).length,cp]
        ![out 0++selected keep (nativeWord gs),out 1++selected keep (supportWord gs),out 2,out 3] 1)
      (tailData ![np++nativeWord gs++nt,sp++supportWord gs++st,cs]
        ![out 0++selected keep (nativeWord gs),out 1++selected keep (supportWord gs),out 2,out 3] gs.length) := by
  apply dock_exact (pairs_unary_run keep gs np nt sp st (out 0) (out 1)) bottomSlots (by decide)
  · intro i;fin_cases i <;> simp [tailHeads,bottomSlots,pairsHeads,pairHeads,fieldHeads,Fin.addCases]
  · intro i;fin_cases i <;> simp [tailData,bottomSlots,pairsData,pairData,fieldData,Fin.addCases]
  · intro i;fin_cases i <;> simp [tailHeads,bottomSlots,pairsHeads,pairHeads,fieldHeads,Fin.addCases]
  · intro i;fin_cases i <;> simp [tailData,bottomSlots,pairsData,pairData,fieldData,Fin.addCases]
  · intro i hi
    fin_cases i
    all_goals first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl) | exact False.elim (hi 4 rfl) | simp [tailHeads,tailData]

theorem count_dock (keep : Bool) (source : Fin 3→List Bool) (pos : Fin 3→ℕ)
    (out : Fin 4→List Bool) (n : ℕ) :
    Step (countStage keep) (n+1) (tailHeads pos out 1) (tailData source out n)
      (tailHeads pos (Function.update out 3 (out 3++selected keep (countWord n))) (n+2))
      (tailData source (Function.update out 3 (out 3++selected keep (countWord n))) n) := by
  have raw : Step (countMachine keep) (n+1) (fieldHeads 1 (out 3)) (fieldData (UnaryTemplate.tape n) (out 3))
      (fieldHeads (n+2) (out 3++selected keep (countWord n)))
      (fieldData (UnaryTemplate.tape n) (out 3++selected keep (countWord n))) := by
    have h := count_run keep [false] [] (out 3) n
    simp only [List.append_nil] at h
    apply h.congr
    · change fieldHeads (1+n+1) _=fieldHeads (n+2) _
      rw [show 1+n+1=n+2 by omega]
    · rfl
  apply dock_exact raw countSlots (by decide)
  · intro i;fin_cases i <;> simp [tailHeads,countSlots,fieldHeads]
  · intro i;fin_cases i <;> simp [tailData,countSlots,fieldData]
  · intro i;fin_cases i <;> simp [tailHeads,countSlots,fieldHeads]
  · intro i;fin_cases i <;> simp [tailData,countSlots,fieldData]
  · intro i hi
    fin_cases i
    all_goals first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | simp [tailHeads,tailData]

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
