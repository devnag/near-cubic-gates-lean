import Proof.CaseAnalysis.RowsTupleSeekTailStages

/-! One selected term consumes its original top, coefficient record and
same-count native/support bottoms, then retains that count for the mask. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def topStage (keep : Bool) := RecoveryFocus.machine (streamSlots 0) (frameMachine keep)
noncomputable def coefficientStage (keep : Bool) := RecoveryFocus.machine (streamSlots 2) (threeFrames keep)
noncomputable def tailMachine (keep : Bool) := Composition.machine
  (Composition.machine (Composition.machine (topStage keep) (coefficientStage keep)) (bottomStage keep)) (countStage keep)
def tailCost (top a b c : List Bool) (gs : List GatePair) :=
  2*top.length+(record a b c).length+pairsCost gs+gs.length+7
def tailOutput (keep : Bool) (top a b c : List Bool) (gs : List GatePair) (out : Fin 4→List Bool) : Fin 4→List Bool :=
  ![out 0++selected keep (frame top++nativeWord gs),out 1++selected keep (supportWord gs),
    out 2++selected keep (record a b c),out 3++selected keep (countWord gs.length)]

theorem tail_run (keep : Bool) (np top nt sp st cp a b c ct : List Bool)
    (gs : List GatePair) (out : Fin 4→List Bool) :
    Step (tailMachine keep) (tailCost top a b c gs) (tailHeads ![np.length,sp.length,cp.length] out 1)
      (tailData ![np++frame top++nativeWord gs++nt,sp++supportWord gs++st,cp++record a b c++ct] out gs.length)
      (tailHeads ![np.length+(frame top++nativeWord gs).length,sp.length+(supportWord gs).length,
        cp.length+(record a b c).length] (tailOutput keep top a b c gs out) (gs.length+2))
      (tailData ![np++frame top++nativeWord gs++nt,sp++supportWord gs++st,cp++record a b c++ct]
        (tailOutput keep top a b c gs out) gs.length) := by
  let source : Fin 3→List Bool :=
    ![np++frame top++nativeWord gs++nt,sp++supportWord gs++st,cp++record a b c++ct]
  let pos : Fin 3→ℕ := ![np.length,sp.length,cp.length]
  let out1 := Function.update out 0 (out 0++selected keep (frame top))
  let pos1 := Function.update pos 0 (np.length+(frame top).length)
  let out2 := Function.update out1 2 (out1 2++selected keep (record a b c))
  let midPos : Fin 3→ℕ := ![np.length+(frame top).length,sp.length,cp.length+(record a b c).length]
  have topRun := field_dock (frameMachine keep) 0 source pos out gs.length 1
    (np.length+(frame top).length) (out 0++selected keep (frame top))
    (by simpa [source,pos,outSlot,List.append_assoc] using frame_run keep np top (nativeWord gs++nt) (out 0))
  have coefRun := field_dock (threeFrames keep) 2 source pos1 out1 gs.length 1
    (cp.length+(record a b c).length) (out1 2++selected keep (record a b c))
    (by simpa [source,pos1,pos,outSlot] using three_run keep cp a b c ct (out1 2))
  have coefRun' : Step (coefficientStage keep) ((record a b c).length+2)
      (tailHeads pos1 out1 1) (tailData source out1 gs.length)
      (tailHeads midPos out2 1) (tailData source out2 gs.length) := by
    apply coefRun.congr
    · funext i;fin_cases i <;> rfl
    · rfl
  have bottomRun := bottom_dock keep gs (np++frame top) nt sp st (cp++record a b c++ct)
    (cp.length+(record a b c).length) out2
  simp only [List.length_append] at bottomRun
  have first := (topRun.seq coefRun').seq bottomRun
  let endPos : Fin 3→ℕ := ![np.length+(frame top).length+(nativeWord gs).length,
    sp.length+(supportWord gs).length,cp.length+(record a b c).length]
  let out3 : Fin 4→List Bool := ![out2 0++selected keep (nativeWord gs),
    out2 1++selected keep (supportWord gs),out2 2,out2 3]
  have last := count_dock keep source endPos out3 gs.length
  have all := first.seq last
  have time : (2*top.length+1)+1+((record a b c).length+2)+1+pairsCost gs+1+(gs.length+1)=
      tailCost top a b c gs := by unfold tailCost;omega
  rw [time] at all
  have he : Function.update out3 3 (out3 3++selected keep (countWord gs.length))=
      tailOutput keep top a b c gs out := by
    cases keep <;> funext i <;> fin_cases i <;>
      simp [out3,out2,out1,tailOutput,selected,List.append_assoc]
  apply all.congr
  · rw [he]
    funext i;fin_cases i <;> simp [tailHeads,endPos,List.length_append,Nat.add_assoc]
  · rw [he]

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
