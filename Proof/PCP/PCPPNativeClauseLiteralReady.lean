import Proof.PCP.PCPPNativeLiteralSplit

/-! Physically restore the literal-code splitter's cursors. Raw index and
the original sign are ready for ordinary native-address arithmetic. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeLiteralSplit
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine := Rewind.machine raw

theorem ready_run (index : ℕ) (negative : Bool) :
    ReadyRun machine (4*index+2*negative.toNat+6)
      ![UnaryTemplate.tape (2*index+negative.toNat),[],[],[]]
      ![UnaryTemplate.tape (2*index+negative.toNat),List.replicate index true,[negative],
        List.replicate (2*index+negative.toNat+2) false] := by
  obtain ⟨base,hb,hf,hs⟩:=raw_run index negative
  obtain ⟨r,hr,ht,log,hh,rs,_⟩:=Rewind.Workspace.reset_workspace raw _ _ base hb 0
  have hi : (Fin.addCases (m := 3) (n := 1) (motive := fun _ : Fin 4=>List Bool)
      ![UnaryTemplate.tape (2*index+negative.toNat),[],[]] (fun _=>List.replicate 0 false))=
      ![UnaryTemplate.tape (2*index+negative.toNat),[],[],[]] := by
    funext i; fin_cases i <;> rfl
  have htime : 2*base.steps+2=4*index+2*negative.toNat+6 := by omega
  change run machine (2*base.steps+2)
    (Fin.addCases (m := 3) (n := 1) (motive := fun _ : Fin 4=>List Bool)
      ![UnaryTemplate.tape (2*index+negative.toNat),[],[]] (fun _=>List.replicate 0 false))=some r at hr
  rw [hi,htime] at hr
  refine ⟨r,hr,?_,hh,by omega⟩
  funext i
  fin_cases i
  · exact (ht 0).trans (by rw [hf]; rfl)
  · exact (ht 1).trans (by rw [hf]; rfl)
  · exact (ht 2).trans (by rw [hf]; rfl)
  · simpa [hs,Fin.natAdd] using log

end NearCubicWires.RepairOrdinary.PCPPNativeLiteralSplit
