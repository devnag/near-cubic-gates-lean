import Proof.Supplier.EquationScalarStreamLayout

namespace NearCubicWires.RepairOrdinary.EquationScalarStream
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def cleared (C : Nat) : Fin 15→List Bool :=
  Fin.addCases (m:=14) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
      (fun _=>List.replicate C false) (fun _=>List.replicate C true))
    (fun _=>List.replicate (C+1) false)
def erased (C : Nat) (a : Fin 17→List Bool) := install eraseSlots a (cleared C)

theorem erase_run (C pos : Nat) (out : List Bool) (a : Fin 17→List Bool)
    (hb : ∀ j,(a (scratchSlots j)).length ≤ C)
    (hd : a 15=List.replicate C true) (hl : a 16=List.replicate (C+1) false) :
    ∃ r,runFrom eraseProgram (2*C+4) ⟨eraseProgram.start,heads pos out.length,a⟩=some r ∧
      r.final.heads=heads pos out.length ∧ r.final.tapes=erased C a ∧ r.steps=2*C+4 := by
  have h := RecoveryScratchErase.erase_ready C (C+1) (fun j=>a (scratchSlots j)) hb
  have he : max (C+1) (C+1)=C+1 := max_self _
  rw [he] at h
  apply h.focus_at eraseSlots erase_injective (heads pos out.length) a
  · intro j
    refine Fin.addCases (m:=14) (n:=1) (fun i=>?_) (fun i=>?_) j
    · refine Fin.addCases (m:=13) (n:=1) (fun i=>?_) (fun i=>?_) i
      · simp only [eraseSlots,Fin.addCases_left]
      · simpa only [eraseSlots,Fin.addCases_left,Fin.addCases_right] using hd
    · simpa only [eraseSlots,Fin.addCases_right] using hl
  · intro j
    fin_cases j <;> simp [heads,eraseSlots,scratchSlots,Fin.addCases]

theorem erased_slot (C : Nat) (a : Fin 17→List Bool) (j : Fin 13) :
    erased C a (scratchSlots j)=List.replicate C false := by
  have h := install_slot eraseSlots erase_injective a (cleared C) ((j.castAdd 1).castAdd 1)
  simpa only [erased,eraseSlots,cleared,Fin.addCases_left] using h
theorem erased_driver (C : Nat) (a : Fin 17→List Bool) : erased C a 15=List.replicate C true := by
  have h := install_slot eraseSlots erase_injective a (cleared C) (((0 : Fin 1).natAdd 13).castAdd 1)
  simpa only [erased,eraseSlots,cleared,Fin.addCases_left,Fin.addCases_right] using h
theorem erased_log (C : Nat) (a : Fin 17→List Bool) : erased C a 16=List.replicate (C+1) false := by
  have h := install_slot eraseSlots erase_injective a (cleared C) ((0 : Fin 1).natAdd 14)
  simpa only [erased,eraseSlots,cleared,Fin.addCases_right] using h
theorem erased_live (C : Nat) (a : Fin 17→List Bool) (i : Fin 17) (hi : i=0 ∨ i=14) :
    erased C a i=a i := by
  apply install_other
  intro j
  rcases hi with rfl|rfl
  all_goals fin_cases j <;> decide

theorem erased_tapes (C : Nat) (a : Fin 17→List Bool) : erased C a=tapes C (a 0) (a 14) := by
  funext i
  fin_cases i
  · exact erased_live C a 0 (Or.inl rfl)
  · exact erased_slot C a 0
  · exact erased_slot C a 1
  · exact erased_slot C a 2
  · exact erased_slot C a 3
  · exact erased_slot C a 4
  · exact erased_slot C a 5
  · exact erased_slot C a 6
  · exact erased_slot C a 7
  · exact erased_slot C a 8
  · exact erased_slot C a 9
  · exact erased_slot C a 10
  · exact erased_slot C a 11
  · exact erased_slot C a 12
  · exact erased_live C a 14 (Or.inr rfl)
  · exact erased_driver C a
  · exact erased_log C a

end
end NearCubicWires.RepairOrdinary.EquationScalarStream
