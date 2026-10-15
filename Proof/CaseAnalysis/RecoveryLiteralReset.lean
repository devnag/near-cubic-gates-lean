import Proof.CaseAnalysis.RecoveryLiteralDecode
import Proof.Amplification.RecoveryScratchErase

/-! One paid coarse sweep prepares every literal: original decoder work,
lookup scratch and its selected operand. The other live operand is retained,
including before the third literal in the original clause order. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralReset
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def target (second : Bool) : Fin 71:=if second then 47 else 45
def workSlots (second : Bool) : Fin 14→Fin 71:=
  ![61,62,63,64,65,66,48,67,68,49,69,37,30,target second]
def slots (second : Bool) (i : Fin 16) : Fin 71:=Fin.addCases
  (fun j : Fin 15=>Fin.addCases (workSlots second) (fun _ : Fin 1=>22) j) (fun _ : Fin 1=>23) i
theorem slots_injective (second : Bool) : Function.Injective (slots second):=by cases second <;> decide
theorem work_injective (second : Bool) : Function.Injective (workSlots second):=by cases second <;> decide
noncomputable def machine (second : Bool):=RecoveryFocus.machine (slots second) (RecoveryScratchErase.resetMachine 14)
noncomputable def output (A : Fin 71→List Bool) (second : Bool) (C : ℕ):=
  install (workSlots second) A (fun _=>List.replicate C false)

theorem reset_run (second : Bool) (H : Fin 71→ℕ) (A : Fin 71→List Bool) (C : ℕ)
    (hH : ∀ j,H (slots second j)=0)
    (hA : A 22=List.replicate C true) (hLog : A 23=List.replicate (C+1) false)
    (hWork : ∀ j,(A (workSlots second j)).length ≤ C) :
    ∃ r,runFrom (machine second) (2*C+4) ⟨(machine second).start,H,A⟩=some r ∧
      r.steps ≤ 2*C+4 ∧ r.final.heads=H ∧ r.final.tapes=output A second C := by
  have hr:=RecoveryScratchErase.erase_ready C (C+1) (fun j=>A (workSlots second j)) hWork
  obtain ⟨r,rr,rh,rt,rs⟩:=hr.focus_at (slots second) (slots_injective second) H A
    (by intro j
        refine Fin.addCases (m:=15) (n:=1) ?_ ?_ j
        · intro j
          refine Fin.addCases (m:=14) (n:=1) ?_ ?_ j
          · intro j;simp only [slots,Fin.addCases_left]
          · intro j;simpa only [slots,Fin.addCases_left,Fin.addCases_right] using hA
        · intro j;simpa only [slots,Fin.addCases_right] using hLog) hH
  have he : install (slots second) A
      (fun i : Fin 16=>Fin.addCases (fun j : Fin 15=>Fin.addCases (fun _ : Fin 14=>List.replicate C false)
        (fun _ : Fin 1=>List.replicate C true) j)
        (fun _ : Fin 1=>List.replicate (max (C+1) (C+1)) false) i)=output A second C := by
    apply HierarchyWidth.install_eq (slots second) (slots_injective second)
    · intro j
      refine Fin.addCases (m:=15) (n:=1) ?_ ?_ j
      · intro j
        refine Fin.addCases (m:=14) (n:=1) ?_ ?_ j
        · intro j
          simp only [slots,Fin.addCases_left,output]
          exact install_slot (workSlots second) (work_injective second) _ _ j
        · intro j
          simp only [slots,Fin.addCases_left,Fin.addCases_right,output]
          rw [install_other _ _ _ _ (by cases second <;> decide)]
          exact hA
      · intro j
        simp only [slots,Fin.addCases_right,output]
        rw [install_other _ _ _ _ (by cases second <;> decide),max_self]
        exact hLog
    · intro i hi
      exact install_other _ _ _ _ (by intro j;simpa only [slots,Fin.addCases_left] using hi ((j.castAdd 1).castAdd 1))
  exact ⟨r,rr,rs.le,rh,rt.trans he⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralReset
