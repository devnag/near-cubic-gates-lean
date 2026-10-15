import Proof.CaseAnalysis.RecoveryUniversalNodeTableBoundary

/-! The original table pays to clear the four saved child/constant/packet
tapes. The rest of its retained bank and every cursor are unchanged. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableSavedClear
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def saved : Fin 4→Fin 55:=![45,47,48,51]
def slots : Fin 6→Fin 55:=![45,47,48,51,22,23]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def machine:=RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 4)
def output (A : Fin 55→List Bool) (C : ℕ) (i : Fin 55):=
  if i=45 ∨ i=47 ∨ i=48 ∨ i=51 then List.replicate C false else A i

theorem clear_run (H : Fin 55→ℕ) (A : Fin 55→List Bool) (C : ℕ)
    (hH : ∀ j,H (slots j)=0) (hT : A 22=List.replicate C true) (hZ : A 23=List.replicate (C+1) false)
    (hfit : ∀ j,(A (saved j)).length ≤ C) :
    ∃ r,runFrom machine (2*C+4) ⟨machine.start,H,A⟩=some r ∧
      r.steps=2*C+4 ∧ r.final.heads=H ∧ r.final.tapes=output A C := by
  let backing : Fin 4→List Bool:=fun j=>A (saved j)
  have hA : ∀ j,A (slots j)=
      (Fin.addCases (m:=5) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool) backing (fun _=>List.replicate C true))
        (fun _=>List.replicate (C+1) false)) j := by
    intro j
    fin_cases j <;> first | rfl | exact hT | exact hZ
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryScratchErase.erase_ready C (C+1) backing hfit).focus_at slots slots_injective H A hA hH
  have he : install slots A
      (Fin.addCases (m:=5) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool)
          (fun _=>List.replicate C false) (fun _=>List.replicate C true))
        (fun _=>List.replicate (max (C+1) (C+1)) false))=output A C := by
    apply HierarchyWidth.install_eq slots slots_injective
    · intro j
      fin_cases j
      all_goals first | rfl | exact hT |
        (change A 23=List.replicate (max (C+1) (C+1)) false;rw [max_self];exact hZ)
    · intro i hi
      have h45 : i≠45:=fun h=>hi 0 h.symm
      have h47 : i≠47:=fun h=>hi 1 h.symm
      have h48 : i≠48:=fun h=>hi 2 h.symm
      have h51 : i≠51:=fun h=>hi 3 h.symm
      simp only [output,h45,h47,h48,h51,or_self,if_false]
  exact ⟨r,hr,rs,rh,rt.trans he⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableSavedClear
