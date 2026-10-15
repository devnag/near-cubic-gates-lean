import Proof.CaseAnalysis.RowsTupleSeekCount

/-! Exact endpoint docking keeps the shared tuple joins symbolic in the
ambient size. All local and untouched fields remain explicit premises. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem dock_exact {t u s n : ℕ} {p : Machine t s}
    {hin hout : Fin t→ℕ} {tin tout : Fin t→List Bool}
    (run : Step p n hin tin hout tout) (slots : Fin t→Fin u) (hi:Function.Injective slots)
    (H H' : Fin u→ℕ) (A A' : Fin u→List Bool)
    (hH:∀ j,H (slots j)=hin j) (hA:∀ j,A (slots j)=tin j)
    (hH':∀ j,H' (slots j)=hout j) (hA':∀ j,A' (slots j)=tout j)
    (hkeep:∀ i,(∀ j,slots j≠i)→H' i=H i ∧ A' i=A i):
    Step (RecoveryFocus.machine slots p) n H A H' A':=by
  apply (run.dock slots hi H A hH hA).congr
  · funext i
    cases hp:RecoveryFocus.pick slots i with
    | none=>
      have hn:∀ j,slots j≠i:=by
        intro j he
        have h:=RecoveryFocus.pick_slot slots hi j
        rw [he,hp] at h
        contradiction
      rw [dockH_other slots H hout i hn]
      exact (hkeep i hn).1.symm
    | some j=>
      have he:=RecoveryFocus.slot_of_pick slots hp
      rw [←he,dockH_slot slots hi]
      exact (hH' j).symm
  · exact HierarchyWidth.install_eq slots hi A A' tout hA' (fun i hn=>(hkeep i hn).2)

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
