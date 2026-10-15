import Proof.CaseAnalysis.RowsEstimatorReuseLayout

/-! Execute the D sweep on exactly the owned estimator scratch. The native
cut tape, native C, growing scalar stream, D driver and log are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def erased (p : Program) (D : ℕ) : Fin (WholePrefix.tapes p-2+1+1)→List Bool:=
  Fin.addCases (Fin.addCases (fun _ : Fin (WholePrefix.tapes p-2)=>List.replicate D false)
    (fun _ : Fin 1=>List.replicate D true)) (fun _ : Fin 1=>List.replicate (D+1) false)

theorem erase_avoids (p : Program) (i : Fin (tapes p))
    (hi:i=native p ∨ i=capacity p ∨ i=output p) : ∀ j,eraseSlots p j≠i:=by
  have hv:i.val=52 ∨ i.val=68 ∨ i.val=WholePrefix.tapes p+1:=by
    rcases hi with rfl|rfl|rfl <;>simp [native,capacity,Retained.capacity,old,output]
  have ht:70≤WholePrefix.tapes p:=by unfold WholePrefix.tapes;omega
  intro j
  refine Fin.addCases (fun k=>?_) (fun k=>?_) j
  · refine Fin.addCases (fun l=>?_) (fun l=>?_) k
    · intro he
      have hh:=congrArg Fin.val he
      have hw:=work_bounds p l
      simp only [eraseSlots,Fin.addCases_left] at hh
      omega
    · intro he
      have hh:=congrArg Fin.val he
      simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right,driver,Fin.val_natAdd] at hh
      omega
  · intro he
    have hh:=congrArg Fin.val he
    simp only [eraseSlots,Fin.addCases_right,log,Fin.val_castAdd,Fin.val_natAdd] at hh
    omega

theorem erase_run (p : Program) (D : ℕ) (H : Fin (tapes p)→ℕ) (A : Fin (tapes p)→List Bool)
    (hh:∀ j,H (eraseSlots p j)=0)
    (hs:∀ i,(A (work p i)).length≤D)
    (hd:A (driver p)=List.replicate D true) (hl:A (log p)=List.replicate (D+1) false) :
    ∃ r,runFrom (erase p) (2*D+4) ⟨(erase p).start,H,A⟩=some r ∧
      r.steps=2*D+4 ∧ r.final.heads=H ∧
      r.final.tapes=install (eraseSlots p) A (erased p D) ∧
      (∀ i,r.final.tapes (work p i)=List.replicate D false) ∧
      r.final.tapes (driver p)=List.replicate D true ∧
      r.final.tapes (log p)=List.replicate (D+1) false ∧
      (∀ i,i=native p ∨ i=capacity p ∨ i=output p→ r.final.tapes i=A i):=by
  have base:=RecoveryScratchErase.erase_ready D (D+1) (fun i=>A (work p i)) hs
  obtain ⟨r,rr,rh,rt,rs⟩:=base.focus_at (eraseSlots p) (erase_injective p) H A (by
    intro j
    refine Fin.addCases (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (fun i=>?_) (fun i=>?_) k
      · simp only [eraseSlots,Fin.addCases_left]
      · simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right]
        exact hd
    · simp only [eraseSlots,Fin.addCases_right]
      exact hl) hh
  have hdata:r.final.tapes=install (eraseSlots p) A (erased p D):=by
    apply rt.trans
    apply congrArg (install (eraseSlots p) A)
    funext j
    refine Fin.addCases (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (fun i=>?_) (fun i=>?_) k
      all_goals simp only [erased,Fin.addCases_left,Fin.addCases_right]
    · simp only [erased,Fin.addCases_right,Nat.max_self]
  refine ⟨r,rr,rs,rh,hdata,?_,?_,?_,?_⟩
  · intro i
    have h:=congrFun hdata (eraseSlots p ((i.castAdd 1).castAdd 1))
    rw [install_slot _ (erase_injective p)] at h
    simpa only [erase_work,erased,Fin.addCases_left] using h
  · have h:=congrFun hdata (eraseSlots p ((((0 : Fin 1).natAdd (WholePrefix.tapes p-2)).castAdd 1)))
    rw [install_slot _ (erase_injective p)] at h
    simpa only [eraseSlots,erased,Fin.addCases_left,Fin.addCases_right] using h
  · have h:=congrFun hdata (eraseSlots p ((0 : Fin 1).natAdd (WholePrefix.tapes p-2+1)))
    rw [install_slot _ (erase_injective p)] at h
    simpa only [eraseSlots,erased,Fin.addCases_right] using h
  · intro i hi
    exact (congrFun hdata i).trans (install_other _ _ _ _ (erase_avoids p i hi))

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
