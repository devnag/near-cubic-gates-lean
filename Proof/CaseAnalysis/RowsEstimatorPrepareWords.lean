import Proof.CaseAnalysis.RowsEstimatorPrepareLayout

/-! Exact projection and extensionality at the owned preparation boundary. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepare
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def spare (p : Program) : Fin (tapes p) := (Reuse.output p).castAdd 7
def owned (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool)
    (i : Fin (WholePrefix.tapes p-2)) := A ⟨(Reuse.work p i).val,(Reuse.work_bounds p i).1⟩

@[simp] theorem at_old (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D L : ℕ)
    (fields : Fin 7 → List Bool) (i : Fin (WholePrefix.tapes p)) :
    data p A D L fields (old p i)=A i := by
  simp only [data,bank,old,Reuse.old,Fin.addCases_left]
@[simp] theorem at_source (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D L : ℕ)
    (fields : Fin 7 → List Bool) (i : Fin 7) : data p A D L fields (source p i)=fields i := by
  simp only [data,source,Fin.addCases_right]
@[simp] theorem at_driver (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D L : ℕ)
    (fields : Fin 7 → List Bool) : data p A D L fields (driver p)=List.replicate D true := by
  simp only [data,bank,driver,Reuse.driver,Fin.addCases_left,Fin.addCases_right,Matrix.cons_val_one,Matrix.cons_val_zero]
@[simp] theorem at_log (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D L : ℕ)
    (fields : Fin 7 → List Bool) : data p A D L fields (log p)=List.replicate L false := by
  simp only [data,bank,log,Reuse.log,Fin.addCases_left,Fin.addCases_right]
@[simp] theorem at_spare (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D L : ℕ)
    (fields : Fin 7 → List Bool) : data p A D L fields (spare p)=[] := by
  simp only [data,bank,spare,Reuse.output,Fin.addCases_left,Fin.addCases_right,Matrix.cons_val_zero]
@[simp] theorem at_work (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D L : ℕ)
    (fields : Fin 7 → List Bool) (i : Fin (WholePrefix.tapes p-2)) :
    data p A D L fields (work p i)=owned p A i := by
  change data p A D L fields ((Reuse.work p i).castAdd 7)=_
  rw [Reuse.work_old]
  exact at_old p A D L fields _

@[simp] theorem pad_work (p : Program) (i : Fin (WholePrefix.tapes p-2)) :
    padSlots p ((i.castAdd 1).castAdd 1)=work p i := by
  simp only [padSlots,Reuse.erase_work,work]
@[simp] theorem pad_driver (p : Program) (i : Fin 1) :
    padSlots p ((i.natAdd (WholePrefix.tapes p-2)).castAdd 1)=driver p := by
  simp only [padSlots,Reuse.eraseSlots,Fin.addCases_left,Fin.addCases_right,driver]
@[simp] theorem pad_log (p : Program) (i : Fin 1) :
    padSlots p (i.natAdd (WholePrefix.tapes p-2+1))=log p := by
  simp only [padSlots,Reuse.eraseSlots,Fin.addCases_right,log]

@[simp] theorem owned_pad (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool)
    (D : ℕ) (i : Fin (WholePrefix.tapes p-2)) :
    owned p (WarmReuse.padded p D A) i=ZeroPadding.pad D (owned p A i) := by
  have h:=(Reuse.work_bounds p i).2
  simp only [owned,WarmReuse.padded,Reset.caps,h,or_self,ite_false]

theorem data_ext (p : Program) (X Y : Fin (tapes p) → List Bool)
    (ho : ∀ i,X (old p i)=Y (old p i))
    (hl : X (log p)=Y (log p)) (hs : X (spare p)=Y (spare p))
    (hd : X (driver p)=Y (driver p)) (hf : ∀ i,X (source p i)=Y (source p i)) : X=Y := by
  funext i
  refine Fin.addCases (m:=Reuse.tapes p) (n:=7) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=WholePrefix.tapes p+1) (n:=2) (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (m:=WholePrefix.tapes p) (n:=1) (fun l=>?_) (fun l=>?_) k
      · exact ho l
      · have he : l=0:=Subsingleton.elim _ _
        subst l;exact hl
    · fin_cases k
      · exact hs
      · exact hd
  · exact hf j

theorem pad_avoids (p : Program) (i : Fin (tapes p))
    (hi : i.val=52 ∨ i.val=68 ∨ i.val=WholePrefix.tapes p+1 ∨ Reuse.tapes p ≤ i.val) :
    ∀ j,padSlots p j≠i := by
  intro j he
  have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
  revert hv
  refine Fin.addCases (m:=WholePrefix.tapes p-2+1) (n:=1) (fun k=>?_) (fun k=>?_) j
  · refine Fin.addCases (m:=WholePrefix.tapes p-2) (n:=1) (fun k=>?_) (fun k=>?_) k
    · intro hv
      rw [pad_work] at hv
      have hw:=Reuse.work_bounds p k
      change (Reuse.work p k).val=i.val at hv
      unfold Reuse.tapes at hi
      omega
    · intro hv
      rw [pad_driver,driver_val] at hv
      unfold Reuse.tapes at hi
      have ht : 70 ≤ WholePrefix.tapes p:=by unfold WholePrefix.tapes;omega
      omega
  · intro hv
    rw [pad_log,log_val] at hv
    unfold Reuse.tapes at hi
    have ht : 70 ≤ WholePrefix.tapes p:=by unfold WholePrefix.tapes;omega
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepare
