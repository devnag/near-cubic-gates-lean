import Proof.CaseAnalysis.RowsEstimatorBacking
import Proof.CaseAnalysis.RowsEstimatorPad

/-! Owned padding and seven simultaneous metadata copies. The extra
unused output port is empty; the growing scalar stream stays external. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepare
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p : Program) := Reuse.tapes p+7
def old (p : Program) (i : Fin (WholePrefix.tapes p)) : Fin (tapes p) := (Reuse.old p i).castAdd 7
def work (p : Program) (i : Fin (WholePrefix.tapes p-2)) : Fin (tapes p) := (Reuse.work p i).castAdd 7
def source (p : Program) (i : Fin 7) : Fin (tapes p) := i.natAdd (Reuse.tapes p)
def dest (p : Program) (i : Fin 7) : Fin (tapes p) := old p (WarmFields.slots p i)
def driver (p : Program) : Fin (tapes p) := (Reuse.driver p).castAdd 7
def log (p : Program) : Fin (tapes p) := (Reuse.log p).castAdd 7
def padSlots (p : Program) (i : Fin (WholePrefix.tapes p-2+1+1)) : Fin (tapes p) :=
  (Reuse.eraseSlots p i).castAdd 7
def copySlots (p : Program) : Fin (7+(7+1)+1) → Fin (tapes p) :=
  Fin.addCases (Fin.addCases (source p) (Fin.addCases (dest p) (fun _ : Fin 1=>driver p))) (fun _ : Fin 1=>log p)

def bank (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D L : ℕ) : Fin (Reuse.tapes p) → List Bool :=
  Fin.addCases (Fin.addCases A (fun _ : Fin 1=>List.replicate L false)) (![[],List.replicate D true] : Fin 2 → List Bool)
def data (p : Program) (A : Fin (WholePrefix.tapes p) → List Bool) (D L : ℕ)
    (fields : Fin 7 → List Bool) : Fin (tapes p) → List Bool := Fin.addCases (bank p A D L) fields
noncomputable def pad (p : Program) := RecoveryFocus.machine (padSlots p) (Pad.machine (WholePrefix.tapes p-2))
noncomputable def copy (p : Program) := RecoveryFocus.machine (copySlots p) (MetadataBatch.machine 7)
noncomputable def machine (p : Program) := Composition.machine (pad p) (copy p)

theorem source_val (p : Program) (i : Fin 7) : (source p i).val=Reuse.tapes p+i.val := rfl
theorem dest_val (p : Program) (i : Fin 7) : (dest p i).val=(WarmFields.slots p i).val := rfl
theorem driver_val (p : Program) : (driver p).val=WholePrefix.tapes p+2 := rfl
theorem log_val (p : Program) : (log p).val=WholePrefix.tapes p := rfl
theorem source_injective (p : Program) : Function.Injective (source p) := by
  intro i j he
  have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
  rw [source_val,source_val] at hv
  exact Fin.ext (by omega)
theorem dest_injective (p : Program) : Function.Injective (dest p) := by
  intro i j he
  apply WarmFields.injective p
  exact Fin.ext (congrArg (fun z : Fin (tapes p)=>z.val) he)
theorem pad_injective (p : Program) : Function.Injective (padSlots p) := by
  intro i j he
  apply Reuse.erase_injective p
  exact Fin.ext (congrArg (fun z : Fin (tapes p)=>z.val) he)

theorem copy_injective (p : Program) : Function.Injective (copySlots p) := by
  have tail : Function.Injective (Fin.append (dest p) (fun _ : Fin 1=>driver p)) := by
    apply Fin.append_injective_iff.mpr
    refine ⟨dest_injective p,fun _ _ _=>Subsingleton.elim _ _,?_⟩
    intro i _ he
    have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
    rw [dest_val,driver_val] at hv
    have hi:=(WarmFields.slots p i).isLt
    omega
  have first : Function.Injective (Fin.append (source p) (Fin.append (dest p) (fun _ : Fin 1=>driver p))) := by
    apply Fin.append_injective_iff.mpr
    refine ⟨source_injective p,tail,?_⟩
    intro i j
    refine Fin.addCases (m:=7) (n:=1) (fun k=>?_) (fun k=>?_) j
    · intro he
      have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
      simp only [Fin.append_left,source_val,dest_val] at hv
      have hi:=(WarmFields.slots p k).isLt
      unfold Reuse.tapes at hv
      omega
    · intro he
      have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
      simp only [Fin.append_right,source_val,driver_val] at hv
      unfold Reuse.tapes at hv
      omega
  apply Fin.append_injective_iff.mpr
  refine ⟨first,fun _ _ _=>Subsingleton.elim _ _,?_⟩
  intro i _
  refine Fin.addCases (m:=7) (n:=7+1) (fun k=>?_) (fun k=>?_) i
  · intro he
    have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
    simp only [Fin.addCases_left,source_val,log_val] at hv
    unfold Reuse.tapes at hv
    omega
  · refine Fin.addCases (m:=7) (n:=1) (fun j=>?_) (fun j=>?_) k
    · intro he
      have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
      simp only [Fin.addCases_right,Fin.addCases_left,dest_val,log_val] at hv
      have hi:=(WarmFields.slots p j).isLt
      omega
    · intro he
      have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
      simp only [Fin.addCases_right,driver_val,log_val] at hv
      omega

theorem cover (p : Program) (i : Fin (WholePrefix.tapes p)) (h52 : i.val≠52) (h68 : i.val≠68) :
    ∃ j,work p j=old p i := by
  have hi:=i.isLt
  have ht : 70 ≤ WholePrefix.tapes p := by unfold WholePrefix.tapes;omega
  let j : Fin (WholePrefix.tapes p-2):=
    ⟨if i.val<52 then i.val else if i.val<68 then i.val-1 else i.val-2,by split_ifs <;> omega⟩
  refine ⟨j,Fin.ext ?_⟩
  change (Reuse.work p j).val=i.val
  rw [Reuse.work_val]
  dsimp [j]
  split_ifs <;> omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepare
