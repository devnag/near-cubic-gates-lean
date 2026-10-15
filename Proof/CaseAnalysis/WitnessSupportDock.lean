import Proof.Amplification.RecoveryAllCodeLayout

/-! One added public stream lifts an existing physical tape injection.
Old aliases are unchanged in value, and the new tape has its own alias. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SupportDock
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def lift {t : ℕ} {α : Type} (data : Fin t→α) (last : α) : Fin (t+1)→α:=
  Fin.addCases (m:=t) (n:=1) data (fun _=>last)
def slots {m t : ℕ} (old : Fin m→Fin t) : Fin (m+1)→Fin (t+1):=
  Fin.addCases (m:=m) (n:=1) (fun i=>(old i).castAdd 1) (fun i=>i.natAdd t)

theorem slots_old {m t : ℕ} (old : Fin m→Fin t) (i : Fin m) :
    slots old (i.castAdd 1)=(old i).castAdd 1:=by simp only [slots,Fin.addCases_left]
theorem slots_new {m t : ℕ} (old : Fin m→Fin t) (i : Fin 1) :
    slots old (i.natAdd m)=i.natAdd t:=by simp only [slots,Fin.addCases_right]

theorem injective {m t : ℕ} (old : Fin m→Fin t) (hi:Function.Injective old) :
    Function.Injective (slots old) := by
  apply RecoveryColdAllCode.join_injective
  · exact (Fin.castAdd_injective _ _).comp hi
  · intro i j h
    apply Fin.ext
    have hv:=congrArg Fin.val h
    simpa only [Fin.val_natAdd] using Nat.add_left_cancel hv
  · intro i j h
    have hv:=congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    have bound:=(old i).isLt
    omega

theorem local_fields {m t : ℕ} {α : Type} (old : Fin m→Fin t) (data : Fin t→α) (inner : Fin m→α) (last : α)
    (h:∀ i,data (old i)=inner i) (i : Fin (m+1)) :
    lift data last (slots old i)=lift inner last i := by
  refine Fin.addCases (m:=m) (n:=1) ?_ ?_ i
  · intro j
    simpa only [slots_old,lift,Fin.addCases_left] using h j
  · intro j
    simp only [slots_new,lift,Fin.addCases_right]

theorem outside {m t : ℕ} (old : Fin m→Fin t) (i : Fin t) (hi:∀ j,old j≠i) :
    ∀ j,slots old j≠i.castAdd 1 := by
  intro j
  refine Fin.addCases (m:=m) (n:=1) ?_ ?_ j
  · intro k h
    rw [slots_old] at h
    exact hi k ((Fin.castAdd_injective _ _) h)
  · intro k h
    rw [slots_new] at h
    have hv:=congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    omega

end NearCubicWires.RepairOrdinary.CloseoutWitness.SupportDock
