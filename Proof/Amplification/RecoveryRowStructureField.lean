import Proof.Amplification.RecoveryRowCountRun

/-! Tape-update equations for the structural row's code copy into the
existing retained-field unpair input. The generic bank equations avoid
expanding unrelated finite call-graph controls in physical layout proofs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bank_update_left {m n : Nat} (left : Fin m→List Bool) (right : Fin n→List Bool)
    (i : Fin m) (word : List Bool) :
    Fin.addCases (m:=m) (n:=n) (motive:=fun _=>List Bool) (Function.update left i word) right=
      Function.update (Fin.addCases (m:=m) (n:=n) (motive:=fun _=>List Bool) left right) (i.castAdd n) word := by
  funext k
  refine Fin.addCases (m:=m) (n:=n) (fun j=>?_) (fun j=>?_) k
  · simp [Function.update,Fin.castAdd_inj]
  · have hne : j.natAdd m≠i.castAdd n := by intro h; have hh:=congrArg Fin.val h; simp at hh; omega
    simp [Function.update_of_ne hne]

theorem bank_update_right {m n : Nat} (left : Fin m→List Bool) (right : Fin n→List Bool)
    (i : Fin n) (word : List Bool) :
    Fin.addCases (m:=m) (n:=n) (motive:=fun _=>List Bool) left (Function.update right i word)=
      Function.update (Fin.addCases (m:=m) (n:=n) (motive:=fun _=>List Bool) left right) (i.natAdd m) word := by
  funext k
  refine Fin.addCases (m:=m) (n:=n) (fun j=>?_) (fun j=>?_) k
  · have hne : j.castAdd n≠i.natAdd m := by intro h; have hh:=congrArg Fin.val h; simp at hh; omega
    simp [Function.update_of_ne hne]
  · simp [Function.update,Fin.natAdd_inj]

def setField (s : State) (which : Fin 3) (word : List Bool) : State :=
  {s with fields:=Function.update s.fields which word}

theorem setField_tapes (s : State) (which : Fin 3) (word : List Bool) :
    (setField s which word).tapes=Function.update s.tapes (savedSlot which) word := by
  change Fin.addCases (m:=24) (n:=4) (motive:=fun _=>List Bool) s.core
    (Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool) (Function.update s.fields which word) (fun _=>[s.result]))=_
  rw [bank_update_left,bank_update_right]
  rfl

theorem setField_valid (s : State) (which : Fin 3) (word : List Bool) (hs : s.Valid)
    (hw : word.length≤2*s.bits.length+1) : (setField s which word).Valid := by
  refine ⟨hs.1,?_⟩
  intro i
  by_cases hi : i=which
  · subst i; simpa only [setField,Function.update_self] using hw
  · simpa only [setField,Function.update_of_ne hi] using hs.2 i

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
