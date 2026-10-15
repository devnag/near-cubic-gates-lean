import Proof.CaseAnalysis.RetainedRefuterRun
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.ScheduleGuardedBound
import Proof.Amplification.RecoveryPrefixPrepareCall
import Proof.Amplification.RecoveryCaseOneBooleanOutput

namespace GR

/-! The common schedule's finite-branch controller. It executes the refuter
only when the already-computed onset flag is true; the false branch uses the
existing one-step canonical Boolean-output core. All other old tapes survive. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.RefuterPrefix
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound
open CloseoutRetainedRefuter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def rejectSlots {t : Nat} (r : OrdinaryOracleProgram) (flag : Fin t) : Fin 2→Fin (tapes t r):=
  ![old r flag,fresh t r 0]
theorem reject_injective {t : Nat} (r : OrdinaryOracleProgram) (flag : Fin t) :
    Function.Injective (rejectSlots r flag):=by
  have h01:=old_fresh r flag 0
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [rejectSlots]

def first {t s : Nat} (p : Machine t s) (r : OrdinaryOracleProgram):=
  RecoveryFocus.machine (old r) p
def pieces {t s : Nat} (p : Machine t s) (r : OrdinaryOracleProgram) (source flag : Fin t)
    (j : Fin 3) : Piece (tapes t r):=
  match j.val with
  | 0=>ordinary (first p r)
  | 1=>graph (CloseoutRetainedRefuter.pieces r source) 0 (CloseoutRetainedRefuter.next r source)
  | _=>ordinary (RecoveryFocus.machine (rejectSlots r flag) RecoveryCaseOneBooleanOutput.core)
def next {t s : Nat} (p : Machine t s) (r : OrdinaryOracleProgram) (source flag : Fin t)
    (j : Fin 3) (_ : Fin (pieces p r source flag j).states) (scanned : Fin (tapes t r)→Bool) : Option (Fin 3):=
  if j=0 then some (if scanned (old r flag) then 1 else 2) else none
def program {t s : Nat} (p : Machine t s) (r : OrdinaryOracleProgram) (source flag : Fin t):=
  (ports r source).program (graph (pieces p r source flag) 0 (next p r source flag))

theorem input_old {t : Nat} (r : OrdinaryOracleProgram) (a : Fin t→List Bool) (i : Fin t) :
    input r a (old r i)=a i:=by simp [input,old,i.isLt]
theorem input_fresh {t : Nat} (r : OrdinaryOracleProgram) (a : Fin t→List Bool) (i : Fin 3) :
    input r a (fresh t r i)=[]:=by
  simp [input,fresh,show ¬t+(clocked r).base.tapeCount+i.val<t by omega]
theorem install_old {t : Nat} (r : OrdinaryOracleProgram) (a b : Fin t→List Bool) :
    install (old r) (input r a) b=input r b:=by
  funext i
  by_cases hi:i.val<t
  · let j : Fin t:=⟨i.val,hi⟩
    have he:i=old r j:=Fin.ext rfl
    rw [he,install_slot _ (old_injective r),input_old]
  · rw [install_other _ _ _ _ (by
      intro j h
      have hv:=congrArg Fin.val h
      have hj:=j.isLt
      change j.val=i.val at hv
      omega)]
    simp [input,hi]

theorem first_ready {t s fuel : Nat} {o : Nat→Bool} (p : Machine t s)
    (r : OrdinaryOracleProgram) (source : Fin t) (a b : Fin t→List Bool)
    (h : ClockJoin.ReadyRun p fuel a b) :
    ∃ cost≤fuel,Ready o ((ports r source).program (ordinary (first p r))) cost (input r a) (input r b):=by
  have hf:=h.focus (old r) (old_injective r) (input r a) (input_old r a)
  rw [install_old] at hf
  exact RecoveryPrefixCold.ordinary_ready (ports r source) (first p r) _ _ hf

theorem reject_ready {t : Nat} {o : Nat→Bool} (r : OrdinaryOracleProgram)
    (source flag : Fin t) (a : Fin t→List Bool) (hflag : a flag=[false]) :
    ∃ out,Ready o ((ports r source).program
      (ordinary (RecoveryFocus.machine (rejectSlots r flag) RecoveryCaseOneBooleanOutput.core)))
      1 (input r a) out ∧
      (∀ i : Fin t,out (old r i)=a i) ∧ out (fresh t r 0)=frame []:=by
  have hlocal : RecoveryRootRound.ReadyRun RecoveryCaseOneBooleanOutput.core 1
      ![[false],[]] ![[false],[false]]:=
    ⟨_,rfl,by funext i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl,rfl⟩
  let out:=install (rejectSlots r flag) (input r a) ![[false],[false]]
  have hr:=hlocal.focus (rejectSlots r flag) (reject_injective r flag) (input r a) (by
    intro j
    fin_cases j
    · exact (input_old r a flag).trans hflag
    · exact input_fresh r a 0)
  refine ⟨out,Ready.ordinary (ports r source) hr,?_,?_⟩
  · intro i
    by_cases hi:i=flag
    · subst i
      change install (rejectSlots r flag) _ _ (rejectSlots r flag 0)=a flag
      rw [install_slot _ (reject_injective r flag)]
      exact hflag.symm
    · rw [show out (old r i)=input r a (old r i) from install_other _ _ _ _ (by
        intro j h
        fin_cases j
        · exact hi ((old_injective r h).symm)
        · exact (old_fresh r i 0) h.symm)]
      exact input_old r a i
  · change install (rejectSlots r flag) _ _ (rejectSlots r flag 1)=_
    rw [install_slot _ (reject_injective r flag)]
    rfl

end
end NearCubicWires.RepairSource.CloseoutSchedule.RefuterPrefix

end GR
