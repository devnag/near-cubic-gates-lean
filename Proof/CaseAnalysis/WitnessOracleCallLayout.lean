import Proof.CaseAnalysis.WitnessOracleRun
import Proof.MachineModel.OrdinaryOracleComposeHandoff

/-! Copy only the three parser inputs from the retained selected-source
bank. The bank is preserved in full for the native PCPP continuation; the
oracle decoder's own scratch starts cold. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.OracleCall
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (t : ℕ):=t+1385
def old {t : ℕ} (i : Fin t) : Fin (tapes t):=i.castAdd 1385
def extra (t : ℕ) (i : Fin 1385) : Fin (tapes t):=i.natAdd t
def parserSlots (t : ℕ) (i : Fin (Oracle.tapes+1)) : Fin (tapes t):=(i.castAdd 4).natAdd t
def copySlots {t : ℕ} (fields : Fin 3→Fin t) (j : Fin 2) : Fin 3→Fin (tapes t):=
  ![old (fields (j.castAdd 1)),extra t (if j=0 then 0 else 2),extra t ⟨1381+j.val,by omega⟩]
def rawSlots {t : ℕ} (fields : Fin 3→Fin t) : Fin 4→Fin (tapes t):=
  ![old (fields 2),extra t 1383,extra t 3,extra t 1384]

theorem old_injective (t : ℕ) : Function.Injective (@old t):=by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin (tapes t)=>i.val) h)
theorem parser_injective (t : ℕ) : Function.Injective (parserSlots t):=by
  intro a b h
  have hv:=congrArg Fin.val h
  simp only [parserSlots,Fin.val_natAdd,Fin.val_castAdd] at hv
  exact Fin.ext (by omega)
theorem copy_injective {t : ℕ} (fields : Fin 3→Fin t) (j : Fin 2) :
    Function.Injective (copySlots fields j):=by
  intro a b h
  have hs: (fields (j.castAdd 1)).val<t:=(fields (j.castAdd 1)).isLt
  have hv:=congrArg Fin.val h
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [copySlots,old,extra,Fin.ext_iff] at hv ⊢ <;> omega
theorem raw_injective {t : ℕ} (fields : Fin 3→Fin t) : Function.Injective (rawSlots fields):=by
  intro a b h
  have hs:(fields 2).val<t:=(fields 2).isLt
  have hv:=congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [rawSlots,old,extra,Fin.ext_iff] at hv ⊢ <;> omega

def input {t : ℕ} (base : Fin t→List Bool) (bits : List Bool) : Fin (tapes t)→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (t+1385)=>List Bool) base (fun i=>if i.val=1 then frame bits else [])
noncomputable def copy {t : ℕ} (fields : Fin 3→Fin t) (j : Fin 2):=
  RecoveryFocus.machine (copySlots fields j) PCPFieldMoves.readyMachine
noncomputable def raw {t : ℕ} (fields : Fin 3→Fin t):=
  RecoveryFocus.machine (rawSlots fields) ClockUnarySum.machine
noncomputable def parser (t : ℕ):=RecoveryFocus.machine (parserSlots t) Oracle.machine
noncomputable def copies {t : ℕ} (fields : Fin 3→Fin t):=Composition.machine (copy fields 0) (copy fields 1)
noncomputable def prepare {t : ℕ} (fields : Fin 3→Fin t):=Composition.machine (copies fields) (raw fields)
noncomputable def machine {t : ℕ} (fields : Fin 3→Fin t):=Composition.machine (prepare fields) (parser t)

def copiedX {t : ℕ} (base : Fin t→List Bool) (bits x : List Bool):=
  Function.update (Function.update (input base bits) (extra t 0) (frame x))
    (extra t 1381) (List.replicate (2*x.length+1) false)
def copied {t : ℕ} (base : Fin t→List Bool) (bits x arityBits : List Bool):=
  Function.update (Function.update (copiedX base bits x) (extra t 2) (frame arityBits))
    (extra t 1382) (List.replicate (2*arityBits.length+1) false)
noncomputable def prepared {t : ℕ} (fields : Fin 3→Fin t) (base : Fin t→List Bool)
    (bits x arityBits : List Bool):=
  install (rawSlots fields) (copied base bits x arityBits)
    ![List.replicate (value arityBits) true,[],List.replicate (value arityBits) true,
      List.replicate (value arityBits+2) false]
def prepareBudget (x arityBits : List Bool):=4*x.length+4+1+(4*arityBits.length+4)+1+(2*value arityBits+6)
def budget (x bits arityBits : List Bool):=prepareBudget x arityBits+1+Oracle.budget x bits arityBits

theorem input_old {t : ℕ} (base : Fin t→List Bool) (bits : List Bool) (i : Fin t) :
    input base bits (old i)=base i:=by simp only [input,old,Fin.addCases_left]
theorem input_extra {t : ℕ} (base : Fin t→List Bool) (bits : List Bool) (i : Fin 1385) :
    input base bits (extra t i)=if i.val=1 then frame bits else []:=by
  simp only [input,extra,Fin.addCases_right]

theorem old_ne_extra {t : ℕ} (i : Fin t) (j : Fin 1385) : old i≠extra t j:=by
  intro h
  have hv:=congrArg Fin.val h
  simp only [old,extra,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem copiedX_old {t : ℕ} (base : Fin t→List Bool) (bits x : List Bool) (i : Fin t) :
    copiedX base bits x (old i)=base i:=by
  rw [copiedX,Function.update_of_ne (old_ne_extra i _),
    Function.update_of_ne (old_ne_extra i _),input_old]
theorem copied_old {t : ℕ} (base : Fin t→List Bool) (bits x arityBits : List Bool) (i : Fin t) :
    copied base bits x arityBits (old i)=base i:=by
  rw [copied,Function.update_of_ne (old_ne_extra i _),
    Function.update_of_ne (old_ne_extra i _),copiedX_old]

end NearCubicWires.RepairOrdinary.CloseoutWitness.OracleCall
