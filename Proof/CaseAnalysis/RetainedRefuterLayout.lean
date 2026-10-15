import Proof.MachineModel.OrdinaryOracleCompose

/-! The common recovery program calls its refuter on the already-produced
framed request. Static input-tape aliasing avoids another copy; the original
address and finite-branch flag remain outside the refuter bank. The output
copy precedes paid query erasure because a source may share those two tapes. -/
namespace NearCubicWires.RepairSource.CloseoutRetainedRefuter
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (t : Nat) (p : OrdinaryOracleProgram):=t+(clocked p).base.tapeCount+3
def old {t : Nat} (p : OrdinaryOracleProgram) (i : Fin t) : Fin (tapes t p):=
  ⟨i.val,by have hi:=i.isLt; unfold tapes; omega⟩
def bank {t : Nat} (p : OrdinaryOracleProgram) (source : Fin t)
    (i : Fin (clocked p).base.tapeCount) : Fin (tapes t p):=
  if i.val=0 then old p source else ⟨t+i.val,by have hi:=i.isLt; unfold tapes; omega⟩
def fresh (t : Nat) (p : OrdinaryOracleProgram) (i : Fin 3) : Fin (tapes t p):=
  ⟨t+(clocked p).base.tapeCount+i.val,by have hi:=i.isLt; unfold tapes; omega⟩
def input {t : Nat} (p : OrdinaryOracleProgram) (ambient : Fin t→List Bool) :
    Fin (tapes t p)→List Bool:=fun i=>if h:i.val<t then ambient ⟨i.val,h⟩ else []

theorem old_injective {t : Nat} (p : OrdinaryOracleProgram) : Function.Injective (old (t:=t) p):=by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin (tapes t p)=>i.val) h)
theorem fresh_injective (t : Nat) (p : OrdinaryOracleProgram) : Function.Injective (fresh t p):=by
  intro a b h
  have hv:=congrArg Fin.val h
  apply Fin.ext
  change t+(clocked p).base.tapeCount+a.val=t+(clocked p).base.tapeCount+b.val at hv
  omega
theorem bank_injective {t : Nat} (p : OrdinaryOracleProgram) (source : Fin t) :
    Function.Injective (bank p source):=by
  intro a b h
  have hv:=congrArg Fin.val h
  have hs:=source.isLt
  apply Fin.ext
  by_cases ha:a.val=0 <;> by_cases hb:b.val=0 <;>
    simp only [bank,ha,hb,if_true,if_false,old] at hv <;> omega
theorem bank_old {t : Nat} (p : OrdinaryOracleProgram) (source i : Fin t)
    (hi : i≠source) (j : Fin (clocked p).base.tapeCount) : bank p source j≠old p i:=by
  intro h
  have hv:=congrArg Fin.val h
  have ht:=i.isLt
  by_cases hj:j.val=0
  · rw [bank,if_pos hj] at h
    exact hi ((old_injective p h).symm)
  · simp only [bank,hj,if_false,old] at hv
    omega
theorem bank_fresh {t : Nat} (p : OrdinaryOracleProgram) (source : Fin t)
    (i : Fin (clocked p).base.tapeCount) (j : Fin 3) : bank p source i≠fresh t p j:=by
  intro h
  have hv:=congrArg Fin.val h
  have hs:=source.isLt
  have hi:=i.isLt
  by_cases hz:i.val=0 <;> simp only [bank,hz,if_true,if_false,old,fresh] at hv <;> omega
theorem old_fresh {t : Nat} (p : OrdinaryOracleProgram) (i : Fin t) (j : Fin 3) :
    old p i≠fresh t p j:=by
  intro h
  have hv:=congrArg Fin.val h
  have hi:=i.isLt
  change i.val=t+(clocked p).base.tapeCount+j.val at hv
  omega

def copySlots {t : Nat} (p : OrdinaryOracleProgram) (source : Fin t) : Fin 3→Fin (tapes t p):=
  ![bank p source (clocked p).base.outputTape,fresh t p 0,fresh t p 1]
def clearSlots {t : Nat} (p : OrdinaryOracleProgram) (source : Fin t) : Fin 3→Fin (tapes t p):=
  ![bank p source (clocked p).queryTape,bank p source (clockTape p),fresh t p 2]
theorem copy_injective {t : Nat} (p : OrdinaryOracleProgram) (source : Fin t) :
    Function.Injective (copySlots p source):=by
  have h01:=bank_fresh p source (clocked p).base.outputTape 0
  have h02:=bank_fresh p source (clocked p).base.outputTape 1
  have h12 : fresh t p 0≠fresh t p 1:=fun h=>(by decide : (0 : Fin 3)≠1) (fresh_injective t p h)
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [copySlots]
theorem clear_injective {t : Nat} (p : OrdinaryOracleProgram) (source : Fin t) :
    Function.Injective (clearSlots p source):=by
  have h01 : bank p source (clocked p).queryTape≠bank p source (clockTape p):=
    fun h=>query_ne_clock p (bank_injective p source h)
  have h02:=bank_fresh p source (clocked p).queryTape 2
  have h12:=bank_fresh p source (clockTape p) 2
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [clearSlots]

def ports {t : Nat} (p : OrdinaryOracleProgram) (source : Fin t) : Ports (tapes t p) where
  twoTapes:=by unfold tapes; omega
  outputTape:=fresh t p 0
  outputFresh:=by have hp:=(clocked p).base.twoTapes; simp only [fresh]; omega
  queryTape:=bank p source (clocked p).queryTape
  queryFresh:=by
    have hp:=(clocked p).queryFresh
    simp only [bank,hp,if_false]
    omega
def pieces {t : Nat} (p : OrdinaryOracleProgram) (source : Fin t) (j : Fin 3) : Piece (tapes t p):=
  match j.val with
  | 0=>focused (clocked p) (bank p source)
  | 1=>ordinary (RecoveryFocus.machine (copySlots p source) PCPFieldMoves.readyMachine)
  | _=>ordinary (RecoveryFocus.machine (clearSlots p source) (RecoveryScratchErase.resetMachine 1))
def next {t : Nat} (p : OrdinaryOracleProgram) (source : Fin t) (j : Fin 3)
    (_ : Fin (pieces p source j).states) (_ : Fin (tapes t p)→Bool) : Option (Fin 3):=
  if j=0 then some 1 else if j=1 then some 2 else none
def program {t : Nat} (p : OrdinaryOracleProgram) (source : Fin t):=
  (ports p source).program (graph (pieces p source) 0 (next p source))

end
end NearCubicWires.RepairSource.CloseoutRetainedRefuter
