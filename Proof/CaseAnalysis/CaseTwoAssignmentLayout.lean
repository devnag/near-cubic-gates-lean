import Proof.CaseAnalysis.CaseTwoSystematicReady
import Proof.CaseAnalysis.CaseTwoAuxiliaryBit
import Proof.CaseAnalysis.CaseTwoVariablePrep
import Proof.Amplification.RecoveryCursorCalls

/-! One fixed original-assignment dispatcher. It compares the actual unsigned
variable with the source's systematic count, then selects the original support
parity or the original honest auxiliary bit. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Assignment
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (a : PointwisePCPPAlgorithm)
def tapes:=30+AuxiliaryBit.tapes a
def low (i : Fin 30) : Fin (tapes a):=i.castAdd (AuxiliaryBit.tapes a)
def prepareSlots (i : Fin 6) : Fin (tapes a):=low a (![13,14,15,16,17,18] i)
def systematicSlots (i : Fin 13) : Fin (tapes a):=low a (![0,1,2,3,4,15,6,7,8,11,12,25,26] i)
def offsetSlots (i : Fin 8) : Fin (tapes a):=low a (![15,14,19,20,21,22,23,24] i)
def auxiliarySlots (i : Fin (AuxiliaryBit.tapes a)) : Fin (tapes a):=
  if i.val=0 then low a 9 else if i.val=1 then low a 10
  else if i=AuxiliaryBit.indexSlot a then low a 21
  else if i=AuxiliaryBit.outputSlot a then low a 25 else i.natAdd 30
theorem low_injective : Function.Injective (low a):=by
  intro i j he;apply Fin.ext;exact congrArg (fun x : Fin (tapes a)=>x.val) he
theorem prepare_injective : Function.Injective (prepareSlots a):=
  (low_injective a).comp (by decide)
theorem systematic_injective : Function.Injective (systematicSlots a):=
  (low_injective a).comp (by decide)
theorem offset_injective : Function.Injective (offsetSlots a):=
  (low_injective a).comp (by decide)
theorem auxiliary_injective : Function.Injective (auxiliarySlots a):=by
  intro i j he
  have hv:=congrArg Fin.val he
  apply Fin.ext
  dsimp only [auxiliarySlots,low] at hv
  split_ifs at hv <;>simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  all_goals omega

def prepare:=RecoveryFocus.machine (prepareSlots a) VariablePrep.machine
def systematic:=RecoveryFocus.machine (systematicSlots a) SystematicReady.machine
def offset:=RecoveryFocus.machine (offsetSlots a) VariablePrep.auxiliary
def auxiliary:=RecoveryFocus.machine (auxiliarySlots a) (AuxiliaryBit.machine a)
def workers : Fin 4→(Σ s,Machine (tapes a) s):=
  ![⟨_,prepare a⟩,⟨_,systematic a⟩,⟨_,offset a⟩,⟨_,auxiliary a⟩]
def sizes (j : Fin 4):=(workers a j).1
def programs (j : Fin 4) : Machine (tapes a) (sizes a j):=(workers a j).2
def next (j : Fin 4) (_ : Fin (sizes a j)) (bits : Fin (tapes a)→Bool) : Option (Fin 4):=
  if j=0 then some (if bits (low a 17) then 2 else 1) else if j=2 then some 3 else none
def machine:=RecoveryCalls.machine (sizes a) (programs a) 0 (next a)
def heads (i : Fin (tapes a)):=if i.val=3 ∨ i.val=5 then 1 else 0
def input (r : PCPPRequest a.minimumArity) (u : BitInput r.arity) (index oldIndex : ℕ)
    (i : Fin (tapes a)) : List Bool:=
  if h : i.val<9 then PCPPQuerySupportReuse.data (pcppOutput r (a.output r)) r.arity oldIndex
      (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [] ⟨i.val,h⟩
  else if i.val=9 then frame (pcppInput r) else if i.val=10 then frame (List.ofFn u)
  else if i.val=11 then List.replicate r.arity true else if i.val=12 then List.ofFn u
  else if i.val=13 then List.replicate index true else if i.val=14 then UnaryTemplate.tape (a.output r).systematicBits else []
def budget (r : PCPPRequest a.minimumArity) (u : BitInput r.arity) (index : ℕ):=
  VariablePrep.budget index (a.output r).systematicBits+1+
    (1+1+SystematicBit.budget a r)+1+
    VariablePrep.auxiliaryBudget index (a.output r).systematicBits+1+
    AuxiliaryBit.budget a r u (index-(a.output r).systematicBits)+1
def cfg (j : Fin 4) (H : Fin (tapes a)→ℕ) (A : Fin (tapes a)→List Bool):=
  controlConfig (RecoveryCalls.code (sizes a) j)
    (⟨(programs a j).start,H,A⟩ : Configuration (tapes a) (sizes a j))

theorem high_input (r : PCPPRequest a.minimumArity) (u : BitInput r.arity) (index oldIndex : ℕ)
    (i : Fin (tapes a)) (hi : 15 ≤ i.val) : input a r u index oldIndex i=[]:=by
  simp [input,show ¬i.val<9 by omega,show i.val≠9 by omega,show i.val≠10 by omega,
    show i.val≠11 by omega,show i.val≠12 by omega,show i.val≠13 by omega,show i.val≠14 by omega]
theorem high_heads (i : Fin (tapes a)) (hi : 6 ≤ i.val) : heads a i=0:=by
  simp [heads,show i.val≠3 by omega,show i.val≠5 by omega]

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Assignment
