import Proof.CaseAnalysis.RowsCircuitAppend

/-! One bottom traversal bank. Source, selected-membership cursor, native
request stream and cumulative resource totals stay outside the gate scratch.
Only the actual core template has a nonzero local entry head. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
open LocalBitMultitape RadixSemantics RecoveryRootRound CloseoutRowsGatePairHeads
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coreSlots (i : Fin 1049) : Fin 1059:=i.castAdd 10
def loadSlots : Fin 3→Fin 1059:=![1052,1,1057]
def nativeSlots : Fin 3→Fin 1059:=![1033,1049,1057]
def descriptionSlots : Fin 4→Fin 1059:=![1041,1045,1050,1057]
def wireSlots : Fin 4→Fin 1059:=![1047,1058,1051,1057]
def flagSlots : Fin 2→Fin 1059:=![1037,1054]
def scratchSlots (i : Fin 1048) : Fin 1059:=
  if i.val<1035 then ⟨i.val,by omega⟩ else ⟨i.val+1,by omega⟩
def eraseSlots : Fin 1050→Fin 1059:=Fin.addCases (m:=1048) (n:=2) scratchSlots ![1055,1056]

theorem core_injective : Function.Injective coreSlots:=by
  intro i j h;exact Fin.ext (congrArg (fun k : Fin 1059=>k.val) h)
theorem scratch_val (i : Fin 1048) : (scratchSlots i).val=if i.val<1035 then i.val else i.val+1:=by
  unfold scratchSlots;split <;> rfl
theorem scratch_small (i : Fin 1048) : (scratchSlots i).val<1049:=by
  rw [scratch_val];split_ifs <;> omega
theorem scratch_not_core (i : Fin 1048) : (scratchSlots i).val≠1035:=by
  rw [scratch_val];split_ifs <;> omega
theorem core_other (i : Fin 10) : ∀ j,coreSlots j≠i.natAdd 1049:=by
  intro j h;have hv:=congrArg Fin.val h
  change j.val=1049+i.val at hv;omega

def heads (pos memberPos : ℕ) (out : List Bool) (description wires : ℕ) (i : Fin 1059):=
  if i.val=1035 then 1 else if i.val=1049 then out.length else
    if i.val=1050 then description else if i.val=1051 then wires else
      if i.val=1052 then pos else if i.val=1053 then memberPos else 0
def extra (cap : ℕ) (out source membership : List Bool) (description wires : ℕ) (flag : Bool) : Fin 10→List Bool:=
  ![out,List.replicate description true,List.replicate wires true,source,membership,[flag],
    List.replicate cap true,List.replicate (cap+1) false,List.replicate cap false,
    ZeroPadding.pad cap [true]]
def data (cap core : ℕ) (bits out source membership : List Bool) (description wires : ℕ) (flag : Bool) :
    Fin 1059→List Bool:=Fin.addCases (m:=1049) (n:=10)
      (CloseoutRowsGateBank.input cap core bits) (extra cap out source membership description wires flag)
def cfg {s : ℕ} (q : Fin s) (cap core pos memberPos : ℕ) (bits out source membership : List Bool)
    (description wires : ℕ) (flag : Bool) : Configuration 1059 s:=
  ⟨q,heads pos memberPos out description wires,data cap core bits out source membership description wires flag⟩

theorem data_core (cap core : ℕ) (bits out source membership : List Bool) (description wires : ℕ)
    (flag : Bool) (i : Fin 1049) :
    data cap core bits out source membership description wires flag (coreSlots i)=CloseoutRowsGateBank.input cap core bits i:=by
  simp only [data,coreSlots,Fin.addCases_left]
theorem data_extra (cap core : ℕ) (bits out source membership : List Bool) (description wires : ℕ)
    (flag : Bool) (i : Fin 10) :
    data cap core bits out source membership description wires flag (i.natAdd 1049)=
      extra cap out source membership description wires flag i:=by
  simp only [data,Fin.addCases_right]
theorem heads_core (pos memberPos : ℕ) (out : List Bool) (description wires : ℕ) (i : Fin 1049) :
    heads pos memberPos out description wires (coreSlots i)=CloseoutRowsGateMeasured.heads i:=by
  rw [CloseoutRowsGateBank.heads_eq]
  simp only [heads,coreSlots,Fin.val_castAdd,
    if_neg (show i.val≠1049 by omega),if_neg (show i.val≠1050 by omega),
    if_neg (show i.val≠1051 by omega),if_neg (show i.val≠1052 by omega),if_neg (show i.val≠1053 by omega)]

structure Stored (cap core : ℕ) (out source membership : List Bool) (description wires : ℕ) (flag : Bool)
    (tapes : Fin 1059→List Bool) : Prop where
  scratch : ∀ i,(tapes (scratchSlots i)).length ≤ cap
  domain : tapes 1035=UnaryTemplate.tape core
  extra : ∀ i,tapes (i.natAdd 1049)=CloseoutRowsCircuitBottom.extra cap out source membership description wires flag i

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
