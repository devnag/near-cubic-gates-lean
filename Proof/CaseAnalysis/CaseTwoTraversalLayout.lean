import Proof.CaseAnalysis.CaseTwoTagReady
import Proof.CaseAnalysis.CaseTwoFieldStep

/-! The original description walk shares one source/offset, two paid field
widths and one native append cursor. The node count is produced during the
walk. Extra source words and C.12 scalars remain outside this local bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
open LocalBitMultitape RepairRepresentation OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data (C F count : ℕ) (source : List Bool) (offset : ℕ) (tagWord out : List Bool) (flag : Bool) : Fin 30→List Bool:=
  Fin.addCases (m:=27) (n:=3) (TagReady.data C source offset tagWord flag)
    ![out,ZeroPadding.pad C (List.replicate F true),List.replicate count true]
def heads (out : List Bool) (i : Fin 30):=if i=27 then out.length else 0
def tagSlots (i : Fin 27) : Fin 30:=i.castAdd 3
def publishSlots (i : Fin 28) : Fin 30:=i.castAdd 2
def fieldSlots (i : Fin 25) : Fin 30:=if i=3 then 28 else if i=21 then 27 else i.castAdd 5
def countSlots : Fin 2→Fin 30:=![29,22]
theorem tag_injective : Function.Injective tagSlots:=by
  intro i j h;apply Fin.ext;exact congrArg (fun x : Fin 30=>x.val) h
theorem publish_injective : Function.Injective publishSlots:=by
  intro i j h;apply Fin.ext;exact congrArg (fun x : Fin 30=>x.val) h
theorem field_injective : Function.Injective fieldSlots:=by decide

theorem field_heads (out : List Bool) (i : Fin 25) : heads out (fieldSlots i)=FieldClear.heads out i:=by
  fin_cases i <;> rfl
theorem field_data (C F count : ℕ) (source : List Bool) (offset : ℕ) (tagWord out : List Bool) (flag : Bool)
    (i : Fin 25) : data C F count source offset tagWord out flag (fieldSlots i)=
      FieldClear.data C source offset F out i:=by
  fin_cases i <;> simp [data,fieldSlots,TagReady.data,TagReady.localData,TagReady.pads,
    TagObserve.data,FieldClear.data,Fin.addCases]
theorem field_outside (C F count oldOffset offset : ℕ) (source tagWord oldOut out : List Bool) (flag : Bool)
    (i : Fin 30) (hi : ∀ j,fieldSlots j≠i) :
    data C F count source offset tagWord out flag i=data C F count source oldOffset tagWord oldOut flag i:=by
  have h2 : i≠2:=fun h=>hi 2 h.symm
  have h27 : i≠27:=fun h=>hi 21 h.symm
  fin_cases i <;> first | contradiction | rfl
theorem field_head_outside (oldOut out : List Bool) (i : Fin 30) (hi : ∀ j,fieldSlots j≠i) :
    heads out i=heads oldOut i:=by
  have hn : i≠27:=fun h=>hi 21 h.symm
  simp only [heads,if_neg hn]

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
