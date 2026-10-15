import Proof.CaseAnalysis.CaseTwoOccurrenceAddressRun
import Proof.CaseAnalysis.CaseTwoOccurrenceBitRun

/-! The two checked whole occurrence workers share the actual source bank.
Only the query index is redirected to the freshly decoded native address;
the old padded index remains outside the clause consumer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Occurrence
open LocalBitMultitape SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (D : ℕ) (a : PointwisePCPPAlgorithm):=OccurrenceAddress.tapes D+OccurrenceBit.tapes a
def old (D : ℕ) (a : PointwisePCPPAlgorithm) (i : Fin (OccurrenceAddress.tapes D)) : Fin (tapes D a):=
  i.castAdd (OccurrenceBit.tapes a)
def inputPort (D : ℕ) (j : Fin 25) : Fin (OccurrenceAddress.tapes D):=
  if j.val=14 then OccurrenceAddress.fieldSlots D 19
  else if j.val=19 then OccurrenceAddress.base D 56
  else if j.val=20 then OccurrenceAddress.fieldSlots D 8
  else if j.val=21 then OccurrenceAddress.fieldSlots D 4
  else if j.val=22 then OccurrenceAddress.base D 53
  else if j.val=23 then OccurrenceAddress.base D 28
  else if j.val=24 then OccurrenceAddress.fieldSlots D 21
  else OccurrenceAddress.base D ⟨j.val,by omega⟩
def bitSlots (D : ℕ) (a : PointwisePCPPAlgorithm) (j : Fin (OccurrenceBit.tapes a)) : Fin (tapes D a):=
  if h : j.val<25 then old D a (inputPort D ⟨j.val,h⟩) else j.natAdd (OccurrenceAddress.tapes D)
def first (D block : ℕ) (a : PointwisePCPPAlgorithm):=
  RecoveryFocus.machine (old D a) (OccurrenceAddress.machine D block)
def last (D : ℕ) (a : PointwisePCPPAlgorithm):=
  RecoveryFocus.machine (bitSlots D a) (OccurrenceBit.machine a)
def machine (D block : ℕ) (a : PointwisePCPPAlgorithm):=Composition.machine (first D block a) (last D a)
def input (D : ℕ) (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (address : List Bool) :
    Fin (tapes D a) → List Bool:=Fin.addCases (OccurrenceAddress.input D a r address) (fun _=>[])
def heads (D : ℕ) (a : PointwisePCPPAlgorithm) : Fin (tapes D a) → ℕ:=
  Fin.addCases (OccurrenceAddress.heads D) (fun _=>0)
def outputSlot (D : ℕ) (a : PointwisePCPPAlgorithm):=bitSlots D a (OccurrenceBit.outputSlot a)
def budget (D block : ℕ) (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (clause : BitInput (a.output r).clauseBits) (position : Bool) (padding : ℕ):=
  OccurrenceAddress.budget D block a r padding (binaryAddress clause).val+1+
    OccurrenceBit.budget a r u (binaryAddress clause) position

theorem old_injective (D : ℕ) (a : PointwisePCPPAlgorithm) : Function.Injective (old D a):=by
  intro i j he;apply Fin.ext;exact congrArg (fun k : Fin (tapes D a)=>k.val) he
theorem port_value (D : ℕ) (j : Fin 25) : (inputPort D j).val=
    if j.val=14 then 58+Widths.tapes D+8+19 else if j.val=19 then 56
    else if j.val=20 then 58+Widths.tapes D+8+8 else if j.val=21 then 58+Widths.tapes D+8+4
    else if j.val=22 then 53 else if j.val=23 then 28
    else if j.val=24 then 58+Widths.tapes D+8+21 else j.val:=by
  unfold inputPort
  split_ifs <;>rfl
theorem port_injective (D : ℕ) : Function.Injective (inputPort D):=by
  intro i j he
  have h:=congrArg Fin.val he
  have hi:=i.isLt
  have hj:=j.isLt
  apply Fin.ext
  simp only [port_value] at h
  split_ifs at h <;>omega
theorem bit_injective (D : ℕ) (a : PointwisePCPPAlgorithm) : Function.Injective (bitSlots D a):=by
  intro i j he
  have h:=congrArg Fin.val he
  by_cases hi : i.val<25 <;>by_cases hj : j.val<25
  · have hm : inputPort D ⟨i.val,hi⟩=inputPort D ⟨j.val,hj⟩:=
      old_injective D a (by simpa only [bitSlots,dif_pos hi,dif_pos hj] using he)
    apply Fin.ext
    exact congrArg (fun k : Fin 25=>k.val) (port_injective D hm)
  · have bound:=(inputPort D ⟨i.val,hi⟩).isLt
    simp only [bitSlots,dif_pos hi,dif_neg hj,old,Fin.val_castAdd,Fin.val_natAdd] at h
    omega
  · have bound:=(inputPort D ⟨j.val,hj⟩).isLt
    simp only [bitSlots,dif_neg hi,dif_pos hj,old,Fin.val_castAdd,Fin.val_natAdd] at h
    omega
  · apply Fin.ext
    simp only [bitSlots,dif_neg hi,dif_neg hj,Fin.val_natAdd] at h
    omega

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Occurrence
