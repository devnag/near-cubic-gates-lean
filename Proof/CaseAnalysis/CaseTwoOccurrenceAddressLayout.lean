import Proof.CaseAnalysis.CaseTwoWidths
import Proof.CaseAnalysis.CaseTwoAddressRetention
import Proof.CaseAnalysis.CaseTwoMetadata

/-! The paid address front starts from the original cache and two retained
frames. Fresh banks hold width arithmetic, one physical block crop, and its
actual occurrence fields. The original cache and request frame stay outside
the field readers. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OccurrenceAddress
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (D : ℕ):=58+(Widths.tapes D+8+27)
def base (D : ℕ) (i : Fin 58) : Fin (tapes D):=i.castAdd (Widths.tapes D+8+27)
def metadataSlots (D : ℕ) (i : Fin 56) : Fin (tapes D):=base D (i.castAdd 2)
def widthSlots (D : ℕ) (i : Fin (Widths.tapes D)) : Fin (tapes D):=
  if i.val=0 then base D 52 else if i.val=1 then base D 48
  else ⟨58+i.val,by have h:=i.isLt;unfold tapes;omega⟩
def scalarPort (D : ℕ) (i : Fin 22):=widthSlots D (Widths.scalarSlots D i)
def cropSlots (D : ℕ) (i : Fin 8) : Fin (tapes D):=
  if i.val=0 then base D 57 else if i.val=2 then scalarPort D 8 else if i.val=3 then scalarPort D 2
  else ⟨58+Widths.tapes D+i.val,by have h:=i.isLt;unfold tapes;omega⟩
def fieldSlots (D : ℕ) (i : Fin 27) : Fin (tapes D):=
  if i.val=0 then cropSlots D 6 else if i.val=1 then base D 53
  else if i.val=2 then scalarPort D 18 else if i.val=3 then scalarPort D 14
  else ⟨58+Widths.tapes D+8+i.val,by have h:=i.isLt;unfold tapes;omega⟩
def metadata (D : ℕ):=RecoveryFocus.machine (metadataSlots D) Metadata.machine
def widths (D block : ℕ):=RecoveryFocus.machine (widthSlots D) (Widths.machine D block)
def crop (D : ℕ):=RecoveryFocus.machine (cropSlots D) SliceFrame.machine
def fields (D : ℕ):=RecoveryFocus.machine (fieldSlots D) AddressFields.machine
def machine (D block : ℕ):=Composition.machine
  (Composition.machine (Composition.machine (metadata D) (widths D block)) (crop D)) (fields D)
def input (D : ℕ) (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (address : List Bool) (i : Fin (tapes D)) : List Bool:=
  if h : i.val<19 then PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
    (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [] ⟨i.val,h⟩
  else if i.val=56 then frame (pcppInput r) else if i.val=57 then frame address else []
def heads (D : ℕ) (i : Fin (tapes D)):=if i.val=13 ∨ i.val=14 then 1 else 0
def budget (D block : ℕ) (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (padding index : ℕ):=
  Metadata.budget r (a.output r)+1+Widths.budget D block r.arity (a.output r).clauseBits+1+
  SliceFrame.budget (block*(r.arity+RepairSource.CloseoutLanguage.clauseWidth D r.arity+1))
    (r.arity+RepairSource.CloseoutLanguage.clauseWidth D r.arity+1)+1+
  AddressFields.budget r.arity (a.output r).clauseBits padding index

theorem base_injective (D : ℕ) : Function.Injective (base D):=by
  intro i j he;apply Fin.ext;exact congrArg (fun k : Fin (tapes D)=>k.val) he
theorem metadata_injective (D : ℕ) : Function.Injective (metadataSlots D):=by
  intro i j he;apply Fin.ext;exact congrArg (fun k : Fin (tapes D)=>k.val) he
theorem width_injective (D : ℕ) : Function.Injective (widthSlots D):=by
  intro i j he
  have h:=congrArg Fin.val he
  apply Fin.ext
  dsimp only [widthSlots,base] at h
  split_ifs at h <;>(try simp only [Fin.val_castAdd] at h) <;>omega
theorem width_upper (D : ℕ) (i : Fin (Widths.tapes D)) :
    (widthSlots D i).val<58+Widths.tapes D:=by
  have h:=i.isLt
  dsimp only [widthSlots,base]
  split_ifs <;>(try simp only [Fin.val_castAdd]) <;>omega
theorem scalar_high (D : ℕ) (i : Fin 22) (hi : 2 ≤ i.val) :
    58 ≤ (scalarPort D i).val:=by
  have h0 : i.val≠0:=by omega
  have h1 : i.val≠1:=by omega
  have hs : 2 ≤ (Widths.scalarSlots D i).val:=by
    simp only [Widths.scalarSlots,h0,h1,if_false,Fin.val_mk]
    omega
  unfold scalarPort
  simp only [widthSlots,show (Widths.scalarSlots D i).val≠0 by omega,
    show (Widths.scalarSlots D i).val≠1 by omega,if_false,Fin.val_mk]
  omega
theorem scalar_injective (D : ℕ) : Function.Injective (scalarPort D):=
  (width_injective D).comp (Widths.scalar_injective D)
theorem scalar_ne (D : ℕ) (i j : Fin 22) (hij : i≠j) :
    (scalarPort D i).val≠(scalarPort D j).val:=
  fun h=>hij (scalar_injective D (Fin.ext h))
theorem crop_injective (D : ℕ) : Function.Injective (cropSlots D):=by
  intro i j he
  have h:=congrArg Fin.val he
  have h8:=scalar_high D 8 (by decide)
  have h2:=scalar_high D 2 (by decide)
  have u8:=width_upper D (Widths.scalarSlots D 8)
  have u2:=width_upper D (Widths.scalarSlots D 2)
  have hn:=scalar_ne D 8 2 (by decide)
  change (scalarPort D 8).val<58+Widths.tapes D at u8
  change (scalarPort D 2).val<58+Widths.tapes D at u2
  apply Fin.ext
  dsimp only [cropSlots,base] at h
  split_ifs at h <;>(try simp only [Fin.val_castAdd] at h) <;>omega
theorem field_injective (D : ℕ) : Function.Injective (fieldSlots D):=by
  intro i j he
  have h:=congrArg Fin.val he
  have h18:=scalar_high D 18 (by decide)
  have h14:=scalar_high D 14 (by decide)
  have u18:=width_upper D (Widths.scalarSlots D 18)
  have u14:=width_upper D (Widths.scalarSlots D 14)
  have hn:=scalar_ne D 18 14 (by decide)
  have hc : (cropSlots D 6).val=58+Widths.tapes D+6:=rfl
  change (scalarPort D 18).val<58+Widths.tapes D at u18
  change (scalarPort D 14).val<58+Widths.tapes D at u14
  apply Fin.ext
  dsimp only [fieldSlots,base] at h
  split_ifs at h <;>(try simp only [Fin.val_castAdd] at h) <;>omega

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OccurrenceAddress
