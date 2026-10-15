import Proof.CaseAnalysis.CaseTwoXorRun
import Proof.CaseAnalysis.CaseTwoPreparedFrames

/-! Final five-port Case 2 boundary. Canonical conversion and hierarchy
framing run once, then the fixed family consumes those paid frames. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Execution
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
def foldTapes (k D copies : ℕ):=FixedFold.tapes (XorFamily.tapes source a k D) copies
def tapes (k D copies : ℕ):=140+foldTapes source a k D copies
def old (k D copies : ℕ) (j : Fin 140) : Fin (tapes source a k D copies):=
  j.castAdd (foldTapes source a k D copies)
def fields : Fin 3→Fin 140:=![138,132,2]
def slots (k D copies : ℕ) (j : Fin (foldTapes source a k D copies)) : Fin (tapes source a k D copies):=
  if h : j.val<3 then old source a k D copies (fields ⟨j.val,h⟩) else j.natAdd 140
theorem old_injective (k D copies : ℕ) : Function.Injective (old source a k D copies):=by
  intro i j he;exact Fin.ext (congrArg (fun x : Fin (tapes source a k D copies)=>x.val) he)
theorem slots_injective (k D copies : ℕ) : Function.Injective (slots source a k D copies):=by
  intro i j he
  by_cases hi : i.val<3 <;>by_cases hj : j.val<3
  · have hp : fields ⟨i.val,hi⟩=fields ⟨j.val,hj⟩:=old_injective source a k D copies
      (by simpa only [slots,dif_pos hi,dif_pos hj] using he)
    have hm:=(by decide : Function.Injective fields) hp
    exact Fin.ext (congrArg (fun x : Fin 3=>x.val) hm)
  · have hv:=congrArg Fin.val he
    have hb:=(fields ⟨i.val,hi⟩).isLt
    simp only [slots,dif_pos hi,dif_neg hj,old,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · have hv:=congrArg Fin.val he
    have hb:=(fields ⟨j.val,hj⟩).isLt
    simp only [slots,dif_neg hi,dif_pos hj,old,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · have hv:=congrArg Fin.val he
    apply Fin.ext
    simp only [slots,dif_neg hi,dif_neg hj,Fin.val_natAdd] at hv
    omega
def input (k D copies : ℕ) (hierarchy description address : List Bool) (R B : ℕ) :
    Fin (tapes source a k D copies)→List Bool:=
  Fin.addCases (PreparedFrames.input hierarchy description address R B) (fun _=>[])
def first (k D copies : ℕ):=RecoveryFocus.machine (old source a k D copies) PreparedFrames.machine
def last (k D copies CH Cpad : ℕ) (code : List Bool):=
  RecoveryFocus.machine (slots source a k D copies) (XorFamily.machine source a k D copies CH Cpad code)
def machine (k D copies CH Cpad : ℕ) (code : List Bool):=
  Composition.machine (first source a k D copies) (last source a k D copies CH Cpad code)
def outputSlot (k D copies : ℕ):=slots source a k D copies
  (FixedFold.low (XorFamily.tapes source a k D) copies 3)
theorem field_slot (k D copies : ℕ) (i : Fin 3) :
    slots source a k D copies (FixedFold.low (XorFamily.tapes source a k D) copies (i.castAdd 1))=
      old source a k D copies (fields i):=by
  unfold slots
  have hi : (FixedFold.low (XorFamily.tapes source a k D) copies (i.castAdd 1)).val<3:=i.isLt
  rw [dif_pos hi]
  rfl
theorem old_outside (k D copies : ℕ) (i : Fin 2) :
    ∀ j,slots source a k D copies j≠old source a k D copies (i.castAdd 138):=by
  intro j he
  by_cases hj : j.val<3
  · have hf : fields ⟨j.val,hj⟩=i.castAdd 138:=old_injective source a k D copies
      (by simpa only [slots,dif_pos hj] using he)
    have forbidden (k : Fin 3) : fields k≠i.castAdd 138:=by
      intro h
      have hv:=congrArg Fin.val h
      have hi:=i.isLt
      fin_cases k <;>simp [fields] at hv <;>omega
    exact forbidden _ hf
  · have hv:=congrArg Fin.val he
    have hi:=i.isLt
    simp only [slots,dif_neg hj,old,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Execution
