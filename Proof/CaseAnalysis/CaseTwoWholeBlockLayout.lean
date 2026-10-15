import Proof.CaseAnalysis.CaseTwoSourceBlockPorts
import Proof.CaseAnalysis.CaseTwoOccurrenceRun

/-! One original source block and one actual occurrence worker. Twenty-one
paid source fields are shared; every other occurrence tape is fresh. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.WholeBlock
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
def tapes (k D : ℕ):=SourceBlock.tapes source a k+Occurrence.tapes D a
def old (k D : ℕ) (j : Fin (SourceBlock.tapes source a k)) : Fin (tapes source a k D):=
  j.castAdd (Occurrence.tapes D a)
def port (k : ℕ) : Fin 21→Fin (SourceBlock.tapes source a k):=
  Fin.append (SourceBlock.cacheSlots source a k)
    ![SourceBlock.requestSlot source a k,SourceBlock.old source a k 2]
theorem port_injective (k : ℕ) : Function.Injective (port source a k):=by
  apply Fin.append_injective_iff.mpr
  refine ⟨SourceBlock.cache_injective source a k,?_,?_⟩
  · intro i j he
    fin_cases i <;>fin_cases j <;>try rfl
    · exact ((SourceBlock.request_away source a k 2) he).elim
    · exact ((SourceBlock.request_away source a k 2) he.symm).elim
  · intro i j
    fin_cases j
    · exact SourceBlock.cache_request source a k i
    · exact SourceBlock.cache_away source a k 2 i
def shared {t : ℕ} (j : Fin t):=j.val<19 ∨ j.val=56 ∨ j.val=57
instance sharedDecidable {t : ℕ} (j : Fin t) : Decidable (shared j):=
  inferInstanceAs (Decidable (j.val<19 ∨ j.val=56 ∨ j.val=57))
def key {t : ℕ} (j : Fin t) : Fin 21:=
  if h : j.val<19 then ⟨j.val,by omega⟩ else if j.val=56 then 19 else 20
theorem key_value {t : ℕ} (j : Fin t) : (key j).val=
    if j.val<19 then j.val else if j.val=56 then 19 else 20:=by
  unfold key
  split_ifs <;>rfl
theorem key_injective {t : ℕ} (i j : Fin t) (hi : shared i) (hj : shared j)
    (he : key i=key j) : i=j:=by
  have hv:=congrArg Fin.val he
  apply Fin.ext
  simp only [key_value] at hv
  unfold shared at hi hj
  split_ifs at hv <;>omega
def slots (k D : ℕ) (j : Fin (Occurrence.tapes D a)) : Fin (tapes source a k D):=
  if shared j then old source a k D (port source a k (key j))
  else j.natAdd (SourceBlock.tapes source a k)
theorem old_injective (k D : ℕ) : Function.Injective (old source a k D):=by
  intro i j he;apply Fin.ext;exact congrArg (fun x : Fin (tapes source a k D)=>x.val) he
theorem slots_injective (k D : ℕ) : Function.Injective (slots source a k D):=by
  intro i j he
  by_cases hi : shared i <;>by_cases hj : shared j
  · exact key_injective i j hi hj (port_injective source a k
      (old_injective source a k D (by simpa only [slots,if_pos hi,if_pos hj] using he)))
  · have hv:=congrArg Fin.val he
    have bound:=(port source a k (key i)).isLt
    simp only [slots,if_pos hi,if_neg hj,old,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · have hv:=congrArg Fin.val he
    have bound:=(port source a k (key j)).isLt
    simp only [slots,if_neg hi,if_pos hj,old,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · apply Fin.ext
    have hv:=congrArg Fin.val he
    simp only [slots,if_neg hi,if_neg hj,Fin.val_natAdd] at hv
    omega
def first (k D CH Cpad : ℕ) (code : List Bool):=
  RecoveryFocus.machine (old source a k D) (SourceBlock.machine source a k CH Cpad code)
def last (k D block : ℕ):=RecoveryFocus.machine (slots source a k D) (Occurrence.machine D block a)
def machine (k D block CH Cpad : ℕ) (code : List Bool):=
  Composition.machine (first source a k D CH Cpad code) (last source a k D block)
def input (k D : ℕ) (hierarchy descriptor address : List Bool) : Fin (tapes source a k D)→List Bool:=
  Fin.addCases (SourceBlock.input source a k hierarchy descriptor address) (fun _=>[])
def outputSlot (k D : ℕ):=slots source a k D (Occurrence.outputSlot D a)

theorem port_away (k : ℕ) (i : Fin 2) (j : Fin 21) :
    port source a k j≠SourceBlock.old source a k (i.castAdd 6):=by
  refine Fin.addCases (motive:=fun j=>port source a k j≠SourceBlock.old source a k (i.castAdd 6))
    (fun j : Fin 19=>?_) (fun j : Fin 2=>?_) j
  · rw [port,Fin.append_left]
    exact SourceBlock.cache_away source a k (i.castAdd 1) j
  · fin_cases j
    · exact SourceBlock.request_away source a k (i.castAdd 1)
    · intro he
      have hv:=congrArg Fin.val he
      have hi:=i.isLt
      change 2=i.val at hv
      omega
theorem slots_away (k D : ℕ) (i : Fin 2) :
    ∀ j,slots source a k D j≠old source a k D (SourceBlock.old source a k (i.castAdd 6)):=by
  intro j he
  by_cases hj : shared j
  · exact port_away source a k i (key j)
      (old_injective source a k D (by simpa only [slots,if_pos hj] using he))
  · have hv:=congrArg Fin.val he
    have bound:=(SourceBlock.old source a k (i.castAdd 6)).isLt
    simp only [slots,if_neg hj,old,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
theorem address_slot (k D : ℕ) :
    slots source a k D (Occurrence.old D a (OccurrenceAddress.base D 57))=
      old source a k D (SourceBlock.old source a k 2):=rfl

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.WholeBlock
