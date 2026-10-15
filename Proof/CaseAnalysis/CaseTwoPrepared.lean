import Proof.CaseAnalysis.CaseTwoAllocation
import Proof.CaseAnalysis.CaseTwoLoad

/-! Three bounded physical copies load the original description, fixed tag
width and produced field width into the allocated traversal bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Cold
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def afterDesc (C : ℕ) (description : List Bool) (A : Fin 135→List Bool):=
  Function.update (longData C A) 60 (ZeroPadding.pad C description)
def afterTag (C : ℕ) (description : List Bool) (A : Fin 135→List Bool):=
  Function.update (afterDesc C description A) 63 (ZeroPadding.pad C (List.replicate 6 true))
def prepared (R B C : ℕ) (description : List Bool) (A : Fin 135→List Bool):=
  Function.update (afterTag C description A) 88 (ZeroPadding.pad C (List.replicate (R+B+1) true))
noncomputable def descProgram:=RecoveryFocus.machine descSlots RecoveryBoundedTapeCopy.machine
noncomputable def tagProgram:=RecoveryFocus.machine tagSlots RecoveryBoundedTapeCopy.machine
noncomputable def fieldProgram:=RecoveryFocus.machine fieldSlots RecoveryBoundedTapeCopy.machine
noncomputable def loadsProgram:=Composition.machine (Composition.machine descProgram tagProgram) fieldProgram
noncomputable def prepareProgram:=Composition.machine allocationProgram loadsProgram
def loadsBudget (C : ℕ):=(2*C+4)+1+(2*C+4)+1+(2*C+4)
def prepareBudget (C : ℕ):=allocationBudget C+1+loadsBudget C

theorem long_old (C : ℕ) (A : Fin 135→List Bool) (i : Fin 135) (hi : i.val<60) : longData C A i=A i:=by
  have h86 : i≠86:=by intro he;subst i;contradiction
  have h134 : i≠134:=by intro he;subst i;contradiction
  simp only [longData,Function.update_of_ne h134,Function.update_of_ne h86,small_old C A i hi]
theorem long_work (C : ℕ) (A : Fin 135→List Bool) (j : Fin 25) :
    longData C A (smallWork j)=List.replicate C false:=by
  have h86 : smallWork j≠86:=by fin_cases j <;> decide
  have h134 : smallWork j≠134:=by fin_cases j <;> decide
  simp only [longData,Function.update_of_ne h134,Function.update_of_ne h86,small_work]
theorem long_log (C : ℕ) (A : Fin 135→List Bool) : longData C A 84=List.replicate (C+1) false:=by
  simp [longData,smallData]

theorem desc_input (hierarchy description address : List Bool) (R B C : ℕ) (A : Fin 135→List Bool)
    (h : Funded hierarchy description address R B C A) (j : Fin 4) :
    longData C A (descSlots j)=CloseoutRowsMetadataCopy.input description C j:=by
  fin_cases j
  · exact (long_old C A 1 (by decide)).trans h.description
  · exact long_work C A 0
  · exact (long_old C A 17 (by decide)).trans h.capacity
  · exact long_log C A
theorem tag_input (hierarchy description address : List Bool) (R B C : ℕ) (A : Fin 135→List Bool)
    (h : Funded hierarchy description address R B C A) (j : Fin 4) :
    afterDesc C description A (tagSlots j)=CloseoutRowsMetadataCopy.input (List.replicate 6 true) C j:=by
  rw [afterDesc,Function.update_of_ne (by fin_cases j <;> decide)]
  fin_cases j
  · exact (long_old C A 58 (by decide)).trans h.six
  · exact long_work C A 3
  · exact (long_old C A 17 (by decide)).trans h.capacity
  · exact long_log C A
theorem field_input (hierarchy description address : List Bool) (R B C : ℕ) (A : Fin 135→List Bool)
    (h : Funded hierarchy description address R B C A) (j : Fin 4) :
    afterTag C description A (fieldSlots j)=CloseoutRowsMetadataCopy.input (List.replicate (R+B+1) true) C j:=by
  rw [afterTag,Function.update_of_ne (by fin_cases j <;> decide),
    afterDesc,Function.update_of_ne (by fin_cases j <;> decide)]
  fin_cases j
  · exact (long_old C A 32 (by decide)).trans h.field
  · exact long_work C A 24
  · exact (long_old C A 17 (by decide)).trans h.capacity
  · exact long_log C A

theorem loads_ready (hierarchy description address : List Bool) (R B C : ℕ) (A : Fin 135→List Bool)
    (h : Funded hierarchy description address R B C A)
    (hd : description.length≤C) (h6 : 6≤C) (hf : R+B+1≤C) :
    ClockJoin.ReadyRun loadsProgram (loadsBudget C) (longData C A) (prepared R B C description A):=by
  have d:=load_ready descSlots (by decide) C description (longData C A) hd (desc_input hierarchy description address R B C A h)
  have t:=load_ready tagSlots (by decide) C (List.replicate 6 true) (afterDesc C description A)
    (by simpa only [List.length_replicate] using h6) (tag_input hierarchy description address R B C A h)
  have f:=load_ready fieldSlots (by decide) C (List.replicate (R+B+1) true) (afterTag C description A)
    (by simpa only [List.length_replicate] using hf) (field_input hierarchy description address R B C A h)
  exact ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ d t) f

theorem prepare_ready (hierarchy description address : List Bool) (R B C : ℕ) (A : Fin 135→List Bool)
    (h : Funded hierarchy description address R B C A)
    (hd : description.length≤C) (h6 : 6≤C) (hf : R+B+1≤C) :
    ClockJoin.ReadyRun prepareProgram (prepareBudget C) A (prepared R B C description A):=
  ClockJoin.join _ _ _ _ _ _ _ (allocation_ready hierarchy description address R B C A h)
    (loads_ready hierarchy description address R B C A h hd h6 hf)

theorem prepared_old (R B C : ℕ) (description : List Bool) (A : Fin 135→List Bool)
    (i : Fin 135) (hi : i.val<60) : prepared R B C description A i=A i:=by
  have h60 : i≠60:=by intro he;subst i;contradiction
  have h63 : i≠63:=by intro he;subst i;contradiction
  have h88 : i≠88:=by intro he;subst i;contradiction
  simp only [prepared,afterTag,afterDesc,Function.update_of_ne h88,Function.update_of_ne h63,
    Function.update_of_ne h60,long_old C A i hi]

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Cold
