import Proof.PCP.PCPPNativeSumReusable
import Proof.PCP.PCPPNativeLiteralAppend
import Proof.PCP.PCPPNativeClauseNodes

/-! The compact clause emitter retains its actual raw references and two
clause counters while sharing one reusable native-field printing bank. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseBank
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawSlots (j : Fin 7) : Fin 29 := ⟨if j.val<2 then j.val else j.val+22,by have h:=j.isLt; split_ifs <;> omega⟩
theorem raw_injective : Function.Injective rawSlots := by
  intro i j h
  apply Fin.ext
  have hv:=congrArg Fin.val h
  dsimp [rawSlots] at hv
  split_ifs at hv <;> omega
theorem raw_range (j : Fin 7) : (rawSlots j).val<2 ∨ 24 ≤ (rawSlots j).val := by
  dsimp [rawSlots]
  split_ifs <;> omega

def data (values : Fin 7→ℕ) (C : ℕ) (out : List Bool) (i : Fin 29) : List Bool :=
  if i=0 then List.replicate (values 0) true else if i=1 then List.replicate (values 1) true
  else if i=20 then out else if i=22 then List.replicate C true
  else if i=23 then List.replicate (C+1) false
  else if h : 24 ≤ i.val then List.replicate (values ⟨i.val-22,by omega⟩) true
  else List.replicate C false
def heads (out : List Bool) (i : Fin 29) : ℕ := if i=20 then out.length else 0
theorem raw_data (values : Fin 7→ℕ) (C : ℕ) (out : List Bool) (j : Fin 7) :
    data values C out (rawSlots j)=List.replicate (values j) true := by
  fin_cases j <;> simp [data,rawSlots]
theorem raw_heads (out : List Bool) (j : Fin 7) : heads out (rawSlots j)=0 := by
  have h:=raw_range j
  simp [heads,show rawSlots j≠20 by intro he; have :=congrArg Fin.val he; omega]

def sumSlots (left right : Fin 7) (j : Fin 24) : Fin 29 :=
  if j=0 then rawSlots left else if j=1 then rawSlots right else j.castAdd 5
theorem sum_injective (left right : Fin 7) (hne : left≠right) : Function.Injective (sumSlots left right) := by
  intro i j he
  by_cases hi0 : i=0
  · subst i
    by_cases hj0 : j=0
    · exact hj0.symm
    · by_cases hj1 : j=1
      · subst j
        exact False.elim (hne (raw_injective (by simpa [sumSlots] using he)))
      · have hraw:=raw_range left
        have hj:=j.isLt
        have hv:=congrArg Fin.val he
        simp [sumSlots,hj0,hj1] at hv
        have hjv : j.val≠0 ∧ j.val≠1 := ⟨fun h=>hj0 (Fin.ext h),fun h=>hj1 (Fin.ext h)⟩
        omega
  · by_cases hi1 : i=1
    · subst i
      by_cases hj0 : j=0
      · subst j
        exact False.elim (hne (raw_injective (by simpa [sumSlots] using he.symm)))
      · by_cases hj1 : j=1
        · exact hj1.symm
        · have hraw:=raw_range right
          have hj:=j.isLt
          have hv:=congrArg Fin.val he
          simp [sumSlots,hj0,hj1] at hv
          have hjv : j.val≠0 ∧ j.val≠1 := ⟨fun h=>hj0 (Fin.ext h),fun h=>hj1 (Fin.ext h)⟩
          omega
    · have hiv : i.val≠0 ∧ i.val≠1 := ⟨fun h=>hi0 (Fin.ext h),fun h=>hi1 (Fin.ext h)⟩
      have hi:=i.isLt
      have hv:=congrArg Fin.val he
      by_cases hj0 : j=0
      · subst j
        have hr:=raw_range left
        simp [sumSlots,hi0,hi1] at hv
        omega
      · by_cases hj1 : j=1
        · subst j
          have hr:=raw_range right
          simp [sumSlots,hi0,hi1] at hv
          omega
        · exact Fin.ext (by simpa [sumSlots,hi0,hi1,hj0,hj1] using hv)

theorem sum_input (left right : Fin 7) (values : Fin 7→ℕ) (C : ℕ) (out : List Bool) (j : Fin 24) :
    heads out (sumSlots left right j)=PCPPNativeSumReusable.heads out j ∧
      data values C out (sumSlots left right j)=PCPPNativeSumReusable.data (values left) (values right) C out j := by
  fin_cases j
  · exact ⟨raw_heads out left,raw_data values C out left⟩
  · exact ⟨raw_heads out right,raw_data values C out right⟩
  all_goals simp [sumSlots,heads,data,PCPPNativeSumReusable.heads,PCPPNativeSumReusable.data]

noncomputable def sumMachine (left right : Fin 7) := RecoveryFocus.machine (sumSlots left right) PCPPNativeSumReusable.machine
def entry {s : ℕ} (p : Machine 29 s) (values : Fin 7→ℕ) (C : ℕ) (out : List Bool) :=
  (⟨p.start,heads out,data values C out⟩ : Configuration 29 s)
def AppendRun {s : ℕ} (p : Machine 29 s) (fuel : ℕ) (values : Fin 7→ℕ) (C : ℕ)
    (out bits : List Bool) : Prop :=
  ∃ r,runFrom p fuel (entry p values C out)=some r ∧ r.steps ≤ fuel ∧
    r.final.heads=heads (out++bits) ∧ r.final.tapes=data values C (out++bits)

end NearCubicWires.RepairOrdinary.PCPPNativeClauseBank
