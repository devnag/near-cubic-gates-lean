import Proof.Amplification.RecoveryTseitinNativeReferences
import Proof.PCP.PCPPNativeNodeRead
import Proof.PCP.PCPPNativeTemplateRaw

/-! Read the actual original node descriptor alongside the physical arity
and node counter. The source cursor and native fields are retained for the
subsequent finite dispatch and ordinary reference producer. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary RepairRepresentation RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def readSlots (j : Fin 31) : Fin 1099 := ⟨1062+j.val,by have hj:=j.isLt; omega⟩
theorem read_injective : Function.Injective readSlots := by
  intro i j he
  have h:=congrArg Fin.val he
  apply Fin.ext
  dsimp only [readSlots] at h
  omega
def input (arity index : Nat) (word : List Bool) (i : Fin 1099) : List Bool :=
  if i=1062 then word else if h : i.val<1062 then RecoveryTseitinReferences.coldInput arity index 0 0 ⟨i.val,h⟩ else []
def heads (pos : Nat) (i : Fin 1099) : Nat := if i=1062 then pos else 0
noncomputable def readMachine := RecoveryFocus.machine readSlots PCPPNativeNodeRead.machine
def argSlots (right : Bool) : Fin 5→Fin 1099 :=
  if right then ![1092,3,1096,1097,1098] else ![1082,2,1093,1094,1095]
theorem arg_injective (right : Bool) : Function.Injective (argSlots right) := by cases right <;> decide

theorem read_other (i : Fin 1099) (hi : i.val < 1062 ∨ 1093 ≤ i.val) : ∀ j,readSlots j≠i := by
  intro j he
  have h:=congrArg Fin.val he
  have hj:=j.isLt
  dsimp only [readSlots] at h
  omega

theorem read_run (arity index : Nat) (pre tail : List Bool) (tag a b : Nat) :
    ∃ r,runFrom readMachine (PCPPNativeNodeRead.budget tag a b)
      ⟨readMachine.start,heads pre.length,input arity index (PCPPNativeNodeRead.source pre tail tag a b)⟩=some r ∧
      r.steps≤PCPPNativeNodeRead.budget tag a b ∧
      r.final.tapes 1062=PCPPNativeNodeRead.source pre tail tag a b ∧
      r.final.heads 1062=pre.length+(natWord tag).length+(natWord a).length+(natWord b).length ∧
      (∀ i : Fin 3,r.final.tapes (readSlots (PCPPNativeNodeRead.outputSlot i))=UnaryTemplate.tape (![tag,a,b] i) ∧
        r.final.heads (readSlots (PCPPNativeNodeRead.outputSlot i))=1) ∧
      (∀ i,i.val < 1062 ∨ 1093 ≤ i.val →
        r.final.tapes i=input arity index (PCPPNativeNodeRead.source pre tail tag a b) i ∧
        r.final.heads i=heads pre.length i) := by
  obtain ⟨base,hb,bs,b0,bh,bt,bth⟩:=PCPPNativeNodeRead.cold_run pre tail tag a b
  have hn (j : Fin 31) (hj : j≠0) : readSlots j≠1062 := by
    intro he
    have hv:=congrArg Fin.val he
    have hjv : j.val≠0 := by intro he; exact hj (Fin.ext he)
    dsimp only [readSlots] at hv
    omega
  obtain ⟨r,hr,_rc,rs,rh,rt,ro⟩:=RecoveryFocus.dock readSlots read_injective
    PCPPNativeNodeRead.machine _ (heads pre.length)
    (input arity index (PCPPNativeNodeRead.source pre tail tag a b)) _
    (by
      intro j
      by_cases hj : j=0
      · subst j; rfl
      simp only [heads,if_neg (hn j hj),PCPPNativeNodeRead.entry,if_neg hj])
    (by
      intro j
      by_cases hj : j=0
      · subst j; rfl
      have hv : ¬(readSlots j).val<1062 := by dsimp only [readSlots]; omega
      simp only [input,if_neg (hn j hj),dif_neg hv,PCPPNativeNodeRead.entry,if_neg hj]) base hb
  refine ⟨r,hr,rs.le.trans bs,(rt 0).trans b0,(rh 0).trans bh,?_,?_⟩
  · intro i
    exact ⟨(rt (PCPPNativeNodeRead.outputSlot i)).trans (bt i),
      (rh (PCPPNativeNodeRead.outputSlot i)).trans (bth i)⟩
  · intro i hi
    have h:=ro i (read_other i hi)
    exact ⟨h.2,h.1⟩

end NearCubicWires.RepairSource.RecoveryTseitinNative
