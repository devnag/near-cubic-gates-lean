import Proof.Amplification.RecoveryOriginal
import Proof.Amplification.RecoveryRawViewEntryPosition

/-! A fresh scanner bank reuses the checked cold reader, sharing only the
retained original code/witness. Both final raw banks remain disjoint. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdScanner
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 100) : Fin 270 := if j.val<2 then ⟨j.val,by omega⟩ else ⟨j.val+170,by omega⟩
theorem slot_val (j : Fin 100) : (slots j).val=if j.val<2 then j.val else j.val+170 := by
  unfold slots
  split <;> rfl
theorem slots_injective : Function.Injective slots := by
  intro i j h
  have he : (slots i).val=(slots j).val := congrArg (fun k : Fin 270=>k.val) h
  apply Fin.ext
  rw [slot_val,slot_val] at he
  split at he <;> split at he <;> omega
def heads (h : Fin 172→Nat) : Fin 270→Nat :=
  Fin.addCases (m:=172) (n:=98) (motive:=fun _=>Nat) h (fun _=>0)
def tapes (a : Fin 172→List Bool) : Fin 270→List Bool :=
  Fin.addCases (m:=172) (n:=98) (motive:=fun _=>List Bool) a (fun _=>[])
noncomputable def program := RecoveryFocus.machine slots RecoveryColdView.coldProgram

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem initial_layout {s : Nat} (bits word : List Bool) (h : Fin 172→Nat) (a : Fin 172→List Bool)
    (hh : h 0=0 ∧ h 1=0) (ht : a 0=frame bits ∧ a 1=frame word) (q : Fin s) :
    RecoveryFocus.config slots (heads h) (tapes a) ⟨q,(fun _=>0),RecoveryColdView.input bits word⟩=
      (⟨q,heads h,tapes a⟩ : Configuration 270 s) := by
  apply focus_configuration slots slots_injective
  · rfl
  · intro j
    fin_cases j <;> first | exact hh.1.symm | exact hh.2.symm | rfl
  · intro j
    rw [RecoveryColdView.input_layout]
    fin_cases j <;> first | exact ht.1.symm | exact ht.2.symm | rfl
  · intro i _; rfl
  · intro i _; rfl

theorem low_other (i : Fin 172) (h0 : i≠0) (h1 : i≠1) : ∀ j,slots j≠i.castAdd 98 := by
  intro j he
  have hv : (slots j).val=i.val := congrArg (fun k : Fin 270=>k.val) he
  have hi := i.isLt
  have hi0 : i.val≠0 := by intro h; exact h0 (Fin.ext h)
  have hi1 : i.val≠1 := by intro h; exact h1 (Fin.ext h)
  rw [slot_val] at hv
  split at hv <;> omega

theorem retained {s : Nat} (h : Fin 172→Nat) (a : Fin 172→List Bool) (c : Configuration 100 s)
    (hh : c.heads 0=h 0 ∧ c.heads 1=h 1)
    (ht : c.tapes 0=a 0 ∧ c.tapes 1=a 1) :
    (fun i : Fin 172=>(RecoveryFocus.config slots (heads h) (tapes a) c).heads (i.castAdd 98))=h ∧
    (fun i : Fin 172=>(RecoveryFocus.config slots (heads h) (tapes a) c).tapes (i.castAdd 98))=a := by
  constructor
  · funext i
    by_cases hi0 : i=0
    · subst i
      change (RecoveryFocus.config slots (heads h) (tapes a) c).heads (slots 0)=_
      simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using hh.1
    · by_cases hi1 : i=1
      · subst i
        change (RecoveryFocus.config slots (heads h) (tapes a) c).heads (slots 1)=_
        simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using hh.2
      · have hn : ¬∃ j,slots j=i.castAdd 98 := by rintro ⟨j,hj⟩; exact low_other i hi0 hi1 j hj
        simp only [RecoveryFocus.config,RecoveryFocus.pick,hn,↓reduceDIte,heads,Fin.addCases_left]
  · funext i
    by_cases hi0 : i=0
    · subst i
      change (RecoveryFocus.config slots (heads h) (tapes a) c).tapes (slots 0)=_
      simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using ht.1
    · by_cases hi1 : i=1
      · subst i
        change (RecoveryFocus.config slots (heads h) (tapes a) c).tapes (slots 1)=_
        simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using ht.2
      · have hn : ¬∃ j,slots j=i.castAdd 98 := by rintro ⟨j,hj⟩; exact low_other i hi0 hi1 j hj
        simp only [RecoveryFocus.config,RecoveryFocus.pick,hn,↓reduceDIte,tapes,Fin.addCases_left]

end NearCubicWires.RepairOrdinary.RecoveryColdScanner
