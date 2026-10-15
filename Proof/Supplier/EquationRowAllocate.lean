import Proof.Supplier.EquationHeader
import Proof.Amplification.RecoveryScratchErase

/-! One actual capacity sweep prepares all fourteen C-zero scratch tapes
and the C+1 erase log. Existing source/output/count cursors are preserved. -/
namespace NearCubicWires.RepairOrdinary.EquationRowAllocate
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 16) : Fin 126 :=
  if h : j.val<14 then ⟨111+j.val,by omega⟩ else if j.val=14 then 60 else 125
theorem slots_injective : Function.Injective slots := by decide
noncomputable def machine := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 14)
def extra (C : ℕ) (i : Fin 15) := List.replicate (if i.val<14 then C else C+1) false
noncomputable def entry {s : ℕ} (ambient : Configuration 111 s) :=
  Composition.restart (TapeEmbedding.config (fun _ : Fin 15 => 0) (fun _ : Fin 15 => []) ambient) machine.start

theorem old_none (i : Fin 111) (hi : i≠60) :
    RecoveryFocus.pick slots (i.castAdd 15)=none := by
  have no : ¬∃ j,slots j=i.castAdd 15 := by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    have hival := i.isLt
    have hjval := j.isLt
    have h60 : i.val≠60 := fun h => hi (Fin.ext h)
    simp only [slots,Fin.val_castAdd] at hv
    split_ifs at hv <;> dsimp at hv <;> omega
  simp [RecoveryFocus.pick,no]

theorem allocate_run {s : ℕ} (ambient : Configuration 111 s) (C : ℕ)
    (hC : ambient.tapes 60=List.replicate C true) (hCH : ambient.heads 60=0) : ∃ actual,
    runFrom machine (2*C+4) (entry ambient)=some actual ∧
    (∀ i : Fin 111,actual.final.tapes (i.castAdd 15)=ambient.tapes i ∧
      actual.final.heads (i.castAdd 15)=ambient.heads i) ∧
    (∀ i : Fin 15,actual.final.tapes (i.natAdd 111)=extra C i ∧
      actual.final.heads (i.natAdd 111)=0) ∧ actual.steps=2*C+4 := by
  let before := TapeEmbedding.config (fun _ : Fin 15 => 0) (fun _ : Fin 15 => []) ambient
  obtain ⟨base,hb,bt,bh,bs⟩ := RecoveryScratchErase.erase_ready C 0 (fun _ : Fin 14 => [])
    (by intro i; simp)
  have hi : RecoveryFocus.config slots before.heads before.tapes
      (initialConfiguration (RecoveryScratchErase.resetMachine 14)
        (Fin.addCases (m := 15) (n := 1) (motive := fun _ => List Bool)
          (Fin.addCases (m := 14) (n := 1) (motive := fun _ => List Bool)
            (fun _ : Fin 14 => []) (fun _ : Fin 1 => List.replicate C true))
          (fun _ : Fin 1 => List.replicate 0 false)))=entry ambient := by
    apply WilliamsSourceCrop.focus_same
    · intro j; fin_cases j
      all_goals first | exact hCH | rfl
    · intro j; fin_cases j
      all_goals first | exact hC | rfl
  obtain ⟨actual,ha,hf,hs⟩ := RecoveryFocus.run_config slots slots_injective (RecoveryScratchErase.resetMachine 14)
    before.heads before.tapes _ _ base hb
  rw [hi] at ha
  have pick (j : Fin 16) : RecoveryFocus.pick slots (slots j)=some j :=
    RecoveryFocus.pick_slot slots slots_injective j
  have localT (j : Fin 16) : actual.final.tapes (slots j)=base.final.tapes j := by
    rw [hf]
    simp only [RecoveryFocus.config,pick]
  have localH (j : Fin 16) : actual.final.heads (slots j)=0 := by
    rw [hf]
    simpa only [RecoveryFocus.config,pick] using bh j
  refine ⟨actual,ha,?_,?_,hs.trans bs⟩
  · intro i
    by_cases hi : i=60
    · subst i
      constructor
      · change actual.final.tapes (slots 14)=_
        rw [localT,bt]
        exact hC.symm
      · exact (localH 14).trans hCH.symm
    · rw [hf]
      simp only [RecoveryFocus.config,old_none i hi]
      constructor
      · change (Fin.addCases (m := 111) (n := 15) (motive := fun _ => List Bool)
          ambient.tapes (fun _ => [])) (i.castAdd 15)=_
        rw [Fin.addCases_left]
      · change (Fin.addCases (m := 111) (n := 15) (motive := fun _ => ℕ)
          ambient.heads (fun _ => 0)) (i.castAdd 15)=_
        rw [Fin.addCases_left]
  · intro i
    fin_cases i
    · refine ⟨?_,localH 0⟩
      change actual.final.tapes (slots 0)=_
      rw [localT,bt]
      simp [extra, Fin.addCases]
    · refine ⟨?_,localH 1⟩
      change actual.final.tapes (slots 1)=_
      rw [localT,bt]
      simp [extra, Fin.addCases]
    · refine ⟨?_,localH 2⟩
      change actual.final.tapes (slots 2)=_
      rw [localT,bt]
      simp [extra, Fin.addCases]
    · refine ⟨?_,localH 3⟩
      change actual.final.tapes (slots 3)=_
      rw [localT,bt]
      simp [extra, Fin.addCases]
    · refine ⟨?_,localH 4⟩
      change actual.final.tapes (slots 4)=_
      rw [localT,bt]
      simp [extra, Fin.addCases]
    · refine ⟨?_,localH 5⟩
      change actual.final.tapes (slots 5)=_
      rw [localT,bt]
      simp [extra, Fin.addCases]
    · refine ⟨?_,localH 6⟩
      change actual.final.tapes (slots 6)=_
      rw [localT,bt]
      simp [extra, Fin.addCases]
    · refine ⟨?_,localH 7⟩
      change actual.final.tapes (slots 7)=_
      rw [localT,bt]
      simp [extra, Fin.addCases]
    · refine ⟨?_,localH 8⟩
      change actual.final.tapes (slots 8)=_
      rw [localT,bt]
      simp [extra, Fin.addCases]
    · refine ⟨?_,localH 9⟩
      change actual.final.tapes (slots 9)=_
      rw [localT,bt]
      simp [extra, Fin.addCases]
    · refine ⟨?_,localH 10⟩
      change actual.final.tapes (slots 10)=_
      rw [localT,bt]
      simp [extra, Fin.addCases]
    · refine ⟨?_,localH 11⟩
      change actual.final.tapes (slots 11)=_
      rw [localT,bt]
      simp [extra, Fin.addCases]
    · refine ⟨?_,localH 12⟩
      change actual.final.tapes (slots 12)=_
      rw [localT,bt]
      simp [extra, Fin.addCases]
    · refine ⟨?_,localH 13⟩
      change actual.final.tapes (slots 13)=_
      rw [localT,bt]
      simp [extra, Fin.addCases]
    · refine ⟨?_,localH 15⟩
      change actual.final.tapes (slots 15)=_
      rw [localT,bt]
      simp [extra, Fin.addCases]

end NearCubicWires.RepairOrdinary.EquationRowAllocate
