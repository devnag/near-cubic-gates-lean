import Proof.MachineModel.UWitnessField
import Proof.MachineModel.UWitnessChoiceReady

/-! Fixed local witness layout, with source0, raw width1, normalized B2,
blank scratch3..14. The source cursor stays continuous between phases. -/
namespace NearCubicWires.RepairOrdinary.UWitness
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Store := Fin 15 → List Bool
abbrev Heads := Fin 15 → ℕ

theorem focus_config_eq {t u s : ℕ} (slot : Fin t → Fin u) (_hi : Function.Injective slot)
    (c : Configuration t s) (ambientHeads : Fin u → ℕ) (ambientTapes : Fin u → List Bool)
    (hh : ∀ j,ambientHeads (slot j)=c.heads j) (ht : ∀ j,ambientTapes (slot j)=c.tapes j) :
    RecoveryFocus.config slot ambientHeads ambientTapes c=⟨c.control,ambientHeads,ambientTapes⟩ := by
  apply configuration_ext
  · rfl
  · funext i
    cases hp : RecoveryFocus.pick slot i with
    | none => simp [RecoveryFocus.config,hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slot hp
      simp only [RecoveryFocus.config,hp]
      exact (hh j).symm.trans (congrArg ambientHeads he)
  · exact install_existing slot ambientTapes c.tapes ht

theorem pick_other {t u : ℕ} (slot : Fin t → Fin u) (i : Fin u)
    (hi : ∀ j,slot j≠i) : RecoveryFocus.pick slot i=none := by
  have hn : ¬∃ j,slot j=i := by simpa using hi
  simp [RecoveryFocus.pick,hn]

def bootSlots : Fin 6 → Fin 15 := ![1,3,4,5,6,7]
theorem boot_injective : Function.Injective bootSlots := by decide
theorem boot_pick (i : Fin 15) : RecoveryFocus.pick bootSlots i=
    if i.val=1 then some 0 else if i.val=3 then some 1 else if i.val=4 then some 2 else if i.val=5 then some 3 else if i.val=6 then some 4 else if i.val=7 then some 5 else none := by
  fin_cases i
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact RecoveryFocus.pick_slot _ boot_injective 0
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact RecoveryFocus.pick_slot _ boot_injective 1
  · exact RecoveryFocus.pick_slot _ boot_injective 2
  · exact RecoveryFocus.pick_slot _ boot_injective 3
  · exact RecoveryFocus.pick_slot _ boot_injective 4
  · exact RecoveryFocus.pick_slot _ boot_injective 5
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)

def fieldSlots : Fin 3 → Fin 15 := ![0,8,7]
theorem field_injective : Function.Injective fieldSlots := by decide
theorem field_pick (i : Fin 15) : RecoveryFocus.pick fieldSlots i=
    if i.val=0 then some 0 else if i.val=8 then some 1 else if i.val=7 then some 2 else none := by
  fin_cases i
  · exact RecoveryFocus.pick_slot _ field_injective 0
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact RecoveryFocus.pick_slot _ field_injective 2
  · exact RecoveryFocus.pick_slot _ field_injective 1
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)

def compareSlots : Fin 4 → Fin 15 := ![8,2,9,10]
theorem compare_injective : Function.Injective compareSlots := by decide
theorem compare_pick (i : Fin 15) : RecoveryFocus.pick compareSlots i=
    if i.val=8 then some 0 else if i.val=2 then some 1 else if i.val=9 then some 2 else if i.val=10 then some 3 else none := by
  fin_cases i
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact RecoveryFocus.pick_slot _ compare_injective 1
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact RecoveryFocus.pick_slot _ compare_injective 0
  · exact RecoveryFocus.pick_slot _ compare_injective 2
  · exact RecoveryFocus.pick_slot _ compare_injective 3
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)

def choiceSlots : Fin 8 → Fin 15 := ![4,2,11,6,0,12,13,14]
theorem choice_injective : Function.Injective choiceSlots := by decide
theorem choice_pick (i : Fin 15) : RecoveryFocus.pick choiceSlots i=
    if i.val=4 then some 0 else if i.val=2 then some 1 else if i.val=11 then some 2 else if i.val=6 then some 3 else if i.val=0 then some 4 else if i.val=12 then some 5 else if i.val=13 then some 6 else if i.val=14 then some 7 else none := by
  fin_cases i
  · exact RecoveryFocus.pick_slot _ choice_injective 4
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact RecoveryFocus.pick_slot _ choice_injective 1
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact RecoveryFocus.pick_slot _ choice_injective 0
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact RecoveryFocus.pick_slot _ choice_injective 3
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact pick_other _ _ (by intro j; fin_cases j <;> decide)
  · exact RecoveryFocus.pick_slot _ choice_injective 2
  · exact RecoveryFocus.pick_slot _ choice_injective 5
  · exact RecoveryFocus.pick_slot _ choice_injective 6
  · exact RecoveryFocus.pick_slot _ choice_injective 7

noncomputable def bootPhase := RecoveryFocus.machine bootSlots UWitnessBootstrap.machine
noncomputable def fieldPhase := RecoveryFocus.machine fieldSlots RepairSource.VerifierDecoding.FieldMachine.machine
noncomputable def comparePhase := RecoveryFocus.machine compareSlots ClockBoundGuard.comparison
noncomputable def choicePhase := RecoveryFocus.machine choiceSlots UWitnessChoices.machine

def input (w B : ℕ) (witness : List Bool) : Store := fun i =>
  if i.val=0 then frame witness else if i.val=1 then List.replicate w true
  else if i.val=2 then frame (binary w B) else []
def bootHeads : Heads := fun i => if i.val=7 then 1 else 0
def afterBoot (w B : ℕ) (witness : List Bool) : Store := fun i =>
  if i.val=3 then [false] else if i.val=4 then frame (binary w 0)
  else if i.val=5 then [true] else if i.val=6 then List.replicate (2*w+1) false
  else if i.val=7 then RepairSource.VerifierDecoding.CompareMachine.word w else input w B witness i

def fieldHeads (w : ℕ) : Heads := fun i => if i.val=0 then 2*w else bootHeads i
def afterField (w B : ℕ) (witness : List Bool) : Store := fun i =>
  if i.val=8 then frame (witness.take w) else afterBoot w B witness i

theorem boot_run (w B : ℕ) (witness : List Bool) :
    ∃ r,run bootPhase (8*w+10) (input w B witness)=some r ∧
      r.final.tapes=afterBoot w B witness ∧ r.final.heads=bootHeads ∧ r.steps ≤ 8*w+10 := by
  obtain ⟨base,hb,ht,hh,hs⟩ := UWitnessBootstrap.bootstrap_run w
  obtain ⟨r,hr,hf,hrs⟩ := RecoveryFocus.run_config bootSlots boot_injective UWitnessBootstrap.machine
    (fun _ => 0) (input w B witness) (8*w+10) _ base hb
  have he := focus_config_eq bootSlots boot_injective
    (initialConfiguration UWitnessBootstrap.machine (UWitnessBootstrap.input w)) (fun _ => 0) (input w B witness)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [he] at hr
  refine ⟨r,hr,?_,?_,hrs.trans_le hs⟩
  · funext i
    fin_cases i <;> simp [hf,RecoveryFocus.config,boot_pick,ht,afterBoot,UWitnessBootstrap.output,input]
  · funext i
    fin_cases i <;> simp [hf,RecoveryFocus.config,boot_pick,hh,bootHeads,UWitnessBootstrap.heads]

noncomputable def fieldInput (w B : ℕ) (witness : List Bool) : Configuration 15 6 :=
  ⟨fieldPhase.start,bootHeads,afterBoot w B witness⟩

theorem field_run (w B : ℕ) (witness : List Bool) :
    ∃ r,runFrom fieldPhase (4*w+2) (fieldInput w B witness)=some r ∧
      r.final.control=(if w ≤ witness.length then 4 else 5) ∧
      r.final.tapes 0=frame witness ∧ r.final.tapes 1=List.replicate w true ∧
      r.final.tapes 2=frame (binary w B) ∧ r.final.tapes 13=[] ∧
      (w ≤ witness.length → r.final.heads=fieldHeads w ∧ r.final.tapes=afterField w B witness) ∧
      r.steps ≤ 4*w+2 := by
  obtain ⟨base,hb,hbf,hbs⟩ := UWitnessField.read_run w witness
  obtain ⟨r,hr,hf,hrs⟩ := RecoveryFocus.run_config fieldSlots field_injective
    RepairSource.VerifierDecoding.FieldMachine.machine bootHeads (afterBoot w B witness) (4*w+2) _ base hb
  have hi := focus_config_eq fieldSlots field_injective (UWitnessField.input w witness)
    bootHeads (afterBoot w B witness) (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,?_,?_,?_,?_,hrs.trans_le hbs⟩
  · by_cases hw : w ≤ witness.length <;>
      simp [hf,hbf,hw,UWitnessField.accepted,UWitnessField.rejected,RecoveryFocus.config,
        RepairSource.VerifierDecoding.FieldMachine.finished,RepairSource.VerifierDecoding.FieldMachine.scan]
  · by_cases hw : w ≤ witness.length <;>
      simp [hf,hbf,hw,UWitnessField.accepted,UWitnessField.rejected,RecoveryFocus.config,field_pick,
        RepairSource.VerifierDecoding.FieldMachine.finished,RepairSource.VerifierDecoding.FieldMachine.scan]
  · simp [hf,RecoveryFocus.config,field_pick,afterBoot,input]
  · simp [hf,RecoveryFocus.config,field_pick,afterBoot,input]
  · simp [hf,RecoveryFocus.config,field_pick,afterBoot,input]
  · intro hw
    constructor
    · funext i
      fin_cases i <;> simp [hf,hbf,hw,UWitnessField.accepted,RecoveryFocus.config,field_pick,
        RepairSource.VerifierDecoding.FieldMachine.finished,fieldHeads,bootHeads]
    · funext i
      fin_cases i <;> simp [hf,hbf,hw,UWitnessField.accepted,RecoveryFocus.config,field_pick,
        RepairSource.VerifierDecoding.FieldMachine.finished,afterField,afterBoot,input]

end NearCubicWires.RepairOrdinary.UWitness
