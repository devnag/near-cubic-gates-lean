import Proof.MachineModel.UWitnessLayout

/-! The m comparison and bounded choice copy consume the exact streaming
endpoint of the m-field read. Every unrelated cursor is retained. -/
namespace NearCubicWires.RepairOrdinary.UWitness
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mValue (w : ℕ) (witness : List Bool) := value (witness.take w)
def mFlag (w B : ℕ) (witness : List Bool) := decide (mValue w witness ≤ B)
def afterCompare (w B : ℕ) (witness : List Bool) : Store := fun i =>
  if i.val=9 then [mFlag w B witness] else if i.val=10 then List.replicate (2*w+1) false
  else afterField w B witness i
noncomputable def compareInput (w B : ℕ) (witness : List Bool) : Configuration 15 7 :=
  ⟨comparePhase.start,fieldHeads w,afterField w B witness⟩

theorem compare_run (w B : ℕ) (witness : List Bool) (hw : w ≤ witness.length) (hb : B < 2^w) :
    ∃ r,runFrom comparePhase (4*w+4) (compareInput w B witness)=some r ∧
      r.final.heads=fieldHeads w ∧ r.final.tapes=afterCompare w B witness ∧ r.steps ≤ 4*w+4 := by
  have hl : (witness.take w).length=w := by simp [List.length_take,Nat.min_eq_left hw]
  obtain ⟨base,hbase,ht,hh,hs⟩ := ClockBoundGuard.comparison_ready (witness.take w) (binary w B) (by simp [hl])
  rw [hl] at hbase hs
  obtain ⟨r,hr,hf,hrs⟩ := RecoveryFocus.run_config compareSlots compare_injective ClockBoundGuard.comparison
    (fieldHeads w) (afterField w B witness) (4*w+4) _ base hbase
  have hi := focus_config_eq compareSlots compare_injective
    (initialConfiguration ClockBoundGuard.comparison (ClockBoundGuard.comparisonInput (witness.take w) (binary w B)))
    (fieldHeads w) (afterField w B witness) (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,hrs.trans_le hs⟩
  · funext i
    fin_cases i <;> simp [hf,RecoveryFocus.config,compare_pick,hh,fieldHeads,bootHeads]
  · funext i
    fin_cases i <;> simp [hf,RecoveryFocus.config,compare_pick,ht,afterCompare,afterField,afterBoot,input,
      hl,binary_value _ _ hb,mFlag,mValue]

def readChoices (w B : ℕ) (witness : List Bool) := UWitnessChoices.consumed B (witness.drop w)
def choiceFlag (w B : ℕ) (witness : List Bool) := decide (B ≤ (witness.drop w).length)
def choiceHeads (w B : ℕ) (witness : List Bool) : Heads := fun i =>
  if i.val=0 then 2*w+2*readChoices w B witness else bootHeads i
def afterChoices (w B : ℕ) (witness : List Bool) (g : ℕ) : Store := fun i =>
  if i.val=4 then frame (binary w (readChoices w B witness+1))
  else if i.val=11 then [decide ((witness.drop w).length < B)]
  else if i.val=12 then UWitnessChoices.copied B (witness.drop w)
  else if i.val=13 then [choiceFlag w B witness]
  else if i.val=14 then List.replicate g false else afterCompare w B witness i
noncomputable def choiceInput (w B : ℕ) (witness : List Bool) :=
  RecoveryCalls.restarted choicePhase (fieldHeads w) (afterCompare w B witness)

theorem choice_run (w B : ℕ) (witness : List Bool) (hw : w ≤ witness.length) (hb : B+1 < 2^w) :
    ∃ g r,runFrom choicePhase (UWitnessChoices.budget w B) (choiceInput w B witness)=some r ∧
      r.final.heads=choiceHeads w B witness ∧ r.final.tapes=afterChoices w B witness g ∧
      r.steps ≤ UWitnessChoices.budget w B := by
  let pre := Streaming.marks (witness.take w)
  have hsource : pre++frame (witness.drop w)=frame witness := (UWitnessField.frame_split witness w).symm
  have hpre : pre.length=2*w := by simp [pre,Streaming.marks_length,List.length_take,Nat.min_eq_left hw]
  obtain ⟨g,base,hbase,ht,hh,hs,_⟩ := UWitnessChoices.prefix_run w B (2*w+1) pre (witness.drop w) hb (by omega)
  obtain ⟨r,hr,hf,hrs⟩ := RecoveryFocus.run_config choiceSlots choice_injective UWitnessChoices.machine
    (fieldHeads w) (afterCompare w B witness) (UWitnessChoices.budget w B) _ base hbase
  have hi := focus_config_eq choiceSlots choice_injective
    (UWitnessChoices.input w B (2*w+1) (pre++frame (witness.drop w)) pre.length)
    (fieldHeads w) (afterCompare w B witness)
    (by rw [hsource,hpre]; intro j; fin_cases j <;> rfl)
    (by rw [hsource,hpre]; intro j; fin_cases j <;> rfl)
  rw [hi] at hr
  refine ⟨g,r,hr,?_,?_,hrs.trans_le hs⟩
  · funext i
    fin_cases i <;> simp [hf,RecoveryFocus.config,choice_pick,hh,UWitnessChoices.finalHeads,
      hpre,choiceHeads,readChoices,fieldHeads,bootHeads]
  · funext i
    fin_cases i <;> simp [hf,RecoveryFocus.config,choice_pick,ht,UWitnessChoices.output,
      hsource,afterChoices,afterCompare,afterField,afterBoot,input,readChoices,choiceFlag]

end NearCubicWires.RepairOrdinary.UWitness
