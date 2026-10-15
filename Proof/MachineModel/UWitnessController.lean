import Proof.MachineModel.UWitnessPhases

/-! One controller enforces the complete m field and m<=B before entering
the bounded choice copier. Its success predicate concerns only the consumed
prefix, leaving claimed scans and all later witness bits unread. -/
namespace NearCubicWires.RepairOrdinary.UWitness
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 4 → ℕ := ![14,6,7,Fintype.card (RecoveryCalls.Control UWitnessChoices.sizes)+2]
noncomputable def programs : (j : Fin 4) → Machine 15 (sizes j)
  | ⟨0,_⟩ => bootPhase
  | ⟨1,_⟩ => fieldPhase
  | ⟨2,_⟩ => comparePhase
  | ⟨3,_⟩ => choicePhase
  | ⟨n+4,h⟩ => False.elim (by omega)
def next (j : Fin 4) (q : Fin (sizes j)) (scan : Fin 15 → Bool) : Option (Fin 4) :=
  if j.val=0 then some 1 else if j.val=1 then if q.val=4 then some 2 else none
  else if j.val=2 then if scan 9 then some 3 else none else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def budget (w B : ℕ) := 128*(B+1)*(w+1)
def Valid (w B : ℕ) (witness : List Bool) : Prop :=
  w ≤ witness.length ∧ mValue w witness ≤ B ∧ w+B ≤ witness.length
def successHeads (w B : ℕ) : Heads := fun i => if i.val=0 then 2*(w+B) else bootHeads i
def Outcome {s : ℕ} (w B : ℕ) (witness : List Bool) (c : Configuration 15 s) : Prop :=
  c.tapes 0=frame witness ∧ c.tapes 1=List.replicate w true ∧ c.tapes 2=frame (binary w B) ∧
  (c.scanned 13=true ↔ Valid w B witness) ∧
  (c.scanned 13=true → c.heads=successHeads w B ∧
    c.tapes 8=frame (binary w (mValue w witness)) ∧
    c.tapes 12=frame ((witness.drop w).take B) ∧
    c.tapes 7=RepairSource.VerifierDecoding.CompareMachine.word w)

theorem rejected_outcome {s : ℕ} (w B : ℕ) (witness : List Bool) (c : Configuration 15 s)
    (h0 : c.tapes 0=frame witness) (h1 : c.tapes 1=List.replicate w true)
    (h2 : c.tapes 2=frame (binary w B)) (h13 : c.tapes 13=[])
    (hbad : ¬Valid w B witness) : Outcome w B witness c := by
  have hf : c.scanned 13=false := by simp [Configuration.scanned,h13,readTapeBit]
  exact ⟨h0,h1,h2,by simp [hf,hbad],by simp [hf]⟩

theorem choice_outcome {s : ℕ} (w B : ℕ) (witness : List Bool) (g : ℕ) (c : Configuration 15 s)
    (hw : w ≤ witness.length) (hm : mValue w witness ≤ B)
    (hh : c.heads=choiceHeads w B witness) (ht : c.tapes=afterChoices w B witness g) :
    Outcome w B witness c := by
  have hflag : c.scanned 13=choiceFlag w B witness := by
    simp [Configuration.scanned,ht,hh,choiceHeads,bootHeads,afterChoices,readTapeBit]
  have hiff : choiceFlag w B witness=true ↔ Valid w B witness := by
    simp only [choiceFlag,decide_eq_true_eq,List.length_drop,Valid]
    omega
  refine ⟨by simp [ht,afterChoices,afterCompare,afterField,afterBoot,input],
    by simp [ht,afterChoices,afterCompare,afterField,afterBoot,input],
    by simp [ht,afterChoices,afterCompare,afterField,afterBoot,input],by rw [hflag]; exact hiff,?_⟩
  intro h
  have hc : B ≤ (witness.drop w).length := by simpa [hflag,choiceFlag] using h
  have hread : readChoices w B witness=B := Nat.min_eq_left hc
  have hlen : (witness.take w).length=w := by simp [List.length_take,Nat.min_eq_left hw]
  have hmWord : witness.take w=binary w (mValue w witness) := by
    simpa [hlen,mValue] using (BoundedCounter.binary_of_value (witness.take w)).symm
  refine ⟨?_,?_,?_,?_⟩
  · rw [hh]
    funext i
    simp only [choiceHeads,successHeads,hread]
    split_ifs <;> omega
  · simp only [ht,afterChoices,afterCompare,afterField]
    simpa using congrArg frame hmWord
  · rw [ht]
    change UWitnessChoices.copied B (witness.drop w)=frame ((witness.drop w).take B)
    exact if_pos hc
  · simp [ht,afterChoices,afterCompare,afterField,afterBoot]

theorem choice_tail (w B : ℕ) (witness : List Bool) (hw : w ≤ witness.length)
    (hm : mValue w witness ≤ B) (hb : B+1 < 2^w) :
    ∃ n final,n ≤ UWitnessChoices.budget w B+1 ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 3) (choiceInput w B witness)) final ∧
      machine.halted final.control=true ∧ Outcome w B witness final := by
  obtain ⟨g,r,hr,hh,ht,hs⟩ := choice_run w B witness hw hb
  obtain ⟨n,hn,hstop⟩ := stop_receipt sizes programs 0 next 3 (UWitnessChoices.budget w B) _ r hr (by simp [next])
  refine ⟨n,_,hn,hstop,by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped],?_⟩
  exact choice_outcome w B witness g _ hw hm hh ht

theorem compare_tail (w B : ℕ) (witness : List Bool) (hw : w ≤ witness.length) (hb : B+1 < 2^w) :
    ∃ n final,n ≤ 4*w+6+UWitnessChoices.budget w B ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 2) (compareInput w B witness)) final ∧
      machine.halted final.control=true ∧ Outcome w B witness final := by
  obtain ⟨r,hr,hh,ht,hs⟩ := compare_run w B witness hw (by omega)
  by_cases hm : mValue w witness ≤ B
  · have hnext : next 2 r.final.control r.final.scanned=some 3 := by
      simp [next,Configuration.scanned,ht,hh,afterCompare,fieldHeads,bootHeads,mFlag,hm,readTapeBit]
    obtain ⟨n,hn,hcall⟩ := call_receipt sizes programs 0 next 2 3 (4*w+4) _ r hr hnext
    have he : RecoveryCalls.restarted (programs 3) r.final.heads r.final.tapes=choiceInput w B witness := by
      rw [hh,ht]
      rfl
    rw [he] at hcall
    obtain ⟨m,final,hmcost,htail,hhalt,hout⟩ := choice_tail w B witness hw hm hb
    exact ⟨n+m,final,by omega,hcall.trans htail,hhalt,hout⟩
  · have hnext : next 2 r.final.control r.final.scanned=none := by
      simp [next,Configuration.scanned,ht,hh,afterCompare,fieldHeads,bootHeads,mFlag,hm,readTapeBit]
    obtain ⟨n,hn,hstop⟩ := stop_receipt sizes programs 0 next 2 (4*w+4) _ r hr hnext
    refine ⟨n,_,by omega,hstop,by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped],?_⟩
    apply rejected_outcome
    · simp [RecoveryCalls.stopped,ht,afterCompare,afterField,afterBoot,input]
    · simp [RecoveryCalls.stopped,ht,afterCompare,afterField,afterBoot,input]
    · simp [RecoveryCalls.stopped,ht,afterCompare,afterField,afterBoot,input]
    · simp [RecoveryCalls.stopped,ht,afterCompare,afterField,afterBoot,input]
    · simp [Valid,hm]

theorem field_tail (w B : ℕ) (witness : List Bool) (hb : B+1 < 2^w) :
    ∃ n final,n ≤ 8*w+9+UWitnessChoices.budget w B ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 1) (fieldInput w B witness)) final ∧
      machine.halted final.control=true ∧ Outcome w B witness final := by
  obtain ⟨r,hr,hctrl,h0,h1,h2,h13,hgood,hs⟩ := field_run w B witness
  by_cases hw : w ≤ witness.length
  · obtain ⟨hh,ht⟩ := hgood hw
    have hnext : next 1 r.final.control r.final.scanned=some 2 := by simp [next,hctrl,hw]
    obtain ⟨n,hn,hcall⟩ := call_receipt sizes programs 0 next 1 2 (4*w+2) _ r hr hnext
    have he : RecoveryCalls.restarted (programs 2) r.final.heads r.final.tapes=compareInput w B witness := by
      rw [hh,ht]
      rfl
    rw [he] at hcall
    obtain ⟨m,final,hmcost,htail,hhalt,hout⟩ := compare_tail w B witness hw hb
    exact ⟨n+m,final,by omega,hcall.trans htail,hhalt,hout⟩
  · have hnext : next 1 r.final.control r.final.scanned=none := by simp [next,hctrl,hw]
    obtain ⟨n,hn,hstop⟩ := stop_receipt sizes programs 0 next 1 (4*w+2) _ r hr hnext
    refine ⟨n,_,by omega,hstop,by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped],?_⟩
    exact rejected_outcome w B witness _ h0 h1 h2 h13 (by simp [Valid,hw])

end NearCubicWires.RepairOrdinary.UWitness
