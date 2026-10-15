import Proof.MachineModel.UWitnessReady

/-! Witness preparation after the input/decoder capsule. The old69-tape
ambient state is retained, including all decoder cursors. Fresh workspace
is69..80; ordinary witness1, width20, and normalized B26 are selected inputs. -/
namespace NearCubicWires.RepairOrdinary.UWitnessOrdinary
open LocalBitMultitape RecoveryRootRound SignedSortKey ClockDyadicLedger RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 15) : Fin 81 :=
  if j.val=0 then 1 else if j.val=1 then 20 else if j.val=2 then 26 else ⟨j.val+66,by omega⟩
theorem slot_value (j : Fin 15) : (slots j).val=
    if j.val=0 then 1 else if j.val=1 then 20 else if j.val=2 then 26 else j.val+66 := by
  unfold slots
  split_ifs <;> rfl
theorem slots_injective : Function.Injective slots := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [slot_value,slot_value] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
noncomputable def machine := RecoveryFocus.machine slots UWitness.machine
noncomputable def entry (heads : Fin 81 → ℕ) (tapes : Fin 81 → List Bool) :=
  RecoveryCalls.restarted machine heads tapes
def project {s : ℕ} (c : Configuration 81 s) : Configuration 15 s :=
  ⟨c.control,c.heads ∘ slots,c.tapes ∘ slots⟩

def Preserved {s : ℕ} (heads : Fin 81 → ℕ) (tapes : Fin 81 → List Bool)
    (c : Configuration 81 s) : Prop :=
  ∀ i,(∀ j,slots j≠i) → c.heads i=heads i ∧ c.tapes i=tapes i

theorem entry_run (w B : ℕ) (witness : List Bool)
    (ambientHeads : Fin 81 → ℕ) (ambientTapes : Fin 81 → List Bool)
    (hb : B+1 < 2^w) (hh : ∀ j,ambientHeads (slots j)=0)
    (ht : ∀ j,ambientTapes (slots j)=UWitness.input w B witness j) :
    ∃ r,runFrom machine (UWitness.budget w B) (entry ambientHeads ambientTapes)=some r ∧
      UWitness.Outcome w B witness (project r.final) ∧
      Preserved ambientHeads ambientTapes r.final ∧ r.steps ≤ 128*(B+1)*(w+1) := by
  obtain ⟨base,hbase,hout,hs⟩ := UWitness.total_run w B witness hb
  obtain ⟨r,hr,hf,hrs⟩ := RecoveryFocus.run_config slots slots_injective UWitness.machine
    ambientHeads ambientTapes (UWitness.budget w B) _ base hbase
  have he := UWitness.focus_config_eq slots slots_injective
    (initialConfiguration UWitness.machine (UWitness.input w B witness)) ambientHeads ambientTapes hh ht
  rw [he] at hr
  have hp : project r.final=base.final := by
    apply configuration_ext
    · simp [project,hf,RecoveryFocus.config]
    · funext j
      simp [project,hf,RecoveryFocus.config,RecoveryFocus.pick_slot _ slots_injective,Function.comp_apply]
    · funext j
      simp [project,hf,RecoveryFocus.config,RecoveryFocus.pick_slot _ slots_injective,Function.comp_apply]
  refine ⟨r,hr,by rwa [hp],?_,hrs.trans_le hs⟩
  intro i hi
  have hnone := UWitness.pick_other slots i hi
  simp [hf,RecoveryFocus.config,hnone]

theorem literal_abi {s : ℕ} (w B : ℕ) (witness : List Bool) (c : Configuration 81 s)
    (h : UWitness.Outcome w B witness (project c)) :
    c.tapes 1=frame witness ∧ c.tapes 20=List.replicate w true ∧ c.tapes 26=frame (binary w B) ∧
    (c.scanned 79=true ↔ UWitness.Valid w B witness) ∧
    (c.scanned 79=true → c.heads 1=2*(w+B) ∧ c.tapes 74=frame (binary w (UWitness.mValue w witness)) ∧
      c.tapes 78=frame ((witness.drop w).take B) ∧
      c.tapes 73=RepairSource.VerifierDecoding.CompareMachine.word w ∧ c.heads 73=1 ∧
      ∀ j : Fin 15,j.val≠0 → j.val≠7 → c.heads (slots j)=0) := by
  obtain ⟨h0,h1,h2,hvalid,hgood⟩ := h
  refine ⟨h0,h1,h2,hvalid,?_⟩
  intro hs
  obtain ⟨hh,hm,hchoices,hwidth⟩ := hgood hs
  refine ⟨congrFun hh 0,hm,hchoices,hwidth,congrFun hh 7,?_⟩
  intro j hj0 hj7
  have hj := congrFun hh j
  simpa [project,Function.comp_apply,UWitness.successHeads,UWitness.bootHeads,hj0,hj7] using hj

def old (i : Fin 50) : Fin 81 := i.castAdd 31
def Fresh (heads : Fin 81 → ℕ) (tapes : Fin 81 → List Bool) : Prop :=
  ∀ i,69 ≤ i.val → heads i=0 ∧ tapes i=[]

/-- The actual input preparer's output supplies w/B and the strict binary
counter fit. Decoder work may have changed any inactive head or workspace;
only its old input-field truths and the three selected zero heads are used. -/
theorem from_prepared (raw witness : List Bool)
    (ambientHeads : Fin 81 → ℕ) (ambientTapes : Fin 81 → List Bool)
    (hp : UInputOrdinary.Prepared raw (ambientTapes ∘ old))
    (hwitness : ambientTapes 1=frame witness)
    (hh : ambientHeads 1=0 ∧ ambientHeads 20=0 ∧ ambientHeads 26=0)
    (hfresh : Fresh ambientHeads ambientTapes) :
    ∃ B,B ≤ limit raw.length ∧ ∃ r,
      runFrom machine (UWitness.budget (width raw.length) B) (entry ambientHeads ambientTapes)=some r ∧
      UWitness.Outcome (width raw.length) B witness (project r.final) ∧
      Preserved ambientHeads ambientTapes r.final ∧
      r.steps ≤ 128*(B+1)*(width raw.length+1) := by
  obtain ⟨code,x,bound,padding,_,hguards,_,_,_,_,_,hw,_,_,hB,_,_⟩ := hp
  let B := value bound
  have hBL : B ≤ limit raw.length := hguards.2.2
  have hfit : B+1 < 2^width raw.length := by
    have := (width_bounds raw.length).1
    omega
  have hheads : ∀ j,ambientHeads (slots j)=0 := by
    intro j
    fin_cases j
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2
    all_goals exact (hfresh _ (by decide)).1
  have htapes : ∀ j,ambientTapes (slots j)=UWitness.input (width raw.length) B witness j := by
    intro j
    fin_cases j
    · exact hwitness
    · exact hw
    · exact hB
    all_goals exact (hfresh _ (by decide)).2
  obtain ⟨r,hr,hout,hpres,hsteps⟩ := entry_run (width raw.length) B witness ambientHeads ambientTapes hfit hheads htapes
  exact ⟨B,hBL,r,hr,hout,hpres,hsteps⟩

end NearCubicWires.RepairOrdinary.UWitnessOrdinary
