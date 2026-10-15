import Proof.MachineModel.UInputScan
import Proof.MachineModel.OrdinaryVerifierInputFields
import Proof.Amplification.RecoveryCursorCalls

/-! Paid external unframing and three-field extraction. The enclosing syntax
scan supplies the decomposition; this phase retains both outer and raw input,
all extracted fields, and resets even the consumed raw-source cursor. -/
namespace NearCubicWires.RepairOrdinary.UInputFields
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fieldsMachine := Rewind.machine VerifierFieldLoad.machine
def fieldInput (raw : List Bool) : Fin 8 → List Bool := fun i => if i.val=0 then raw else []
def fieldOutput (raw code x bound : List Bool) (g : ℕ) : Fin 8 → List Bool :=
  ![raw,frame code,List.replicate (frame code).length false,frame x,
    List.replicate (frame x).length false,frame bound,List.replicate (frame bound).length false,
    List.replicate g false]

theorem fields_ready (code x bound padding : List Bool) :
    ∃ g,g ≤ VerifierInputFields.budget code x bound ∧
      ClockJoin.ReadyRun fieldsMachine (8*(VerifierInputFields.source code x bound padding).length+2)
        (fieldInput (VerifierInputFields.source code x bound padding))
        (fieldOutput (VerifierInputFields.source code x bound padding) code x bound g) := by
  obtain ⟨base,hb,hf⟩ := VerifierInputFields.fields_run code x bound padding
  have hs := runFrom_steps_le VerifierFieldLoad.machine _ _ base hb
  obtain ⟨r,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace VerifierFieldLoad.machine
    (VerifierInputFields.budget code x bound)
    (SourceHandoff.sourceTapes (VerifierInputFields.source code x bound padding)) base hb 0
  have hi : (fun i => Fin.addCases (motive := fun _ : Fin (7+1) => List Bool)
      (SourceHandoff.sourceTapes (VerifierInputFields.source code x bound padding))
      (fun _ : Fin 1 => List.replicate 0 false) i)=
      fieldInput (VerifierInputFields.source code x bound padding) := by
    funext i; fin_cases i <;> rfl
  change run fieldsMachine (2*base.steps+2) _=some r at hr
  rw [hi] at hr
  have hlin := VerifierInputFields.linear_budget code x bound padding
  have htbound : 2*base.steps+2 ≤ 8*(VerifierInputFields.source code x bound padding).length+2 := by omega
  have hm := run_moreFuel fieldsMachine _
    ((8*(VerifierInputFields.source code x bound padding).length+2)-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le htbound] at hm
  refine ⟨base.steps,hs,r,hm,?_,hh,by omega⟩
  funext i
  fin_cases i
  · simpa [fieldOutput,hf,VerifierFieldLoad.config] using ht 0
  · simpa [fieldOutput,hf,VerifierFieldLoad.config] using ht 1
  · simpa [fieldOutput,hf,VerifierFieldLoad.config] using ht 2
  · simpa [fieldOutput,hf,VerifierFieldLoad.config] using ht 3
  · simpa [fieldOutput,hf,VerifierFieldLoad.config] using ht 4
  · simpa [fieldOutput,hf,VerifierFieldLoad.config] using ht 5
  · simpa [fieldOutput,hf,VerifierFieldLoad.config] using ht 6
  · simpa [fieldOutput] using hcounter

theorem unwrap_ready (raw : List Bool) :
    ClockJoin.ReadyRun Streaming.machine (4*raw.length+2)
      ![frame raw,[],[]] ![frame raw,raw,List.replicate raw.length false] := by
  obtain ⟨r,hr,hf,hs,_⟩ := Streaming.copy_run raw
  refine ⟨r,?_,?_,?_,hs.le⟩
  · have hi : (fun t : Fin 3 => if t.val=0 then frame raw else [])=![frame raw,[],[]] := by
      funext i; fin_cases i <;> rfl
    rwa [hi] at hr
  · rw [hf]; funext i; fin_cases i <;> simp [Streaming.finished,Streaming.config]
  · rw [hf]; intro i; fin_cases i <;> rfl

def unwrapSlots : Fin 3 → Fin 10 := ![0,1,2]
def fieldSlots : Fin 8 → Fin 10 := ![1,3,4,5,6,7,8,9]
theorem unwrap_injective : Function.Injective unwrapSlots := by decide
theorem field_injective : Function.Injective fieldSlots := by decide
noncomputable def unwrapPhase := RecoveryFocus.machine unwrapSlots Streaming.machine
noncomputable def fieldPhase := RecoveryFocus.machine fieldSlots fieldsMachine
noncomputable def machine := Composition.machine unwrapPhase fieldPhase
def input (raw : List Bool) : Fin 10 → List Bool := fun i => if i.val=0 then frame raw else []
def middle (raw : List Bool) : Fin 10 → List Bool := fun i =>
  if i.val=1 then raw else if i.val=2 then List.replicate raw.length false else input raw i
def output (raw code x bound : List Bool) (g : ℕ) : Fin 10 → List Bool := fun i =>
  if i.val=3 then frame code else if i.val=4 then List.replicate (frame code).length false
  else if i.val=5 then frame x else if i.val=6 then List.replicate (frame x).length false
  else if i.val=7 then frame bound else if i.val=8 then List.replicate (frame bound).length false
  else if i.val=9 then List.replicate g false else middle raw i

theorem unwrap_phase (raw : List Bool) :
    ClockJoin.ReadyRun unwrapPhase (4*raw.length+2) (input raw) (middle raw) := by
  have h := (unwrap_ready raw).focus unwrapSlots unwrap_injective (input raw)
    (by intro i; fin_cases i <;> rfl)
  have ho : install unwrapSlots (input raw) ![frame raw,raw,List.replicate raw.length false]=middle raw := by
    apply HierarchyWidth.install_eq _ unwrap_injective
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h1 := hi 1
      have h2 := hi 2
      change (1 : Fin 10) ≠ i at h1
      change (2 : Fin 10) ≠ i at h2
      have hi1 : i.val≠1 := by intro he; apply h1; apply Fin.ext; omega
      have hi2 : i.val≠2 := by intro he; apply h2; apply Fin.ext; omega
      simp [middle,hi1,hi2]
  rw [ho] at h
  exact h

theorem entry_ready (code x bound padding : List Bool) :
    ∃ g,g ≤ VerifierInputFields.budget code x bound ∧
      ClockJoin.ReadyRun machine (12*(VerifierInputFields.source code x bound padding).length+5)
        (input (VerifierInputFields.source code x bound padding))
        (output (VerifierInputFields.source code x bound padding) code x bound g) := by
  let raw := VerifierInputFields.source code x bound padding
  obtain ⟨g,hg,hf⟩ := fields_ready code x bound padding
  have h := hf.focus fieldSlots field_injective (middle raw)
    (by intro j; fin_cases j <;> rfl)
  have ho : install fieldSlots (middle raw) (fieldOutput raw code x bound g)=output raw code x bound g := by
    apply HierarchyWidth.install_eq _ field_injective
    · intro j; fin_cases j <;> rfl
    · intro i hi
      simp only [Fin.forall_fin_succ] at hi
      fin_cases i <;> simp_all [fieldSlots,output]
  rw [ho] at h
  have hj := ClockJoin.join unwrapPhase fieldPhase _ _ _ _ _ (unwrap_phase raw) h
  have he : 4*raw.length+2+1+(8*raw.length+2)=12*raw.length+5 := by omega
  rw [he] at hj
  exact ⟨g,hg,hj⟩

end NearCubicWires.RepairOrdinary.UInputFields
