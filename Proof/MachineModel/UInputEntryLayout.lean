import Proof.MachineModel.UInputScalarReady

/-! The fixed 49-tape U-input ABI. The source is retained on0; code/x/B are
on5/7/9, prepared N/w/I/K on12/19/20/21, normalized B/L on25/28,
result46, and the exact floor-log sentinel47 at head1. -/
namespace NearCubicWires.RepairOrdinary.UInputEntry
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Store := Fin 49 → List Bool
def scanSlots : Fin 3 → Fin 49 := ![0,1,2]
def fieldSlots : Fin 10 → Fin 49 := ![0,3,4,5,6,7,8,9,10,11]
def scalarSlots (j : Fin 40) : Fin 49 :=
  if j.val=0 then 0 else if j.val=1 then 7 else if j.val=2 then 9
  else ⟨j.val+9,by omega⟩
theorem scan_injective : Function.Injective scanSlots := by decide
theorem field_injective : Function.Injective fieldSlots := by decide
theorem scalar_value (j : Fin 40) : (scalarSlots j).val=
    if j.val=0 then 0 else if j.val=1 then 7 else if j.val=2 then 9 else j.val+9 := by
  unfold scalarSlots
  split_ifs <;> rfl
theorem scalar_injective : Function.Injective scalarSlots := by
  intro a b h
  have hv := congrArg Fin.val h
  apply Fin.ext
  rw [scalar_value,scalar_value] at hv
  split_ifs at hv <;> omega
noncomputable def scanPhase := RecoveryFocus.machine scanSlots UInputScan.machine
noncomputable def fieldPhase := RecoveryFocus.machine fieldSlots UInputFields.machine
noncomputable def scalarPhase := RecoveryFocus.machine scalarSlots UInputScalars.fullMachine
noncomputable def validMachine := Composition.machine fieldPhase scalarPhase

def input (raw : List Bool) : Store := fun i => if i.val=0 then frame raw else []
def afterScan (raw : List Bool) : Store := fun i =>
  if i.val=1 then [UInputSyntax.accepts 0 raw]
  else if i.val=2 then List.replicate (2*raw.length+1) false else input raw i

def extracted (raw code x bound : List Bool) (g : ℕ) : Store := fun i =>
  if i.val=3 then UInputFields.output raw code x bound g 1 else
  if i.val=4 then UInputFields.output raw code x bound g 2 else
  if i.val=5 then UInputFields.output raw code x bound g 3 else
  if i.val=6 then UInputFields.output raw code x bound g 4 else
  if i.val=7 then UInputFields.output raw code x bound g 5 else
  if i.val=8 then UInputFields.output raw code x bound g 6 else
  if i.val=9 then UInputFields.output raw code x bound g 7 else
  if i.val=10 then UInputFields.output raw code x bound g 8 else
  if i.val=11 then UInputFields.output raw code x bound g 9 else
  afterScan raw i

noncomputable def endpoint (raw code x bound : List Bool) (g carry reset degree cap scratch : ℕ) : Store :=
  install scalarSlots (extracted raw code x bound g)
    (UInputScalars.fullOutput raw x bound carry reset degree cap scratch)
def heads : Fin 49 → ℕ := fun i => if i.val=47 then 1 else 0

theorem scan_ready (raw : List Bool) :
    ClockJoin.ReadyRun scanPhase (4*raw.length+4) (input raw) (afterScan raw) := by
  have h := (UInputScan.ready raw).focus scanSlots scan_injective (input raw)
    (by intro j; fin_cases j <;> rfl)
  have ho : install scanSlots (input raw) (UInputScan.output raw)=afterScan raw := by
    apply HierarchyWidth.install_eq _ scan_injective
    · intro j; fin_cases j <;> rfl
    · intro i hi
      simp only [Fin.forall_fin_succ] at hi
      fin_cases i <;> simp_all [scanSlots,afterScan]
  rw [ho] at h
  exact h

theorem field_ready (code x bound padding : List Bool) :
    ∃ g, ClockJoin.ReadyRun fieldPhase
      (12*(VerifierInputFields.source code x bound padding).length+5)
      (afterScan (VerifierInputFields.source code x bound padding))
      (extracted (VerifierInputFields.source code x bound padding) code x bound g) := by
  let raw := VerifierInputFields.source code x bound padding
  obtain ⟨g,_,h⟩ := UInputFields.entry_ready code x bound padding
  have hf := h.focus fieldSlots field_injective (afterScan raw)
    (by intro j; fin_cases j <;> rfl)
  have ho : install fieldSlots (afterScan raw) (UInputFields.output raw code x bound g)=
      extracted raw code x bound g := by
    apply HierarchyWidth.install_eq _ field_injective
    · intro j; fin_cases j <;> rfl
    · intro i hi
      simp only [Fin.forall_fin_succ] at hi
      fin_cases i <;> simp_all [fieldSlots,extracted]
  rw [ho] at hf
  exact ⟨g,hf⟩

theorem scalar_run (raw code x bound : List Bool) (g : ℕ) (hn : 0 < raw.length) :
    ∃ carry reset degree cap scratch r,
      run scalarPhase (UInputScalars.fullBudget raw x) (extracted raw code x bound g)=some r ∧
      r.final.tapes=endpoint raw code x bound g carry reset degree cap scratch ∧
      r.final.heads=heads ∧ r.steps ≤ UInputScalars.fullBudget raw x := by
  obtain ⟨carry,reset,degree,cap,scratch,base,hb,ht,hh,hs⟩ := UInputScalars.full_run raw x bound hn
  obtain ⟨r,hr,hf,hrs⟩ := RecoveryFocus.run_config scalarSlots scalar_injective UInputScalars.fullMachine
    (fun _ => 0) (extracted raw code x bound g) (UInputScalars.fullBudget raw x) _ base hb
  have hi : RecoveryFocus.config scalarSlots (fun _ => 0) (extracted raw code x bound g)
      (initialConfiguration UInputScalars.fullMachine (UInputScalars.input raw x bound))=
      initialConfiguration scalarPhase (extracted raw code x bound g) := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick scalarSlots i <;> simp [RecoveryFocus.config,hp,initialConfiguration]
    · exact install_existing scalarSlots _ _ (by intro j; fin_cases j <;> rfl)
  rw [hi] at hr
  refine ⟨carry,reset,degree,cap,scratch,r,hr,?_,?_,hrs.trans_le hs⟩
  · rw [hf]
    change install scalarSlots _ base.final.tapes=_
    rw [ht]
    rfl
  · funext i
    cases hp : RecoveryFocus.pick scalarSlots i with
    | none =>
      have hn47 : i.val≠47 := by
        intro he
        have hs47 : i=scalarSlots 38 := Fin.ext he
        have hp47 := RecoveryFocus.pick_slot scalarSlots scalar_injective 38
        rw [←hs47,hp] at hp47
        contradiction
      simp [hf,RecoveryFocus.config,hp,heads,hn47]
    | some j =>
      have he := RecoveryFocus.slot_of_pick scalarSlots hp
      simp only [hf,RecoveryFocus.config,hp,hh]
      rw [←he]
      fin_cases j <;> rfl

def validBudget (raw x : List Bool) := 12*raw.length+6+UInputScalars.fullBudget raw x

theorem valid_run (code x bound padding : List Bool) :
    let raw := VerifierInputFields.source code x bound padding
    ∃ g carry reset degree cap scratch r,
      run validMachine (validBudget raw x) (afterScan raw)=some r ∧
      r.final.tapes=endpoint raw code x bound g carry reset degree cap scratch ∧
      r.final.heads=heads ∧ r.steps ≤ validBudget raw x := by
  let raw := VerifierInputFields.source code x bound padding
  have hn : 0 < raw.length := by simp [raw,VerifierInputFields.source]
  obtain ⟨g,first,hfirst,ht,hh,hs⟩ := field_ready code x bound padding
  obtain ⟨carry,reset,degree,cap,scratch,last,hlast,hlt,hlh,hls⟩ := scalar_run raw code x bound g hn
  have he : Composition.restart first.final scalarPhase.start=
      initialConfiguration scalarPhase (extracted raw code x bound g) := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  unfold run at hlast
  rw [←he] at hlast
  have h := Composition.run_join fieldPhase scalarPhase (12*raw.length+5)
    (UInputScalars.fullBudget raw x) _ first last hfirst hlast
  have heq : 12*raw.length+5+1+UInputScalars.fullBudget raw x=validBudget raw x := by
    dsimp [validBudget]
  rw [heq] at h
  refine ⟨g,carry,reset,degree,cap,scratch,Composition.joinedReceipt first last,h,hlt,hlh,?_⟩
  dsimp only [Composition.joinedReceipt,validBudget,raw] at *
  omega

end NearCubicWires.RepairOrdinary.UInputEntry
