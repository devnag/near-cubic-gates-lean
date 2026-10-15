import Proof.MachineModel.UInputReady

/-! Ordinary verifier entry: frame(input) on0 and frame(witness) on1, with
every scratch tape blank. The entire witness tape remains inactive while
input syntax and scalar guards are established. -/
namespace NearCubicWires.RepairOrdinary.UInputOrdinary
open LocalBitMultitape RecoveryRootRound RadixSemantics ClockDyadicLedger
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 49) : Fin 50 := if j.val=0 then 0 else ⟨j.val+1,by omega⟩
theorem slot_value (j : Fin 49) : (slots j).val=if j.val=0 then 0 else j.val+1 := by
  unfold slots
  split_ifs <;> rfl
theorem slots_injective : Function.Injective slots := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [slot_value,slot_value] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
theorem witness_outside : ∀ j,slots j≠(1 : Fin 50) := by
  intro j hj
  have hv := congrArg Fin.val hj
  rw [slot_value] at hv
  split_ifs at hv <;> omega
theorem witness_pick : RecoveryFocus.pick slots (1 : Fin 50)=none := by
  have hn : ¬∃ j,slots j=(1 : Fin 50) := by simpa using witness_outside
  simp [RecoveryFocus.pick,hn]

noncomputable def machine := RecoveryFocus.machine slots UInputEntry.machine
def input (raw witness : List Bool) : Fin 50 → List Bool := fun i =>
  if i.val=0 then frame raw else if i.val=1 then frame witness else []
def heads : Fin 50 → ℕ := fun i => if i.val=48 then 1 else 0

def Prepared (raw : List Bool) (tapes : Fin 50 → List Bool) : Prop := ∃ code x bound padding,
  raw=VerifierInputFields.source code x bound padding ∧
  UInputScalars.Guards raw x bound ∧
  tapes 0=frame raw ∧ tapes 6=frame code ∧ tapes 8=frame x ∧ tapes 10=frame bound ∧
  tapes 13=frame (ClockBinary.word raw.length) ∧
  tapes 20=List.replicate (width raw.length) true ∧
  tapes 21=List.replicate (2*width raw.length) true ∧
  tapes 22=List.replicate (2*width raw.length+2) true ∧
  tapes 26=frame (SignedSortKey.binary (width raw.length) (value bound)) ∧
  tapes 29=frame (SignedSortKey.binary (width raw.length) (limit raw.length)) ∧
  tapes 48=RepairSource.VerifierDecoding.CompareMachine.word (Nat.log 2 raw.length)

theorem prepared_of_projection (raw : List Bool) (tapes : Fin 50 → List Bool)
    (h : UInputEntry.Prepared raw (tapes ∘ slots)) : Prepared raw tapes := h

theorem entry_run (raw witness : List Bool) :
    ∃ r,run machine (UInputEntry.budget raw) (input raw witness)=some r ∧
      r.final.tapes 0=frame raw ∧ r.final.tapes 1=frame witness ∧ r.final.heads 1=0 ∧
      (r.final.scanned 47=true ↔ UInputEntry.Valid raw) ∧
      (r.final.scanned 47=true → Prepared raw r.final.tapes ∧ r.final.heads=heads) ∧
      r.steps ≤ 400*(raw.length+1)*PCPResourceLedger.q raw.length^2 := by
  obtain ⟨base,hb,h0,hvalid,hprepared,hs⟩ := UInputEntry.total_run raw
  obtain ⟨r,hr,hf,hrs⟩ := RecoveryFocus.run_config slots slots_injective UInputEntry.machine
    (fun _ => 0) (input raw witness) (UInputEntry.budget raw) _ base hb
  have hi : RecoveryFocus.config slots (fun _ => 0) (input raw witness)
      (initialConfiguration UInputEntry.machine (UInputEntry.input raw))=
      initialConfiguration machine (input raw witness) := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick slots i <;> simp [RecoveryFocus.config,hp,initialConfiguration]
    · exact install_existing slots _ _ (by intro j; fin_cases j <;> rfl)
  rw [hi] at hr
  have ht (j : Fin 49) : r.final.tapes (slots j)=base.final.tapes j := by
    simp [hf,RecoveryFocus.config,RecoveryFocus.pick_slot _ slots_injective]
  have hscan : r.final.scanned 47=base.final.scanned 46 := by
    have h := congrFun (RecoveryFocus.scanned_config slots slots_injective (fun _ => 0)
      (input raw witness) base.final) 46
    simpa only [hf,Function.comp_apply,show slots 46=(47 : Fin 50) by rfl] using h
  refine ⟨r,hr,(ht 0).trans h0,?_,?_,by rw [hscan]; exact hvalid,?_,hrs.trans_le hs⟩
  · simp [hf,RecoveryFocus.config,witness_pick,input]
  · simp [hf,RecoveryFocus.config,witness_pick]
  · intro h
    obtain ⟨hp,hh⟩ := hprepared (by rwa [←hscan])
    have hproj : r.final.tapes ∘ slots=base.final.tapes := funext ht
    refine ⟨prepared_of_projection raw _ (by rw [hproj]; exact hp),?_⟩
    funext i
    cases hpi : RecoveryFocus.pick slots i with
    | none =>
      have hn48 : i.val≠48 := by
        intro he
        have heq : i=slots 47 := Fin.ext he
        have hs48 := RecoveryFocus.pick_slot slots slots_injective 47
        rw [←heq,hpi] at hs48
        contradiction
      simp [hf,RecoveryFocus.config,hpi,heads,hn48]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slots hpi
      simp only [hf,RecoveryFocus.config,hpi,hh]
      rw [←he]
      fin_cases j <;> rfl

end NearCubicWires.RepairOrdinary.UInputOrdinary
