import Proof.PCP.VerifierDecodingEarlyReject
import Proof.MachineModel.UInputOrdinary

/-! Fixed shared U store: retain all fifty input-preparation tapes and use
nineteen blank tapes for the decoder, sharing code6 and physical limit48. -/
namespace NearCubicWires.RepairOrdinary.UDecoder
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 21 → Fin 69 := ![6,50,51,52,48,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68]
theorem slots_injective : Function.Injective slots := by decide
abbrev states := Fintype.card (RecoveryCalls.Control Ready.sizes)
noncomputable def decoder : Machine 69 states := RecoveryFocus.machine slots Ready.machine

def extended {s : ℕ} (base : Configuration 50 s) : Configuration 69 s :=
  TapeEmbedding.config (fun _ : Fin 19 => 0) (fun _ : Fin 19 => []) base
noncomputable def decoderInput {s : ℕ} (base : Configuration 50 s) : Configuration 69 states :=
  ⟨decoder.start,(extended base).heads,(extended base).tapes⟩

theorem blank_heads (word : List Bool) (limit : ℕ) (i : Fin 21) :
    (Ready.blankEntry word limit).heads i=if i=4 then 1 else 0 := by
  fin_cases i <;> rfl

theorem blank_tapes (word : List Bool) (limit : ℕ) (i : Fin 21) :
    (Ready.blankEntry word limit).tapes i=
      if i=0 then frame word else if i=4 then CompareMachine.word limit else [] := by
  fin_cases i <;> rfl

theorem projected_entry {s : ℕ} (base : Configuration 50 s) (code : List Bool) (N : ℕ)
    (hh : base.heads=UInputOrdinary.heads) (hc : base.tapes 6=frame code)
    (hl : base.tapes 48=CompareMachine.word (Nat.log 2 N)) (j : Fin 21) :
    (extended base).heads (slots j)=(Ready.blankEntry code (Nat.log 2 N)).heads j ∧
      (extended base).tapes (slots j)=(Ready.blankEntry code (Nat.log 2 N)).tapes j := by
  rw [blank_heads,blank_tapes]
  fin_cases j <;> simp [extended,slots,TapeEmbedding.config,Fin.addCases,hh,UInputOrdinary.heads,hc,hl]

theorem decoder_input_eq {s : ℕ} (base : Configuration 50 s) (code : List Bool) (N : ℕ)
    (hh : base.heads=UInputOrdinary.heads) (hc : base.tapes 6=frame code)
    (hl : base.tapes 48=CompareMachine.word (Nat.log 2 N)) :
    RecoveryFocus.config slots (extended base).heads (extended base).tapes
      (Ready.blankEntry code (Nat.log 2 N))=decoderInput base := by
  have hp := projected_entry base code N hh hc hl
  apply configuration_ext
  · rfl
  · funext i
    cases h : RecoveryFocus.pick slots i with
    | none => simp [RecoveryFocus.config,h,decoderInput]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slots h
      simp only [RecoveryFocus.config,h,decoderInput]
      rw [←he]
      exact (hp j).1.symm
  · funext i
    cases h : RecoveryFocus.pick slots i with
    | none => simp [RecoveryFocus.config,h,decoderInput]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slots h
      simp only [RecoveryFocus.config,h,decoderInput]
      rw [←he]
      exact (hp j).2.symm

theorem decoder_run {s : ℕ} (base : Configuration 50 s) (code : List Bool) (N : ℕ)
    (hh : base.heads=UInputOrdinary.heads) (hc : base.tapes 6=frame code)
    (hl : base.tapes 48=CompareMachine.word (Nat.log 2 N)) :
    ∃ r small, runFrom decoder (Ready.limitedBudget code.length (Nat.log 2 N)) (decoderInput base)=some r ∧
      r.steps≤Ready.limitedBudget code.length (Nat.log 2 N) ∧
      r.final=RecoveryFocus.config slots (extended base).heads (extended base).tapes small ∧
      (r.final.scanned 67=true ↔ ∃ v,decode N code=some v) ∧
      Ready.Outcome code (Nat.log 2 N) (ZeroPadding.config (Ready.inputCapacity code) small) := by
  obtain ⟨small,hloc,hs,hbit,hout⟩ := Ready.limited_run N code
  obtain ⟨r,hr,hf,hrs⟩ := RecoveryFocus.run_config slots slots_injective Ready.machine
    (extended base).heads (extended base).tapes _ _ small hloc
  rw [decoder_input_eq base code N hh hc hl] at hr
  refine ⟨r,small.final,hr,hrs.trans_le hs,hf,?_,hout⟩
  have he := congrFun (RecoveryFocus.scanned_config slots slots_injective
    (extended base).heads (extended base).tapes small.final) 19
  have hs67 : r.final.scanned 67=small.final.scanned 19 := by
    simpa only [hf,Function.comp_apply,show slots 19=(67 : Fin 69) by rfl] using he
  rw [hs67]
  exact hbit

end NearCubicWires.RepairOrdinary.UDecoder
