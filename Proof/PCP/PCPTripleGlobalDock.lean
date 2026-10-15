import Proof.PCP.PCPTripleData

/-! Abstract-state composition keeps the large fixed capacity printer out of
kernel reduction while checking every physical data handoff. -/
namespace NearCubicWires.RepairOrdinary.PCPTripleGlobal
open LocalBitMultitape PCPSerializerReuse
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem dock_run {s t : ℕ} (producer : Machine 48 s) (callee : Machine 133 t) (fp : ℕ) (c : Configuration 48 s)
    (p : ExecutionReceipt 48 s) (hp : runFrom producer fp c=some p)
    (E M pos endPos : ℕ) (source out : List Bool)
    (ph : p.final.heads=PCPTripleEnvelope.outputHeads pos)
    (p0 : p.final.tapes 0=CompareMachine.word M)
    (p5 : p.final.tapes 5=source)
    (p37 : p.final.tapes 37=List.replicate E true)
    (ps : p.steps ≤ fp)
    (base : ExecutionReceipt 133 t)
    (hb : runFrom callee (PCPTripleCold.budget E M)
      ⟨callee.start,PCPTripleCold.heads pos 0,
        PCPTripleCold.input E M
          (source) []⟩=some base)
    (bh : base.final.heads=finalHeads (endPos)
      out.length)
    (bt : base.final.tapes=finalTapes E M
      (source) out)
    (bs : base.steps ≤ PCPTripleCold.budget E M) :
    ∃ r,runFrom (Composition.machine (TapeEmbedding.machine 132 producer) (RecoveryFocus.machine slots callee))
      (fp+1+PCPTripleCold.budget E M)
      (Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 132 => 0) (fun _ : Fin 132 => []) c))=some r ∧
      r.final.tapes 0=CompareMachine.word M ∧ r.final.heads 0=1 ∧
      r.final.tapes 5=source ∧
      r.final.heads 5=endPos ∧
      r.final.tapes 177=out ∧
      r.final.heads 177=out.length ∧
      r.final.tapes 37=List.replicate E true ∧
      r.final.heads 37=0 ∧ r.steps ≤ fp+1+PCPTripleCold.budget E M := by
  let prepared := TapeEmbedding.receipt (fun _ : Fin 132 => 0) (fun _ : Fin 132 => []) p
  have hprepared := TapeEmbedding.run_embed producer
    (fun _ : Fin 132 => 0) (fun _ : Fin 132 => []) _ _ p hp
  have oldH (i : Fin 48) : prepared.final.heads (i.castAdd 132)=PCPTripleEnvelope.outputHeads pos i := by
    simp only [prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left,ph]
  have oldT (i : Fin 48) : prepared.final.tapes (i.castAdd 132)=p.final.tapes i := by
    simp only [prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  have newH (i : Fin 132) : prepared.final.heads (i.natAdd 48)=0 := by
    simp only [prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right]
  have newT (i : Fin 132) : prepared.final.tapes (i.natAdd 48)=[] := by
    simp only [prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right]
  have hiT : ∀ j,prepared.final.tapes (slots j)=PCPTripleCold.input E M source [] j := by
    intro j
    refine Fin.addCases (m:=132) (n:=1) (fun i => ?_) (fun i => ?_) j
    · simp only [PCPTripleCold.input,Fin.addCases_left,PCPTripleStart.inputTapes]
      by_cases h0 : i=0
      · subst i; exact (oldT 5).trans p5
      by_cases h130 : i=130
      · subst i; exact (oldT 37).trans p37
      have hv0 : i.val≠0 := fun h => h0 (Fin.ext h)
      have hv130 : i.val≠130 := fun h => h130 (Fin.ext h)
      have hv132 : i.val≠132 := by omega
      have hs : slots (i.castAdd 1)=i.natAdd 48 := by
        apply Fin.ext
        simp [slots,hv0,hv130,hv132,Nat.add_comm]
      rw [hs,newT]
      simp only [h0,h130,ite_false,ite_self]
    · fin_cases i
      exact (oldT 0).trans p0
  have hiH : ∀ j,prepared.final.heads (slots j)=PCPTripleCold.heads pos 0 j := by
    intro j
    refine Fin.addCases (m:=132) (n:=1) (fun i => ?_) (fun i => ?_) j
    · by_cases h0 : i=0
      · subst i; exact oldH 5
      by_cases h130 : i=130
      · subst i; exact oldH 37
      have hv0 : i.val≠0 := fun h => h0 (Fin.ext h)
      have hv130 : i.val≠130 := fun h => h130 (Fin.ext h)
      have hv132 : i.val≠132 := by omega
      have hs : slots (i.castAdd 1)=i.natAdd 48 := by
        apply Fin.ext
        simp [slots,hv0,hv130,hv132,Nat.add_comm]
      rw [hs,newH]
      exact (cold_head_zero pos i h0).symm
    · fin_cases i
      exact oldH 0
  obtain ⟨finished,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective callee
    prepared.final.heads prepared.final.tapes _ _ base hb
  have he : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes
      (⟨callee.start,PCPTripleCold.heads pos 0,PCPTripleCold.input E M
        (source) []⟩ : Configuration 133 t)=
      (⟨callee.start,prepared.final.heads,prepared.final.tapes⟩ : Configuration 180 _) := by
    apply configuration_ext
    · rfl
    · funext i
      cases hpick : RecoveryFocus.pick slots i with
      | none => simp only [RecoveryFocus.config,hpick]
      | some j =>
        have hij := RecoveryFocus.slot_of_pick slots hpick
        simpa only [RecoveryFocus.config,hpick] using
          (hiH j).symm.trans (congrArg prepared.final.heads hij)
    · exact RecoveryRootRound.install_existing slots prepared.final.tapes _ hiT
  rw [he] at hf
  have joined := Composition.run_join (TapeEmbedding.machine 132 producer) (RecoveryFocus.machine slots callee) _ _ _ prepared finished hprepared hf
  have selectedT (j : Fin 133) : finished.final.tapes (slots j)=base.final.tapes j := by
    simp only [ff,RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have selectedH (j : Fin 133) : finished.final.heads (slots j)=base.final.heads j := by
    simp only [ff,RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have ht0 : finished.final.tapes 0=CompareMachine.word M := by
    rw [show (0 : Fin 180)=slots 132 by rfl,selectedT,bt]
    rfl
  have hh0 : finished.final.heads 0=1 := by
    rw [show (0 : Fin 180)=slots 132 by rfl,selectedH,bh]
    rfl
  have sourceT : finished.final.tapes 5=source := by
    rw [show (5 : Fin 180)=slots 0 by rfl,selectedT,bt]
    rfl
  have sourceH : finished.final.heads 5=endPos := by
    rw [show (5 : Fin 180)=slots 0 by rfl,selectedH,bh]
    rfl
  have outT : finished.final.tapes 177=out := by
    rw [show (177 : Fin 180)=slots 129 by rfl,selectedT,bt]
    rfl
  have outH : finished.final.heads 177=out.length := by
    rw [show (177 : Fin 180)=slots 129 by rfl,selectedH,bh]
    rfl
  have driverT : finished.final.tapes 37=List.replicate E true := by
    rw [show (37 : Fin 180)=slots 130 by rfl,selectedT,bt]
    rfl
  have driverH : finished.final.heads 37=0 := by
    rw [show (37 : Fin 180)=slots 130 by rfl,selectedH,bh]
    rfl
  refine ⟨Composition.joinedReceipt prepared finished,joined,?_⟩
  rw [joined_heads,joined_tapes]
  refine ⟨ht0,hh0,sourceT,sourceH,outT,outH,driverT,driverH,?_⟩
  change p.steps+1+finished.steps ≤ _
  change base.steps ≤ PCPTripleCold.budget E M at bs
  omega

end NearCubicWires.RepairOrdinary.PCPTripleGlobal
