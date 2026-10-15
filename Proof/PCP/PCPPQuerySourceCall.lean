import Proof.PCP.PCPPQueryPrepare

/-! One call to the same ordinary PCPP source constructor, on its isolated
literal input and a fresh source workspace. The paid source reset produces
the explicit object at head zero and retains the two physical query drivers. -/
namespace NearCubicWires.RepairOrdinary.PCPPQuerySourceCall
open LocalBitMultitape RepairRepresentation ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : PointwisePCPPAlgorithm)
def program := Rewind.program a.constructor.program
abbrev tapes := 27+(program a).tapeCount
def old (i : Fin 27) : Fin (tapes a) := i.castAdd (program a).tapeCount
def slots (i : Fin (program a).tapeCount) : Fin (tapes a) :=
  if i.val=0 then old a 3 else i.natAdd 27
theorem slots_injective : Function.Injective (slots a) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [slots,old] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
theorem old_none (i : Fin 27) (hi : i≠3) : RecoveryFocus.pick (slots a) (old a i)=none := by
  have hn : ¬∃ j,slots a j=old a i := by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    dsimp [slots,old] at hv
    split_ifs at hv <;> dsimp at hv
    · have he : i=3 := Fin.ext (by omega)
      exact hi he
    · omega
  simp [RecoveryFocus.pick,hn]

noncomputable def prepare := TapeEmbedding.machine (program a).tapeCount PCPPQueryPrepare.machine
noncomputable def sourceProgram := RecoveryFocus.machine (slots a) (program a).machine
noncomputable def machine := Composition.machine (prepare a) (sourceProgram a)
def input (r : PCPPRequest a.minimumArity) (index : ℕ) : Fin (tapes a)→List Bool :=
  Fin.addCases (PCPPQueryPrepare.input r.arity index (encodeBooleanCircuit r.circuit).bits) (fun _ => [])
def sourceBudget (r : PCPPRequest a.minimumArity) := a.coefficient*(r.circuit.size+r.arity+1)^a.degree
def budget (r : PCPPRequest a.minimumArity) (index : ℕ) :=
  PCPPQueryPrepare.budget r.arity index (encodeBooleanCircuit r.circuit).bits+2*sourceBudget a r+3
def outputTape := slots a (program a).outputTape

theorem call_run (r : PCPPRequest a.minimumArity) (index : ℕ) :
    ∃ receipt,run (machine a) (budget a r index) (input a r index)=some receipt ∧
      receipt.steps≤budget a r index ∧
      receipt.final.tapes (outputTape a)=pcppOutput r (a.output r) ∧
      receipt.final.heads (outputTape a)=0 ∧
      receipt.final.tapes (old a 16)=UnaryTemplate.tape index ∧ receipt.final.heads (old a 16)=1 ∧
      receipt.final.tapes (old a 26)=UnaryTemplate.tape r.arity ∧ receipt.final.heads (old a 26)=1 := by
  obtain ⟨base,hb,hbs,hframe,hframeHead,hindex,hindexHead,harity,harityHead⟩ :=
    PCPPQueryPrepare.prepare_run r.arity index (encodeBooleanCircuit r.circuit).bits
  have he := TapeEmbedding.run_embed PCPPQueryPrepare.machine (fun _ : Fin (program a).tapeCount => 0)
    (fun _ : Fin (program a).tapeCount => []) _ _ base hb
  rw [RepairSource.ProjectionNormalization.StreamPrepare.embed_initial] at he
  let ambient := TapeEmbedding.config (fun _ : Fin (program a).tapeCount => 0)
    (fun _ : Fin (program a).tapeCount => []) base.final
  obtain ⟨source,hs,hout,hheads⟩ := a.constructor.reset_realizes r
  have hs' : run (program a).machine (2*sourceBudget a r+2) ((program a).inputTapes (pcppInput r))=some source := hs
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config (slots a) (slots_injective a) (program a).machine
    ambient.heads ambient.tapes _ _ source hs'
  have hi : RecoveryFocus.config (slots a) ambient.heads ambient.tapes
      (initialConfiguration (program a).machine ((program a).inputTapes (pcppInput r)))=
      Composition.restart ambient (sourceProgram a).start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      by_cases hj : j.val=0
      · simpa [ambient,slots,hj,old,TapeEmbedding.config,initialConfiguration] using hframeHead
      · simp [ambient,slots,hj,TapeEmbedding.config,initialConfiguration]
    · intro j
      by_cases hj : j.val=0
      · simpa [ambient,slots,hj,old,TapeEmbedding.config,initialConfiguration,Program.inputTapes,
          pcppInput,PCPPQueryPrepare.word] using hframe
      · simp [ambient,slots,hj,TapeEmbedding.config,initialConfiguration,Program.inputTapes]
  rw [hi] at hf
  have hj := Composition.run_join (prepare a) (sourceProgram a) _ (2*sourceBudget a r+2) _
    (TapeEmbedding.receipt (fun _ : Fin (program a).tapeCount => 0) (fun _ : Fin (program a).tapeCount => []) base)
    focused he hf
  have ht : PCPPQueryPrepare.budget r.arity index (encodeBooleanCircuit r.circuit).bits+1+(2*sourceBudget a r+2)=
      budget a r index := by unfold budget; omega
  rw [ht] at hj
  change run (machine a) (budget a r index) (input a r index)=some
    (Composition.joinedReceipt
      (TapeEmbedding.receipt (fun _ : Fin (program a).tapeCount => 0)
        (fun _ : Fin (program a).tapeCount => []) base) focused) at hj
  have htape (j : Fin (program a).tapeCount) : focused.final.tapes (slots a j)=source.final.tapes j := by
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot (slots a) (slots_injective a)]
  have hhead (j : Fin (program a).tapeCount) : focused.final.heads (slots a j)=source.final.heads j := by
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot (slots a) (slots_injective a)]
  have hother (i : Fin 27) (hi : i≠3) : focused.final.tapes (old a i)=base.final.tapes i ∧
      focused.final.heads (old a i)=base.final.heads i := by
    simp only [hff,RecoveryFocus.config,old_none a i hi]
    simp [ambient,old,TapeEmbedding.config]
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin (program a).tapeCount => 0) (fun _ : Fin (program a).tapeCount => []) base)
    focused,hj,?_,htape _ |>.trans hout,hhead _ |>.trans (hheads _),
    (hother 16 (by decide)).1.trans hindex,(hother 16 (by decide)).2.trans hindexHead,
    (hother 26 (by decide)).1.trans harity,(hother 26 (by decide)).2.trans harityHead⟩
  change base.steps+1+focused.steps≤_
  rw [hfs]
  have hsource := runFrom_steps_le (program a).machine _ _ source hs'
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.PCPPQuerySourceCall
