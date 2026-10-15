import Proof.Hierarchy.HierarchyStreamLayout
import Proof.PCP.ProjectionNormalizationStreamBounds

/-! Actual hierarchy request through its one selected source invocation and
whole query/clause normalization. The original scalar snapshot and every
unselected tape remain available for the final balanced serializer. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyStreams
open LocalBitMultitape RepairOrdinary RecoveryRootRound SourceInterfaces VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem slot_unselected (k : ℕ) (i : Fin (base source k))
    (hs : i≠sourceSlot source k) (hr : i≠rawR source k) (hq : i≠rawQ source k) :
    ∀ j,slots source k j≠old source k i := by
  intro j he
  have hi := i.isLt
  have hv := congrArg Fin.val he
  have hs' : i.val≠(sourceSlot source k).val := fun h => hs (Fin.ext h)
  have hr' : i.val≠(rawR source k).val := fun h => hr (Fin.ext h)
  have hq' : i.val≠(rawQ source k).val := fun h => hq (Fin.ext h)
  dsimp only [slots,old] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem raw_run (k CH Cpad : ℕ) (code x bound : List Bool) (hpad : k+3 ≤ Cpad) :
    ∃ r prior,run (machine source k CH Cpad code) (budget source k CH Cpad code x)
      (SourceHandoff.sourceTapes (frame x++frame bound))=some r ∧
      r.steps ≤ budget source k CH Cpad code x ∧
      HierarchySelectedSource.Fields source k CH Cpad code x
        (prior ∘ HierarchySourceInput.slots source k ∘ HierarchySelectedSource.old source k) ∧
      prior (sourceSlot source k)=(source.output (request k CH Cpad code x)).word ∧
      prior ⟨0,by dsimp [base,HierarchySourceInput.tapes]; omega⟩=frame x++frame bound ∧
      (∀ i : Fin (base source k),i≠sourceSlot source k → i≠rawR source k → i≠rawQ source k →
        r.final.tapes (old source k i)=prior i ∧ r.final.heads (old source k i)=0) ∧
      r.final.tapes (slots source k 29)=QueryBytes.framedCodes
        (normalizedRows (source.output (request k CH Cpad code x)) (R source k CH Cpad code x) (Q source k CH Cpad code x)).flatten ∧
      r.final.tapes (slots source k 25)=CompareMachine.word (R source k CH Cpad code x*Q source k CH Cpad code x) ∧
      r.final.tapes (slots source k 38)=DedupBytes.fields (source.output (request k CH Cpad code x)) ∧
      r.final.tapes (slots source k 46)=CompareMachine.word (Codec.clauses (source.output (request k CH Cpad code x))).length ∧
      r.final.heads (slots source k 29)=0 ∧ r.final.heads (slots source k 25)=1 ∧
      r.final.heads (slots source k 38)=0 ∧ r.final.heads (slots source k 46)=1 := by
  let p := source.output (request k CH Cpad code x)
  let width := R source k CH Cpad code x
  let queries := Q source k CH Cpad code x
  obtain ⟨prior,hprior,hfields,hpword,hinput⟩ := HierarchySourceInput.raw_run source k CH Cpad code x bound hpad
  obtain ⟨a,ha,hat,hah,has⟩ := hprior
  let firstRun : ExecutionReceipt (tapes source k) _ := TapeEmbedding.receipt
    (fun _ : Fin 48 => 0) (fun _ : Fin 48 => []) a
  have hfirst := TapeEmbedding.run_embed (HierarchySourceInput.machine source k CH Cpad code)
    (fun _ : Fin 48 => 0) (fun _ : Fin 48 => []) _ _ a ha
  have hi : TapeEmbedding.config (fun _ : Fin 48 => 0) (fun _ : Fin 48 => [])
      (initialConfiguration (HierarchySourceInput.machine source k CH Cpad code)
        (SourceHandoff.sourceTapes (frame x++frame bound)))=
      initialConfiguration (first source k CH Cpad code) (SourceHandoff.sourceTapes (frame x++frame bound)) := by
    apply configuration_ext
    · rfl
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [TapeEmbedding.config,initialConfiguration]
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [TapeEmbedding.config,initialConfiguration,SourceHandoff.sourceTapes]
      · simp [TapeEmbedding.config,initialConfiguration,SourceHandoff.sourceTapes,HierarchySourceInput.tapes]
  rw [hi] at hfirst
  have hfirstHeads : ∀ i,firstRun.final.heads i=0 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [firstRun,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left] using hah j
    · simp only [firstRun,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right]
  have hsource : firstRun.final.tapes (old source k (sourceSlot source k))=p.word := by
    simp only [firstRun,TapeEmbedding.receipt,TapeEmbedding.config,old,Fin.addCases_left,hat]
    exact hpword
  have hR : firstRun.final.tapes (old source k (rawR source k))=List.replicate width true := by
    simp only [firstRun,TapeEmbedding.receipt,TapeEmbedding.config,old,Fin.addCases_left,hat]
    exact hfields.rawR
  have hQ : firstRun.final.tapes (old source k (rawQ source k))=List.replicate queries true := by
    simp only [firstRun,TapeEmbedding.receipt,TapeEmbedding.config,old,Fin.addCases_left,hat]
    exact hfields.rawQ
  have hinit : ∀ i,firstRun.final.tapes (slots source k i)=Streams.input p width queries i := by
    intro i
    rw [Streams.input_literal]
    change firstRun.final.tapes (slots source k i)=if i=0 then p.word else if i=13 then List.replicate width true
      else if i=14 then List.replicate queries true else []
    by_cases h0 : i=0
    · subst i; exact hsource
    by_cases h13 : i=13
    · subst i; exact hR
    by_cases h14 : i=14
    · subst i; exact hQ
    · simp only [slots,h0,h13,h14,if_false]
      simp only [firstRun,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_right]
  have hn : 1 ≤ (request k CH Cpad code x).1 := by
    have h := (HierarchyPadding.linear_length k CH Cpad code x hpad).1
    change 1 ≤ (HierarchyPadding.rawInput k CH Cpad code x).length
    omega
  obtain ⟨localRun,hl,hls,hlq,hlqc,hlc,hlcc,hlqh,hlqch,hlch,hlcch⟩ := Streams.streams_run p width queries
    (Dimensions.width_fits source (request k CH Cpad code x) hn)
    (Dimensions.queries_fit source (request k CH Cpad code x) hn)
  obtain ⟨last,hlt,hlf,hlsteps⟩ := RecoveryFocus.run_config (slots source k) (slots_injective source k)
    Streams.machine firstRun.final.heads firstRun.final.tapes _ _ localRun hl
  have he : RecoveryFocus.config (slots source k) firstRun.final.heads firstRun.final.tapes
      (initialConfiguration Streams.machine (Streams.input p width queries))=
      Composition.restart firstRun.final (second source k).start := by
    apply TransitionEvent.focused_eq (slots source k) (slots_injective source k)
      (Composition.restart firstRun.final (second source k).start)
    · rfl
    · intro i; exact (hfirstHeads _).symm
    · intro i; exact (hinit i).symm
    · intro i _; rfl
    · intro i _; rfl
  rw [he] at hlt
  have hall := Composition.run_join (first source k CH Cpad code) (second source k) _ _ _ firstRun last hfirst hlt
  have hselectedTape (i : Fin 48) : last.final.tapes (slots source k i)=localRun.final.tapes i := by
    simp [hlf,RecoveryFocus.config,RecoveryFocus.pick_slot _ (slots_injective source k)]
  have hselectedHead (i : Fin 48) : last.final.heads (slots source k i)=localRun.final.heads i := by
    simp [hlf,RecoveryFocus.config,RecoveryFocus.pick_slot _ (slots_injective source k)]
  refine ⟨Composition.joinedReceipt firstRun last,prior,hall,?_,hfields,hpword,hinput,?_,
    (hselectedTape 29).trans hlq,(hselectedTape 25).trans hlqc,
    (hselectedTape 38).trans hlc,(hselectedTape 46).trans hlcc,
    (hselectedHead 29).trans hlqh,(hselectedHead 25).trans hlqch,
    (hselectedHead 38).trans hlch,(hselectedHead 46).trans hlcch⟩
  · change a.steps+1+last.steps ≤ _
    dsimp only [budget]
    dsimp only [p,width,queries] at hls
    omega
  · intro i hsi hri hqi
    have hnone : RecoveryFocus.pick (slots source k) (old source k i)=none := by
      simp [RecoveryFocus.pick,show ¬∃ j,slots source k j=old source k i from
        fun ⟨j,hj⟩ => slot_unselected source k i hsi hri hqi j hj]
    constructor
    · change last.final.tapes (old source k i)=prior i
      simp only [hlf,RecoveryFocus.config,hnone]
      simpa only [firstRun,TapeEmbedding.receipt,TapeEmbedding.config,old,Fin.addCases_left] using congrFun hat i
    · change last.final.heads (old source k i)=0
      simp only [hlf,RecoveryFocus.config,hnone]
      exact hfirstHeads _

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyStreams
