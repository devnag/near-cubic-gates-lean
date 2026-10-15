import Proof.Hierarchy.CompetitorSameBucketLeftLoad

/-! One outer row obtains its cached left record from the actual advancing
gate packet, then executes the complete right-bucket scan and return. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketOuterBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request)
open CompetitorSameBucketPackets (word width)
open CompetitorSameBucketLeftLoad (cfg heads tapes)
open CompetitorSameBucketCandidate (State Fits)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem change_left (r : Request) (cap : ℕ) (coefficient : ℤ) (old new : Option KeyLoop.Record)
    (source out : List Bool) (ambient : Fin 41 → List Bool) (h : State r cap coefficient old source out ambient) :
    State r cap coefficient new source out (Function.update ambient 0 (ZeroPadding.pad cap (word r new))) := by
  constructor
  · constructor
    · exact (Function.update_of_ne (by decide : (36 : Fin 41)≠0) _ _).trans h.store.driver
    · exact (Function.update_of_ne (by decide : (37 : Fin 41)≠0) _ _).trans h.store.reset
    · intro i
      have hn : CompetitorSameBucketCandidate.workSlots i≠0 := by fin_cases i <;> decide
      rw [Function.update_of_ne hn]
      exact h.store.support i
  · intro i
    fin_cases i
    · exact Function.update_self ..
    all_goals
      rw [Function.update_of_ne (by decide)]
      exact h.fields _
  · exact (Function.update_of_ne (by decide : (38 : Fin 41)≠0) _ _).trans h.width
  · exact (Function.update_of_ne (by decide : (39 : Fin 41)≠0) _ _).trans h.source

noncomputable def native := TapeEmbedding.machine 2 CompetitorSameBucketInnerRow.machine
noncomputable def machine := Composition.machine CompetitorSameBucketLeftLoad.machine native
def budget (r : Request) (cap b : ℕ) := 2*cap+4*width r+16+CompetitorSameBucketInnerRow.budget r cap b

theorem embed {s : ℕ} (q : Fin s) (sourcePos outPos : ℕ) (ambient : Fin 41 → List Bool)
    (h b : ℕ) (source log : List Bool) :
    TapeEmbedding.config (![sourcePos,0] : Fin 2 → ℕ) ![source,log]
      (CompetitorSameBucketInnerRow.cfg q 0 outPos ambient h b)=cfg q sourcePos outPos ambient h b source log := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem native_run (r : Request) (cap sourcePos : ℕ) (coefficient : ℤ) (left : Option KeyLoop.Record)
    (xs : List (Option KeyLoop.Record)) (rightSuffix source out log : List Bool) (ambient : Fin 41 → List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap) (hl : Fits r left) (hv : ∀ a∈xs,Fits r a)
    (hstate : State r cap coefficient left (CompetitorSameBucketCandidate.words r xs++rightSuffix) out ambient) :
    ∃ b output,runFrom native (CompetitorSameBucketInnerRow.budget r cap xs.length)
        (cfg native.start sourcePos out.length ambient (H r) xs.length source log)=some b ∧
      b.steps≤CompetitorSameBucketInnerRow.budget r cap xs.length ∧
      b.final.heads=heads sourcePos (out++CompetitorSameBucketCandidate.emissions r coefficient left xs).length ∧
      b.final.tapes=tapes output (H r) xs.length source log ∧
      State r cap coefficient left (CompetitorSameBucketCandidate.words r xs++rightSuffix)
        (out++CompetitorSameBucketCandidate.emissions r coefficient left xs) output := by
  obtain ⟨base,output,hb,bs,bh,bt,bo⟩ := CompetitorSameBucketInnerRow.row_run r cap coefficient left xs [] rightSuffix out ambient
    hc hp hl hv (by simpa using hstate)
  have hr := TapeEmbedding.run_embed CompetitorSameBucketInnerRow.machine (![sourcePos,0] : Fin 2 → ℕ) ![source,log] _ _ base hb
  simp only [List.length_nil] at hr
  rw [embed] at hr
  have he : base.final=CompetitorSameBucketInnerRow.cfg base.final.control 0
      (out++CompetitorSameBucketCandidate.emissions r coefficient left xs).length output (H r) xs.length :=
    configuration_ext rfl bh bt
  refine ⟨TapeEmbedding.receipt (![sourcePos,0] : Fin 2 → ℕ) ![source,log] base,output,hr,bs,?_,?_,by simpa using bo⟩
  · change (TapeEmbedding.config _ _ base.final).heads=_
    rw [he,embed]
    rfl
  · change (TapeEmbedding.config _ _ base.final).tapes=_
    rw [he,embed]
    rfl

theorem body_run (r : Request) (cap : ℕ) (coefficient : ℤ) (old left : Option KeyLoop.Record)
    (xs : List (Option KeyLoop.Record)) (pre suffix rightSuffix out log : List Bool) (ambient : Fin 41 → List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap) (hl : Fits r left) (hv : ∀ a∈xs,Fits r a)
    (hlog : log.length≤cap)
    (hstate : State r cap coefficient old (CompetitorSameBucketCandidate.words r xs++rightSuffix) out ambient) :
    ∃ b output,runFrom machine (budget r cap xs.length)
        (cfg machine.start pre.length out.length ambient (H r) xs.length (pre++word r left++suffix) log)=some b ∧
      b.steps≤budget r cap xs.length ∧
      b.final.heads=heads (pre.length+width r) (out++CompetitorSameBucketCandidate.emissions r coefficient left xs).length ∧
      b.final.tapes=tapes output (H r) xs.length (pre++word r left++suffix) (List.replicate cap false) ∧
      State r cap coefficient left (CompetitorSameBucketCandidate.words r xs++rightSuffix)
        (out++CompetitorSameBucketCandidate.emissions r coefficient left xs) output := by
  have hw : 2*(word r left).length+4≤cap := by rw [CompetitorSameBucketPackets.word_length]; unfold width at *; omega
  have oldFit : (ambient 0).length≤cap := by
    have he := hstate.fields 0
    change ambient 0=ZeroPadding.pad cap (word r old) at he
    rw [he,ZeroPadding.pad_length,CompetitorSameBucketPackets.word_length]
    unfold width at *
    omega
  obtain ⟨prep,hp0,ph,pt,ps⟩ := CompetitorSameBucketLeftLoad.prepare_run cap (H r) xs.length out.length ambient pre
    (word r left) suffix log hstate.store.driver hstate.store.reset oldFit hlog
    (by rw [CompetitorSameBucketPackets.word_length]; exact hstate.width) hw
  obtain ⟨row,output,hr,rs,rh,rt,ro⟩ := native_run r cap (pre.length+(word r left).length) coefficient left xs rightSuffix
    (pre++word r left++suffix) out (List.replicate cap false) (Function.update ambient 0 (ZeroPadding.pad cap (word r left)))
    hc hp hl hv (change_left r cap coefficient old left _ out ambient hstate)
  have hi : Composition.restart prep.final native.start=
      cfg native.start (pre.length+(word r left).length) out.length (Function.update ambient 0 (ZeroPadding.pad cap (word r left)))
        (H r) xs.length (pre++word r left++suffix) (List.replicate cap false) := configuration_ext rfl ph pt
  rw [←hi] at hr
  have hall := Composition.run_join CompetitorSameBucketLeftLoad.machine native _ _ _ prep row hp0 hr
  have he : (2*cap+4*(word r left).length+15)+1+CompetitorSameBucketInnerRow.budget r cap xs.length=budget r cap xs.length := by
    rw [CompetitorSameBucketPackets.word_length]
    unfold budget
    omega
  rw [he] at hall
  refine ⟨Composition.joinedReceipt prep row,output,hall,?_,?_,rt,ro⟩
  · change prep.steps+1+row.steps≤budget r cap xs.length
    rw [←he]
    omega
  · change row.final.heads=_
    simpa only [CompetitorSameBucketPackets.word_length] using rh

end NearCubicWires.RepairOrdinary.CompetitorSameBucketOuterBody
