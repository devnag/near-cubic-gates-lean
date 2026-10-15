import Proof.Hierarchy.CompetitorSameBucketCandidateWorkspace

/-! The next right-hand record is physically copied from the advancing
bucket cursor after scalar erasure. Cached left and contribution cursors
are excluded from every local reset. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketCandidate
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def loadSlots : Fin 4 → Fin 41 := ![38,39,13,40]
theorem load_injective : Function.Injective loadSlots := by decide
noncomputable def load := RecoveryFocus.machine loadSlots CompetitorSameBucketRecordCopy.machine
noncomputable def loaded (cap : ℕ) (bits : List Bool) (ambient : Fin 41 → List Bool) :=
  Function.update (clean cap ambient) 13 (ZeroPadding.pad cap bits)

theorem Store.loaded {cap : ℕ} {ambient : Fin 41 → List Bool} (h : Store cap ambient)
    (bits : List Bool) (hb : bits.length≤cap) : Store cap (loaded cap bits ambient) := by
  exact h.clean.update_work 11 (ZeroPadding.pad cap bits) (by simp [ZeroPadding.pad_length,hb])

theorem load_output {s : ℕ} (q : Fin s) (cap po : ℕ) (pre bits suffix : List Bool) (ambient : Fin 41 → List Bool)
    (hin : ∀ i,clean cap ambient (loadSlots i)=
      (![UnaryTemplate.tape bits.length,pre++bits++suffix,List.replicate cap false,List.replicate cap false] : Fin 4 → List Bool) i) :
    RecoveryFocus.config loadSlots (heads pre.length po) (clean cap ambient)
      (⟨q,![1,pre.length+bits.length,0,0],![UnaryTemplate.tape bits.length,pre++bits++suffix,
        ZeroPadding.pad cap bits,List.replicate cap false]⟩ : Configuration 4 s)=
      cfg q (pre.length+bits.length) po (loaded cap bits ambient) := by
  have pick13 : RecoveryFocus.pick loadSlots 13=some 2 := RecoveryFocus.pick_slot loadSlots load_injective 2
  have pick39 : RecoveryFocus.pick loadSlots 39=some 1 := RecoveryFocus.pick_slot loadSlots load_injective 1
  apply configuration_ext
  · rfl
  · funext i
    cases he : RecoveryFocus.pick loadSlots i with
    | none =>
      have hn : i≠39 := by intro hi; subst i; rw [pick39] at he; contradiction
      simp [RecoveryFocus.config,he,cfg,heads,hn]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick loadSlots he
      simp only [RecoveryFocus.config,he]
      rw [←hj]
      fin_cases j <;> simp [cfg,heads,loadSlots]
  · funext i
    cases he : RecoveryFocus.pick loadSlots i with
    | none =>
      have hn : i≠13 := by intro hi; subst i; rw [pick13] at he; contradiction
      simp [RecoveryFocus.config,he,cfg,loaded,hn]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick loadSlots he
      simp only [RecoveryFocus.config,he]
      rw [←hj]
      fin_cases j
      · simpa [cfg,loaded,loadSlots] using (hin 0).symm
      · simpa [cfg,loaded,loadSlots] using (hin 1).symm
      · simp [cfg,loaded,loadSlots]
      · simpa [cfg,loaded,loadSlots] using (hin 3).symm

theorem load_run (cap po : ℕ) (pre bits suffix : List Bool) (ambient : Fin 41 → List Bool)
    (width : ambient 38=UnaryTemplate.tape bits.length) (source : ambient 39=pre++bits++suffix)
    (hc : 2*bits.length+4≤cap) :
    ∃ r,runFrom load (CompetitorSameBucketRecordCopy.budget bits.length)
        (cfg load.start pre.length po (clean cap ambient))=some r ∧
      r.final.heads=heads (pre.length+bits.length) po ∧ r.final.tapes=loaded cap bits ambient ∧
      r.steps=CompetitorSameBucketRecordCopy.budget bits.length := by
  have hin : ∀ i,clean cap ambient (loadSlots i)=
      (![UnaryTemplate.tape bits.length,pre++bits++suffix,List.replicate cap false,List.replicate cap false] : Fin 4 → List Bool) i := by
    intro i
    fin_cases i
    · exact (clean_other cap ambient 38 (by decide)).trans width
    · exact (clean_other cap ambient 39 (by decide)).trans source
    · exact clean_work cap ambient 11
    · exact clean_work cap ambient 29
  obtain ⟨base,hb,bh,bt,bs⟩ := CompetitorSameBucketRecordCopy.padded_run cap pre bits suffix hc
  have hi : RecoveryFocus.config loadSlots (heads pre.length po) (clean cap ambient)
      (CompetitorSameBucketRecordCopy.paddedInput cap pre bits suffix)=cfg load.start pre.length po (clean cap ambient) := by
    apply WilliamsSourceCrop.focus_same loadSlots (cfg load.start pre.length po (clean cap ambient))
      (CompetitorSameBucketRecordCopy.paddedInput cap pre bits suffix)
    · intro i
      rw [CompetitorSameBucketRecordCopy.padded_heads]
      fin_cases i <;> rfl
    · intro i
      rw [CompetitorSameBucketRecordCopy.padded_tapes]
      exact hin i
  obtain ⟨actual,hr,hf,hs⟩ := RecoveryFocus.run_config loadSlots load_injective CompetitorSameBucketRecordCopy.machine
    (heads pre.length po) (clean cap ambient) _ _ base hb
  rw [hi] at hr
  have he : base.final=⟨base.final.control,![1,pre.length+bits.length,0,0],
      ![UnaryTemplate.tape bits.length,pre++bits++suffix,ZeroPadding.pad cap bits,List.replicate cap false]⟩ :=
    configuration_ext rfl bh bt
  refine ⟨actual,hr,?_,?_,hs.trans bs⟩
  · rw [hf,he,load_output _ cap po pre bits suffix ambient hin]
    rfl
  · rw [hf,he,load_output _ cap po pre bits suffix ambient hin]
    rfl

noncomputable def prepare := Composition.machine clear load

theorem prepare_run (cap po : ℕ) (pre bits suffix : List Bool) (ambient : Fin 41 → List Bool)
    (hstore : Store cap ambient) (width : ambient 38=UnaryTemplate.tape bits.length)
    (source : ambient 39=pre++bits++suffix) (hc : 2*bits.length+4≤cap) :
    ∃ r,runFrom prepare (2*cap+4*bits.length+15) (cfg prepare.start pre.length po ambient)=some r ∧
      r.final.heads=heads (pre.length+bits.length) po ∧ r.final.tapes=loaded cap bits ambient ∧
      r.steps=2*cap+4*bits.length+15 := by
  obtain ⟨r0,h0,hh0,ht0,hs0⟩ := clear_run cap pre.length po ambient hstore
  obtain ⟨r1,h1,hh1,ht1,hs1⟩ := load_run cap po pre bits suffix ambient width source hc
  have hi : Composition.restart r0.final load.start=cfg load.start pre.length po (clean cap ambient) :=
    configuration_ext rfl hh0 ht0
  rw [←hi] at h1
  have hall := Composition.run_join clear load _ _ _ r0 r1 h0 h1
  have he : (2*cap+4)+1+CompetitorSameBucketRecordCopy.budget bits.length=2*cap+4*bits.length+15 := by
    unfold CompetitorSameBucketRecordCopy.budget
    omega
  rw [he] at hall
  refine ⟨Composition.joinedReceipt r0 r1,hall,hh1,ht1,?_⟩
  change r0.steps+1+r1.steps=_
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketCandidate
