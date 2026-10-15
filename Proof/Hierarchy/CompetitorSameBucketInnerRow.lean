import Proof.Hierarchy.CompetitorSameBucketCandidateLoop

/-! One complete inner row scans the right bucket once and then physically
returns its cursor using the retained H and B templates. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketInnerRow
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos out : ℕ) : Fin 43 → ℕ := fun i =>
  if i=34 then out else if i=38 ∨ i=41 then 1 else if i=39 then pos else 0
def capacities (b : ℕ) : Fin 43 → ℕ := fun i => if i=41 then b+2 else 0
def tapes (ambient : Fin 41 → List Bool) (h b : ℕ) : Fin 43 → List Bool :=
  Fin.addCases (m := 41) (n := 2) (motive := fun _ => List Bool) ambient ![UnaryTemplate.tape b,UnaryTemplate.tape h]
def cfg {s : ℕ} (q : Fin s) (pos out : ℕ) (ambient : Fin 41 → List Bool) (h b : ℕ) : Configuration 43 s :=
  ⟨q,heads pos out,tapes ambient h b⟩
noncomputable def first := TapeEmbedding.machine 1 CompetitorSameBucketCandidate.loop
def reverseSlots : Fin 3 → Fin 43 := ![39,42,41]
theorem reverse_injective : Function.Injective reverseSlots := by decide
noncomputable def last := RecoveryFocus.machine reverseSlots MatrixRankRowReverse.machine
noncomputable def machine := Composition.machine first last
def budget (r : Request) (cap b : ℕ) := CompetitorSameBucketCandidate.loopBudget r cap b+1+MatrixRankRowReverse.budget (H r) b

theorem embed_heads (phase : Fin 5) (pos out b : ℕ) (ambient : Fin 41 → List Bool) (h : ℕ) :
    (ZeroPadding.config (capacities b) (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ => UnaryTemplate.tape h)
      (RepeatMachine.cfg phase (CompetitorSameBucketCandidate.cfg CompetitorSameBucketCandidate.body.start pos out ambient) b 1))).heads=heads pos out := by
  funext i
  fin_cases i <;> rfl
theorem embed_tapes (phase : Fin 5) (pos out b : ℕ) (ambient : Fin 41 → List Bool) (h : ℕ) :
    (ZeroPadding.config (capacities b) (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ => UnaryTemplate.tape h)
      (RepeatMachine.cfg phase (CompetitorSameBucketCandidate.cfg CompetitorSameBucketCandidate.body.start pos out ambient) b 1))).tapes=tapes ambient h b := by
  funext i
  fin_cases i <;> simp [ZeroPadding.config,capacities,TapeEmbedding.config,RepeatMachine.cfg,controlConfig,
    CompetitorSameBucketCandidate.cfg,tapes,Fin.addCases,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem forward_run (r : Request) (cap : ℕ) (coefficient : ℤ) (left : Option KeyLoop.Record)
    (xs : List (Option KeyLoop.Record)) (pre suffix out : List Bool) (ambient : Fin 41 → List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap) (hl : CompetitorSameBucketCandidate.Fits r left) (hv : ∀ a∈xs,CompetitorSameBucketCandidate.Fits r a)
    (hstate : CompetitorSameBucketCandidate.State r cap coefficient left (pre++CompetitorSameBucketCandidate.words r xs++suffix) out ambient) :
    ∃ b output,runFrom first (CompetitorSameBucketCandidate.loopBudget r cap xs.length)
        (cfg first.start pre.length out.length ambient (H r) xs.length)=some b ∧
      b.steps≤CompetitorSameBucketCandidate.loopBudget r cap xs.length ∧
      b.final.heads=heads (pre.length+(CompetitorSameBucketCandidate.words r xs).length) (out++CompetitorSameBucketCandidate.emissions r coefficient left xs).length ∧
      b.final.tapes=tapes output (H r) xs.length ∧
      CompetitorSameBucketCandidate.State r cap coefficient left (pre++CompetitorSameBucketCandidate.words r xs++suffix) (out++CompetitorSameBucketCandidate.emissions r coefficient left xs) output := by
  obtain ⟨base,hout,hb,bs,bf,bo⟩ := CompetitorSameBucketCandidate.loop_run r cap coefficient left xs pre suffix out ambient hc hp hl hv hstate
  have run := TapeEmbedding.run_embed CompetitorSameBucketCandidate.loop (fun _ : Fin 1 => 0) (fun _ => UnaryTemplate.tape (H r)) _ _ base hb
  obtain ⟨actual,padded,af,ast,_⟩ := ZeroPadding.run_config first (capacities xs.length) _ _ _ run
  have hi : ZeroPadding.config (capacities xs.length) (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ => UnaryTemplate.tape (H r))
      (RepeatMachine.cfg 0 (CompetitorSameBucketCandidate.cfg CompetitorSameBucketCandidate.body.start pre.length out.length ambient) xs.length 1))=
      cfg first.start pre.length out.length ambient (H r) xs.length :=
    configuration_ext rfl (embed_heads 0 pre.length out.length xs.length ambient (H r)) (embed_tapes 0 pre.length out.length xs.length ambient (H r))
  rw [hi] at padded
  refine ⟨actual,hout,padded,ast.trans_le bs,?_,?_,bo⟩
  · rw [af]
    change (ZeroPadding.config _ (TapeEmbedding.config _ _ base.final)).heads=_
    rw [bf]
    exact embed_heads 3 (pre.length+(CompetitorSameBucketCandidate.words r xs).length) (out++CompetitorSameBucketCandidate.emissions r coefficient left xs).length xs.length hout (H r)
  · rw [af]
    change (ZeroPadding.config _ (TapeEmbedding.config _ _ base.final)).tapes=_
    rw [bf]
    exact embed_tapes 3 (pre.length+(CompetitorSameBucketCandidate.words r xs).length) (out++CompetitorSameBucketCandidate.emissions r coefficient left xs).length xs.length hout (H r)

theorem reverse_run (h b pos out : ℕ) (ambient : Fin 41 → List Bool) :
    ∃ r,runFrom last (MatrixRankRowReverse.budget h b) (cfg last.start pos out ambient h b)=some r ∧
      r.final.heads=heads (pos-b*(4*h+1)) out ∧ r.final.tapes=tapes ambient h b ∧ r.steps≤MatrixRankRowReverse.budget h b := by
  obtain ⟨base,hb,bs,bf⟩ := MatrixRankRowReverse.row_run (ambient 39) h b pos
  let entry := cfg last.start pos out ambient h b
  have hi : RecoveryFocus.config reverseSlots entry.heads entry.tapes (MatrixRankRowReverse.cfg 0 (ambient 39) h b pos)=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [MatrixRankRowReverse.cfg_heads]
      fin_cases i <;> rfl
    · intro i
      rw [MatrixRankRowReverse.cfg_tapes]
      fin_cases i <;> rfl
  obtain ⟨actual,hr,hf,hs⟩ := RecoveryFocus.run_config reverseSlots reverse_injective MatrixRankRowReverse.machine
    entry.heads entry.tapes _ _ base hb
  rw [hi] at hr
  have pick39 : RecoveryFocus.pick reverseSlots 39=some 0 := RecoveryFocus.pick_slot reverseSlots reverse_injective 0
  refine ⟨actual,hr,?_,?_,hs.trans_le bs⟩
  · rw [hf,bf]
    funext i
    cases he : RecoveryFocus.pick reverseSlots i with
    | none =>
      have hn : i≠39 := by intro hh; subst i; rw [pick39] at he; contradiction
      simp [RecoveryFocus.config,he,entry,cfg,heads,hn]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick reverseSlots he
      simp only [RecoveryFocus.config,he]
      rw [←hj]
      fin_cases j <;> simp [MatrixRankRowReverse.cfg_heads,reverseSlots,heads,MatrixRankFieldReverse.distance]
  · rw [hf,bf]
    funext i
    cases he : RecoveryFocus.pick reverseSlots i with
    | none => simp [RecoveryFocus.config,he,entry,cfg]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick reverseSlots he
      simp only [RecoveryFocus.config,he]
      rw [←hj]
      fin_cases j <;> simp [MatrixRankRowReverse.cfg_tapes,reverseSlots,tapes,Fin.addCases]

theorem row_run (r : Request) (cap : ℕ) (coefficient : ℤ) (left : Option KeyLoop.Record)
    (xs : List (Option KeyLoop.Record)) (pre suffix out : List Bool) (ambient : Fin 41 → List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap) (hl : CompetitorSameBucketCandidate.Fits r left) (hv : ∀ a∈xs,CompetitorSameBucketCandidate.Fits r a)
    (hstate : CompetitorSameBucketCandidate.State r cap coefficient left (pre++CompetitorSameBucketCandidate.words r xs++suffix) out ambient) :
    ∃ b output,runFrom machine (budget r cap xs.length)
        (cfg machine.start pre.length out.length ambient (H r) xs.length)=some b ∧
      b.steps≤budget r cap xs.length ∧
      b.final.heads=heads pre.length (out++CompetitorSameBucketCandidate.emissions r coefficient left xs).length ∧
      b.final.tapes=tapes output (H r) xs.length ∧
      CompetitorSameBucketCandidate.State r cap coefficient left (pre++CompetitorSameBucketCandidate.words r xs++suffix) (out++CompetitorSameBucketCandidate.emissions r coefficient left xs) output := by
  obtain ⟨forward,output,hf,fs,fh,ft,fo⟩ := forward_run r cap coefficient left xs pre suffix out ambient hc hp hl hv hstate
  obtain ⟨back,hb,bh,bt,bs⟩ := reverse_run (H r) xs.length (pre.length+(CompetitorSameBucketCandidate.words r xs).length)
    (out++CompetitorSameBucketCandidate.emissions r coefficient left xs).length output
  have hi : Composition.restart forward.final last.start=
      cfg last.start (pre.length+(CompetitorSameBucketCandidate.words r xs).length) (out++CompetitorSameBucketCandidate.emissions r coefficient left xs).length output (H r) xs.length :=
    configuration_ext rfl fh ft
  rw [←hi] at hb
  have hall := Composition.run_join first last _ _ _ forward back hf hb
  have pos : pre.length+(CompetitorSameBucketCandidate.words r xs).length-xs.length*(4*H r+1)=pre.length := by
    rw [CompetitorSameBucketCandidate.words_length]
    unfold CompetitorSameBucketPackets.width
    omega
  rw [pos] at bh
  refine ⟨Composition.joinedReceipt forward back,output,hall,?_,bh,bt,fo⟩
  change forward.steps+1+back.steps≤budget r cap xs.length
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketInnerRow
