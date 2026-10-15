import Proof.Hierarchy.CompetitorSameBucketBucketPrepare

/-! Whole bucket: paid D-sized clear/copy followed by the actual B×B scan.
The original packet advances one bucket; only bounded scalar scratch is
cleared inside the square. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketBucketBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request)
open CompetitorSameBucketCandidate (State Fits words)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (d cap h b pos outPos : ℕ) (ambient : Fin 41 → List Bool) (source log : List Bool) : Configuration 50 s :=
  CompetitorSameBucketBucketPrepare.cfg q pos outPos (CompetitorSameBucketSquare.tapes ambient h b cap source) d h b log
noncomputable def native := TapeEmbedding.machine 4 CompetitorSameBucketSquare.machine
noncomputable def machine := Composition.machine CompetitorSameBucketBucketPrepare.machine native
def budget (r : Request) (d cap b : ℕ) :=
  CompetitorSameBucketBucketPrepare.budget d (H r) b+1+CompetitorSameBucketSquare.budget r cap b

theorem change_right (r : Request) (cap : ℕ) (coefficient : ℤ) (old : Option KeyLoop.Record)
    (source out next : List Bool) (ambient : Fin 41 → List Bool) (h : State r cap coefficient old source out ambient) :
    State r cap coefficient old next out (Function.update ambient 39 next) := by
  constructor
  · constructor
    · exact (Function.update_of_ne (by decide : (36 : Fin 41)≠39) _ _).trans h.store.driver
    · exact (Function.update_of_ne (by decide : (37 : Fin 41)≠39) _ _).trans h.store.reset
    · intro i
      have hn : CompetitorSameBucketCandidate.workSlots i≠39 := by fin_cases i <;> decide
      rw [Function.update_of_ne hn]
      exact h.store.support i
  · intro i
    have hn : CompetitorSameBucketCandidate.fixedSlots i≠39 := by fin_cases i <;> decide
    rw [Function.update_of_ne hn]
    exact h.fields i
  · exact (Function.update_of_ne (by decide : (38 : Fin 41)≠39) _ _).trans h.width
  · exact Function.update_self ..

theorem update_square (ambient : Fin 41 → List Bool) (h b cap : ℕ) (source bits : List Bool) :
    Function.update (CompetitorSameBucketSquare.tapes ambient h b cap source) 39 bits=
      CompetitorSameBucketSquare.tapes (Function.update ambient 39 bits) h b cap source := by
  funext i
  fin_cases i <;> simp [CompetitorSameBucketSquare.tapes,CompetitorSameBucketLeftLoad.tapes,Fin.addCases]

theorem embed {s : ℕ} (q : Fin s) (d cap h b pos outPos : ℕ) (ambient : Fin 41 → List Bool) (source log : List Bool) :
    TapeEmbedding.config (![0,0,1,0] : Fin 4 → ℕ)
      ![List.replicate d true,List.replicate (d+1) false,UnaryTemplate.tape ((4*h+1)*b),log]
      (CompetitorSameBucketSquare.cfg q pos outPos ambient h b cap source)=cfg q d cap h b pos outPos ambient source log := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem native_run (r : Request) (d cap : ℕ) (coefficient : ℤ) (old : Option KeyLoop.Record)
    (xs : List (Option KeyLoop.Record)) (pre suffix rightSuffix out log : List Bool) (ambient : Fin 41 → List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap) (hx : ∀ a∈xs,Fits r a)
    (hstate : State r cap coefficient old (words r xs++rightSuffix) out ambient) :
    ∃ b output,runFrom native (CompetitorSameBucketSquare.budget r cap xs.length)
        (cfg native.start d cap (H r) xs.length pre.length out.length ambient (pre++words r xs++suffix) log)=some b ∧
      b.steps≤CompetitorSameBucketSquare.budget r cap xs.length ∧
      b.final.heads=CompetitorSameBucketBucketPrepare.heads (pre.length+(words r xs).length)
        (out++CompetitorSameBucketOuterLoop.emissions r coefficient xs xs).length ∧
      b.final.tapes=(cfg native.start d cap (H r) xs.length (pre.length+(words r xs).length)
        (out++CompetitorSameBucketOuterLoop.emissions r coefficient xs xs).length output (pre++words r xs++suffix) log).tapes ∧
      State r cap coefficient (CompetitorSameBucketOuterLoop.last old xs) (words r xs++rightSuffix)
        (out++CompetitorSameBucketOuterLoop.emissions r coefficient xs xs) output := by
  obtain ⟨base,output,hb,bs,bh,bt,bo⟩ := CompetitorSameBucketSquare.square_run r cap coefficient old xs pre suffix rightSuffix out ambient hc hp hx hstate
  have hr := TapeEmbedding.run_embed CompetitorSameBucketSquare.machine (![0,0,1,0] : Fin 4 → ℕ)
    ![List.replicate d true,List.replicate (d+1) false,UnaryTemplate.tape ((4*H r+1)*xs.length),log] _ _ base hb
  rw [embed] at hr
  have he : base.final=CompetitorSameBucketSquare.cfg base.final.control (pre.length+(words r xs).length)
      (out++CompetitorSameBucketOuterLoop.emissions r coefficient xs xs).length output (H r) xs.length cap (pre++words r xs++suffix) :=
    configuration_ext rfl bh bt
  refine ⟨TapeEmbedding.receipt (![0,0,1,0] : Fin 4 → ℕ)
    ![List.replicate d true,List.replicate (d+1) false,UnaryTemplate.tape ((4*H r+1)*xs.length),log] base,output,hr,bs,?_,?_,bo⟩
  · change (TapeEmbedding.config _ _ base.final).heads=_
    rw [he,embed]
    rfl
  · change (TapeEmbedding.config _ _ base.final).tapes=_
    rw [he,embed]
    rfl

theorem body_run (r : Request) (d cap : ℕ) (coefficient : ℤ) (old : Option KeyLoop.Record)
    (xs : List (Option KeyLoop.Record)) (pre suffix oldRight out log : List Bool) (ambient : Fin 41 → List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap) (hx : ∀ a∈xs,Fits r a)
    (hd : 2*(words r xs).length+4≤d) (targetFit : (ambient 39).length≤d) (logFit : log.length≤d)
    (hstate : State r cap coefficient old oldRight out ambient) :
    ∃ b output,runFrom machine (budget r d cap xs.length)
        (cfg machine.start d cap (H r) xs.length pre.length out.length ambient (pre++words r xs++suffix) log)=some b ∧
      b.steps≤budget r d cap xs.length ∧
      b.final.heads=CompetitorSameBucketBucketPrepare.heads (pre.length+(words r xs).length)
        (out++CompetitorSameBucketOuterLoop.emissions r coefficient xs xs).length ∧
      b.final.tapes=(cfg machine.start d cap (H r) xs.length (pre.length+(words r xs).length)
        (out++CompetitorSameBucketOuterLoop.emissions r coefficient xs xs).length output
        (pre++words r xs++suffix) (List.replicate d false)).tapes ∧
      State r cap coefficient (CompetitorSameBucketOuterLoop.last old xs) (ZeroPadding.pad d (words r xs))
        (out++CompetitorSameBucketOuterLoop.emissions r coefficient xs xs) output ∧ (output 39).length≤d := by
  have hlen : (words r xs).length=(4*H r+1)*xs.length := by
    rw [CompetitorSameBucketCandidate.words_length]
    unfold CompetitorSameBucketPackets.width
    ring
  obtain ⟨prep,hp0,ph,pt,ps⟩ := CompetitorSameBucketBucketPrepare.prepare_run d (H r) xs.length out.length
    (CompetitorSameBucketSquare.tapes ambient (H r) xs.length cap (pre++words r xs++suffix)) pre (words r xs) suffix log
    rfl rfl rfl targetFit logFit hlen hd
  rw [update_square] at pt
  have state := change_right r cap coefficient old oldRight out (ZeroPadding.pad d (words r xs)) ambient hstate
  obtain ⟨square,output,hr,rs,rh,rt,ro⟩ := native_run r d cap coefficient old xs pre suffix
    (List.replicate (d-(words r xs).length) false) out (List.replicate d false)
    (Function.update ambient 39 (ZeroPadding.pad d (words r xs))) hc hp hx state
  have hi : Composition.restart prep.final native.start=
      cfg native.start d cap (H r) xs.length pre.length out.length
        (Function.update ambient 39 (ZeroPadding.pad d (words r xs))) (pre++words r xs++suffix) (List.replicate d false) :=
    configuration_ext rfl ph pt
  rw [←hi] at hr
  have hall := Composition.run_join CompetitorSameBucketBucketPrepare.machine native _ _ _ prep square hp0 hr
  refine ⟨Composition.joinedReceipt prep square,output,hall,?_,rh,rt,ro,?_⟩
  · change prep.steps+1+square.steps≤budget r d cap xs.length
    unfold budget
    omega
  · rw [ro.source]
    change (ZeroPadding.pad d (words r xs)).length≤d
    rw [ZeroPadding.pad_length]
    omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketBucketBody
