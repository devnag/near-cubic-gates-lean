import Proof.Hierarchy.CompetitorSameBucketOuterLoop

/-! Literal supplied-bucket B×B execution with both actual B templates.
The source packet advances by B records and the copied right bucket returns
to zero. All scalar and loop work is included in the quadratic pair ledger. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketSquare
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request)
open RepairSource.VerifierDecoding
open CompetitorSameBucketCandidate (State Fits words)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos outPos : ℕ) : Fin 46 → ℕ :=
  Fin.addCases (m := 45) (n := 1) (motive := fun _ => ℕ) (CompetitorSameBucketLeftLoad.heads pos outPos) (fun _ => 1)
def tapes (ambient : Fin 41 → List Bool) (h b cap : ℕ) (source : List Bool) : Fin 46 → List Bool :=
  Fin.addCases (m := 45) (n := 1) (motive := fun _ => List Bool)
    (CompetitorSameBucketLeftLoad.tapes ambient h b source (List.replicate cap false)) (fun _ => UnaryTemplate.tape b)
def cfg {s : ℕ} (q : Fin s) (pos outPos : ℕ) (ambient : Fin 41 → List Bool) (h b cap : ℕ) (source : List Bool) : Configuration 46 s :=
  ⟨q,heads pos outPos,tapes ambient h b cap source⟩
def capacities (b : ℕ) : Fin 46 → ℕ := fun i => if i=45 then b+2 else 0
noncomputable def machine := CompetitorSameBucketOuterLoop.machine
def budget (r : Request) (cap b : ℕ) := CompetitorSameBucketOuterLoop.budget r cap b b

theorem padded_heads (phase : Fin 5) (pos outPos : ℕ) (ambient : Fin 41 → List Bool) (h b cap : ℕ) (source : List Bool) :
    (ZeroPadding.config (capacities b) (RepeatMachine.cfg phase
      (CompetitorSameBucketLeftLoad.cfg CompetitorSameBucketOuterBody.machine.start pos outPos ambient h b source
        (List.replicate cap false)) b 1)).heads=heads pos outPos := by
  funext i; fin_cases i <;> rfl
theorem padded_tapes (phase : Fin 5) (pos outPos : ℕ) (ambient : Fin 41 → List Bool) (h b cap : ℕ) (source : List Bool) :
    (ZeroPadding.config (capacities b) (RepeatMachine.cfg phase
      (CompetitorSameBucketLeftLoad.cfg CompetitorSameBucketOuterBody.machine.start pos outPos ambient h b source
        (List.replicate cap false)) b 1)).tapes=tapes ambient h b cap source := by
  funext i
  fin_cases i <;> simp [ZeroPadding.config,capacities,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    CompetitorSameBucketLeftLoad.cfg,tapes,Fin.addCases,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem square_run (r : Request) (cap : ℕ) (coefficient : ℤ) (old : Option KeyLoop.Record)
    (xs : List (Option KeyLoop.Record)) (pre suffix rightSuffix out : List Bool) (ambient : Fin 41 → List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap) (hx : ∀ a∈xs,Fits r a)
    (hstate : State r cap coefficient old (words r xs++rightSuffix) out ambient) :
    ∃ b output,runFrom machine (budget r cap xs.length)
        (cfg machine.start pre.length out.length ambient (H r) xs.length cap (pre++words r xs++suffix))=some b ∧
      b.steps≤budget r cap xs.length ∧
      b.final.heads=heads (pre.length+(words r xs).length) (out++CompetitorSameBucketOuterLoop.emissions r coefficient xs xs).length ∧
      b.final.tapes=tapes output (H r) xs.length cap (pre++words r xs++suffix) ∧
      State r cap coefficient (CompetitorSameBucketOuterLoop.last old xs) (words r xs++rightSuffix)
        (out++CompetitorSameBucketOuterLoop.emissions r coefficient xs xs) output := by
  obtain ⟨base,output,hb,bs,bf,bo⟩ := CompetitorSameBucketOuterLoop.loop_run r cap coefficient old xs xs pre suffix rightSuffix out ambient hc hp hx hx hstate
  obtain ⟨actual,ha,hf,hs,_⟩ := ZeroPadding.run_config machine (capacities xs.length) _ _ base hb
  have hi : ZeroPadding.config (capacities xs.length) (RepeatMachine.cfg 0
      (CompetitorSameBucketLeftLoad.cfg CompetitorSameBucketOuterBody.machine.start pre.length out.length ambient (H r) xs.length
        (pre++words r xs++suffix) (List.replicate cap false)) xs.length 1)=
      cfg machine.start pre.length out.length ambient (H r) xs.length cap (pre++words r xs++suffix) :=
    configuration_ext rfl (padded_heads 0 pre.length out.length ambient (H r) xs.length cap _) (padded_tapes 0 pre.length out.length ambient (H r) xs.length cap _)
  rw [hi] at ha
  refine ⟨actual,output,ha,hs.trans_le bs,?_,?_,bo⟩
  · rw [hf,bf]
    exact padded_heads 3 _ _ output (H r) xs.length cap _
  · rw [hf,bf]
    exact padded_tapes 3 _ _ output (H r) xs.length cap _

theorem budget_eq (r : Request) (cap b : ℕ) :
    budget r cap b=b^2*(2*cap+121*H r+32*r.M+4*r.p+162)+b*(2*cap+16*H r+30)+3 := by
  unfold budget CompetitorSameBucketOuterLoop.budget CompetitorSameBucketOuterBody.budget CompetitorSameBucketInnerRow.budget
    CompetitorSameBucketCandidate.loopBudget CompetitorSameBucketCandidate.budget
  rw [CompetitorSameBucketPairEmit.budget_eq]
  unfold MatrixRankRowReverse.budget MatrixRankFieldReverse.budget CompetitorSameBucketPackets.width H
  ring

theorem budget_bound (r : Request) (cap b : ℕ) (hb : 1≤b) :
    budget r cap b≤400*b^2*(cap+H r+r.M+r.p+1) := by
  rw [budget_eq]
  have hB : b≤b^2 := by nlinarith
  have hB1 : 1≤b^2 := by nlinarith
  have linear := Nat.mul_le_mul_right (2*cap+16*H r+30) hB
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorSameBucketSquare
