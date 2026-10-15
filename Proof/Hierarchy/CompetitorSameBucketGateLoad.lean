import Proof.Hierarchy.CompetitorSameBucketStreamLoad

/-! Execute both gate inputs from the global streams. The local packet is
cleared with D and the coefficient with C, each once per gate. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGateLoad
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def core (r : Request) (cap : ℕ) (ambient : Fin 41 → List Bool) (packet : List Bool) : Fin 51 → List Bool :=
  Fin.addCases (m := 50) (n := 1) (motive := fun _ => List Bool)
    (CompetitorSameBucketBucketBody.cfg CompetitorSameBucketBucketBody.machine.start (MatrixScoreReusableRanks.D r) cap (H r)
      (r.bucketSize+1) 0 0 ambient packet (List.replicate (MatrixScoreReusableRanks.D r) false)).tapes
    (fun _ => UnaryTemplate.tape r.Buckets)
noncomputable def tapes (r : Request) (cap : ℕ) (ambient : Fin 41 → List Bool)
    (packet rankSource coefficientSource rankLog coefficientLog : List Bool) : Fin 55 → List Bool :=
  Fin.addCases (m := 51) (n := 4) (motive := fun _ => List Bool) (core r cap ambient packet)
    ![rankSource,coefficientSource,rankLog,coefficientLog]
def heads (rankPos coefficientPos outPos : ℕ) : Fin 55 → ℕ :=
  Fin.addCases (m := 51) (n := 4) (motive := fun _ => ℕ) (CompetitorSameBucketGateScan.heads 0 outPos)
    ![rankPos,coefficientPos,0,0]
noncomputable def cfg {s : ℕ} (q : Fin s) (r : Request) (cap rankPos coefficientPos outPos : ℕ) (ambient : Fin 41 → List Bool)
    (packet rankSource coefficientSource rankLog coefficientLog : List Bool) : Configuration 55 s :=
  ⟨q,heads rankPos coefficientPos outPos,tapes r cap ambient packet rankSource coefficientSource rankLog coefficientLog⟩
def packetSlots : Fin 5 → Fin 55 := ![51,43,53,46,47]
def coefficientSlots : Fin 5 → Fin 55 := ![52,31,54,36,37]
theorem packet_injective : Function.Injective packetSlots := by decide
theorem coefficient_injective : Function.Injective coefficientSlots := by decide
noncomputable def first := RecoveryFocus.machine packetSlots CompetitorSameBucketStreamLoad.packet
noncomputable def last := RecoveryFocus.machine coefficientSlots CompetitorSameBucketStreamLoad.coefficient
noncomputable def machine := Composition.machine first last

theorem packet_pick (i : Fin 55) : RecoveryFocus.pick packetSlots i=
    (if i=51 then some 0 else if i=43 then some 1 else if i=53 then some 2 else if i=46 then some 3 else if i=47 then some 4 else none) := by
  classical
  by_cases h51 : i=51
  · subst i; exact RecoveryFocus.pick_slot packetSlots packet_injective 0
  by_cases h43 : i=43
  · subst i; exact RecoveryFocus.pick_slot packetSlots packet_injective 1
  by_cases h53 : i=53
  · subst i; exact RecoveryFocus.pick_slot packetSlots packet_injective 2
  by_cases h46 : i=46
  · subst i; exact RecoveryFocus.pick_slot packetSlots packet_injective 3
  by_cases h47 : i=47
  · subst i; exact RecoveryFocus.pick_slot packetSlots packet_injective 4
  simp only [h51,h43,h53,h46,h47,ite_false]
  unfold RecoveryFocus.pick
  apply dif_neg
  rintro ⟨j,hj⟩
  fin_cases j <;> simp_all [packetSlots]
theorem coefficient_pick (i : Fin 55) : RecoveryFocus.pick coefficientSlots i=
    (if i=52 then some 0 else if i=31 then some 1 else if i=54 then some 2 else if i=36 then some 3 else if i=37 then some 4 else none) := by
  classical
  by_cases h52 : i=52
  · subst i; exact RecoveryFocus.pick_slot coefficientSlots coefficient_injective 0
  by_cases h31 : i=31
  · subst i; exact RecoveryFocus.pick_slot coefficientSlots coefficient_injective 1
  by_cases h54 : i=54
  · subst i; exact RecoveryFocus.pick_slot coefficientSlots coefficient_injective 2
  by_cases h36 : i=36
  · subst i; exact RecoveryFocus.pick_slot coefficientSlots coefficient_injective 3
  by_cases h37 : i=37
  · subst i; exact RecoveryFocus.pick_slot coefficientSlots coefficient_injective 4
  simp only [h52,h31,h54,h36,h37,ite_false]
  unfold RecoveryFocus.pick
  apply dif_neg
  rintro ⟨j,hj⟩
  fin_cases j <;> simp_all [coefficientSlots]

noncomputable def packetBudget (r : Request) (gate : Fin r.Gates) :=
  2*MatrixScoreReusableRanks.D r+MatrixRankPacketLoad.budget (MatrixBatchRankedGate.rankWords r gate)+5
def coefficientBudget (cap : ℕ) (bits : List Bool) := 2*cap+CompetitorSameBucketCoefficientLoad.budget bits+5

theorem packet_run (r : Request) (cap coefficientPos outPos : ℕ) (gate : Fin r.Gates)
    (ambient : Fin 41 → List Bool) (pre suffix packet coefficientSource rankLog coefficientLog : List Bool)
    (ht : packet.length≤MatrixScoreReusableRanks.D r) (hl : rankLog.length≤MatrixScoreReusableRanks.D r) :
    ∃ actual,runFrom first (packetBudget r gate)
        (cfg first.start r cap pre.length coefficientPos outPos ambient packet
          (pre++MatrixScoreRawRanks.output r gate++suffix) coefficientSource rankLog coefficientLog)=some actual ∧
      actual.final.heads=heads (pre.length+(MatrixScoreRawRanks.output r gate).length) coefficientPos outPos ∧
      actual.final.tapes=tapes r cap ambient (CompetitorSameBucketGateScan.source r gate)
        (pre++MatrixScoreRawRanks.output r gate++suffix) coefficientSource (List.replicate (MatrixScoreReusableRanks.D r) false) coefficientLog ∧
      actual.steps≤packetBudget r gate := by
  obtain ⟨base,hb,bh,bt,bs⟩ := CompetitorSameBucketStreamLoad.packet_run (MatrixScoreReusableRanks.D r)
    (MatrixBatchRankedGate.rankWords r gate) pre suffix packet rankLog ht hl
    (MatrixBatchRankedGate.words_nonempty r gate) (MatrixBatchRankedGate.packet_fits r gate)
  rw [MatrixBatchRankedGate.stream_eq] at hb bh bt
  let entry := cfg first.start r cap pre.length coefficientPos outPos ambient packet
    (pre++MatrixScoreRawRanks.output r gate++suffix) coefficientSource rankLog coefficientLog
  have hi : RecoveryFocus.config packetSlots entry.heads entry.tapes
      (CompetitorSameBucketStreamLoad.cfg CompetitorSameBucketStreamLoad.packet.start (MatrixScoreReusableRanks.D r)
        pre.length (pre++MatrixScoreRawRanks.output r gate++suffix) packet rankLog)=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
  obtain ⟨actual,ha,hf,hs⟩ := RecoveryFocus.run_config packetSlots packet_injective CompetitorSameBucketStreamLoad.packet
    entry.heads entry.tapes _ _ base hb
  rw [hi] at ha
  refine ⟨actual,ha,?_,?_,hs.trans_le bs⟩
  · rw [hf]
    funext i
    simp only [RecoveryFocus.config,packet_pick,bh]
    fin_cases i <;> simp [entry,cfg,heads,CompetitorSameBucketGateScan.heads,CompetitorSameBucketBucketPrepare.heads,Fin.addCases]
  · rw [hf]
    funext i
    simp only [RecoveryFocus.config,packet_pick,bt]
    fin_cases i <;> simp [entry,cfg,tapes,core,CompetitorSameBucketStreamLoad.cfg,CompetitorSameBucketGateScan.source,
      CompetitorSameBucketBucketBody.cfg,CompetitorSameBucketBucketPrepare.cfg,CompetitorSameBucketSquare.tapes,
      CompetitorSameBucketLeftLoad.tapes,CompetitorSameBucketBucketPrepare.tapes,Fin.addCases]

theorem coefficient_run (r : Request) (cap rankPos outPos : ℕ) (ambient : Fin 41 → List Bool)
    (bits pre suffix packet rankSource rankLog coefficientLog : List Bool)
    (driver : ambient 36=List.replicate cap true) (reset : ambient 37=List.replicate (cap+1) false)
    (ht : (ambient 31).length≤cap) (hl : coefficientLog.length≤cap) (hc : 2*bits.length+1≤cap) :
    ∃ actual,runFrom last (coefficientBudget cap bits)
        (cfg last.start r cap rankPos pre.length outPos ambient packet rankSource
          (pre++frame bits++suffix) rankLog coefficientLog)=some actual ∧
      actual.final.heads=heads rankPos (pre.length+(frame bits).length) outPos ∧
      actual.final.tapes=tapes r cap (Function.update ambient 31 (ZeroPadding.pad cap (frame bits))) packet rankSource
        (pre++frame bits++suffix) rankLog (List.replicate cap false) ∧
      actual.steps≤coefficientBudget cap bits := by
  obtain ⟨base,hb,bh,bt,bs⟩ := CompetitorSameBucketStreamLoad.coefficient_run cap bits pre suffix (ambient 31) coefficientLog ht hl hc
  let entry := cfg last.start r cap rankPos pre.length outPos ambient packet rankSource (pre++frame bits++suffix) rankLog coefficientLog
  have hi : RecoveryFocus.config coefficientSlots entry.heads entry.tapes
      (CompetitorSameBucketStreamLoad.cfg CompetitorSameBucketStreamLoad.coefficient.start cap pre.length
        (pre++frame bits++suffix) (ambient 31) coefficientLog)=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> first | exact driver | exact reset | rfl
  obtain ⟨actual,ha,hf,hs⟩ := RecoveryFocus.run_config coefficientSlots coefficient_injective CompetitorSameBucketStreamLoad.coefficient
    entry.heads entry.tapes _ _ base hb
  rw [hi] at ha
  refine ⟨actual,ha,?_,?_,hs.trans_le bs⟩
  · rw [hf]
    funext i
    simp only [RecoveryFocus.config,coefficient_pick,bh]
    fin_cases i <;> simp [entry,cfg,heads,CompetitorSameBucketGateScan.heads,CompetitorSameBucketBucketPrepare.heads,Fin.addCases]
  · rw [hf]
    funext i
    simp only [RecoveryFocus.config,coefficient_pick,bt]
    fin_cases i <;> simp [entry,cfg,tapes,core,CompetitorSameBucketStreamLoad.cfg,
      CompetitorSameBucketBucketBody.cfg,CompetitorSameBucketBucketPrepare.cfg,CompetitorSameBucketSquare.tapes,
      CompetitorSameBucketLeftLoad.tapes,CompetitorSameBucketBucketPrepare.tapes,Fin.addCases,driver,reset]

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGateLoad
