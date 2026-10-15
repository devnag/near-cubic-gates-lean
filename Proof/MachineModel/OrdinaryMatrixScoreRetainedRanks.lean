import Proof.MachineModel.OrdinaryMatrixBatchSetup

/-! The actual gate-score and sort/rank consumer with shared native fields.
Only the local output is returned before sorting; source/driver state stays
available to the enclosing raw all-gates caller. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreRetainedRanks
open LocalBitMultitape SignedSortKey MatrixScoreBatch
open MatrixScoreLeftLoop (C State)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 30) : Bool := decide (i=24)
noncomputable def scoreMachine := MaskedReset.machine MatrixScoreGateStream.machine selected
noncomputable def scoreInput (r : Request) (gate : Fin r.Gates) (state : State r) :=
  Rewind.recording (Composition.leftConfig 2 (MatrixScoreBothHalves.initial r gate state (C r+1) [] [] [])) 0
def scoreBudget (r : Request) := 2*MatrixScoreGateStream.budget r+2
noncomputable def finalFields (r : Request) (gate : Fin r.Gates) (state : State r) :=
  MatrixScoreHalvesReset.tapes (cutWord r.p (r.cuts.get gate)) r.width (r.phi (r.U-1))
    (C r) (r.S+1) (2^r.S) r.M (r.U+(r.U-1)) r.U r.U state.returnCap state.work
    (ZeroPadding.pad (C r) [true,true]) (MatrixScoreWeight.zeros (C r)) (gateRecords r gate) r.cols

theorem score_run (r : Request) (gate : Fin r.Gates) (state : State r) :
    ∃ final : State r,∃ count : ℕ,count≤MatrixScoreGateStream.budget r ∧
    ∃ actual,runFrom scoreMachine (scoreBudget r) (scoreInput r gate state)=some actual ∧
      actual.final.tapes=Fin.addCases (m := 30) (n := 1) (motive := fun _ => List Bool)
        (finalFields r gate final) (fun _ => List.replicate count false) ∧
      actual.final.heads=Fin.addCases (m := 30) (n := 1) (motive := fun _ => ℕ)
        (MatrixScoreHalvesReset.heads 0) (fun _ => 0) ∧ actual.steps≤ scoreBudget r := by
  obtain ⟨final,body,hb,bh,bt,bs⟩ := MatrixScoreGateStream.gate_run r gate state (C r+1) [] [] []
    (by omega) (by simp) (by simp)
  simp only [List.nil_append] at bh bt
  let entry := Composition.leftConfig 2 (MatrixScoreBothHalves.initial r gate state (C r+1) [] [] [])
  have hhead (i : Fin 30) (hi : selected i=true) : body.final.heads i≤body.steps := by
    have he : i=24 := by simpa only [selected,decide_eq_true_eq] using hi
    subst i
    have hp := SelectiveReset.prefix_head (prefix_of_run MatrixScoreGateStream.machine _ entry body hb).1 24
    have hz : entry.heads 24=0 := rfl
    simpa only [hz,Nat.zero_add] using hp
  obtain ⟨actual,hr,hf,hs,_⟩ := MaskedReset.reset_run MatrixScoreGateStream.machine selected _ entry body hb hhead
  have hbnd : 2*body.steps+2≤ scoreBudget r := by unfold scoreBudget; omega
  have he := runFrom_moreFuel scoreMachine _ (scoreBudget r-(2*body.steps+2)) _ actual hr
  rw [Nat.add_sub_of_le hbnd] at he
  refine ⟨final,body.steps,bs,actual,he,?_,?_,hs.trans_le hbnd⟩
  · rw [hf,bt]
    rfl
  · rw [hf,bh]
    funext i
    fin_cases i <;> rfl

def slots : Fin 12 → Fin 42 := ![24,31,32,33,34,35,36,37,38,39,40,41]
theorem slots_injective : Function.Injective slots := by decide
theorem pick_old (i : Fin 30) (hi : i≠24) : RecoveryFocus.pick slots (i.castAdd 12)=none := by
  fin_cases i <;> first | contradiction | decide
def retainedHeads (i : Fin 42) : ℕ := if i=17 ∨ i=28 then 1 else 0
theorem heads_embed :
    (Fin.addCases (m := 31) (n := 11) (motive := fun _ => ℕ)
      (Fin.addCases (m := 30) (n := 1) (motive := fun _ => ℕ)
        (MatrixScoreHalvesReset.heads 0) (fun _ => 0)) (fun _ => 0))=retainedHeads := by
  funext i
  fin_cases i <;> rfl
theorem picked_head_zero (i : Fin 42) (j : Fin 12) (hj : RecoveryFocus.pick slots i=some j) : retainedHeads i=0 := by
  have hn : i≠17 ∧ i≠28 := by
    constructor
    · intro heq
      subst i
      have he : RecoveryFocus.pick slots (17 : Fin 42)=none := pick_old 17 (by decide)
      rw [he] at hj
      contradiction
    · intro heq
      subst i
      have he : RecoveryFocus.pick slots (28 : Fin 42)=none := pick_old 28 (by decide)
      rw [he] at hj
      contradiction
  simp [retainedHeads,hn.1,hn.2]
noncomputable def first := TapeEmbedding.machine 11 scoreMachine
noncomputable def last := RecoveryFocus.machine slots MatrixScoreRawRanks.rankMachine
noncomputable def machine := Composition.machine first last
noncomputable def input (r : Request) (gate : Fin r.Gates) (state : State r) :=
  Composition.leftConfig 110 (TapeEmbedding.config (fun _ : Fin 11 => 0) (fun _ : Fin 11 => []) (scoreInput r gate state))
def budget (r : Request) (gate : Fin r.Gates) := scoreBudget r+1+MatrixScoreRawRanks.rankBudget r gate

theorem gate_run (r : Request) (gate : Fin r.Gates) (state : State r) :
    ∃ final : State r,∃ actual,runFrom machine (budget r gate) (input r gate state)=some actual ∧
      actual.final.tapes 37=MatrixScoreRawRanks.output r gate ∧
      (∀ i : Fin 30,i≠24 → actual.final.tapes (i.castAdd 12)=finalFields r gate final i) ∧
      (∀ i : Fin 42,actual.final.heads i=if i=17 ∨ i=28 then 1 else 0) ∧
      actual.steps≤budget r gate := by
  obtain ⟨final,count,_,body,hb,bt,bh,bs⟩ := score_run r gate state
  have he := TapeEmbedding.run_embed scoreMachine (fun _ : Fin 11 => 0) (fun _ : Fin 11 => []) _ _ body hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 11 => 0) (fun _ : Fin 11 => []) body
  obtain ⟨ranked,hr,rt,rh,rs⟩ := MatrixScoreRawRanks.rank_run r gate
  let entry := initialConfiguration MatrixScoreRawRanks.rankMachine (MatrixScoreRawRanks.rankInput r gate)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i
      · change body.final.heads 24=0
        rw [bh]
        rfl
      all_goals rfl
    · intro i
      fin_cases i
      · change body.final.tapes 24=gateRecords r gate
        rw [bt]
        rfl
      all_goals rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots slots_injective MatrixScoreRawRanks.rankMachine
    prepared.final.heads prepared.final.tapes _ entry ranked hr
  rw [hi] at hf
  have joined := Composition.run_join first last _ _ _ prepared focused he hf
  refine ⟨final,Composition.joinedReceipt prepared focused,joined,?_,?_,?_,?_⟩
  · change focused.final.tapes (slots 7)=_
    rw [hff]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using rt
  · intro i hn
    change focused.final.tapes (i.castAdd 12)=_
    rw [hff]
    have hp := pick_old i hn
    simp only [RecoveryFocus.config,hp]
    rw [← show (i.castAdd 1).castAdd 11=i.castAdd 12 by rfl]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config,bt]
  · intro i
    change focused.final.heads i=_
    rw [hff]
    have ph (j : Fin 42) : prepared.final.heads j=retainedHeads j := by
      change (TapeEmbedding.config (fun _ : Fin 11 => 0) (fun _ : Fin 11 => []) body.final).heads j=_
      simp only [TapeEmbedding.config]
      rw [bh]
      exact congrFun heads_embed j
    change (RecoveryFocus.config slots prepared.final.heads prepared.final.tapes ranked.final).heads i=retainedHeads i
    simp only [RecoveryFocus.config]
    split
    · rename_i j hj
      exact (rh j).trans (picked_head_zero i j hj).symm
    · exact ph i
  · change prepared.steps+1+focused.steps≤_
    rw [hfs]
    change body.steps+1+ranked.steps≤budget r gate
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreRetainedRanks
