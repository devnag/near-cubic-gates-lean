import Proof.MachineModel.OrdinaryMatrixScoreRawGateBounds
import Proof.MachineModel.OrdinaryKeyDominanceScan

/-! Cold raw cut through actual score enumeration, ordinary sort and rank
annotation. The executed local return exposes the exact existing bucket
scanner stream at head zero; no supplied sorted records or rank labels. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreRawRanks
open LocalBitMultitape SignedSortKey MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem size_fit (r : Request) : r.U+r.U≤2^r.M := by
  have hp := Nat.lt_pow_succ_log_self (by decide : 1<2) (r.U+r.U)
  change r.U+r.U<2^natBitLength (r.U+r.U) at hp
  exact hp.le.trans (Nat.pow_le_pow_right (by decide) (by unfold Request.M; omega))

def request (r : Request) (gate : Fin r.Gates) : SortRank.Request :=
  DominanceLabels.request r.S r.M (leftScore r) (rightScore r) gate (size_fit r)
noncomputable def entries (r : Request) (gate : Fin r.Gates) :=
  KeyLoop.indexed 0 (KeyLoop.dominanceEntries r.S r.M (leftScore r) (rightScore r) gate)
noncomputable def output (r : Request) (gate : Fin r.Gates) := KeyLoop.stream r.S r.M (entries r gate)
def rankMachine := Rewind.machine SortRank.machine
def rankInput (r : Request) (gate : Fin r.Gates) : Fin 12 → List Bool :=
  fun i => if i=0 then gateRecords r gate else []
def rankBudget (r : Request) (gate : Fin r.Gates) := 2*SortRank.rawBudget (request r gate)+2

theorem rank_run (r : Request) (gate : Fin r.Gates) :
    ∃ actual,run rankMachine (rankBudget r gate) (rankInput r gate)=some actual ∧
      actual.final.tapes 7=output r gate ∧ (∀ i,actual.final.heads i=0) ∧
      actual.steps≤rankBudget r gate := by
  obtain ⟨base,hb,bt,bs⟩ := SortRank.raw_run (request r gate)
  obtain ⟨actual,hr,ht,hh,hs,_⟩ := Rewind.reset_run SortRank.machine _ _ base hb
  have hin : Fin.addCases (m := 11) (n := 1) (motive := fun _ => List Bool)
      (SourceHandoff.sourceTapes (StablePartition.stream (request r gate).records))
      (fun _ : Fin 1 => [])=rankInput r gate := by
    funext i
    fin_cases i <;> rfl
  rw [hin] at hr
  have htime : 2*base.steps+2≤rankBudget r gate := by unfold rankBudget; omega
  have he := run_moreFuel rankMachine _ (rankBudget r gate-(2*base.steps+2)) _ actual hr
  rw [Nat.add_sub_of_le htime] at he
  have hout : RankLoop.labels (request r gate).width 0 (request r gate).sortedWords++[false]=output r gate := by
    rw [RankMeaning.output_stream]
    unfold output entries
    rw [KeyLoop.indexed_stream,KeyLoop.dominance_words r.S r.M (leftScore r) (rightScore r) gate
      (size_fit r) (score_lo r gate) (score_hi r gate)]
    rfl
  exact ⟨actual,he,(ht 7).trans (bt.trans hout),hh,hs.trans_le htime⟩

def budget (r : Request) (gate : Fin r.Gates) :=
  100000*(r.U+1)*(r.d+r.p+1)^2+1+rankBudget r gate

end NearCubicWires.RepairOrdinary.MatrixScoreRawRanks
