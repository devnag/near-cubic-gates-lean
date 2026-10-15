import Proof.MachineModel.OrdinaryMatrixScoreRawRanks
import Proof.Amplification.RecoveryTapeSupport

/-! The actual raw sort/rank call has both time and materialized-work bounds
needed by the enclosing paid clear-and-reuse gate scheduler. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreRawRanksBounds
open LocalBitMultitape SignedSortKey MatrixScoreBatch MatrixScoreRawRanks
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (r : Request) := 300000*(r.U+1)*(r.d+r.p+1)^2

theorem header_width (r : Request) : r.M+r.S+2≤8*(r.d+r.p+1) := by
  have hd : natBitLength r.d≤r.d+1 := Nat.add_le_add_right (Nat.log_le_self _ _) _
  rw [common_width]
  unfold Request.S
  omega

theorem budget_lt (r : Request) (gate : Fin r.Gates) : MatrixScoreRawRanks.budget r gate<capacity r := by
  have hs := SortRank.carrier_budget (request r gate)
  have hn : (request r gate).records.length=r.U+r.U := by
    simp [request,DominanceLabels.request,DominanceSort.records,DominanceSort.copies]
  have hw : (request r gate).width=r.M+r.S+1 := rfl
  rw [hn,hw] at hs
  have hwidth := Nat.pow_le_pow_left (header_width r) 2
  have hsort : SortRank.rawBudget (request r gate)≤512*(r.U+r.U+1)*(r.M+r.S+2)^2 := by
    simpa only [Nat.add_assoc] using (show SortRank.rawBudget (request r gate)≤
      512*(r.U+r.U+1)*(r.M+r.S+1+1)^2 by omega)
  have hb : SortRank.rawBudget (request r gate)≤65536*(r.U+1)*(r.d+r.p+1)^2 := by
    calc
      _ ≤ 512*(r.U+r.U+1)*(r.M+r.S+2)^2 := hsort
      _ ≤ 512*(2*(r.U+1))*(8*(r.d+r.p+1))^2 := by gcongr; omega
      _ = _ := by ring
  have hp : 0<(r.U+1)*(r.d+r.p+1)^2 := by positivity
  unfold MatrixScoreRawRanks.budget rankBudget capacity
  nlinarith

theorem input_fit (r : Request) (gate : Fin r.Gates) : (frame (gateWord r gate)).length≤capacity r := by
  have hd : natBitLength r.d≤r.d+1 := Nat.add_le_add_right (Nat.log_le_self _ _) _
  have hp : natBitLength r.p≤r.p+1 := Nat.add_le_add_right (Nat.log_le_self _ _) _
  have hc := cutWord_length r (r.cuts.get gate) (List.get_mem _ _)
  simp only [frame_length,gateWord,List.length_append,MatrixScoreRawGateBounds.natWord_length,hc]
  have hw := r.widthLe
  have hle : (2*r.width+2)*(2*r.p+3)≤6*(r.d+r.p+1)^2 := by nlinarith
  have hpos : 1≤(r.d+r.p+1)^2 := by nlinarith
  have hm : (r.d+r.p+1)^2≤(r.U+1)*(r.d+r.p+1)^2 := by nlinarith
  unfold capacity
  nlinarith

end NearCubicWires.RepairOrdinary.MatrixScoreRawRanksBounds
