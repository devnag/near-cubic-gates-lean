import Proof.Amplification.RecoveryOuterRowRetained

/-! One polynomial pays all outer-row work, including a full retained
inner scan for every singleton and the actual prior-count increment. -/
namespace NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tableBudget (width limit : Nat) :=
  9000000*(width+1)^2+6*limit*(32*width+53)+512*(width+1)+2*limit+32

theorem read_row_time_le (x : State) (bits input : List Bool) (width limit : Nat)
    (hw : x.outer.base.state.bits.length=width) (hb : x.outer.bank.row.width ≤ width)
    (hj : x.outer.total ≤ limit) (hi : x.inner.row.width ≤ width) (hn : x.total ≤ limit) :
    readRowCost x bits input+1+(2*x.outer.total+6)+1 ≤ tableBudget width limit := by
  have hlen : ∀ i : Fin 4,(RecoveryRowFields.words width input i).length ≤ width := by
    intro i
    simp only [RecoveryRowFields.words,List.length_take]
    exact Nat.min_le_left _ _
  have hrw : (readChildren x.outer input).base.state.bits.length ≤ width := by
    change (RecoveryRowFields.words x.outer.base.state.bits.length input 3).length ≤ width
    rw [hw]; exact hlen 3
  have hrc : (readChildren x.outer input).base.count.length ≤ width := by
    change (RecoveryRowFields.words x.outer.base.state.bits.length input 2).length ≤ width
    rw [hw]; exact hlen 2
  have hrk : (readChildren x.outer input).base.code.length ≤ width := by
    change (RecoveryRowFields.words x.outer.base.state.bits.length input 1).length ≤ width
    rw [hw]; exact hlen 1
  have hs := structure_time_le (readChildren x.outer input) width limit hrw hrc hrk hb hj
  have hsr := congrArg List.length (structure_retained (readChildren x.outer input) bits).1
  have hinner : x.total*(32*x.inner.row.width+53) ≤ limit*(32*width+53) :=
    Nat.mul_le_mul hn (by omega)
  unfold readRowCost rowCost leafCost checkedCost cost time bankTime
  change RecoveryRowFields.budget x.outer.base.state.bits.length+
    (structureTime (readChildren x.outer input)+
      (8*(structureOutput (readChildren x.outer input) bits).base.state.bits.length+9+
        (2*x.total*(RecoveryRowLookupStream.budget x.inner.row.width+3)+12)+2+2)+2)+2+1+(2*x.outer.total+6)+1 ≤ _
  unfold RecoveryRowFields.budget RecoveryRowLookupStream.budget tableBudget
  rw [hw,hsr]
  have he : 32*x.inner.row.width+50+3=32*x.inner.row.width+53 := by omega
  rw [he]
  nlinarith only [hs,hrw,hinner,hj]

end NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
