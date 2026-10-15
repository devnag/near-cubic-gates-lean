import Proof.Amplification.RecoveryRowReadReturned

/-! One uniform polynomial budget for every table row, including malformed
rows. Unary prior-row scans are charged for their actual number of rows. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem decode_time_le (word : List Bool) (width : Nat) (hw : word.length ≤ width) :
    RecoveryDecodeStep.time word ≤ 65536*(width+1)^2 := by
  have h := RecoveryDecodeStep.time_bound word
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) 2
  unfold RecoveryDecodeStep.budget at h
  omega

theorem front_time_le (d : Data) (width : Nat) (hw : d.code.length ≤ width) :
    frontTime d ≤ 65536*(width+1)^2+28*width+52 := by
  have h := decode_time_le d.code width hw
  unfold frontTime prepareTime codeTime RecoveryRowKind.time
  rw [(RecoveryFixedUnpair.word_lengths d.code).1]
  omega

theorem children_time_le (x : Children) (pair : List Bool) (width limit : Nat)
    (hw : x.base.state.bits.length ≤ width) (hc : x.base.count.length ≤ width)
    (hp : pair.length ≤ width) (hb : x.bank.row.width ≤ width) (hj : x.total ≤ limit) :
    childrenTime x pair ≤ 65536*(width+1)^2+28*width+64+4*limit*(32*width+53) := by
  have hd := decode_time_le pair width hp
  have hm : x.total*(32*x.bank.row.width+53) ≤ limit*(32*width+53) :=
    Nat.mul_le_mul hj (by omega)
  unfold childrenTime leftTime bankTime
  change RecoveryDecodeStep.time pair+1+
    ((8*(RecoveryFixedUnpair.leftWord pair).length+8)+1+(2*x.total*(32*x.bank.row.width+53)+12)+1+
      (8*x.base.state.bits.length+8)+1+
      ((8*(RecoveryChildSelection.word false pair).length+8)+1+(2*x.total*(32*x.bank.row.width+53)+12)+1+
        (4*x.base.count.length+5))) ≤ _
  rw [(RecoveryFixedUnpair.word_lengths pair).1,RecoveryChildSelection.word_length]
  nlinarith only [hd,hm,hw,hc,hp]

theorem structure_time_le (x : Children) (width limit : Nat)
    (hw : x.base.state.bits.length ≤ width) (hc : x.base.count.length ≤ width)
    (hk : x.base.code.length ≤ width) (hb : x.bank.row.width ≤ width) (hj : x.total ≤ limit) :
    structureTime x ≤ 131072*(width+1)^2+256*(width+1)+4*limit*(32*width+53) := by
  have hfront := front_time_le x.base width hk
  have hret := front_retained x.base
  have hpair : (pairWord x.base).length ≤ width := (RecoveryChildSelection.word_length false x.base.code).le.trans hk
  have hchild := children_time_le (structureFront x) (pairWord x.base) width limit
    ((congrArg List.length hret.2.2.2.1).le.trans hw) ((congrArg List.length hret.2.2.1).le.trans hc) hpair hb hj
  have hzero : zeroTime (frontOutput x.base) ≤ 16*width+24 := by
    unfold zeroTime RecoveryRowKind.time
    rw [hret.2.1,hret.2.2.1]
    omega
  have hone : oneTime (frontOutput x.base) (pairWord x.base) ≤ 20*width+40 := by
    unfold oneTime RecoveryRowKind.time
    rw [hret.2.2.1]
    omega
  have hm : max (zeroTime (frontOutput x.base))
      (max (oneTime (frontOutput x.base) (pairWord x.base)) (childrenTime (structureFront x) (pairWord x.base))) ≤
      65536*(width+1)^2+28*width+64+4*limit*(32*width+53) := by
    exact max_le (by omega) (max_le (by omega) hchild)
  unfold structureTime
  omega

def tableRowBudget (width limit : Nat) :=
  9000000*(width+1)^2+4*limit*(32*width+53)+512*(width+1)+2*limit+16

theorem read_whole_time_le (x : Children) (bits input : List Bool) (width limit : Nat)
    (hw : x.base.state.bits.length=width) (hb : x.bank.row.width ≤ width) (hj : x.total ≤ limit) :
    readWholeTime x bits input+1+(2*x.total+6)+1 ≤ tableRowBudget width limit := by
  have hlen : ∀ i : Fin 4,(RecoveryRowFields.words width input i).length ≤ width := by
    intro i
    simp only [RecoveryRowFields.words,List.length_take]
    exact Nat.min_le_left _ _
  have hrw : (readChildren x input).base.state.bits.length ≤ width := by
    change (RecoveryRowFields.words x.base.state.bits.length input 3).length ≤ width
    rw [hw]
    exact hlen 3
  have hrc : (readChildren x input).base.count.length ≤ width := by
    change (RecoveryRowFields.words x.base.state.bits.length input 2).length ≤ width
    rw [hw]
    exact hlen 2
  have hrk : (readChildren x input).base.code.length ≤ width := by
    change (RecoveryRowFields.words x.base.state.bits.length input 1).length ≤ width
    rw [hw]
    exact hlen 1
  have hs := structure_time_le (readChildren x input) width limit hrw hrc hrk hb hj
  have hsr := congrArg List.length (structure_retained (readChildren x input) bits).1
  have hh := Nat.pow_le_pow_left (Nat.add_le_add_right (hsr.le.trans hrw) 1) 2
  unfold readWholeTime wholeRowTime leafWholeTime RecoveryRowFields.budget tableRowBudget
  rw [hw]
  omega

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
