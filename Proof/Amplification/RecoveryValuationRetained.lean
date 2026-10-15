import Proof.Amplification.RecoveryPrefixAssignment

/-! Retained scalar layout at the actual table-scan return. This invariant
allows the enclosing assignment machine to use the same query and workspace. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationTable
open LocalBitMultitape RecoveryValuationStream RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem iterate_retained (count : Nat) (x : Cursor) :
    let y := (RepeatMachine.iterate next count x).2
    y.data.width=x.data.width ∧ y.data.index=x.data.index ∧ y.data.source=x.data.source ∧
      y.data.capacity=max x.data.capacity (if count=0 then 0 else 2*x.data.index.length+2) := by
  induction count generalizing x with
  | zero => simp [RepeatMachine.iterate]
  | succ count ih =>
    simp only [RepeatMachine.iterate]
    split
    · have h := ih (next x).2
      dsimp only at h ⊢
      refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
      rw [h.2.2.2]
      change max (max x.data.capacity (2*x.data.index.length+2))
        (if count=0 then 0 else 2*x.data.index.length+2)=_
      simp only [Nat.add_one_ne_zero,↓reduceIte]
      split <;> omega
    · simp [next,advance,Data.done,Data.afterRow,Data.afterMatch,Data.afterField]

theorem iterate_capacity (count : Nat) (x : Cursor) (hc : 2*x.data.index.length+2≤x.data.capacity) :
    (RepeatMachine.iterate next count x).2.data.capacity=x.data.capacity := by
  rw [(iterate_retained count x).2.2.2]
  split <;> omega

theorem iterate_inv (count width : Nat) (x : Cursor) (hx : Inv width x)
    (ha : (RepeatMachine.iterate next count x).1=true) :
    Inv width (RepeatMachine.iterate next count x).2 := by
  induction count generalizing x with
  | zero => exact hx
  | succ count ih =>
    cases hn : (next x).1 with
    | false => simp [RepeatMachine.iterate,hn] at ha
    | true =>
      simp only [RepeatMachine.iterate,hn,↓reduceIte] at ha ⊢
      exact ih (next x).2 (next_inv width x hx hn) ha

end NearCubicWires.RepairOrdinary.RecoveryValuationTable
