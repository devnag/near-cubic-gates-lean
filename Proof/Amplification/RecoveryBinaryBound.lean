import Proof.Amplification.RecoveryBinaryCount

/-! The natural input-length bound is at least one. Only the empty input
needs a physical replacement of binary zero by binary one; the original
framed code is retained in both cases. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdBinaryBound
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg (q : Fin 5) (source binary : List Bool) (pos : Nat) : Configuration 2 5 :=
  ⟨q,![0,pos],![source,binary]⟩
def action (q : Fin 5) (write : Option Bool) (move : HeadMove) : Action 2 5 :=
  ⟨q,![none,write],![.stay,move]⟩
def machine : Machine 2 5 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==4
  rule := fun q bits=> ![
    some (if bits 0 then action 4 none .stay else action 1 (some true) .right),
    some (action 2 (some true) .right),some (action 3 (some false) .left),
    some (action 4 none .left),none] q

theorem zero_trace : Timed machine 4 (cfg 0 [false] [false] 0) (cfg 4 [false] (frame [true]) 0) := by
  have h0 : Timed machine 1 (cfg 0 [false] [false] 0) (cfg 1 [false] [true] 1) :=
    Timed.single (by rfl) (by
      apply congrArg some
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl)
  have h1 : Timed machine 1 (cfg 1 [false] [true] 1) (cfg 2 [false] [true,true] 2) :=
    Timed.single (by rfl) (by
      apply congrArg some
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl)
  have h2 : Timed machine 1 (cfg 2 [false] [true,true] 2) (cfg 3 [false] [true,true,false] 1) :=
    Timed.single (by rfl) (by
      apply congrArg some
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl)
  have h3 : Timed machine 1 (cfg 3 [false] [true,true,false] 1) (cfg 4 [false] [true,true,false] 0) :=
    Timed.single (by rfl) (by
      apply congrArg some
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl)
  exact ((h0.trans h1).trans h2).trans h3

theorem nonempty_trace (bit : Bool) (bits binary : List Bool) :
    Timed machine 1 (cfg 0 (frame (bit::bits)) binary 0) (cfg 4 (frame (bit::bits)) binary 0) :=
  Timed.single (by rfl) (by
      apply congrArg some
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl)

theorem bound_run (bits : List Bool) :
    ∃ r,runFrom machine 4 (cfg 0 (frame bits) (frame (ClockBinary.word bits.length)) 0)=some r ∧
      r.final=cfg 4 (frame bits) (frame (ClockBinary.word (max 1 bits.length))) 0 ∧ r.steps ≤ 4 := by
  cases bits with
  | nil=>
    obtain ⟨r,hr,hf,hs⟩ := zero_trace.run (by rfl)
    exact ⟨r,hr,hf,hs.le⟩
  | cons bit bits=>
    obtain ⟨r,hr,hf,hs⟩ := (nonempty_trace bit bits (frame (ClockBinary.word (bit::bits).length))).run (by rfl)
    have hm := runFrom_moreFuel machine 1 3 _ r hr
    refine ⟨r,hm,?_,by omega⟩
    rw [List.length_cons,Nat.max_eq_right (by omega)]
    exact hf

end NearCubicWires.RepairOrdinary.RecoveryColdBinaryBound
