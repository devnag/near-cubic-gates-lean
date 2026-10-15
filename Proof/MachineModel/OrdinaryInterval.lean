import Proof.MachineModel.OrdinaryRightCellCapacity

/-! The left bit-plane cell's two boundary tests, fused in one actual scan.
The coefficient bit is read from its scalar tape; the result is appended to
the matrix output without moving that output cursor backwards. -/
namespace NearCubicWires.RepairOrdinary.Interval
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scanState (lo hi : Bool) : Fin 9 := ⟨lo.toNat + 2 * hi.toNat, by cases lo <;> cases hi <;> decide⟩
def bitState (lo hi : Bool) : Fin 9 := ⟨4 + lo.toNat + 2 * hi.toNat, by cases lo <;> cases hi <;> decide⟩
def lowFlag (state : Fin 9) : Bool := state.val % 2 == 1
def highFlag (state : Fin 9) : Bool := state.val % 4 / 2 == 1
def action (state : Fin 9) (inputMove : HeadMove) (output : Option Bool) : Action 5 9 :=
  ⟨state, fun i => if i.val = 3 then output else none,
    fun i => if i.val < 3 then inputMove else if i.val = 3 then
      if output.isSome then .right else .stay else .stay⟩
def machine : Machine 5 9 where
  descriptionBits := 0
  start := scanState true true
  halted := fun state => state.val == 8
  rule := fun state scanned => if state.val < 4 then
      if scanned 0 then some (action (bitState (lowFlag state) (highFlag state)) .right none)
      else some (action 8 .stay (some (lowFlag state && !highFlag state && scanned 4)))
    else if state.val < 8 then some (action
      (scanState (Compare.next (scanned 0) (scanned 1) (lowFlag state))
        (Compare.next (scanned 2) (scanned 1) (highFlag state))) .right none)
    else none

def config (state : Fin 9) (lower rank upper : List Bool) (lowHead rankHead highHead : ℕ)
    (output : List Bool) (mask : Bool) : Configuration 5 9 :=
  ⟨state, ![lowHead, rankHead, highHead, output.length, 0], ![lower, rank, upper, output, [mask]]⟩

@[simp] theorem config_cells (state : Fin 9) (lower rank upper : List Bool) (lowHead rankHead highHead : ℕ)
    (output : List Bool) (mask : Bool) :
    (config state lower rank upper lowHead rankHead highHead output mask).tapeCells =
      lower.length + rank.length + upper.length + output.length + 1 := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]
  omega

theorem marker_step (lower rank upper : List Bool) (lowHead rankHead highHead : ℕ)
    (output : List Bool) (mask lo hi : Bool) (hr : readTapeBit lower lowHead = true) :
    step machine (config (scanState lo hi) lower rank upper lowHead rankHead highHead output mask) =
      some (config (bitState lo hi) lower rank upper (lowHead + 1) (rankHead + 1) (highHead + 1) output mask) := by
  cases lo <;> cases hi <;>
    simp [step, machine, scanState, bitState, lowFlag, highFlag, config, Configuration.scanned, hr] <;>
      apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply])

theorem bit_step (lower rank upper : List Bool) (lowHead rankHead highHead : ℕ)
    (output : List Bool) (mask lo hi a b c : Bool)
    (ha : readTapeBit lower lowHead = a) (hb : readTapeBit rank rankHead = b) (hc : readTapeBit upper highHead = c) :
    step machine (config (bitState lo hi) lower rank upper lowHead rankHead highHead output mask) =
      some (config (scanState (Compare.next a b lo) (Compare.next c b hi)) lower rank upper
        (lowHead + 1) (rankHead + 1) (highHead + 1) output mask) := by
  cases lo <;> cases hi <;>
    simp [step, machine, scanState, bitState, lowFlag, highFlag, config, Configuration.scanned, ha, hb, hc] <;>
      apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply])

theorem finish_step (lower rank upper : List Bool) (lowHead rankHead highHead : ℕ)
    (output : List Bool) (mask lo hi : Bool) (hr : readTapeBit lower lowHead = false) :
    step machine (config (scanState lo hi) lower rank upper lowHead rankHead highHead output mask) =
      some (config 8 lower rank upper lowHead rankHead highHead (output ++ [lo && !hi && mask]) mask) := by
  have hm : readTapeBit [mask] 0 = mask := rfl
  cases lo <;> cases hi <;>
    simp [step, machine, scanState, lowFlag, highFlag, config, Configuration.scanned, hr, hm] <;>
      apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply, Streaming.write_append])

theorem interval_prefix (preLow preRank preHigh lower rank upper tailLow tailRank tailHigh output : List Bool)
    (mask lo hi : Bool) (hl : lower.length = rank.length) (hh : upper.length = rank.length) :
    Prefix machine
      ((preLow ++ frame lower ++ tailLow).length + (preRank ++ frame rank ++ tailRank).length +
        (preHigh ++ frame upper ++ tailHigh).length + output.length + 2)
      (2 * lower.length + 1)
      (config (scanState lo hi) (preLow ++ frame lower ++ tailLow) (preRank ++ frame rank ++ tailRank)
        (preHigh ++ frame upper ++ tailHigh) preLow.length preRank.length preHigh.length output mask)
      (config 8 (preLow ++ frame lower ++ tailLow) (preRank ++ frame rank ++ tailRank)
        (preHigh ++ frame upper ++ tailHigh) (preLow.length + 2 * lower.length) (preRank.length + 2 * rank.length)
        (preHigh.length + 2 * upper.length)
        (output ++ [Compare.decision lower rank lo && !Compare.decision upper rank hi && mask]) mask) := by
  induction lower generalizing preLow preRank preHigh rank upper lo hi with
  | nil =>
    have hr : rank = [] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
    subst rank
    have hu : upper = [] := List.length_eq_zero_iff.mp hh
    subst upper
    have hread := Streaming.read_append preLow tailLow false
    have hs := finish_step (preLow ++ frame [] ++ tailLow) (preRank ++ frame [] ++ tailRank)
      (preHigh ++ frame [] ++ tailHigh) preLow.length preRank.length preHigh.length output mask lo hi
      (by simpa [frame, List.append_assoc] using hread)
    refine Prefix.step (by simp) (by cases lo <;> cases hi <;> rfl) hs ?_
    simpa [Compare.decision] using Prefix.refl
      (config 8 (preLow ++ frame [] ++ tailLow) (preRank ++ frame [] ++ tailRank) (preHigh ++ frame [] ++ tailHigh)
        preLow.length preRank.length preHigh.length (output ++ [lo && !hi && mask]) mask) (by simp; omega)
  | cons a lower ih =>
    cases rank with
    | nil => simp at hl
    | cons b rank =>
      cases upper with
      | nil => simp at hh
      | cons c upper =>
        have hl' : lower.length = rank.length := by simpa using hl
        have hh' : upper.length = rank.length := by simpa using hh
        let lhs := preLow ++ frame (a :: lower) ++ tailLow
        let rhs := preRank ++ frame (b :: rank) ++ tailRank
        let top := preHigh ++ frame (c :: upper) ++ tailHigh
        let space := lhs.length + rhs.length + top.length + output.length + 2
        have ht : Prefix machine space (2 * lower.length + 1)
            (config (scanState (Compare.next a b lo) (Compare.next c b hi)) lhs rhs top
              (preLow.length + 2) (preRank.length + 2) (preHigh.length + 2) output mask)
            (config 8 lhs rhs top (preLow.length + 2 * (a :: lower).length) (preRank.length + 2 * (b :: rank).length)
              (preHigh.length + 2 * (c :: upper).length)
              (output ++ [Compare.decision (a :: lower) (b :: rank) lo &&
                !Compare.decision (c :: upper) (b :: rank) hi && mask]) mask) := by
          have hp := ih (preLow ++ [true, a]) (preRank ++ [true, b]) (preHigh ++ [true, c]) rank upper
            (Compare.next a b lo) (Compare.next c b hi) hl' hh'
          convert hp using 1 <;> simp [lhs, rhs, top, space, frame, Compare.decision, List.append_assoc, Nat.mul_add,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        have hread : readTapeBit lhs preLow.length = true := by
          simpa [lhs, frame, List.append_assoc] using Streaming.read_append preLow (a :: frame lower ++ tailLow) true
        have ha : readTapeBit lhs (preLow.length + 1) = a := by
          simpa [lhs, frame, List.append_assoc] using Streaming.read_append (preLow ++ [true]) (frame lower ++ tailLow) a
        have hb : readTapeBit rhs (preRank.length + 1) = b := by
          simpa [rhs, frame, List.append_assoc] using Streaming.read_append (preRank ++ [true]) (frame rank ++ tailRank) b
        have hc : readTapeBit top (preHigh.length + 1) = c := by
          simpa [top, frame, List.append_assoc] using Streaming.read_append (preHigh ++ [true]) (frame upper ++ tailHigh) c
        have hs := bit_step lhs rhs top (preLow.length + 1) (preRank.length + 1) (preHigh.length + 1)
          output mask lo hi a b c ha hb hc
        have hp := Prefix.step (by simp [space] :
            (config (bitState lo hi) lhs rhs top (preLow.length + 1) (preRank.length + 1) (preHigh.length + 1) output mask).tapeCells ≤ space)
          (by cases lo <;> cases hi <;> rfl) hs (by simpa [Nat.add_assoc] using ht)
        have hstart := Prefix.step (by simp [space] :
            (config (scanState lo hi) lhs rhs top preLow.length preRank.length preHigh.length output mask).tapeCells ≤ space)
          (by cases lo <;> cases hi <;> rfl) (marker_step lhs rhs top preLow.length preRank.length preHigh.length output mask lo hi hread) hp
        convert hstart using 1 <;> simp [lhs, rhs, top, Nat.mul_add, Nat.add_assoc]

theorem interval_run (width lower rank upper : ℕ) (output : List Bool) (mask : Bool)
    (hlo : lower < 2 ^ width) (hr : rank < 2 ^ width) (hhi : upper < 2 ^ width) :
    ∃ r : ExecutionReceipt 5 9,
      runFrom machine (2 * width + 1)
        (config (scanState true true) (frame (SignedSortKey.binary width lower)) (frame (SignedSortKey.binary width rank))
          (frame (SignedSortKey.binary width upper)) 0 0 0 output mask) = some r ∧
      r.final.tapes 3 = output ++ [(decide (lower ≤ rank) && !decide (upper ≤ rank)) && mask] ∧
      r.final.heads 3 = output.length + 1 ∧ r.steps = 2 * width + 1 ∧
      r.peakTapeCells ≤ 6 * width + output.length + 5 := by
  have hp := interval_prefix [] [] [] (SignedSortKey.binary width lower) (SignedSortKey.binary width rank)
    (SignedSortKey.binary width upper) [] [] [] output mask true true (by simp) (by simp)
  obtain ⟨r, hrun, hf, hs, hpeak⟩ := hp.run (by rfl) (by simp; omega)
  refine ⟨r, by simpa using hrun, ?_, by simp [hf, config], by simpa using hs, ?_⟩
  · have hlc := Compare.decision_le (SignedSortKey.binary width lower) (SignedSortKey.binary width rank) (by simp)
    have hhc := Compare.decision_le (SignedSortKey.binary width upper) (SignedSortKey.binary width rank) (by simp)
    simp [hf, config, hlc, hhc, SignedSortKey.binary_value _ _ hlo,
      SignedSortKey.binary_value _ _ hr, SignedSortKey.binary_value _ _ hhi]
  · simp only [List.nil_append, List.append_nil, frame_length, SignedSortKey.binary_length] at hpeak
    omega

end NearCubicWires.RepairOrdinary.Interval
