import Proof.Amplification.RecoveryTimedExecution

namespace NearCubicWires.RepairOrdinary.RecoveryRootCandidates
open LocalBitMultitape RecoveryExecution RecoveryRadixInput
open StablePartition.Workspace (overlay overlay_write)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def appendWrites (out : Fin 4 → List Bool) (writes : Fin 4 → Option Bool) : Fin 4 → List Bool :=
  fun i => out i ++ (writes i).toList

def emit (state : Fin 9) (inputMove : HeadMove) (writes : Fin 4 → Option Bool) : Action 6 9 :=
  ⟨state, ![none, none, writes 0, writes 1, writes 2, writes 3],
    ![inputMove, inputMove,
      if (writes 0).isSome then .right else .stay,
      if (writes 1).isSome then .right else .stay,
      if (writes 2).isSome then .right else .stay,
      if (writes 3).isSome then .right else .stay]⟩

def machine (lo hi : Bool) : Machine 6 9 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 8
  rule := fun q scanned =>
    if q.val = 0 then some (emit 1 .stay (fun _ => some true))
    else if q.val = 1 then some (emit 2 .stay ![some false, some true, some true, some lo])
    else if q.val = 2 then some (emit 3 .stay ![none, none, some true, some true])
    else if q.val = 3 then some (emit 4 .stay ![none, none, some false, some hi])
    else if q.val = 4 then
      if scanned 0 then some (emit 5 .right (fun _ => some true))
      else some (emit 6 .stay ![some true, some true, some false, some false])
    else if q.val = 5 then some (emit 4 .right
      ![some (scanned 0), some (scanned 0), some (scanned 0), some (scanned 1)])
    else if q.val = 6 then some (emit 7 .stay ![some false, some false, none, none])
    else if q.val = 7 then some (emit 8 .stay ![some false, some false, none, none])
    else none

def config (q : Fin 9) (left right : List Bool) (lh rh : Nat)
    (out backing : Fin 4 → List Bool) : Configuration 6 9 :=
  ⟨q, ![lh, rh, (out 0).length, (out 1).length, (out 2).length, (out 3).length],
    ![left, right, overlay (out 0) (backing 0), overlay (out 1) (backing 1),
      overlay (out 2) (backing 2), overlay (out 3) (backing 3)]⟩

theorem emit_config (q : Fin 9) (left right : List Bool) (lh rh : Nat)
    (out backing : Fin 4 → List Bool) (next : Fin 9) (move : HeadMove)
    (writes : Fin 4 → Option Bool) :
    applyAction (config q left right lh rh out backing) (emit next move writes) =
      config next left right (move.apply lh) (move.apply rh) (appendWrites out writes) backing := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [config, applyAction, emit, appendWrites]
    all_goals cases writes _ <;> simp [HeadMove.apply]
  · funext i
    fin_cases i <;> simp [config, applyAction, emit, appendWrites]
    all_goals cases writes _ <;> simp [overlay_write]

theorem emit_step (lo hi : Bool) (q : Fin 9) (left right : List Bool) (lh rh : Nat)
    (out backing : Fin 4 → List Bool) (next : Fin 9) (move : HeadMove)
    (writes : Fin 4 → Option Bool)
    (hr : (machine lo hi).rule q (config q left right lh rh out backing).scanned =
      some (emit next move writes)) :
    step (machine lo hi) (config q left right lh rh out backing) =
      some (config next left right (move.apply lh) (move.apply rh) (appendWrites out writes) backing) := by
  change ((machine lo hi).rule q _).map _ = _
  rw [hr]
  exact congrArg some (emit_config q left right lh rh out backing next move writes)

def finished (left right : List Bool) (out : Fin 4 → List Bool) : Fin 4 → List Bool :=
  ![out 0 ++ framePrefix left ++ [true, false, false],
    out 1 ++ framePrefix left ++ [true, false, false],
    out 2 ++ frame left, out 3 ++ frame right]

theorem scan_run (lo hi : Bool) (preLeft preRight left right tailLeft tailRight : List Bool)
    (out backing : Fin 4 → List Bool) (hw : left.length = right.length) :
    Timed (machine lo hi) (2 * left.length + 3)
      (config 4 (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        preLeft.length preRight.length out backing)
      (config 8 (preLeft ++ frame left ++ tailLeft) (preRight ++ frame right ++ tailRight)
        (preLeft.length + 2 * left.length) (preRight.length + 2 * right.length)
        (finished left right out) backing) := by
  induction left generalizing preLeft preRight right out with
  | nil =>
    have hr : right = [] := List.length_eq_zero_iff.mp (by simpa using hw.symm)
    subst right
    let lhs := preLeft ++ frame [] ++ tailLeft
    let rhs := preRight ++ frame [] ++ tailRight
    have hread : readTapeBit lhs preLeft.length = false := by
      simpa [lhs, frame, List.append_assoc] using Streaming.read_append preLeft tailLeft false
    let a := appendWrites out ![some true, some true, some false, some false]
    let b := appendWrites a ![some false, some false, none, none]
    let c := appendWrites b ![some false, some false, none, none]
    have h1 := emit_step lo hi 4 lhs rhs preLeft.length preRight.length out backing 6 .stay
      ![some true, some true, some false, some false]
      (by simp [machine, config, Configuration.scanned, hread])
    have h2 := emit_step lo hi 6 lhs rhs preLeft.length preRight.length a backing 7 .stay
      ![some false, some false, none, none] (by simp [machine])
    have h3 := emit_step lo hi 7 lhs rhs preLeft.length preRight.length b backing 8 .stay
      ![some false, some false, none, none] (by simp [machine])
    have hc : c = finished [] [] out := by
      funext i; fin_cases i <;> simp [c, b, a, appendWrites, finished, frame, framePrefix, List.append_assoc]
    have hp := Timed.step (by rfl) h1 (Timed.step (by rfl) h2
      (Timed.step (by rfl) h3 (Timed.refl (machine lo hi) (config 8 lhs rhs preLeft.length preRight.length c backing))))
    simpa [lhs, rhs, HeadMove.apply, hc] using hp
  | cons a left ih =>
    cases right with
    | nil => simp at hw
    | cons b right =>
      have hlen : left.length = right.length := by simpa using hw
      let lhs := preLeft ++ frame (a :: left) ++ tailLeft
      let rhs := preRight ++ frame (b :: right) ++ tailRight
      let markers := appendWrites out (fun _ => some true)
      let bits := appendWrites markers ![some a, some a, some a, some b]
      have hread : readTapeBit lhs preLeft.length = true := by
        simpa [lhs, frame, List.append_assoc] using Streaming.read_append preLeft (a :: frame left ++ tailLeft) true
      have hl : readTapeBit lhs (preLeft.length + 1) = a := by
        simpa [lhs, frame, List.append_assoc] using Streaming.read_append (preLeft ++ [true]) (frame left ++ tailLeft) a
      have hr : readTapeBit rhs (preRight.length + 1) = b := by
        simpa [rhs, frame, List.append_assoc] using Streaming.read_append (preRight ++ [true]) (frame right ++ tailRight) b
      have h1 := emit_step lo hi 4 lhs rhs preLeft.length preRight.length out backing 5 .right
        (fun _ => some true) (by simp [machine, config, Configuration.scanned, hread])
      have h2 := emit_step lo hi 5 lhs rhs (preLeft.length + 1) (preRight.length + 1) markers backing 4 .right
        ![some a, some a, some a, some b] (by simp [machine, config, Configuration.scanned, hl, hr])
      have hend : finished left right bits = finished (a :: left) (b :: right) out := by
        funext i; fin_cases i <;> simp [finished, bits, markers, appendWrites, framePrefix, frame, List.append_assoc]
      have ht := ih (preLeft ++ [true, a]) (preRight ++ [true, b]) right bits hlen
      have ht' : Timed (machine lo hi) (2 * left.length + 3)
          (config 4 lhs rhs (preLeft.length + 2) (preRight.length + 2) bits backing)
          (config 8 lhs rhs (preLeft.length + 2 * (a :: left).length)
            (preRight.length + 2 * (b :: right).length)
            (finished (a :: left) (b :: right) out) backing) := by
        convert ht using 1 <;> simp [lhs, rhs, frame, List.append_assoc, hend,
          Nat.mul_add, Nat.add_assoc, Nat.add_comm]
      have hp := Timed.step (by rfl) h1 (Timed.step (by rfl) h2
        (by simpa [HeadMove.apply, Nat.add_assoc] using ht'))
      simpa [lhs, rhs, HeadMove.apply, Nat.mul_add, Nat.add_assoc] using hp

def initialized (lo hi : Bool) : Fin 4 → List Bool :=
  ![[true, false], [true, true], [true, true, true, false], [true, lo, true, hi]]

def words (lo hi : Bool) (left right : List Bool) : Fin 4 → List Bool :=
  ![false :: (left ++ [false]), true :: (left ++ [false]), true :: false :: left, lo :: hi :: right]

@[simp] theorem words_length (lo hi : Bool) (left right : List Bool)
    (hw : left.length = right.length) (i : Fin 4) :
    (words lo hi left right i).length = left.length + 2 := by
  fin_cases i <;> simp [words, hw]

theorem initialize_run (lo hi : Bool) (left right : List Bool) (backing : Fin 4 → List Bool) :
    Timed (machine lo hi) 4
      (config 0 left right 0 0 (fun _ => []) backing)
      (config 4 left right 0 0 (initialized lo hi) backing) := by
  let a := appendWrites (fun _ => []) (fun _ => some true)
  let b := appendWrites a ![some false, some true, some true, some lo]
  let c := appendWrites b ![none, none, some true, some true]
  let d := appendWrites c ![none, none, some false, some hi]
  have hd : d = initialized lo hi := by
    funext i; fin_cases i <;> simp [d, c, b, a, appendWrites, initialized]
  have h1 := emit_step lo hi 0 left right 0 0 (fun _ => []) backing 1 .stay
    (fun _ => some true) (by simp [machine])
  have h2 := emit_step lo hi 1 left right 0 0 a backing 2 .stay
    ![some false, some true, some true, some lo] (by simp [machine])
  have h3 := emit_step lo hi 2 left right 0 0 b backing 3 .stay
    ![none, none, some true, some true] (by simp [machine])
  have h4 := emit_step lo hi 3 left right 0 0 c backing 4 .stay
    ![none, none, some false, some hi] (by simp [machine])
  have hp := Timed.step (by rfl) h1 (Timed.step (by rfl) h2 (Timed.step (by rfl) h3
    (Timed.step (by rfl) h4 (Timed.refl (machine lo hi) (config 4 left right 0 0 d backing)))))
  simpa [HeadMove.apply, hd] using hp

theorem candidates_run (lo hi : Bool) (left right : List Bool) (backing : Fin 4 → List Bool)
    (hw : left.length = right.length) :
    ∃ r : ExecutionReceipt 6 9,
      run (machine lo hi) (2 * left.length + 7)
        ![frame left, frame right, backing 0, backing 1, backing 2, backing 3] = some r ∧
      r.final = config 8 (frame left) (frame right) (2 * left.length) (2 * right.length)
        (fun i => frame (words lo hi left right i)) backing ∧
      r.steps = 2 * left.length + 7 := by
  have ht := scan_run lo hi [] [] left right [] [] (initialized lo hi) backing hw
  have he : finished left right (initialized lo hi) =
      (fun i => frame (words lo hi left right i)) := by
    funext i; fin_cases i <;> simp [finished, initialized, words, frame, frame_append]
  rw [he] at ht
  have hp := (initialize_run lo hi (frame left) (frame right) backing).trans (by simpa using ht)
  obtain ⟨r, hr, hf, hs⟩ := hp.run (by rfl)
  refine ⟨r, ?_, hf, ?_⟩
  · have hin : initialConfiguration (machine lo hi)
        ![frame left, frame right, backing 0, backing 1, backing 2, backing 3] =
        config 0 (frame left) (frame right) 0 0 (fun _ => []) backing := by
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · simp [initialConfiguration, config, overlay]
    unfold run
    rw [hin]
    have he : 4 + (2 * left.length + 3) = 2 * left.length + 7 := by omega
    rw [he] at hr
    exact hr
  · omega

end NearCubicWires.RepairOrdinary.RecoveryRootCandidates
