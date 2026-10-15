import Proof.MachineModel.OrdinaryPartitionWorkspace

/-! Rotate the leading bit of each nonempty record to its end. This exposes
the next radix bit while preserving every record and its fixed width. Old
output cells remain as an explicit retained suffix. -/
namespace NearCubicWires.RepairOrdinary.RecordRotate
open LocalBitMultitape StablePartition
open StablePartition.Workspace (overlay overlay_write overlay_length)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rotate (r : Record) : Record := match r.2 with
  | [] => r
  | bit :: tail => (bit, tail ++ [r.1])

@[simp] theorem rotate_record_length (r : Record) : (recordBits (rotate r)).length = (recordBits r).length := by
  rcases r with ⟨tag, bits⟩
  cases bits <;> simp [rotate, recordBits]

theorem rotate_stream_length (rs : List Record) : (stream (rs.map rotate)).length = (stream rs).length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [stream, recordsBits, List.map_cons, List.flatMap_cons, List.length_append] at ih ⊢
    have h := rotate_record_length r
    omega

def firstMarker (tag : Bool) : Fin 14 := if tag then 3 else 2
def firstBit (tag : Bool) : Fin 14 := if tag then 5 else 4
def bodyMarker (tag : Bool) : Fin 14 := if tag then 7 else 6
def bodyBit (tag : Bool) : Fin 14 := if tag then 9 else 8
def finalBit (tag : Bool) : Fin 14 := if tag then 11 else 10

def config (state : Fin 14) (input : List Bool) (head : ℕ) (out backing : List Bool) : Configuration 2 14 where
  control := state
  heads := fun i => if i.val = 0 then head else out.length
  tapes := fun i => if i.val = 0 then input else overlay out backing

@[simp] theorem config_control (state : Fin 14) (input : List Bool) (head : ℕ) (out backing : List Bool) :
    (config state input head out backing).control = state := rfl

theorem config_cells_le (state : Fin 14) (input : List Bool) (head : ℕ) (out backing : List Bool) :
    (config state input head out backing).tapeCells ≤ input.length + out.length + backing.length := by
  simp [Configuration.tapeCells, config, Fin.sum_univ_succ]
  omega

def emitAction (next : Fin 14) (inputMove : HeadMove) (bit : Bool) : Action 2 14 where
  nextControl := next
  write := fun i => if i.val = 0 then none else some bit
  move := fun i => if i.val = 0 then inputMove else .right

def skipAction (next : Fin 14) : Action 2 14 where
  nextControl := next
  write := fun _ => none
  move := fun i => if i.val = 0 then .right else .stay

def machine : Machine 2 14 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val == 13
  rule := fun s scanned =>
    if s.val = 0 then
      if scanned 0 then some (emitAction 1 .right true) else some (emitAction 13 .stay false)
    else if s.val = 1 then some (skipAction (firstMarker (scanned 0)))
    else if s.val = 2 then
      if scanned 0 then some (skipAction (firstBit false)) else some (emitAction 12 .stay false)
    else if s.val = 3 then
      if scanned 0 then some (skipAction (firstBit true)) else some (emitAction 12 .stay true)
    else if s.val = 4 then some (emitAction (bodyMarker false) .right (scanned 0))
    else if s.val = 5 then some (emitAction (bodyMarker true) .right (scanned 0))
    else if s.val = 6 then
      if scanned 0 then some (emitAction (bodyBit false) .right true)
      else some (emitAction (finalBit false) .stay true)
    else if s.val = 7 then
      if scanned 0 then some (emitAction (bodyBit true) .right true)
      else some (emitAction (finalBit true) .stay true)
    else if s.val = 8 then some (emitAction (bodyMarker false) .right (scanned 0))
    else if s.val = 9 then some (emitAction (bodyMarker true) .right (scanned 0))
    else if s.val = 10 then some (emitAction 12 .stay false)
    else if s.val = 11 then some (emitAction 12 .stay true)
    else if s.val = 12 then some (emitAction 0 .right false)
    else none

theorem apply_emit (state next : Fin 14) (input : List Bool) (head : ℕ)
    (out backing : List Bool) (move : HeadMove) (bit : Bool) :
    applyAction (config state input head out backing) (emitAction next move bit) =
      config next input (move.apply head) (out ++ [bit]) backing := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, emitAction, config, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, emitAction, config, overlay_write]

theorem apply_skip (state next : Fin 14) (input : List Bool) (head : ℕ) (out backing : List Bool) :
    applyAction (config state input head out backing) (skipAction next) =
      config next input (head + 1) out backing := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, skipAction, config, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, skipAction, config]

theorem close_record_step (input : List Bool) (head : ℕ) (out backing : List Bool) :
    step machine (config 12 input head out backing) =
      some (config 0 input (head + 1) (out ++ [false]) backing) := by
  have hr : machine.rule 12 (config 12 input head out backing).scanned = some (emitAction 0 .right false) := rfl
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _

theorem final_bit_step (tag : Bool) (input : List Bool) (head : ℕ) (out backing : List Bool) :
    step machine (config (finalBit tag) input head out backing) =
      some (config 12 input head (out ++ [tag]) backing) := by
  have hr : machine.rule (finalBit tag) (config (finalBit tag) input head out backing).scanned =
      some (emitAction 12 .stay tag) := by cases tag <;> rfl
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _

theorem body_end_step (tag : Bool) (pre tail out backing : List Bool) :
    step machine (config (bodyMarker tag) (pre ++ false :: tail) pre.length out backing) =
      some (config (finalBit tag) (pre ++ false :: tail) pre.length (out ++ [true]) backing) := by
  have hread := Streaming.read_append pre tail false
  have hr : machine.rule (bodyMarker tag)
      (config (bodyMarker tag) (pre ++ false :: tail) pre.length out backing).scanned =
      some (emitAction (finalBit tag) .stay true) := by
    cases tag <;> simp [machine, config, Configuration.scanned, bodyMarker, finalBit, hread]
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _

theorem body_marker_step (tag : Bool) (pre tail out backing : List Bool) :
    step machine (config (bodyMarker tag) (pre ++ true :: tail) pre.length out backing) =
      some (config (bodyBit tag) (pre ++ true :: tail) (pre.length + 1) (out ++ [true]) backing) := by
  have hread := Streaming.read_append pre tail true
  have hr : machine.rule (bodyMarker tag)
      (config (bodyMarker tag) (pre ++ true :: tail) pre.length out backing).scanned =
      some (emitAction (bodyBit tag) .right true) := by
    cases tag <;> simp [machine, config, Configuration.scanned, bodyMarker, bodyBit, hread]
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _

theorem body_bit_step (tag bit : Bool) (pre tail out backing : List Bool) :
    step machine (config (bodyBit tag) (pre ++ bit :: tail) pre.length out backing) =
      some (config (bodyMarker tag) (pre ++ bit :: tail) (pre.length + 1) (out ++ [bit]) backing) := by
  have hread := Streaming.read_append pre tail bit
  have hr : machine.rule (bodyBit tag)
      (config (bodyBit tag) (pre ++ bit :: tail) pre.length out backing).scanned =
      some (emitAction (bodyMarker tag) .right bit) := by
    cases tag <;> simp [machine, config, Configuration.scanned, bodyMarker, bodyBit, hread]
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _

theorem body_prefix (tag : Bool) (bits pre tail out backing : List Bool) (space : ℕ)
    (hspace : (pre ++ frame bits ++ tail).length + out.length +
      (frame (bits ++ [tag])).length + backing.length ≤ space) :
    Prefix machine space (frame (bits ++ [tag])).length
      (config (bodyMarker tag) (pre ++ frame bits ++ tail) pre.length out backing)
      (config 0 (pre ++ frame bits ++ tail) (pre.length + (frame bits).length)
        (out ++ frame (bits ++ [tag])) backing) := by
  induction bits generalizing pre out with
  | nil =>
    let input := pre ++ false :: tail
    have hsmall : input.length + out.length + 3 + backing.length ≤ space := by
      simpa [input, frame] using hspace
    have hlast : step machine (config 12 input pre.length (out ++ [true, tag]) backing) =
        some (config 0 input (pre.length + 1) (out ++ [true, tag, false]) backing) := by
      simpa [List.append_assoc] using close_record_step input pre.length (out ++ [true, tag]) backing
    have hmid : step machine (config (finalBit tag) input pre.length (out ++ [true]) backing) =
        some (config 12 input pre.length (out ++ [true, tag]) backing) := by
      simpa [List.append_assoc] using final_bit_step tag input pre.length (out ++ [true]) backing
    have hc : ∀ (s : Fin 14) (head : ℕ) (xs : List Bool), xs.length ≤ 3 →
        (config s input head (out ++ xs) backing).tapeCells ≤ space := by
      intro s head xs hx
      apply (config_cells_le _ _ _ _ _).trans
      simp only [List.length_append]
      omega
    have hrun := Prefix.step (p := machine) (space := space)
      ((config_cells_le (bodyMarker tag) input pre.length out backing).trans (by omega))
      (by cases tag <;> rfl) (body_end_step tag pre tail out backing)
      (Prefix.step (hc _ _ [true] (by decide)) (by cases tag <;> rfl) hmid
        (Prefix.step (hc _ _ [true, tag] (by simp)) (by rfl) hlast
          (Prefix.refl _ (hc _ _ [true, tag, false] (by simp)))))
    simpa [input, frame] using hrun
  | cons bit bits ih =>
    let input := pre ++ frame (bit :: bits) ++ tail
    have htailspace : ((pre ++ [true, bit]) ++ frame bits ++ tail).length +
        (out ++ [true, bit]).length + (frame (bits ++ [tag])).length + backing.length ≤ space := by
      simp only [List.length_append, List.length_cons, List.length_nil, frame_length] at hspace ⊢
      omega
    have htail := ih (pre ++ [true, bit]) (out ++ [true, bit]) htailspace
    have hpre : (pre ++ [true, bit]).length = pre.length + 2 := by simp
    have hpos : pre.length + 2 + (frame bits).length = pre.length + (frame (bit :: bits)).length := by
      simp
      omega
    simp only [hpre] at htail
    rw [hpos] at htail
    have htail' : Prefix machine space (frame (bits ++ [tag])).length
        (config (bodyMarker tag) input (pre.length + 2) (out ++ [true, bit]) backing)
        (config 0 input (pre.length + (frame (bit :: bits)).length)
          (out ++ frame ((bit :: bits) ++ [tag])) backing) := by
      simpa [input, frame, List.append_assoc] using htail
    have hfirst : step machine (config (bodyMarker tag) input pre.length out backing) =
        some (config (bodyBit tag) input (pre.length + 1) (out ++ [true]) backing) := by
      simpa [input, frame, List.append_assoc] using body_marker_step tag pre (bit :: (frame bits ++ tail)) out backing
    have hsecond : step machine (config (bodyBit tag) input (pre.length + 1) (out ++ [true]) backing) =
        some (config (bodyMarker tag) input (pre.length + 2) (out ++ [true, bit]) backing) := by
      simpa [input, frame, List.append_assoc, Nat.add_assoc] using
        body_bit_step tag bit (pre ++ [true]) (frame bits ++ tail) (out ++ [true]) backing
    have hsmall : input.length + out.length + 1 + backing.length ≤ space := by
      change input.length + out.length + (frame ((bit :: bits) ++ [tag])).length + backing.length ≤ space at hspace
      have hp : 1 ≤ (frame ((bit :: bits) ++ [tag])).length := by simp
      omega
    have hmiddle : (config (bodyBit tag) input (pre.length + 1) (out ++ [true]) backing).tapeCells ≤ space := by
      apply (config_cells_le _ _ _ _ _).trans
      simp only [List.length_append, List.length_singleton]
      omega
    have hrun := Prefix.step (p := machine) (space := space)
      ((config_cells_le (bodyMarker tag) input pre.length out backing).trans (by omega))
      (by cases tag <;> rfl) hfirst
      (Prefix.step hmiddle (by cases tag <;> rfl) hsecond htail')
    simpa [input, frame, Nat.add_assoc] using hrun

theorem open_record_step (pre tail out backing : List Bool) :
    step machine (config 0 (pre ++ true :: tail) pre.length out backing) =
      some (config 1 (pre ++ true :: tail) (pre.length + 1) (out ++ [true]) backing) := by
  have hread := Streaming.read_append pre tail true
  have hr : machine.rule 0 (config 0 (pre ++ true :: tail) pre.length out backing).scanned =
      some (emitAction 1 .right true) := by simp [machine, config, Configuration.scanned, hread]
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _

theorem save_tag_step (tag : Bool) (pre tail out backing : List Bool) :
    step machine (config 1 (pre ++ tag :: tail) pre.length out backing) =
      some (config (firstMarker tag) (pre ++ tag :: tail) (pre.length + 1) out backing) := by
  have hread := Streaming.read_append pre tail tag
  have hr : machine.rule 1 (config 1 (pre ++ tag :: tail) pre.length out backing).scanned =
      some (skipAction (firstMarker tag)) := by simp [machine, config, Configuration.scanned, hread]
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_skip _ _ _ _ _ _

theorem single_tag_step (tag : Bool) (pre tail out backing : List Bool) :
    step machine (config (firstMarker tag) (pre ++ false :: tail) pre.length out backing) =
      some (config 12 (pre ++ false :: tail) pre.length (out ++ [tag]) backing) := by
  have hread := Streaming.read_append pre tail false
  have hr : machine.rule (firstMarker tag)
      (config (firstMarker tag) (pre ++ false :: tail) pre.length out backing).scanned =
      some (emitAction 12 .stay tag) := by
    cases tag <;> simp [machine, config, Configuration.scanned, firstMarker, hread]
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _

theorem first_marker_step (tag : Bool) (pre tail out backing : List Bool) :
    step machine (config (firstMarker tag) (pre ++ true :: tail) pre.length out backing) =
      some (config (firstBit tag) (pre ++ true :: tail) (pre.length + 1) out backing) := by
  have hread := Streaming.read_append pre tail true
  have hr : machine.rule (firstMarker tag)
      (config (firstMarker tag) (pre ++ true :: tail) pre.length out backing).scanned =
      some (skipAction (firstBit tag)) := by
    cases tag <;> simp [machine, config, Configuration.scanned, firstMarker, firstBit, hread]
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_skip _ _ _ _ _ _

theorem first_bit_step (tag bit : Bool) (pre tail out backing : List Bool) :
    step machine (config (firstBit tag) (pre ++ bit :: tail) pre.length out backing) =
      some (config (bodyMarker tag) (pre ++ bit :: tail) (pre.length + 1) (out ++ [bit]) backing) := by
  have hread := Streaming.read_append pre tail bit
  have hr : machine.rule (firstBit tag)
      (config (firstBit tag) (pre ++ bit :: tail) pre.length out backing).scanned =
      some (emitAction (bodyMarker tag) .right bit) := by
    cases tag <;> simp [machine, config, Configuration.scanned, firstBit, bodyMarker, hread]
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _

def recordCost (r : Record) : ℕ := match r.2 with
  | [] => 4
  | _ :: _ => 2 * r.2.length + 5

theorem record_prefix (r : Record) (pre tail out backing : List Bool) (space : ℕ)
    (hspace : (pre ++ recordBits r ++ tail).length + out.length + (recordBits r).length + backing.length ≤ space) :
    Prefix machine space (recordCost r)
      (config 0 (pre ++ recordBits r ++ tail) pre.length out backing)
      (config 0 (pre ++ recordBits r ++ tail) (pre.length + (recordBits r).length)
        (out ++ recordBits (rotate r)) backing) := by
  rcases r with ⟨tag, bits⟩
  let input := pre ++ recordBits (tag, bits) ++ tail
  have hc : ∀ (s : Fin 14) (head : ℕ) (xs : List Bool), xs.length ≤ (recordBits (tag, bits)).length →
      (config s input head (out ++ xs) backing).tapeCells ≤ space := by
    intro s head xs hx
    apply (config_cells_le _ _ _ _ _).trans
    simp only [List.length_append]
    change input.length + out.length + (recordBits (tag, bits)).length + backing.length ≤ space at hspace
    omega
  have hzero : (config 0 input pre.length out backing).tapeCells ≤ space := by
    simpa using hc 0 pre.length [] (by simp)
  have hone : (config 1 input (pre.length + 1) (out ++ [true]) backing).tapeCells ≤ space :=
    hc _ _ [true] (by simp [recordBits])
  have hmarker : (config (firstMarker tag) input (pre.length + 2) (out ++ [true]) backing).tapeCells ≤ space :=
    hc _ _ [true] (by simp [recordBits])
  have hfirst : step machine (config 0 input pre.length out backing) =
      some (config 1 input (pre.length + 1) (out ++ [true]) backing) := by
    simpa [input, recordBits] using open_record_step pre (tag :: (frame bits ++ tail)) out backing
  have hsave : step machine (config 1 input (pre.length + 1) (out ++ [true]) backing) =
      some (config (firstMarker tag) input (pre.length + 2) (out ++ [true]) backing) := by
    simpa [input, recordBits, List.append_assoc, Nat.add_assoc] using
      save_tag_step tag (pre ++ [true]) (frame bits ++ tail) (out ++ [true]) backing
  cases bits with
  | nil =>
    have hsingle : step machine (config (firstMarker tag) input (pre.length + 2) (out ++ [true]) backing) =
        some (config 12 input (pre.length + 2) (out ++ [true, tag]) backing) := by
      simpa [input, recordBits, frame, List.append_assoc] using
        single_tag_step tag (pre ++ [true, tag]) tail (out ++ [true]) backing
    have hclose : step machine (config 12 input (pre.length + 2) (out ++ [true, tag]) backing) =
        some (config 0 input (pre.length + 3) (out ++ [true, tag, false]) backing) := by
      simpa [List.append_assoc, Nat.add_assoc] using
        close_record_step input (pre.length + 2) (out ++ [true, tag]) backing
    have hp := Prefix.step hzero (by rfl) hfirst
      (Prefix.step hone (by rfl) hsave
        (Prefix.step hmarker (by cases tag <;> rfl) hsingle
          (Prefix.step (hc _ _ [true, tag] (by simp [recordBits])) (by rfl) hclose
            (Prefix.refl _ (hc _ _ [true, tag, false] (by simp [recordBits]))))))
    simpa [input, recordCost, recordBits, rotate, frame] using hp
  | cons bit bits =>
    have hbodyspace : ((pre ++ [true, tag, true, bit]) ++ frame bits ++ tail).length +
        (out ++ [true, bit]).length + (frame (bits ++ [tag])).length + backing.length ≤ space := by
      simp only [recordBits, List.length_append, List.length_cons, List.length_nil, frame_length] at hspace ⊢
      omega
    have hbody := body_prefix tag bits (pre ++ [true, tag, true, bit]) tail (out ++ [true, bit]) backing space hbodyspace
    have hpre : (pre ++ [true, tag, true, bit]).length = pre.length + 4 := by simp
    have hpos : pre.length + 4 + (frame bits).length = pre.length + (recordBits (tag, bit :: bits)).length := by
      simp [recordBits]
      omega
    simp only [hpre] at hbody
    rw [hpos] at hbody
    have hbody' : Prefix machine space (frame (bits ++ [tag])).length
        (config (bodyMarker tag) input (pre.length + 4) (out ++ [true, bit]) backing)
        (config 0 input (pre.length + (recordBits (tag, bit :: bits)).length)
          (out ++ recordBits (rotate (tag, bit :: bits))) backing) := by
      simpa [input, recordBits, rotate, frame, List.append_assoc] using hbody
    have hskip : step machine (config (firstMarker tag) input (pre.length + 2) (out ++ [true]) backing) =
        some (config (firstBit tag) input (pre.length + 3) (out ++ [true]) backing) := by
      simpa [input, recordBits, frame, List.append_assoc, Nat.add_assoc] using
        first_marker_step tag (pre ++ [true, tag]) (bit :: (frame bits ++ tail)) (out ++ [true]) backing
    have hcopy : step machine (config (firstBit tag) input (pre.length + 3) (out ++ [true]) backing) =
        some (config (bodyMarker tag) input (pre.length + 4) (out ++ [true, bit]) backing) := by
      simpa [input, recordBits, frame, List.append_assoc, Nat.add_assoc] using
        first_bit_step tag bit (pre ++ [true, tag, true]) (frame bits ++ tail) (out ++ [true]) backing
    have hp := Prefix.step hzero (by rfl) hfirst
      (Prefix.step hone (by rfl) hsave
        (Prefix.step hmarker (by cases tag <;> rfl) hskip
          (Prefix.step (hc _ _ [true] (by simp [recordBits])) (by cases tag <;> rfl) hcopy hbody')))
    simpa [input, recordCost, Nat.add_assoc, Nat.mul_add] using hp

def recordsCost (rs : List Record) : ℕ := (rs.map recordCost).sum

theorem recordCost_le (r : Record) : recordCost r ≤ 2 * (recordBits r).length := by
  rcases r with ⟨tag, bits⟩
  cases bits <;> simp [recordCost, recordBits]
  omega

theorem recordsCost_le (rs : List Record) : recordsCost rs ≤ 2 * (recordsBits rs).length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have h := recordCost_le r
    simp only [recordsCost, List.map_cons, List.sum_cons, recordsBits, List.flatMap_cons, List.length_append] at ih ⊢
    omega

theorem records_prefix (rs : List Record) (pre tail out backing : List Bool) (space : ℕ)
    (hspace : (pre ++ recordsBits rs ++ tail).length + out.length + (recordsBits rs).length + backing.length ≤ space) :
    Prefix machine space (recordsCost rs)
      (config 0 (pre ++ recordsBits rs ++ tail) pre.length out backing)
      (config 0 (pre ++ recordsBits rs ++ tail) (pre.length + (recordsBits rs).length)
        (out ++ recordsBits (rs.map rotate)) backing) := by
  induction rs generalizing pre out with
  | nil =>
    simp only [recordsBits, List.flatMap_nil, List.map_nil, List.length_nil, List.append_nil,
      Nat.add_zero, recordsCost, List.sum_nil] at hspace ⊢
    exact Prefix.refl _ ((config_cells_le _ _ _ _ _).trans hspace)
  | cons r rs ih =>
    let input := pre ++ recordsBits (r :: rs) ++ tail
    have htailspace : ((pre ++ recordBits r) ++ recordsBits rs ++ tail).length +
        (out ++ recordBits (rotate r)).length + (recordsBits rs).length + backing.length ≤ space := by
      simp only [recordsBits, List.flatMap_cons, List.length_append, rotate_record_length] at hspace ⊢
      omega
    have htail := ih (pre ++ recordBits r) (out ++ recordBits (rotate r)) htailspace
    have htail' : Prefix machine space (recordsCost rs)
        (config 0 input (pre.length + (recordBits r).length) (out ++ recordBits (rotate r)) backing)
        (config 0 input (pre.length + (recordsBits (r :: rs)).length)
          (out ++ recordsBits ((r :: rs).map rotate)) backing) := by
      simpa [input, recordsBits, List.append_assoc, Nat.add_assoc] using htail
    have hrecordspace : (pre ++ recordBits r ++ (recordsBits rs ++ tail)).length + out.length +
        (recordBits r).length + backing.length ≤ space := by
      simp only [recordsBits, List.flatMap_cons, List.length_append] at hspace ⊢
      omega
    have hfirst := record_prefix r pre (recordsBits rs ++ tail) out backing space hrecordspace
    have hfirst' : Prefix machine space (recordCost r)
        (config 0 input pre.length out backing)
        (config 0 input (pre.length + (recordBits r).length) (out ++ recordBits (rotate r)) backing) := by
      simpa [input, recordsBits, List.append_assoc] using hfirst
    have hj := hfirst'.trans htail'
    simpa [input, recordsCost, recordsBits, List.append_assoc] using hj

theorem finish_step (pre junk out backing : List Bool) :
    step machine (config 0 (pre ++ false :: junk) pre.length out backing) =
      some (config 13 (pre ++ false :: junk) pre.length (out ++ [false]) backing) := by
  have hread := Streaming.read_append pre junk false
  have hr : machine.rule 0 (config 0 (pre ++ false :: junk) pre.length out backing).scanned =
      some (emitAction 13 .stay false) := by simp [machine, config, Configuration.scanned, hread]
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _

theorem rotate_run (rs : List Record) (junk backing : List Bool) (capacity : ℕ)
    (hi : (stream rs).length + junk.length ≤ capacity) (hb : backing.length ≤ capacity) :
    ∃ r : ExecutionReceipt 2 14,
      run machine (recordsCost rs + 1)
        (fun i => if i.val = 0 then stream rs ++ junk else backing) = some r ∧
      r.final.tapes 0 = stream rs ++ junk ∧
      r.final.tapes 1 = overlay (stream (rs.map rotate)) backing ∧
      (∀ i, (r.final.tapes i).length ≤ capacity) ∧
      r.steps = recordsCost rs + 1 ∧ r.steps ≤ 2 * (stream rs).length ∧
      r.peakTapeCells ≤ 3 * capacity := by
  let input := stream rs ++ junk
  let output := stream (rs.map rotate)
  let space := input.length + (stream rs).length + backing.length
  have hl := rotate_stream_length rs
  have he : (recordsBits (rs.map rotate)).length = (recordsBits rs).length := by
    simpa only [stream, List.length_append, List.length_singleton, Nat.add_right_cancel_iff] using hl
  have hprefix := records_prefix rs [] (false :: junk) [] backing space (by
    simp only [space, input, stream, List.length_append, List.length_nil, List.length_cons, List.nil_append]
    omega)
  have hprefix' : Prefix machine space (recordsCost rs)
      (config 0 input 0 [] backing)
      (config 0 input (recordsBits rs).length (recordsBits (rs.map rotate)) backing) := by
    simpa [input, stream, List.append_assoc] using hprefix
  have hfinalspace : (config 13 input (recordsBits rs).length output backing).tapeCells ≤ space := by
    apply (config_cells_le _ _ _ _ _).trans
    dsimp only [space, output]
    rw [hl]
  have hfinishspace : (config 0 input (recordsBits rs).length (recordsBits (rs.map rotate)) backing).tapeCells ≤ space := by
    apply (config_cells_le _ _ _ _ _).trans
    simp only [space, stream, List.length_append, List.length_singleton, he]
    omega
  have hfinish : step machine (config 0 input (recordsBits rs).length (recordsBits (rs.map rotate)) backing) =
      some (config 13 input (recordsBits rs).length output backing) := by
    simpa [input, output, stream, List.append_assoc] using finish_step (recordsBits rs) junk (recordsBits (rs.map rotate)) backing
  have hwhole := hprefix'.trans (Prefix.step hfinishspace (by rfl) hfinish (Prefix.refl _ hfinalspace))
  obtain ⟨r, hr, hf, hs, hp⟩ := hwhole.run (by rfl) hfinalspace
  refine ⟨r, ?_, ?_, ?_, ?_, hs, ?_, ?_⟩
  · simpa [run, initialConfiguration, machine, config, overlay, input] using hr
  · simp [hf, config, input]
  · simp [hf, config, output]
  · intro i
    fin_cases i
    · simpa [hf, config, input] using hi
    · have hmax : max output.length backing.length ≤ capacity := max_le (by dsimp [output]; rw [hl]; omega) hb
      simpa [hf, config] using hmax
  · have h := recordsCost_le rs
    simp only [stream, List.length_append, List.length_singleton]
    omega
  · simp only [space, input, List.length_append] at hp
    omega

end NearCubicWires.RepairOrdinary.RecordRotate
