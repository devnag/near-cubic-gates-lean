import Proof.Foundations.OrdinaryStreaming
import Proof.Foundations.OrdinaryExecutionPrefix

/-! One ordinary stable partition pass for labelled variable-length records.
The tag and every payload bit are copied, in input order, to one of two
sequential tapes. This is the distribution operation needed by the matrix
record sorting route, not a complete sorter or matrix generator. -/
namespace NearCubicWires.RepairOrdinary.StablePartition
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Record := Bool × List Bool

def recordBits (r : Record) : List Bool := true :: r.1 :: frame r.2
def recordsBits (rs : List Record) : List Bool := rs.flatMap recordBits
def stream (rs : List Record) : List Bool := recordsBits rs ++ [false]
def selected (b : Bool) (rs : List Record) : List Record := rs.filter (fun r => r.1 == b)

def extend (b : Bool) (bits : List Bool) (out : Bool → List Bool) : Bool → List Bool :=
  fun tag => if tag = b then out tag ++ bits else out tag

@[simp] theorem extend_nil (b : Bool) (out : Bool → List Bool) : extend b [] out = out := by
  funext tag
  simp [extend]

@[simp] theorem extend_extend (b : Bool) (xs ys : List Bool) (out : Bool → List Bool) :
    extend b ys (extend b xs out) = extend b (xs ++ ys) out := by
  funext tag
  by_cases ht : tag = b <;> simp [extend, ht, List.append_assoc]

def outCells (out : Bool → List Bool) : ℕ := (out false).length + (out true).length

@[simp] theorem extend_cells (b : Bool) (bits : List Bool) (out : Bool → List Bool) :
    outCells (extend b bits out) = outCells out + bits.length := by
  cases b <;> simp [outCells, extend] <;> omega

def config (state : Fin 9) (input : List Bool) (head : ℕ)
    (out : Bool → List Bool) : Configuration 3 9 where
  control := state
  heads := fun t => if t.val = 0 then head
    else if t.val = 1 then (out false).length else (out true).length
  tapes := fun t => if t.val = 0 then input else if t.val = 1 then out false else out true

@[simp] theorem config_control (state : Fin 9) (input : List Bool) (head : ℕ)
    (out : Bool → List Bool) : (config state input head out).control = state := rfl

@[simp] theorem config_cells (state : Fin 9) (input : List Bool) (head : ℕ)
    (out : Bool → List Bool) : (config state input head out).tapeCells = input.length + outCells out := by
  simp [Configuration.tapeCells, config, outCells, Fin.sum_univ_succ]

def tagState (b : Bool) : Fin 9 := if b then 3 else 2
def bodyState (b : Bool) : Fin 9 := if b then 6 else 4
def bitState (b : Bool) : Fin 9 := if b then 7 else 5

def emitAction (next : Fin 9) (move : HeadMove) (tag bit : Bool) : Action 3 9 where
  nextControl := next
  write := fun t => if t.val = (if tag then 2 else 1) then some bit else none
  move := fun t => if t.val = 0 then move
    else if t.val = (if tag then 2 else 1) then .right else .stay

def markAction : Action 3 9 where
  nextControl := 1
  write := fun _ => none
  move := fun t => if t.val = 0 then .right else .stay

def finishAction : Action 3 9 where
  nextControl := 8
  write := fun t => if t.val = 0 then none else some false
  move := fun t => if t.val = 0 then .stay else .right

def machine : Machine 3 9 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val == 8
  rule := fun s scanned =>
    if s.val = 0 then
      if scanned 0 then some markAction else some finishAction
    else if s.val = 1 then some (emitAction (tagState (scanned 0)) .stay (scanned 0) true)
    else if s.val = 2 then some (emitAction (bodyState false) .right false false)
    else if s.val = 3 then some (emitAction (bodyState true) .right true true)
    else if s.val = 4 then
      some (emitAction (if scanned 0 then bitState false else 0) .right false (scanned 0))
    else if s.val = 5 then some (emitAction (bodyState false) .right false (scanned 0))
    else if s.val = 6 then
      some (emitAction (if scanned 0 then bitState true else 0) .right true (scanned 0))
    else if s.val = 7 then some (emitAction (bodyState true) .right true (scanned 0))
    else none

theorem apply_emit (s next : Fin 9) (input : List Bool) (head : ℕ)
    (out : Bool → List Bool) (move : HeadMove) (tag bit : Bool) :
    applyAction (config s input head out) (emitAction next move tag bit) =
      config next input (move.apply head) (extend tag [bit] out) := by
  apply configuration_ext
  · rfl
  · funext t
    cases tag <;> fin_cases t <;>
      simp [applyAction, emitAction, config, extend, HeadMove.apply]
  · funext t
    cases tag <;> fin_cases t <;>
      simp [applyAction, emitAction, config, extend, Streaming.write_append]

theorem body_step (tag bit : Bool) (pre suffix : List Bool) (out : Bool → List Bool) :
    step machine (config (bodyState tag) (pre ++ bit :: suffix) pre.length out) =
      some (config (if bit then bitState tag else 0) (pre ++ bit :: suffix)
        (pre.length + 1) (extend tag [bit] out)) := by
  have hread := Streaming.read_append pre suffix bit
  have hr : machine.rule (bodyState tag)
      (config (bodyState tag) (pre ++ bit :: suffix) pre.length out).scanned =
      some (emitAction (if bit then bitState tag else 0) .right tag bit) := by
    cases tag <;> simp [machine, bodyState, bitState, Configuration.scanned, config, hread]
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _

theorem bit_step (tag bit : Bool) (pre suffix : List Bool) (out : Bool → List Bool) :
    step machine (config (bitState tag) (pre ++ bit :: suffix) pre.length out) =
      some (config (bodyState tag) (pre ++ bit :: suffix)
        (pre.length + 1) (extend tag [bit] out)) := by
  have hread := Streaming.read_append pre suffix bit
  have hr : machine.rule (bitState tag)
      (config (bitState tag) (pre ++ bit :: suffix) pre.length out).scanned =
      some (emitAction (bodyState tag) .right tag bit) := by
    cases tag <;> simp [machine, bodyState, bitState, Configuration.scanned, config, hread]
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _

theorem body_prefix (tag : Bool) (bits pre suffix : List Bool) (out : Bool → List Bool)
    (space : ℕ) (hspace : (pre ++ frame bits ++ suffix).length + outCells out +
      (frame bits).length ≤ space) :
    Prefix machine space (frame bits).length
      (config (bodyState tag) (pre ++ frame bits ++ suffix) pre.length out)
      (config 0 (pre ++ frame bits ++ suffix) (pre.length + (frame bits).length)
        (extend tag (frame bits) out)) := by
  induction bits generalizing pre out with
  | nil =>
    refine Prefix.step ?_ ?_ ?_ (Prefix.refl _ ?_)
    · simpa [frame] using (show (pre ++ frame [] ++ suffix).length + outCells out ≤ space by omega)
    · cases tag <;> rfl
    · simpa [frame] using body_step tag false pre suffix out
    · simp only [config_cells, extend_cells, frame_length, List.length_nil] at hspace ⊢
      omega
  | cons bit bits ih =>
    let input := pre ++ frame (bit :: bits) ++ suffix
    let nextOut := extend tag [true, bit] out
    have hnext : ((pre ++ [true, bit]) ++ frame bits ++ suffix).length + outCells nextOut +
        (frame bits).length ≤ space := by
      simp only [List.length_append, frame_length, List.length_cons, List.length_nil,
        nextOut, extend_cells] at hspace ⊢
      omega
    have htail := ih (pre ++ [true, bit]) nextOut hnext
    have hpre : (pre ++ [true, bit]).length = pre.length + 2 := by simp
    have hpos : pre.length + 2 + (frame bits).length =
        pre.length + (frame (bit :: bits)).length := by simp; omega
    simp only [hpre] at htail
    rw [hpos] at htail
    have htail' : Prefix machine space (frame bits).length
        (config (bodyState tag) input (pre.length + 2) nextOut)
        (config 0 input (pre.length + (frame (bit :: bits)).length)
          (extend tag (frame (bit :: bits)) out)) := by
      simpa [input, nextOut, frame, List.append_assoc] using htail
    have hfirst : step machine (config (bodyState tag) input pre.length out) =
        some (config (bitState tag) input (pre.length + 1) (extend tag [true] out)) := by
      simpa [input, frame, List.append_assoc] using
        body_step tag true pre (bit :: (frame bits ++ suffix)) out
    have hsecond : step machine (config (bitState tag) input (pre.length + 1)
        (extend tag [true] out)) =
        some (config (bodyState tag) input (pre.length + 2) nextOut) := by
      simpa [input, nextOut, frame, List.append_assoc, Nat.add_assoc] using
        bit_step tag bit (pre ++ [true]) (frame bits ++ suffix) (extend tag [true] out)
    have hmidspace : (config (bitState tag) input (pre.length + 1)
        (extend tag [true] out)).tapeCells ≤ space := by
      simp only [config_cells, extend_cells, List.length_singleton]
      change input.length + outCells out + (frame (bit :: bits)).length ≤ space at hspace
      have hpos : 1 ≤ (frame (bit :: bits)).length := by simp
      omega
    have hrun := Prefix.step (p := machine) (space := space)
      (c := config (bodyState tag) input pre.length out)
      (by simp only [config_cells, input]; omega)
      (by cases tag <;> rfl) hfirst
      (Prefix.step hmidspace (by cases tag <;> rfl) hsecond htail')
    simpa [input, frame, Nat.add_assoc] using hrun

theorem mark_step (pre suffix : List Bool) (out : Bool → List Bool) :
    step machine (config 0 (pre ++ true :: suffix) pre.length out) =
      some (config 1 (pre ++ true :: suffix) (pre.length + 1) out) := by
  have hread := Streaming.read_append pre suffix true
  simp [step, machine, Configuration.scanned, config, hread]
  apply configuration_ext
  · rfl
  · funext t
    fin_cases t <;> simp [applyAction, markAction, HeadMove.apply]
  · funext t
    fin_cases t <;> simp [applyAction, markAction]

theorem dispatch_step (tag : Bool) (pre suffix : List Bool) (out : Bool → List Bool) :
    step machine (config 1 (pre ++ tag :: suffix) pre.length out) =
      some (config (tagState tag) (pre ++ tag :: suffix) pre.length (extend tag [true] out)) := by
  have hread := Streaming.read_append pre suffix tag
  have hr : machine.rule 1 (config 1 (pre ++ tag :: suffix) pre.length out).scanned =
      some (emitAction (tagState tag) .stay tag true) := by
    simp [machine, Configuration.scanned, config, hread]
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _

theorem tag_step (tag : Bool) (input : List Bool) (head : ℕ) (out : Bool → List Bool) :
    step machine (config (tagState tag) input head out) =
      some (config (bodyState tag) input (head + 1) (extend tag [tag] out)) := by
  have hr : machine.rule (tagState tag) (config (tagState tag) input head out).scanned =
      some (emitAction (bodyState tag) .right tag tag) := by
    cases tag <;> rfl
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _

theorem record_prefix (r : Record) (pre suffix : List Bool) (out : Bool → List Bool)
    (space : ℕ) (hspace : (pre ++ recordBits r ++ suffix).length + outCells out +
      (recordBits r).length ≤ space) :
    Prefix machine space ((recordBits r).length + 1)
      (config 0 (pre ++ recordBits r ++ suffix) pre.length out)
      (config 0 (pre ++ recordBits r ++ suffix) (pre.length + (recordBits r).length)
        (extend r.1 (recordBits r) out)) := by
  rcases r with ⟨tag, bits⟩
  let input := pre ++ recordBits (tag, bits) ++ suffix
  have htailspace : ((pre ++ [true, tag]) ++ frame bits ++ suffix).length +
      outCells (extend tag [true, tag] out) + (frame bits).length ≤ space := by
    simp only [List.length_append, List.length_cons, List.length_nil, extend_cells,
      recordBits, frame_length] at hspace ⊢
    omega
  have htail := body_prefix tag bits (pre ++ [true, tag]) suffix
    (extend tag [true, tag] out) space htailspace
  have hpre : (pre ++ [true, tag]).length = pre.length + 2 := by simp
  have hpos : pre.length + 2 + (frame bits).length =
      pre.length + (recordBits (tag, bits)).length := by simp [recordBits]; omega
  simp only [hpre] at htail
  rw [hpos] at htail
  have htail' : Prefix machine space (frame bits).length
      (config (bodyState tag) input (pre.length + 2) (extend tag [true, tag] out))
      (config 0 input (pre.length + (recordBits (tag, bits)).length)
        (extend tag (recordBits (tag, bits)) out)) := by
    simpa [input, recordBits, List.append_assoc] using htail
  have hfirst : step machine (config 0 input pre.length out) =
      some (config 1 input (pre.length + 1) out) := by
    simpa [input, recordBits] using mark_step pre (tag :: (frame bits ++ suffix)) out
  have hsecond : step machine (config 1 input (pre.length + 1) out) =
      some (config (tagState tag) input (pre.length + 1) (extend tag [true] out)) := by
    simpa [input, recordBits, List.append_assoc] using
      dispatch_step tag (pre ++ [true]) (frame bits ++ suffix) out
  have hthird : step machine
      (config (tagState tag) input (pre.length + 1) (extend tag [true] out)) =
      some (config (bodyState tag) input (pre.length + 2) (extend tag [true, tag] out)) := by
    simpa [Nat.add_assoc] using tag_step tag input (pre.length + 1) (extend tag [true] out)
  have hsmall : input.length + outCells out + 1 ≤ space := by
    change input.length + outCells out + (recordBits (tag, bits)).length ≤ space at hspace
    have hlen : 1 ≤ (recordBits (tag, bits)).length := by simp [recordBits]
    omega
  have hzero : input.length + outCells out ≤ space := by omega
  have hrun := Prefix.step (p := machine) (space := space)
    (by simpa only [config_cells] using hzero) (by rfl) hfirst
    (Prefix.step (by simpa only [config_cells] using hzero) (by rfl) hsecond
      (Prefix.step (by simpa only [config_cells, extend_cells, List.length_singleton,
          Nat.add_assoc] using hsmall)
        (by cases tag <;> rfl) hthird htail'))
  simpa [input, recordBits, Nat.add_assoc] using hrun

def finishedOut (out : Bool → List Bool) (rs : List Record) : Bool → List Bool :=
  fun b => out b ++ recordsBits (selected b rs) ++ [false]

@[simp] theorem finishedOut_cons (out : Bool → List Bool) (r : Record) (rs : List Record) :
    finishedOut (extend r.1 (recordBits r) out) rs = finishedOut out (r :: rs) := by
  funext b
  rcases r with ⟨tag, bits⟩
  cases tag <;> cases b <;> simp [finishedOut, extend, selected, recordsBits, List.append_assoc]

theorem selected_lengths (rs : List Record) :
    (recordsBits (selected false rs)).length + (recordsBits (selected true rs)).length =
      (recordsBits rs).length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨tag, bits⟩
    cases tag <;> simp [selected, recordsBits] at * <;> omega

@[simp] theorem finishedOut_cells (out : Bool → List Bool) (rs : List Record) :
    outCells (finishedOut out rs) = outCells out + (recordsBits rs).length + 2 := by
  have h := selected_lengths rs
  simp only [outCells, finishedOut, List.length_append, List.length_cons, List.length_nil]
  omega

theorem finish_step (pre : List Bool) (out : Bool → List Bool) :
    step machine (config 0 (pre ++ [false]) pre.length out) =
      some (config 8 (pre ++ [false]) pre.length (finishedOut out [])) := by
  have hread := Streaming.read_append pre [] false
  simp [step, machine, Configuration.scanned, config, hread]
  apply configuration_ext
  · rfl
  · funext t
    fin_cases t <;>
      simp [applyAction, finishAction, HeadMove.apply, finishedOut, selected, recordsBits]
  · funext t
    fin_cases t <;>
      simp [applyAction, finishAction, finishedOut, selected, recordsBits, Streaming.write_append]

theorem records_prefix (rs : List Record) (pre : List Bool) (out : Bool → List Bool)
    (space : ℕ) (hspace : (pre ++ stream rs).length + outCells out +
      (recordsBits rs).length + 2 ≤ space) :
    Prefix machine space ((recordsBits rs).length + rs.length + 1)
      (config 0 (pre ++ stream rs) pre.length out)
      (config 8 (pre ++ stream rs) (pre.length + (recordsBits rs).length) (finishedOut out rs)) := by
  induction rs generalizing pre out with
  | nil =>
    simp only [recordsBits, List.flatMap_nil, List.length_nil, Nat.zero_add, stream,
      List.nil_append, Nat.add_zero] at hspace ⊢
    refine Prefix.step ?_ (by rfl) (finish_step pre out) (Prefix.refl _ ?_)
    · simp only [config_cells]
      omega
    · simpa only [config_cells, finishedOut_cells, recordsBits, List.flatMap_nil,
        List.length_nil, Nat.add_zero, Nat.add_assoc] using hspace
  | cons r rs ih =>
    let input := pre ++ stream (r :: rs)
    have htailspace : ((pre ++ recordBits r) ++ stream rs).length +
        outCells (extend r.1 (recordBits r) out) + (recordsBits rs).length + 2 ≤ space := by
      simp only [stream, recordsBits, List.flatMap_cons, List.length_append,
        extend_cells] at hspace ⊢
      omega
    have htail := ih (pre ++ recordBits r) (extend r.1 (recordBits r) out) htailspace
    have htail' : Prefix machine space ((recordsBits rs).length + rs.length + 1)
        (config 0 input (pre.length + (recordBits r).length) (extend r.1 (recordBits r) out))
        (config 8 input (pre.length + (recordsBits (r :: rs)).length)
          (finishedOut out (r :: rs))) := by
      simpa [input, stream, recordsBits, List.append_assoc, Nat.add_assoc] using htail
    have hrecordspace : (pre ++ recordBits r ++ stream rs).length + outCells out +
        (recordBits r).length ≤ space := by
      simp only [stream, recordsBits, List.flatMap_cons, List.length_append] at hspace ⊢
      omega
    have hfirst := record_prefix r pre (stream rs) out space hrecordspace
    have hfirst' : Prefix machine space ((recordBits r).length + 1)
        (config 0 input pre.length out)
        (config 0 input (pre.length + (recordBits r).length) (extend r.1 (recordBits r) out)) := by
      simpa [input, stream, recordsBits, List.append_assoc] using hfirst
    have hj := hfirst'.trans htail'
    simpa [recordsBits, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj

theorem record_count_le (rs : List Record) : rs.length ≤ (recordsBits rs).length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [recordsBits, List.flatMap_cons, List.length_append, List.length_cons,
      recordBits, frame_length] at ih ⊢
    omega

theorem partition_run (rs : List Record) :
    ∃ r : ExecutionReceipt 3 9,
      run machine ((stream rs).length + rs.length)
        (fun t => if t.val = 0 then stream rs else []) = some r ∧
      r.final = config 8 (stream rs) (recordsBits rs).length
        (fun b => stream (selected b rs)) ∧
      r.final.tapes 1 = stream (selected false rs) ∧
      r.final.tapes 2 = stream (selected true rs) ∧
      r.steps = (stream rs).length + rs.length ∧
      r.steps ≤ 2 * (stream rs).length ∧
      r.peakTapeCells ≤ 2 * (stream rs).length + 1 := by
  have hprefix := records_prefix rs [] (fun _ => []) (2 * (stream rs).length + 1)
    (by simp [stream, outCells]; omega)
  have hspace : (config 8 ([] ++ stream rs) (0 + (recordsBits rs).length)
      (finishedOut (fun _ => []) rs)).tapeCells ≤ 2 * (stream rs).length + 1 := by
    rw [config_cells, finishedOut_cells]
    simp only [outCells, List.length_nil, List.nil_append, stream, List.length_append,
      List.length_singleton]
    omega
  obtain ⟨r, hr, hf, hs, hp⟩ := hprefix.run (by rfl) hspace
  refine ⟨r, ?_, ?_, ?_, ?_, ?_, ?_, hp⟩
  · simpa [run, initialConfiguration, machine, config, outCells, stream,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr
  · rw [hf]
    apply configuration_ext
    · rfl
    · funext t
      fin_cases t <;> simp [config, finishedOut, stream]
    · funext t
      fin_cases t <;> simp [config, finishedOut, stream]
  · simp [hf, config, finishedOut, stream]
  · simp [hf, config, finishedOut, stream]
  · simpa [stream, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  · have hc := record_count_le rs
    simp only [stream, List.length_append, List.length_singleton] at hs ⊢
    omega

end NearCubicWires.RepairOrdinary.StablePartition
