import Proof.MachineModel.OrdinaryPartitionWorkspace

/-! Sequential concatenation of two self-delimiting record streams. The first
stream terminator triggers a real switch; only the final terminator is emitted.
Output overwrites retained storage, rather than allocating another tape. -/
namespace NearCubicWires.RepairOrdinary.StreamConcat
open LocalBitMultitape StablePartition
open StablePartition.Workspace (overlay overlay_write overlay_length)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def activeTape (phase : Bool) : Fin 3 := if phase then 1 else 0
def baseState (phase : Bool) : Fin 9 := if phase then 4 else 0
def tagState (phase : Bool) : Fin 9 := if phase then 5 else 1
def bodyState (phase : Bool) : Fin 9 := if phase then 6 else 2
def bitState (phase : Bool) : Fin 9 := if phase then 7 else 3

def config (phase : Bool) (state : Fin 9) (active : List Bool) (head : ℕ)
    (other : List Bool) (otherHead : ℕ) (out backing : List Bool) : Configuration 3 9 where
  control := state
  heads := fun i => if i.val = 2 then out.length
    else if i = activeTape phase then head else otherHead
  tapes := fun i => if i.val = 2 then overlay out backing
    else if i = activeTape phase then active else other

@[simp] theorem config_control (phase : Bool) (state : Fin 9) (active : List Bool) (head : ℕ)
    (other : List Bool) (otherHead : ℕ) (out backing : List Bool) :
    (config phase state active head other otherHead out backing).control = state := rfl

theorem config_cells_le (phase : Bool) (state : Fin 9) (active : List Bool) (head : ℕ)
    (other : List Bool) (otherHead : ℕ) (out backing : List Bool) :
    (config phase state active head other otherHead out backing).tapeCells ≤
      active.length + other.length + out.length + backing.length := by
  cases phase <;> simp [Configuration.tapeCells, config, activeTape, Fin.sum_univ_succ] <;> omega

def emitAction (phase : Bool) (next : Fin 9) (bit : Bool) : Action 3 9 where
  nextControl := next
  write := fun i => if i.val = 2 then some bit else none
  move := fun i => if i.val = 2 ∨ i = activeTape phase then .right else .stay

def switchAction : Action 3 9 where
  nextControl := 4
  write := fun _ => none
  move := fun _ => .stay

def finishAction : Action 3 9 where
  nextControl := 8
  write := fun i => if i.val = 2 then some false else none
  move := fun i => if i.val = 2 then .right else .stay

def machine : Machine 3 9 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val == 8
  rule := fun s scanned =>
    if s.val = 0 then
      if scanned 0 then some (emitAction false (tagState false) true) else some switchAction
    else if s.val = 1 then some (emitAction false (bodyState false) (scanned 0))
    else if s.val = 2 then some (emitAction false
      (if scanned 0 then bitState false else baseState false) (scanned 0))
    else if s.val = 3 then some (emitAction false (bodyState false) (scanned 0))
    else if s.val = 4 then
      if scanned 1 then some (emitAction true (tagState true) true) else some finishAction
    else if s.val = 5 then some (emitAction true (bodyState true) (scanned 1))
    else if s.val = 6 then some (emitAction true
      (if scanned 1 then bitState true else baseState true) (scanned 1))
    else if s.val = 7 then some (emitAction true (bodyState true) (scanned 1))
    else none

theorem apply_emit (phase : Bool) (state next : Fin 9) (active : List Bool) (head : ℕ)
    (other : List Bool) (otherHead : ℕ) (out backing : List Bool) (bit : Bool) :
    applyAction (config phase state active head other otherHead out backing) (emitAction phase next bit) =
      config phase next active (head + 1) other otherHead (out ++ [bit]) backing := by
  apply configuration_ext
  · rfl
  · funext i
    cases phase <;> fin_cases i <;> simp [applyAction, config, emitAction, activeTape, HeadMove.apply]
  · funext i
    cases phase <;> fin_cases i <;> simp [applyAction, config, emitAction, activeTape, overlay_write]

theorem body_step (phase bit : Bool) (pre tail other : List Bool) (otherHead : ℕ)
    (out backing : List Bool) :
    step machine (config phase (bodyState phase) (pre ++ bit :: tail) pre.length other otherHead out backing) =
      some (config phase (if bit then bitState phase else baseState phase) (pre ++ bit :: tail)
        (pre.length + 1) other otherHead (out ++ [bit]) backing) := by
  have hread := Streaming.read_append pre tail bit
  have hr : machine.rule (bodyState phase)
      (config phase (bodyState phase) (pre ++ bit :: tail) pre.length other otherHead out backing).scanned =
      some (emitAction phase (if bit then bitState phase else baseState phase) bit) := by
    cases phase <;> simp [machine, config, Configuration.scanned, activeTape, bodyState, bitState, baseState, hread]
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _ _ _

theorem bit_step (phase bit : Bool) (pre tail other : List Bool) (otherHead : ℕ)
    (out backing : List Bool) :
    step machine (config phase (bitState phase) (pre ++ bit :: tail) pre.length other otherHead out backing) =
      some (config phase (bodyState phase) (pre ++ bit :: tail)
        (pre.length + 1) other otherHead (out ++ [bit]) backing) := by
  have hread := Streaming.read_append pre tail bit
  have hr : machine.rule (bitState phase)
      (config phase (bitState phase) (pre ++ bit :: tail) pre.length other otherHead out backing).scanned =
      some (emitAction phase (bodyState phase) bit) := by
    cases phase <;> simp [machine, config, Configuration.scanned, activeTape, bodyState, bitState, hread]
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _ _ _

theorem body_prefix (phase : Bool) (bits pre tail other : List Bool) (otherHead : ℕ)
    (out backing : List Bool) (space : ℕ)
    (hspace : (pre ++ frame bits ++ tail).length + other.length + out.length +
      (frame bits).length + backing.length ≤ space) :
    Prefix machine space (frame bits).length
      (config phase (bodyState phase) (pre ++ frame bits ++ tail) pre.length other otherHead out backing)
      (config phase (baseState phase) (pre ++ frame bits ++ tail)
        (pre.length + (frame bits).length) other otherHead (out ++ frame bits) backing) := by
  induction bits generalizing pre out with
  | nil =>
    refine Prefix.step ?_ (by cases phase <;> rfl) ?_ (Prefix.refl _ ?_)
    · apply (config_cells_le _ _ _ _ _ _ _ _).trans
      omega
    · simpa [frame] using body_step phase false pre tail other otherHead out backing
    · apply (config_cells_le _ _ _ _ _ _ _ _).trans
      simp only [frame, List.length_append, List.length_singleton] at hspace ⊢
      omega
  | cons bit bits ih =>
    let input := pre ++ frame (bit :: bits) ++ tail
    have htailspace : ((pre ++ [true, bit]) ++ frame bits ++ tail).length + other.length +
        (out ++ [true, bit]).length + (frame bits).length + backing.length ≤ space := by
      simp only [List.length_append, List.length_cons, List.length_nil, frame_length] at hspace ⊢
      omega
    have htail := ih (pre ++ [true, bit]) (out ++ [true, bit]) htailspace
    have hpre : (pre ++ [true, bit]).length = pre.length + 2 := by simp
    have hpos : pre.length + 2 + (frame bits).length = pre.length + (frame (bit :: bits)).length := by
      simp
      omega
    simp only [hpre] at htail
    rw [hpos] at htail
    have htail' : Prefix machine space (frame bits).length
        (config phase (bodyState phase) input (pre.length + 2) other otherHead (out ++ [true, bit]) backing)
        (config phase (baseState phase) input (pre.length + (frame (bit :: bits)).length)
          other otherHead (out ++ frame (bit :: bits)) backing) := by
      simpa [input, frame, List.append_assoc] using htail
    have hfirst : step machine (config phase (bodyState phase) input pre.length other otherHead out backing) =
        some (config phase (bitState phase) input (pre.length + 1) other otherHead (out ++ [true]) backing) := by
      simpa [input, frame, List.append_assoc] using
        body_step phase true pre (bit :: (frame bits ++ tail)) other otherHead out backing
    have hsecond : step machine
        (config phase (bitState phase) input (pre.length + 1) other otherHead (out ++ [true]) backing) =
        some (config phase (bodyState phase) input (pre.length + 2) other otherHead (out ++ [true, bit]) backing) := by
      simpa [input, frame, List.append_assoc, Nat.add_assoc] using
        bit_step phase bit (pre ++ [true]) (frame bits ++ tail) other otherHead (out ++ [true]) backing
    have hsmall : input.length + other.length + out.length + 1 + backing.length ≤ space := by
      change input.length + other.length + out.length + (frame (bit :: bits)).length + backing.length ≤ space at hspace
      have hp : 1 ≤ (frame (bit :: bits)).length := by simp
      omega
    have hmiddle : (config phase (bitState phase) input (pre.length + 1) other otherHead (out ++ [true]) backing).tapeCells ≤ space := by
      apply (config_cells_le _ _ _ _ _ _ _ _).trans
      simp only [List.length_append, List.length_singleton]
      omega
    have hrun := Prefix.step (p := machine) (space := space)
      ((config_cells_le phase (bodyState phase) input pre.length other otherHead out backing).trans (by omega))
      (by cases phase <;> rfl) hfirst
      (Prefix.step hmiddle (by cases phase <;> rfl) hsecond htail')
    simpa [input, frame, Nat.add_assoc] using hrun

theorem mark_step (phase : Bool) (pre tail other : List Bool) (otherHead : ℕ)
    (out backing : List Bool) :
    step machine (config phase (baseState phase) (pre ++ true :: tail) pre.length other otherHead out backing) =
      some (config phase (tagState phase) (pre ++ true :: tail)
        (pre.length + 1) other otherHead (out ++ [true]) backing) := by
  have hread := Streaming.read_append pre tail true
  have hr : machine.rule (baseState phase)
      (config phase (baseState phase) (pre ++ true :: tail) pre.length other otherHead out backing).scanned =
      some (emitAction phase (tagState phase) true) := by
    cases phase <;> simp [machine, config, Configuration.scanned, activeTape, baseState, tagState, hread]
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _ _ _

theorem tag_step (phase bit : Bool) (pre tail other : List Bool) (otherHead : ℕ)
    (out backing : List Bool) :
    step machine (config phase (tagState phase) (pre ++ bit :: tail) pre.length other otherHead out backing) =
      some (config phase (bodyState phase) (pre ++ bit :: tail)
        (pre.length + 1) other otherHead (out ++ [bit]) backing) := by
  have hread := Streaming.read_append pre tail bit
  have hr : machine.rule (tagState phase)
      (config phase (tagState phase) (pre ++ bit :: tail) pre.length other otherHead out backing).scanned =
      some (emitAction phase (bodyState phase) bit) := by
    cases phase <;> simp [machine, config, Configuration.scanned, activeTape, tagState, bodyState, hread]
  simp only [step, config_control, hr, Option.map_some, Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _ _ _

theorem record_prefix (phase : Bool) (r : Record) (pre tail other : List Bool) (otherHead : ℕ)
    (out backing : List Bool) (space : ℕ)
    (hspace : (pre ++ recordBits r ++ tail).length + other.length + out.length +
      (recordBits r).length + backing.length ≤ space) :
    Prefix machine space (recordBits r).length
      (config phase (baseState phase) (pre ++ recordBits r ++ tail) pre.length other otherHead out backing)
      (config phase (baseState phase) (pre ++ recordBits r ++ tail)
        (pre.length + (recordBits r).length) other otherHead (out ++ recordBits r) backing) := by
  rcases r with ⟨tag, bits⟩
  let input := pre ++ recordBits (tag, bits) ++ tail
  have htailspace : ((pre ++ [true, tag]) ++ frame bits ++ tail).length + other.length +
      (out ++ [true, tag]).length + (frame bits).length + backing.length ≤ space := by
    simp only [recordBits, List.length_append, List.length_cons, List.length_nil, frame_length] at hspace ⊢
    omega
  have htail := body_prefix phase bits (pre ++ [true, tag]) tail other otherHead
    (out ++ [true, tag]) backing space htailspace
  have hpre : (pre ++ [true, tag]).length = pre.length + 2 := by simp
  have hpos : pre.length + 2 + (frame bits).length = pre.length + (recordBits (tag, bits)).length := by
    simp [recordBits]
    omega
  simp only [hpre] at htail
  rw [hpos] at htail
  have htail' : Prefix machine space (frame bits).length
      (config phase (bodyState phase) input (pre.length + 2) other otherHead (out ++ [true, tag]) backing)
      (config phase (baseState phase) input (pre.length + (recordBits (tag, bits)).length)
        other otherHead (out ++ recordBits (tag, bits)) backing) := by
    simpa [input, recordBits, List.append_assoc] using htail
  have hfirst : step machine (config phase (baseState phase) input pre.length other otherHead out backing) =
      some (config phase (tagState phase) input (pre.length + 1) other otherHead (out ++ [true]) backing) := by
    simpa [input, recordBits] using
      mark_step phase pre (tag :: (frame bits ++ tail)) other otherHead out backing
  have hsecond : step machine
      (config phase (tagState phase) input (pre.length + 1) other otherHead (out ++ [true]) backing) =
      some (config phase (bodyState phase) input (pre.length + 2) other otherHead (out ++ [true, tag]) backing) := by
    simpa [input, recordBits, List.append_assoc, Nat.add_assoc] using
      tag_step phase tag (pre ++ [true]) (frame bits ++ tail) other otherHead (out ++ [true]) backing
  have hsmall : input.length + other.length + out.length + 1 + backing.length ≤ space := by
    change input.length + other.length + out.length + (recordBits (tag, bits)).length + backing.length ≤ space at hspace
    have hp : 1 ≤ (recordBits (tag, bits)).length := by simp [recordBits]
    omega
  have hmiddle : (config phase (tagState phase) input (pre.length + 1) other otherHead (out ++ [true]) backing).tapeCells ≤ space := by
    apply (config_cells_le _ _ _ _ _ _ _ _).trans
    simp only [List.length_append, List.length_singleton]
    omega
  have hrun := Prefix.step (p := machine) (space := space)
    ((config_cells_le phase (baseState phase) input pre.length other otherHead out backing).trans (by omega))
    (by cases phase <;> rfl) hfirst
    (Prefix.step hmiddle (by cases phase <;> rfl) hsecond htail')
  simpa [input, recordBits, Nat.add_assoc] using hrun

theorem records_prefix (phase : Bool) (rs : List Record) (pre tail other : List Bool) (otherHead : ℕ)
    (out backing : List Bool) (space : ℕ)
    (hspace : (pre ++ recordsBits rs ++ tail).length + other.length + out.length +
      (recordsBits rs).length + backing.length ≤ space) :
    Prefix machine space (recordsBits rs).length
      (config phase (baseState phase) (pre ++ recordsBits rs ++ tail) pre.length other otherHead out backing)
      (config phase (baseState phase) (pre ++ recordsBits rs ++ tail)
        (pre.length + (recordsBits rs).length) other otherHead (out ++ recordsBits rs) backing) := by
  induction rs generalizing pre out with
  | nil =>
    simp only [recordsBits, List.flatMap_nil, List.length_nil, List.append_nil, Nat.add_zero] at hspace ⊢
    exact Prefix.refl _ ((config_cells_le _ _ _ _ _ _ _ _).trans hspace)
  | cons r rs ih =>
    let input := pre ++ recordsBits (r :: rs) ++ tail
    have htailspace : ((pre ++ recordBits r) ++ recordsBits rs ++ tail).length + other.length +
        (out ++ recordBits r).length + (recordsBits rs).length + backing.length ≤ space := by
      simp only [recordsBits, List.flatMap_cons, List.length_append] at hspace ⊢
      omega
    have htail := ih (pre ++ recordBits r) (out ++ recordBits r) htailspace
    have htail' : Prefix machine space (recordsBits rs).length
        (config phase (baseState phase) input (pre.length + (recordBits r).length)
          other otherHead (out ++ recordBits r) backing)
        (config phase (baseState phase) input (pre.length + (recordsBits (r :: rs)).length)
          other otherHead (out ++ recordsBits (r :: rs)) backing) := by
      simpa [input, recordsBits, List.append_assoc, Nat.add_assoc] using htail
    have hrecordspace : (pre ++ recordBits r ++ (recordsBits rs ++ tail)).length + other.length +
        out.length + (recordBits r).length + backing.length ≤ space := by
      simp only [recordsBits, List.flatMap_cons, List.length_append] at hspace ⊢
      omega
    have hfirst := record_prefix phase r pre (recordsBits rs ++ tail) other otherHead out backing space hrecordspace
    have hfirst' : Prefix machine space (recordBits r).length
        (config phase (baseState phase) input pre.length other otherHead out backing)
        (config phase (baseState phase) input (pre.length + (recordBits r).length)
          other otherHead (out ++ recordBits r) backing) := by
      simpa [input, recordsBits, List.append_assoc] using hfirst
    have hj := hfirst'.trans htail'
    simpa [input, recordsBits, List.append_assoc] using hj

theorem switch_step (pre junk right : List Bool) (out backing : List Bool) :
    step machine (config false (baseState false) (pre ++ false :: junk) pre.length right 0 out backing) =
      some (config true (baseState true) right 0 (pre ++ false :: junk) pre.length out backing) := by
  have hread := Streaming.read_append pre junk false
  simp [step, machine, config, activeTape, baseState, Configuration.scanned, hread]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, switchAction, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, switchAction]

theorem finish_step (pre junk left : List Bool) (leftHead : ℕ) (out backing : List Bool) :
    step machine (config true (baseState true) (pre ++ false :: junk) pre.length left leftHead out backing) =
      some (config true 8 (pre ++ false :: junk) pre.length left leftHead (out ++ [false]) backing) := by
  have hread := Streaming.read_append pre junk false
  simp [step, machine, config, activeTape, baseState, Configuration.scanned, hread]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, finishAction, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, finishAction, overlay_write]

theorem concat_run (xs ys : List Record) (leftJunk rightJunk backing : List Bool) :
    ∃ r : ExecutionReceipt 3 9,
      run machine ((stream xs).length + (stream ys).length)
        (fun i => if i.val = 0 then stream xs ++ leftJunk
          else if i.val = 1 then stream ys ++ rightJunk else backing) = some r ∧
      r.final = config true 8 (stream ys ++ rightJunk) (recordsBits ys).length
        (stream xs ++ leftJunk) (recordsBits xs).length (stream (xs ++ ys)) backing ∧
      r.steps = (stream xs).length + (stream ys).length ∧
      r.peakTapeCells ≤ (stream xs ++ leftJunk).length + (stream ys ++ rightJunk).length +
        (stream (xs ++ ys)).length + backing.length := by
  let left := stream xs ++ leftJunk
  let right := stream ys ++ rightJunk
  let output := stream (xs ++ ys)
  let space := left.length + right.length + output.length + backing.length
  have houtput : output = recordsBits xs ++ recordsBits ys ++ [false] := by
    simp [output, stream, recordsBits, List.append_assoc]
  have hfirstspace : ([] ++ recordsBits xs ++ (false :: leftJunk)).length + right.length +
      ([] : List Bool).length + (recordsBits xs).length + backing.length ≤ space := by
    simp only [space, left, houtput, List.nil_append, List.length_nil, List.length_append,
      List.length_cons, stream] at *
    omega
  have hfirst := records_prefix false xs [] (false :: leftJunk) right 0 [] backing space hfirstspace
  have hfirst' : Prefix machine space (recordsBits xs).length
      (config false (baseState false) left 0 right 0 [] backing)
      (config false (baseState false) left (recordsBits xs).length right 0 (recordsBits xs) backing) := by
    simpa [left, stream, List.append_assoc] using hfirst
  have hsecondspace : ([] ++ recordsBits ys ++ (false :: rightJunk)).length + left.length +
      (recordsBits xs).length + (recordsBits ys).length + backing.length ≤ space := by
    simp only [space, right, houtput, List.nil_append, List.length_nil, List.length_append,
      List.length_cons, stream] at *
    omega
  have hsecond := records_prefix true ys [] (false :: rightJunk) left (recordsBits xs).length
    (recordsBits xs) backing space hsecondspace
  have hsecond' : Prefix machine space (recordsBits ys).length
      (config true (baseState true) right 0 left (recordsBits xs).length (recordsBits xs) backing)
      (config true (baseState true) right (recordsBits ys).length left (recordsBits xs).length
        (recordsBits xs ++ recordsBits ys) backing) := by
    simpa [right, stream, List.append_assoc] using hsecond
  have hfinalspace : (config true 8 right (recordsBits ys).length left (recordsBits xs).length output backing).tapeCells ≤ space := by
    apply (config_cells_le _ _ _ _ _ _ _ _).trans
    dsimp [space]
    omega
  have hfinish : step machine
      (config true (baseState true) right (recordsBits ys).length left (recordsBits xs).length
        (recordsBits xs ++ recordsBits ys) backing) =
      some (config true 8 right (recordsBits ys).length left (recordsBits xs).length output backing) := by
    simpa [right, stream, houtput, List.append_assoc] using
      finish_step (recordsBits ys) rightJunk left (recordsBits xs).length (recordsBits xs ++ recordsBits ys) backing
  have hfinishspace : (config true (baseState true) right (recordsBits ys).length left (recordsBits xs).length
        (recordsBits xs ++ recordsBits ys) backing).tapeCells ≤ space := by
    apply (config_cells_le _ _ _ _ _ _ _ _).trans
    simp only [space, houtput, List.length_append, List.length_singleton]
    omega
  have hfinishPrefix := Prefix.step hfinishspace (by rfl) hfinish (Prefix.refl _ hfinalspace)
  have htail := hsecond'.trans hfinishPrefix
  have hswitch : step machine (config false (baseState false) left (recordsBits xs).length right 0 (recordsBits xs) backing) =
      some (config true (baseState true) right 0 left (recordsBits xs).length (recordsBits xs) backing) := by
    simpa [left, stream, List.append_assoc] using switch_step (recordsBits xs) leftJunk right (recordsBits xs) backing
  have hswitchspace : (config false (baseState false) left (recordsBits xs).length right 0 (recordsBits xs) backing).tapeCells ≤ space := by
    apply (config_cells_le _ _ _ _ _ _ _ _).trans
    simp only [space, houtput, List.length_append, List.length_singleton]
    omega
  have hwhole := hfirst'.trans (Prefix.step hswitchspace (by rfl) hswitch htail)
  obtain ⟨r, hr, hf, hs, hp⟩ := hwhole.run (by rfl) hfinalspace
  have hinit : initialConfiguration machine
        (fun i : Fin 3 => if i.val = 0 then stream xs ++ leftJunk
          else if i.val = 1 then stream ys ++ rightJunk else backing) =
      config false (baseState false) left 0 right 0 [] backing := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [initialConfiguration, config]
    · funext i
      fin_cases i <;> simp [initialConfiguration, config, activeTape, overlay, left, right]
  have hfuel : (stream xs).length + (stream ys).length =
      (recordsBits xs).length + ((recordsBits ys).length + 1 + 1) := by
    simp only [stream, List.length_append, List.length_singleton]
    omega
  refine ⟨r, ?_, hf, ?_, hp⟩
  · change runFrom machine _ _ = _
    rw [hinit, hfuel]
    exact hr
  · rw [hfuel]
    exact hs

theorem concat_capacity (xs ys : List Record) (leftJunk rightJunk backing : List Bool)
    (capacity : ℕ)
    (hl : (stream xs).length + leftJunk.length ≤ capacity)
    (hr : (stream ys).length + rightJunk.length ≤ capacity)
    (ho : (stream (xs ++ ys)).length ≤ capacity) (hb : backing.length ≤ capacity) :
    ∃ r : ExecutionReceipt 3 9,
      run machine ((stream xs).length + (stream ys).length)
        (fun i => if i.val = 0 then stream xs ++ leftJunk
          else if i.val = 1 then stream ys ++ rightJunk else backing) = some r ∧
      r.final.tapes 0 = stream xs ++ leftJunk ∧ r.final.tapes 1 = stream ys ++ rightJunk ∧
      r.final.tapes 2 = overlay (stream (xs ++ ys)) backing ∧
      (∀ i, (r.final.tapes i).length ≤ capacity) ∧
      r.steps = (stream xs).length + (stream ys).length ∧ r.peakTapeCells ≤ 4 * capacity := by
  obtain ⟨r, hrun, hf, hs, hp⟩ := concat_run xs ys leftJunk rightJunk backing
  refine ⟨r, hrun, ?_, ?_, ?_, ?_, hs, ?_⟩
  · simp [hf, config, activeTape]
  · simp [hf, config, activeTape]
  · simp [hf, config]
  · intro i
    fin_cases i
    · simpa [hf, config, activeTape] using hl
    · simpa [hf, config, activeTape] using hr
    · simpa [hf, config] using max_le ho hb
  · simp only [List.length_append] at hp
    omega

end NearCubicWires.RepairOrdinary.StreamConcat
