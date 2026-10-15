import Proof.MachineModel.OrdinaryInitializedTrace

/-! Append a bounded raw scalar to a record stream with framing markers.
The unary width is retained. Only scalar/width heads are reset; the large
output cursor advances throughout. This is the serializer used by the event
producer, not a polynomial simulation of the entire event table. -/
namespace NearCubicWires.RepairOrdinary.MemoryEmitField
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (state : Fin 3) (advance : Bool) (out : Option Bool) : Action 3 3 :=
  ⟨state, ![none,none,out],
    ![if advance then .right else .stay, if advance then .right else .stay,
      if out.isSome then .right else .stay]⟩
def machine (close : Bool) : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val == 2
  rule := fun s read => if s.val = 0 then
      some (if read 1 then action 1 false (some true)
        else action 2 false (if close then some false else none))
    else if s.val = 1 then some (action 0 true (some (read 0))) else none
def config (state : Fin 3) (bits : List Bool) (position : ℕ) (out : List Bool) : Configuration 3 3 :=
  ⟨state, ![position,position,out.length], ![bits,List.replicate bits.length true,out]⟩
def suffix (close : Bool) : List Bool := if close then [false] else []
@[simp] theorem config_cells (s : Fin 3) (bits out : List Bool) (pos : ℕ) :
    (config s bits pos out).tapeCells = 2*bits.length+out.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]
  omega

theorem marker_step (close : Bool) (bits out : List Bool) (pos : ℕ) (hpos : pos < bits.length) :
    step (machine close) (config 0 bits pos out) = some (config 1 bits pos (out++[true])) := by
  have hr : readTapeBit (List.replicate bits.length true) pos = true := by
    simp [readTapeBit, hpos]
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, Streaming.write_append]

theorem bit_step (close bit : Bool) (bits out : List Bool) (pos : ℕ)
    (hr : readTapeBit bits pos = bit) :
    step (machine close) (config 1 bits pos out) = some (config 0 bits (pos+1) (out++[bit])) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, Streaming.write_append]

theorem stop_step (close : Bool) (bits out : List Bool) :
    step (machine close) (config 0 bits bits.length out) =
      some (config 2 bits bits.length (out++suffix close)) := by
  have hr : readTapeBit (List.replicate bits.length true) bits.length = false := by
    simp [readTapeBit]
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; cases close <;> fin_cases i <;> simp [applyAction, action, HeadMove.apply, suffix]
  · funext i; cases close <;> fin_cases i <;> simp [applyAction, action, suffix, Streaming.write_append]

theorem append_prefix (close : Bool) (pre bits out : List Bool) :
    Prefix (machine close) (2*(pre++bits).length+out.length+2*bits.length+(suffix close).length)
      (2*bits.length+1) (config 0 (pre++bits) pre.length out)
      (config 2 (pre++bits) (pre.length+bits.length)
        (out++Streaming.marks bits++suffix close)) := by
  induction bits generalizing pre out with
  | nil =>
    have h := Prefix.step (by simp : (config 0 pre pre.length out).tapeCells ≤
        2*pre.length+out.length+(suffix close).length)
      (by rfl : (machine close).halted (0 : Fin 3) = false) (stop_step close pre out)
      (Prefix.refl _ (by simp; omega))
    simpa [Streaming.marks] using h
  | cons bit bits ih =>
    let source := pre++bit::bits
    have he : (pre++[bit])++bits = source := by simp [source, List.append_assoc]
    have ht := ih (pre++[bit]) (out++[true,bit])
    rw [he] at ht
    have ht' : Prefix (machine close)
        (2*source.length+out.length+2*(bit::bits).length+(suffix close).length)
        (2*bits.length+1)
        (config 0 source (pre.length+1) (out++[true,bit]))
        (config 2 source (pre.length+(bit::bits).length)
          (out++Streaming.marks (bit::bits)++suffix close)) := by
      simpa [Streaming.marks, List.append_assoc, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using ht
    have hr : readTapeBit source pre.length = bit := Streaming.read_append pre bits bit
    have hbit := Prefix.step (by simp; omega :
        (config 1 source pre.length (out++[true])).tapeCells ≤
          2*source.length+out.length+2*(bit::bits).length+(suffix close).length)
      (by rfl : (machine close).halted (1 : Fin 3) = false)
      (bit_step close bit source (out++[true]) pre.length hr)
      (by simpa [List.append_assoc] using ht')
    have hmark := Prefix.step (by simp; omega : (config 0 source pre.length out).tapeCells ≤
          2*source.length+out.length+2*(bit::bits).length+(suffix close).length)
      (by rfl : (machine close).halted (0 : Fin 3) = false)
      (marker_step close source out pre.length (by simp [source])) hbit
    have htime : 2*bits.length+1+1+1 = 2*(bit::bits).length+1 := by simp; omega
    rw [htime] at hmark
    simpa only [source, List.append_assoc, List.length_cons] using hmark

theorem append_run (close : Bool) (bits out : List Bool) :
    ∃ r : ExecutionReceipt 3 3,
      runFrom (machine close) (2*bits.length+1) (config 0 bits 0 out) = some r ∧
      r.final = config 2 bits bits.length (out++Streaming.marks bits++suffix close) ∧
      r.steps = 2*bits.length+1 := by
  obtain ⟨r, hr, hf, hs, _⟩ := (append_prefix close [] bits out).run (by rfl) (by simp; omega)
  exact ⟨r, by simpa using hr, by simpa using hf, hs⟩

end NearCubicWires.RepairOrdinary.MemoryEmitField
