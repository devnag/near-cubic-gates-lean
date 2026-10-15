import Proof.MachineModel.OrdinaryKeyReset

/-! Actual increment of a framed binary coordinate. The surrounding stream
is untouched; the reused counter pays the bounded local head reset. -/
namespace NearCubicWires.RepairOrdinary.FramedIncrement
open LocalBitMultitape SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 2
  rule := fun state scanned => if state.val = 0 then some ⟨1, fun _ => none, fun _ => .right⟩
    else if state.val = 1 then some ⟨if scanned 0 then 0 else 2, fun _ => some (!scanned 0), fun _ => .right⟩
    else none
def config (state : Fin 3) (bits : List Bool) (pos : ℕ) : Configuration 1 3 := ⟨state, fun _ => pos, fun _ => bits⟩
@[simp] theorem config_cells (state : Fin 3) (bits : List Bool) (pos : ℕ) :
    (config state bits pos).tapeCells = bits.length := by simp [config, Configuration.tapeCells]

theorem mark_step (source : List Bool) (pos : ℕ) :
    step raw (config 0 source pos) = some (config 1 source (pos + 1)) := by
  simp [step, raw, config]
  rfl
theorem bit_step (pre tail : List Bool) (bit : Bool) :
    step raw (config 1 (pre ++ bit :: tail) pre.length) =
      some (config (if bit then 0 else 2) (pre ++ (!bit) :: tail) (pre.length + 1)) := by
  simp [step, raw, config, Configuration.scanned, Streaming.read_append]
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    exact BinaryIncrement.write_prefix pre tail bit (!bit)

theorem carry_prefix (count : ℕ) (pre tail : List Bool) :
    Prefix raw (pre.length + 2 * (count + 1 + tail.length) + 1) (2 * count + 2)
      (config 0 (pre ++ frame (List.replicate count true ++ false :: tail)) pre.length)
      (config 2 (pre ++ frame (List.replicate count false ++ true :: tail)) (pre.length + 2 * count + 2)) := by
  induction count generalizing pre with
  | zero =>
    have hb := bit_step (pre ++ [true]) (frame tail) false
    have hs : step raw (config 1 (pre ++ frame (false :: tail)) (pre.length + 1)) =
        some (config 2 (pre ++ frame (true :: tail)) (pre.length + 2)) := by
      simpa [frame, List.append_assoc] using hb
    have hp := Prefix.step
      (by simp; omega : (config 1 (pre ++ frame (false :: tail)) (pre.length + 1)).tapeCells ≤ pre.length + 2 * (1 + tail.length) + 1)
      (by rfl : raw.halted (1 : Fin 3) = false) hs (Prefix.refl _ (by simp; omega))
    have h := Prefix.step
      (by simp; omega : (config 0 (pre ++ frame (false :: tail)) pre.length).tapeCells ≤ pre.length + 2 * (1 + tail.length) + 1)
      (by rfl : raw.halted (0 : Fin 3) = false) (mark_step _ _) hp
    simpa using h
  | succ count ih =>
    let old := pre ++ frame (List.replicate (count + 1) true ++ false :: tail)
    let next := pre ++ [true, false] ++ frame (List.replicate count true ++ false :: tail)
    let space := pre.length + 2 * (count + 1 + 1 + tail.length) + 1
    have ht := ih (pre ++ [true, false])
    have hspace : (pre ++ [true, false]).length + 2 * (count + 1 + tail.length) + 1 = space := by simp [space]; omega
    have hlen : (pre ++ [true, false]).length = pre.length + 2 := by simp
    rw [hspace, hlen] at ht
    have hb : step raw (config 1 old (pre.length + 1)) = some (config 0 next (pre.length + 2)) := by
      simpa [old, next, frame, List.replicate_succ, List.append_assoc] using
        bit_step (pre ++ [true]) (frame (List.replicate count true ++ false :: tail)) true
    have h1 := Prefix.step
      (by simp [old, space]; omega : (config 1 old (pre.length + 1)).tapeCells ≤ space)
      (by rfl : raw.halted (1 : Fin 3) = false) hb ht
    have h0 := Prefix.step
      (by simp [old, space]; omega : (config 0 old pre.length).tapeCells ≤ space)
      (by rfl : raw.halted (0 : Fin 3) = false) (mark_step old pre.length) h1
    have htime : 2 * count + 2 + 1 + 1 = 2 * (count + 1) + 2 := by omega
    have hpos : pre.length + 2 + 2 * count + 2 = pre.length + 2 * (count + 1) + 2 := by omega
    rw [htime, hpos] at h0
    simpa [old, space, frame, List.replicate_succ, List.append_assoc] using h0

theorem carry_run (count : ℕ) (tail : List Bool) :
    ∃ r : ExecutionReceipt 1 3,
      run raw (2 * count + 2) (fun _ => frame (List.replicate count true ++ false :: tail)) = some r ∧
      r.final = config 2 (frame (List.replicate count false ++ true :: tail)) (2 * count + 2) ∧
      r.steps = 2 * count + 2 ∧ r.peakTapeCells ≤ 2 * (count + 1 + tail.length) + 1 := by
  obtain ⟨r, hr, hf, hs, hp⟩ := (carry_prefix count [] tail).run (by rfl) (by simp; omega)
  exact ⟨r, by simpa [run, initialConfiguration, raw, config] using hr, by simpa using hf, hs, by simpa using hp⟩

def machine : Machine 2 5 := Rewind.machine raw

theorem increment_run (width n cap : ℕ) (hn : n + 1 < 2 ^ width) (hc : 2 * width ≤ cap) :
    ∃ r : ExecutionReceipt 2 5,
      run machine (4 * width + 2)
        (Fin.addCases (motive := fun _ : Fin (1 + 1) => List Bool)
          (fun _ : Fin 1 => frame (binary width n)) (fun _ : Fin 1 => List.replicate cap false)) = some r ∧
      r.final.tapes 0 = frame (binary width (n + 1)) ∧ r.final.tapes 1 = List.replicate cap false ∧
      (∀ i, r.final.heads i = 0) ∧ r.steps ≤ 4 * width + 2 ∧ r.peakTapeCells ≤ 4 * width + cap + 1 := by
  have hn' : n < 2 ^ width := by omega
  have split : ∃ count tail, binary width n = List.replicate count true ++ false :: tail := by
    rcases BoundedCounter.carry_split (binary width n) with h | h
    · exact h
    · have hv := congrArg value h
      rw [binary_value _ _ hn', binary_length] at hv
      have ht := BoundedCounter.true_value width
      omega
  obtain ⟨count, tail, he⟩ := split
  have hlen : count + 1 + tail.length = width := by
    have h := congrArg List.length he
    simp only [binary_length, List.length_append, List.length_replicate, List.length_cons] at h
    omega
  have ho : List.replicate count false ++ true :: tail = binary width (n + 1) := by
    have hv : value (List.replicate count false ++ true :: tail) = n + 1 := by
      rw [BinaryIncrement.increment_value, ← he, binary_value _ _ hn']
    have h := BoundedCounter.binary_of_value (List.replicate count false ++ true :: tail)
    have hl : (List.replicate count false ++ true :: tail).length = width := by simp; omega
    rw [hl, hv] at h
    exact h.symm
  obtain ⟨base, hb, hf, hs, hp⟩ := carry_run count tail
  obtain ⟨r, hr, ht, hcounter, hheads, hsteps, hpeak⟩ := Rewind.Workspace.reset_workspace raw
    (2 * count + 2) _ base hb cap
  have hbound : 2 * base.steps + 2 ≤ 4 * width + 2 := by omega
  have hmore := run_moreFuel machine (2 * base.steps + 2) ((4 * width + 2) - (2 * base.steps + 2)) _ r hr
  rw [Nat.add_sub_of_le hbound, ← he] at hmore
  refine ⟨r, hmore, ?_, ?_, hheads, by omega, by omega⟩
  · have h := ht (0 : Fin 1)
    simpa [hf, config, ho] using h
  · have hfit : base.steps ≤ cap := by omega
    simpa [max_eq_left hfit] using hcounter

end NearCubicWires.RepairOrdinary.FramedIncrement
