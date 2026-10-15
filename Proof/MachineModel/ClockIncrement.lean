import Proof.MachineModel.OrdinaryFramedIncrement

/-! A growing framed binary counter. Its delimiter is maintained by actual
writes, including the carry that increases the width. No width tape is an
input to this machine; the framed output exposes the physical width. -/
namespace NearCubicWires.RepairOrdinary.ClockIncrement
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def next : List Bool → List Bool
  | [] => [true]
  | false :: bits => true :: bits
  | true :: bits => false :: next bits

def work : List Bool → ℕ
  | [] => 3
  | false :: _ => 2
  | true :: bits => work bits + 2

def distance : List Bool → ℕ
  | [] => 2
  | false :: _ => 2
  | true :: bits => distance bits + 2

theorem next_value (bits : List Bool) : value (next bits) = value bits + 1 := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => cases bit <;> simp [next, value, ih] <;> omega

theorem next_length (bits : List Bool) : bits.length ≤ (next bits).length ∧
    (next bits).length ≤ bits.length + 1 := by
  induction bits with
  | nil => simp [next]
  | cons bit bits ih => cases bit <;> simp_all [next]

theorem work_bound (bits : List Bool) : work bits ≤ 2*bits.length+3 := by
  induction bits with
  | nil => simp [work]
  | cons bit bits ih =>
    cases bit <;> simp [work]
    omega

theorem distance_bound (bits : List Bool) : distance bits ≤ work bits := by
  induction bits with
  | nil => decide
  | cons bit bits ih => cases bit <;> simp_all [distance, work]

def raw : Machine 1 5 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val == 4
  rule := fun s scanned =>
    if s.val = 0 then
      some ⟨if scanned 0 then 1 else 2,
        fun _ => if scanned 0 then none else some true, fun _ => .right⟩
    else if s.val = 1 then
      some ⟨if scanned 0 then 0 else 4, fun _ => some (!scanned 0), fun _ => .right⟩
    else if s.val = 2 then some ⟨3, fun _ => some true, fun _ => .right⟩
    else if s.val = 3 then some ⟨4, fun _ => some false, fun _ => .stay⟩
    else none

def config (s : Fin 5) (bits : List Bool) (pos : ℕ) : Configuration 1 5 :=
  ⟨s, fun _ => pos, fun _ => bits⟩
@[simp] theorem config_cells (s : Fin 5) (bits : List Bool) (pos : ℕ) :
    (config s bits pos).tapeCells = bits.length := by
  simp [config, Configuration.tapeCells]

theorem mark_step (pre bits : List Bool) (bit : Bool) :
    step raw (config 0 (pre ++ frame (bit::bits)) pre.length) =
      some (config 1 (pre ++ frame (bit::bits)) (pre.length+1)) := by
  have hr : readTapeBit (pre ++ frame (bit::bits)) pre.length = true := by
    simpa [frame] using Streaming.read_append pre (bit::frame bits) true
  simp [step, raw, config, Configuration.scanned, hr]
  rfl

theorem bit_step (pre bits : List Bool) (bit : Bool) :
    step raw (config 1 (pre ++ bit::frame bits) pre.length) =
      some (config (if bit then 0 else 4) (pre ++ (!bit)::frame bits) (pre.length+1)) := by
  simp [step, raw, config, Configuration.scanned, Streaming.read_append]
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    exact BinaryIncrement.write_prefix pre (frame bits) bit (!bit)

theorem grow_steps (pre : List Bool) :
    Prefix raw (pre.length+3) 3
      (config 0 (pre++[false]) pre.length)
      (config 4 (pre++[true,true,false]) (pre.length+2)) := by
  have h0 : step raw (config 0 (pre++[false]) pre.length) =
      some (config 2 (pre++[true]) (pre.length+1)) := by
    simp [step, raw, config, Configuration.scanned, Streaming.read_append]
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      exact BinaryIncrement.write_prefix pre [] false true
  have h1 : step raw (config 2 (pre++[true]) (pre.length+1)) =
      some (config 3 (pre++[true,true]) (pre.length+2)) := by
    simp [step, raw, config]
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      simpa [applyAction, List.append_assoc] using Streaming.write_append (pre++[true]) true
  have h2 : step raw (config 3 (pre++[true,true]) (pre.length+2)) =
      some (config 4 (pre++[true,true,false]) (pre.length+2)) := by
    simp [step, raw, config]
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      simpa [applyAction, List.append_assoc] using Streaming.write_append (pre++[true,true]) false
  exact Prefix.step (by simp) (by rfl) h0
    (Prefix.step (by simp) (by rfl) h1
      (Prefix.step (by simp) (by rfl) h2 (Prefix.refl _ (by simp))))

private theorem mono_space {t s old new n : ℕ} {p : Machine t s}
    {a b : Configuration t s} (h : Prefix p old n a b) (hn : old ≤ new) :
    Prefix p new n a b := by
  induction h with
  | refl c hc => exact Prefix.refl c (hc.trans hn)
  | step hc hh hs _ ih => exact Prefix.step (hc.trans hn) hh hs ih

theorem next_prefix (pre bits : List Bool) :
    Prefix raw (pre.length + 2*(bits.length+1)+1) (work bits)
      (config 0 (pre++frame bits) pre.length)
      (config 4 (pre++frame (next bits)) (pre.length+distance bits)) := by
  induction bits generalizing pre with
  | nil => simpa [frame, next, work, distance] using grow_steps pre
  | cons bit bits ih =>
    cases bit with
    | false =>
      have hb := bit_step (pre++[true]) bits false
      have hs : step raw (config 1 (pre++frame (false::bits)) (pre.length+1)) =
          some (config 4 (pre++frame (true::bits)) (pre.length+2)) := by
        simpa [frame, List.append_assoc] using hb
      have hp := Prefix.step (by simp; omega :
          (config 1 (pre++frame (false::bits)) (pre.length+1)).tapeCells ≤
            pre.length+2*((false::bits).length+1)+1)
        (by rfl : raw.halted (1 : Fin 5) = false) hs (Prefix.refl _ (by simp; omega))
      exact Prefix.step (by simp; omega) (by rfl) (mark_step pre bits false) hp
    | true =>
      have hi := ih (pre++[true,false])
      have hb := bit_step (pre++[true]) bits true
      have hs : step raw (config 1 (pre++frame (true::bits)) (pre.length+1)) =
          some (config 0 ((pre++[true,false])++frame bits) (pre.length+2)) := by
        simpa [frame, List.append_assoc] using hb
      have htail : Prefix raw (pre.length+2*((true::bits).length+1)+1) (work bits)
          (config 0 ((pre++[true,false])++frame bits) (pre.length+2))
          (config 4 (pre++frame (next (true::bits))) (pre.length+distance (true::bits))) := by
        have hspace : (pre++[true,false]).length+2*(bits.length+1)+1 =
            pre.length+2*((true::bits).length+1)+1 := by simp; omega
        rw [hspace] at hi
        simpa [frame, next, distance, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
      have hp := Prefix.step (by simp; omega :
          (config 1 (pre++frame (true::bits)) (pre.length+1)).tapeCells ≤
            pre.length+2*((true::bits).length+1)+1)
        (by rfl : raw.halted (1 : Fin 5) = false) hs htail
      have result := Prefix.step (by simp; omega :
          (config 0 (pre++frame (true::bits)) pre.length).tapeCells ≤
            pre.length+2*((true::bits).length+1)+1)
        (by rfl : raw.halted (0 : Fin 5) = false) (mark_step pre bits true) hp
      simpa [work, Nat.add_assoc] using result

theorem next_run (bits : List Bool) :
    ∃ r : ExecutionReceipt 1 5,
      run raw (work bits) (fun _ => frame bits) = some r ∧
      r.final = config 4 (frame (next bits)) (distance bits) ∧
      r.steps = work bits ∧ r.peakTapeCells ≤ 2*(bits.length+1)+1 := by
  obtain ⟨r, hr, hf, hs, hp⟩ := (next_prefix [] bits).run (by rfl)
    (by simp; have := next_length bits; omega)
  exact ⟨r, by simpa [run, initialConfiguration, raw, config] using hr,
    by simpa using hf, hs, by simpa using hp⟩

def machine : Machine 2 7 := Rewind.machine raw

theorem increment_run (bits : List Bool) (cap : ℕ) :
    ∃ r : ExecutionReceipt 2 7,
      run machine (2*work bits+2)
        (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool)
          (fun _ : Fin 1 => frame bits)
          (fun _ : Fin 1 => List.replicate cap false)) = some r ∧
      r.final.tapes 0 = frame (next bits) ∧
      r.final.tapes 1 = List.replicate (max cap (work bits)) false ∧
      (∀ i, r.final.heads i = 0) ∧ r.steps = 2*work bits+2 ∧
      r.peakTapeCells ≤ 2*(bits.length+1)+1+cap+2*work bits := by
  obtain ⟨base, hb, hf, hs, hp⟩ := next_run bits
  obtain ⟨r, hr, ht, hc, hh, hsteps, hpeak⟩ := Rewind.Workspace.reset_workspace raw
    (work bits) _ base hb cap
  refine ⟨r, by simpa [machine, hs] using hr, ?_, by simpa [hs] using hc, hh,
    by omega, by omega⟩
  simpa [hf, config] using ht (0 : Fin 1)

end NearCubicWires.RepairOrdinary.ClockIncrement
