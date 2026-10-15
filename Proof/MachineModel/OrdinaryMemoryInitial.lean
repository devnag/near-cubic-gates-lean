import Proof.MachineModel.OrdinaryMemoryBlank

/-! Generate the initial zero key directly from the first even-width record,
and set the cumulative result to true. All output tapes start blank. The
record is retained; a paid rewind supplies the next machine's entry heads. -/
namespace NearCubicWires.RepairOrdinary.MemoryInitial
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (state : Fin 5) (fast slow : HeadMove)
    (keyWrite resultWrite : Option Bool) : Action 3 5 :=
  ⟨state, ![none,keyWrite,resultWrite], ![fast,slow,.stay]⟩
def machine : Machine 3 5 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 4
  rule := fun state scanned => if state.val = 0 then
      some (if scanned 0 then action 1 .right .stay none none
        else action 4 .stay .stay (some false) (some true))
    else if state.val = 1 then some (action 2 .right .right (some true) none)
    else if state.val = 2 then some (action 3 .right .stay none none)
    else if state.val = 3 then some (action 0 .right .right (some false) none)
    else none
def config (state : Fin 5) (source : List Bool) (position : ℕ)
    (key : List Bool) : Configuration 3 5 :=
  ⟨state, ![position,key.length,0], ![source,key,[]]⟩
def finished (source : List Bool) (position : ℕ) (key : List Bool) : Configuration 3 5 :=
  ⟨4, ![position,key.length,0], ![source,key++[false],[true]]⟩
@[simp] theorem config_cells (s : Fin 5) (source key : List Bool) (pos : ℕ) :
    (config s source pos key).tapeCells = source.length+key.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]
@[simp] theorem finished_cells (source key : List Bool) (pos : ℕ) :
    (finished source pos key).tapeCells = source.length+key.length+2 := by
  simp [finished, Configuration.tapeCells, Fin.sum_univ_succ]
  omega

theorem first_step (source key : List Bool) (pos : ℕ)
    (hr : readTapeBit source pos = true) :
    step machine (config 0 source pos key) = some (config 1 source (pos+1) key) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem marker_step (source key : List Bool) (pos : ℕ) :
    step machine (config 1 source pos key) =
      some (config 2 source (pos+1) (key++[true])) := by
  simp [step, machine, config]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, Streaming.write_append]

theorem advance_step (source key : List Bool) (pos : ℕ) :
    step machine (config 2 source pos key) = some (config 3 source (pos+1) key) := by
  simp [step, machine, config]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem zero_step (source key : List Bool) (pos : ℕ) :
    step machine (config 3 source pos key) =
      some (config 0 source (pos+1) (key++[false])) := by
  simp [step, machine, config]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, Streaming.write_append]

theorem stop_step (source key : List Bool) (pos : ℕ)
    (hr : readTapeBit source pos = false) :
    step machine (config 0 source pos key) = some (finished source pos key) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply, finished]
  · funext i; fin_cases i <;> simp [applyAction, action, finished, Streaming.write_append,
      writeTapeBit]

theorem cycle_prefix (source key : List Bool) (pos : ℕ)
    (hr : readTapeBit source pos = true) :
    Prefix machine (source.length+key.length+2) 4
      (config 0 source pos key) (config 0 source (pos+4) (key++[true,false])) := by
  have h3 := Prefix.step (by simp; omega :
      (config 3 source (pos+3) (key++[true])).tapeCells ≤ source.length+key.length+2)
    (by rfl : machine.halted (3 : Fin 5) = false) (zero_step source (key++[true]) (pos+3))
    (Prefix.refl _ (by simp; omega))
  have h2 := Prefix.step (by simp; omega :
      (config 2 source (pos+2) (key++[true])).tapeCells ≤ source.length+key.length+2)
    (by rfl : machine.halted (2 : Fin 5) = false) (advance_step source (key++[true]) (pos+2))
    (by simpa [Nat.add_assoc] using h3)
  have h1 := Prefix.step (by simp :
      (config 1 source (pos+1) key).tapeCells ≤ source.length+key.length+2)
    (by rfl : machine.halted (1 : Fin 5) = false) (marker_step source key (pos+1))
    (by simpa [Nat.add_assoc] using h2)
  have h0 := Prefix.step (by simp :
      (config 0 source pos key).tapeCells ≤ source.length+key.length+2)
    (by rfl : machine.halted (0 : Fin 5) = false) (first_step source key pos hr) h1
  simpa [Nat.add_assoc, List.append_assoc] using h0

private theorem enlarge {t s n small large : ℕ} {p : Machine t s}
    {c d : Configuration t s} (h : Prefix p small n c d) (hb : small ≤ large) :
    Prefix p large n c d := by
  induction h with
  | refl c hc => exact Prefix.refl c (hc.trans hb)
  | step hc hn hs _ ih => exact Prefix.step (hc.trans hb) hn hs ih

theorem even_prefix (n : ℕ) (pre bits suffix key : List Bool) (hlen : bits.length = 2*n) :
    Prefix machine ((pre++frame bits++suffix).length+key.length+2*n+2) (4*n+1)
      (config 0 (pre++frame bits++suffix) pre.length key)
      (finished (pre++frame bits++suffix) (pre.length+4*n)
        (key++Streaming.marks (List.replicate n false))) := by
  induction n generalizing pre bits key with
  | zero =>
    have hz : bits = [] := List.length_eq_zero_iff.mp (by omega)
    subst bits
    have hr : readTapeBit (pre++frame []++suffix) pre.length = false := by
      simpa [frame] using Streaming.read_append pre suffix false
    have h := Prefix.step (by simp : (config 0 (pre++frame []++suffix) pre.length key).tapeCells ≤
        (pre++frame []++suffix).length+key.length+2)
      (by rfl : machine.halted (0 : Fin 5) = false) (stop_step _ _ _ hr)
      (Prefix.refl _ (by simp))
    simpa [Streaming.marks] using h
  | succ n ih =>
    cases bits with
    | nil => simp at hlen
    | cons first bits =>
      cases bits with
      | nil => simp at hlen; omega
      | cons second bits =>
        have hlen' : bits.length = 2*n := by simp only [List.length_cons] at hlen; omega
        let source := pre++frame (first::second::bits)++suffix
        have he : (pre++[true,first,true,second])++frame bits++suffix = source := by
          simp [source, frame, List.append_assoc]
        have hr : readTapeBit source pre.length = true := by
          simpa [source, frame, List.append_assoc] using
            Streaming.read_append pre (first::true::second::frame bits++suffix) true
        have hc := cycle_prefix source key pre.length hr
        have ht := ih (pre++[true,first,true,second]) bits (key++[true,false]) hlen'
        rw [he] at ht
        have ht' : Prefix machine (source.length+key.length+2*(n+1)+2) (4*n+1)
            (config 0 source (pre.length+4) (key++[true,false]))
            (finished source (pre.length+4*(n+1))
              (key++Streaming.marks (List.replicate (n+1) false))) := by
          simpa [List.replicate_succ, Streaming.marks, List.append_assoc,
            Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
        have hc' := enlarge hc (show source.length+key.length+2 ≤
          source.length+key.length+2*(n+1)+2 by omega)
        have hj := hc'.trans ht'
        convert hj using 1
        omega

theorem initial_run (n : ℕ) (bits suffix : List Bool) (hlen : bits.length = 2*n) :
    ∃ r : ExecutionReceipt 3 5,
      run machine (4*n+1) ![frame bits++suffix,[],[]] = some r ∧
      r.final.tapes = ![frame bits++suffix,frame (List.replicate n false),[true]] ∧
      r.steps = 4*n+1 ∧ r.peakTapeCells ≤ (frame bits++suffix).length+2*n+2 := by
  have h := even_prefix n [] bits suffix [] hlen
  obtain ⟨r, hr, hf, hs, hp⟩ := h.run (by rfl) (by simp)
  refine ⟨r, ?_, ?_, hs, ?_⟩
  · have hi : initialConfiguration machine ![frame bits++suffix,[],[]] =
        config 0 (frame bits++suffix) 0 [] := by
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · rfl
    change runFrom machine _ _ = _
    rw [hi]
    simpa only [List.nil_append, List.length_nil] using hr
  · rw [hf]
    have he : Streaming.marks (List.replicate n false) ++ [false] =
        frame (List.replicate n false) := by
      simpa only [List.append_nil, frame] using
        (Streaming.frame_append (List.replicate n false) []).symm
    simp only [finished, List.nil_append, he]
  · simpa only [List.nil_append, List.length_nil, Nat.add_zero] using hp

end NearCubicWires.RepairOrdinary.MemoryInitial
