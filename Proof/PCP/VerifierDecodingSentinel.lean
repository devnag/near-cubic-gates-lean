import Proof.PCP.VerifierDecodingLength

/-! Convert an actual header-produced raw unary counter to the arithmetic
sentinel ABI. Its endpoint head and the literal code-length cap are paid
inputs; the cap controls a saturating rewind and is itself restored. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.SentinelMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw (cap n : ℕ) := ZeroPadding.pad (cap+2) (List.replicate n true)
def cfg (state : Fin 4) (left right : List Bool) (lh rh : ℕ) : Configuration 2 4 :=
  ⟨state,![lh,rh],![left,right]⟩
def action (next : Fin 4) (lm rm : HeadMove) (write : Option Bool := none) : Action 2 4 :=
  ⟨next,![write,none],![lm,rm]⟩
def machine : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val = 3
  rule := fun state bits =>
    ![some (action 1 .stay .stay (some true)),
      some (if bits 1 then action 1 .left .right else action 2 .right .left (some false)),
      some (if bits 1 then action 2 .stay .left else action 3 .stay .right),none] state

@[simp] theorem cfg_cells (state : Fin 4) (left right : List Bool) (lh rh : ℕ) :
    (cfg state left right lh rh).tapeCells = left.length+right.length := by
  simp [cfg, Configuration.tapeCells, Fin.sum_univ_succ]

theorem raw_length (cap n : ℕ) (hn : n ≤ cap+2) : (raw cap n).length = cap+2 := by
  simp [raw, ZeroPadding.pad_length, max_eq_left hn]

theorem grow_step (cap n : ℕ) :
    step machine (cfg 0 (raw cap n) (CapMachine.counter cap cap) n 1) =
      some (cfg 1 (raw cap (n+1)) (CapMachine.counter cap cap) n 1) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]
    rw [raw, ZeroPadding.write_pad]
    have h := Streaming.write_append (List.replicate n true) true
    simpa only [raw, List.length_replicate, List.replicate_add, List.replicate_one] using
      congrArg (ZeroPadding.pad (cap+2)) h

theorem rewind_step (cap n pos : ℕ) (hp : pos < cap) :
    step machine (cfg 1 (raw cap (n+1)) (CapMachine.counter cap cap) (n-pos) (pos+1)) =
      some (cfg 1 (raw cap (n+1)) (CapMachine.counter cap cap) (n-(pos+1)) (pos+2)) := by
  simp [step, machine, cfg, Configuration.scanned, CapMachine.counter_read, hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply, Nat.sub_sub]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem finish_step (cap n : ℕ) :
    step machine (cfg 1 (raw cap (n+1)) (CapMachine.counter cap cap) 0 (cap+1)) =
      some (cfg 2 (CapMachine.counter cap n) (CapMachine.counter cap cap) 1 cap) := by
  simp [step, machine, cfg, Configuration.scanned, CapMachine.counter_read]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]
    rw [raw, ZeroPadding.write_pad]
    rfl

theorem reset_step (cap n k : ℕ) (hk : k < cap) :
    step machine (cfg 2 (CapMachine.counter cap n) (CapMachine.counter cap cap) 1 (k+1)) =
      some (cfg 2 (CapMachine.counter cap n) (CapMachine.counter cap cap) 1 k) := by
  simp [step, machine, cfg, Configuration.scanned, CapMachine.counter_read, hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem stop_step (cap n : ℕ) :
    step machine (cfg 2 (CapMachine.counter cap n) (CapMachine.counter cap cap) 1 0) =
      some (cfg 3 (CapMachine.counter cap n) (CapMachine.counter cap cap) 1 1) := by
  simp [step, machine, cfg, Configuration.scanned, CapMachine.counter_zero]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem rewind_prefix (steps cap n pos : ℕ) (hn : n ≤ cap) (hp : pos+steps ≤ cap) :
    Prefix machine (2*(cap+2)) steps
      (cfg 1 (raw cap (n+1)) (CapMachine.counter cap cap) (n-pos) (pos+1))
      (cfg 1 (raw cap (n+1)) (CapMachine.counter cap cap) (n-(pos+steps)) (pos+steps+1)) := by
  have hraw := raw_length cap (n+1) (by omega)
  have hc := CapMachine.counter_length cap cap (Nat.le_refl _)
  induction steps generalizing pos with
  | zero => simp; exact Prefix.refl _ (by simp [hraw,hc]; omega)
  | succ steps ih =>
    have hj := Prefix.step (by simp [hraw,hc]; omega) (by rfl)
      (rewind_step cap n pos (by omega)) (ih (pos+1) (by omega))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj

theorem reset_prefix (cap n k : ℕ) (hn : n ≤ cap) (hk : k ≤ cap) :
    Prefix machine (2*(cap+2)) (k+1)
      (cfg 2 (CapMachine.counter cap n) (CapMachine.counter cap cap) 1 k)
      (cfg 3 (CapMachine.counter cap n) (CapMachine.counter cap cap) 1 1) := by
  have hc := CapMachine.counter_length cap cap (Nat.le_refl _)
  have hn' := CapMachine.counter_length cap n hn
  induction k with
  | zero =>
    exact Prefix.step (by simp [hc,hn']; omega) (by rfl) (stop_step cap n)
      (Prefix.refl _ (by simp [hc,hn']; omega))
  | succ k ih =>
    exact Prefix.step (by simp [hc,hn']; omega) (by rfl)
      (reset_step cap n k (by omega)) (ih (by omega))

/-- Paid adapter from the header endpoint, preserving and restoring the cap. -/
theorem sentinel_run (cap n : ℕ) (hn : n ≤ cap) :
    ∃ receipt : ExecutionReceipt 2 4,
      runFrom machine (2*cap+3) (cfg 0 (raw cap n) (CapMachine.counter cap cap) n 1) = some receipt ∧
      receipt.final = cfg 3 (CapMachine.counter cap n) (CapMachine.counter cap cap) 1 1 ∧
      receipt.steps = 2*cap+3 ∧ receipt.peakTapeCells ≤ 2*(cap+2) := by
  have hp := rewind_prefix cap cap n 0 hn (by omega)
  simp only [Nat.sub_zero, Nat.zero_add, Nat.sub_eq_zero_of_le hn] at hp
  have ht := Prefix.step (by simp [raw_length cap (n+1) (by omega),
      CapMachine.counter_length cap cap (Nat.le_refl _)]; omega)
    (by rfl) (finish_step cap n) (reset_prefix cap n cap hn (Nat.le_refl _))
  have hi := Prefix.step (by simp [raw_length cap n (by omega),
      CapMachine.counter_length cap cap (Nat.le_refl _)]; omega)
    (by rfl) (grow_step cap n) (hp.trans ht)
  obtain ⟨r,hr,hf,hs,hpeak⟩ := hi.run (by rfl)
    (by simp [CapMachine.counter_length _ _ hn,CapMachine.counter_length cap cap (Nat.le_refl _)]; omega)
  refine ⟨r, ?_, hf, by omega, hpeak⟩
  have htime : cap+(cap+1+1)+1 = 2*cap+3 := by omega
  simpa only [htime] using hr

end NearCubicWires.RepairSource.VerifierDecoding.SentinelMachine
