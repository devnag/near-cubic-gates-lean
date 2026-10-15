import Proof.PCP.VerifierDecodingProduct

/-! Paid unary copy used by the capped dimension-doubling loop. It overwrites
an existing shorter counter and allocates every additional true cell. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.CopyMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem write_replicate (value pos : ℕ) (hp : pos < value) :
    writeTapeBit (List.replicate value true) pos true = List.replicate value true := by
  induction pos generalizing value with
  | zero => cases value <;> simp_all [List.replicate_succ, writeTapeBit]
  | succ pos ih =>
    cases value with
    | zero => omega
    | succ value =>
      simpa only [List.replicate_succ, writeTapeBit] using
        congrArg (List.cons true) (ih value (by omega))

theorem counter_write_inside (cap value pos : ℕ) (hp : pos < value) :
    writeTapeBit (CapMachine.counter cap value) (pos+1) true = CapMachine.counter cap value := by
  rw [CapMachine.counter, ZeroPadding.write_pad]
  change ZeroPadding.pad (cap+2) (false :: writeTapeBit (List.replicate value true) pos true) = _
  rw [write_replicate value pos hp]

theorem counter_overlay (cap base pos : ℕ) :
    writeTapeBit (CapMachine.counter cap (max base pos)) (pos+1) true =
      CapMachine.counter cap (max base (pos+1)) := by
  by_cases h : pos < base
  · rw [max_eq_left (by omega : pos ≤ base), max_eq_left (by omega : pos+1 ≤ base)]
    exact counter_write_inside cap base pos h
  · rw [max_eq_right (by omega : base ≤ pos), max_eq_right (by omega : base ≤ pos+1)]
    exact CapMachine.counter_write cap pos

def machine : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val = 1
  rule := fun state scanned => if state.val = 0 then
    some ⟨if scanned 0 then 0 else 1,
      ![none, if scanned 0 then some true else none],
      fun _ => if scanned 0 then .right else .stay⟩ else none

def cfg (state : Fin 2) (cap total base pos : ℕ) : Configuration 2 2 :=
  ⟨state,fun _ => pos+1,
    ![CapMachine.counter cap total, CapMachine.counter cap (max base pos)]⟩

theorem cfg_cells (state : Fin 2) (cap total base pos : ℕ)
    (ht : total ≤ cap) (hb : base ≤ cap) (hp : pos ≤ cap) :
    (cfg state cap total base pos).tapeCells = 2*(cap+2) := by
  simp [cfg, Configuration.tapeCells, Fin.sum_univ_succ,
    CapMachine.counter_length _ _ ht, CapMachine.counter_length _ _ (max_le hb hp)]
  omega

theorem copy_step (cap total base pos : ℕ) (hp : pos < total) :
    step machine (cfg 0 cap total base pos) = some (cfg 0 cap total base (pos+1)) := by
  simp [step, machine, cfg, Configuration.scanned, CapMachine.counter_read, hp]
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, counter_overlay]

theorem stop_step (cap total base : ℕ) :
    step machine (cfg 0 cap total base total) = some (cfg 1 cap total base total) := by
  simp [step, machine, cfg, Configuration.scanned, CapMachine.counter_read]
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl

theorem copy_prefix (n cap total base pos : ℕ)
    (ht : total ≤ cap) (hb : base ≤ cap) (hn : pos+n ≤ total) :
    Prefix machine (2*(cap+2)) n (cfg 0 cap total base pos) (cfg 0 cap total base (pos+n)) := by
  induction n generalizing pos with
  | zero => simpa using Prefix.refl _ (by rw [cfg_cells _ _ _ _ _ ht hb (by omega)])
  | succ n ih =>
    have h := Prefix.step (by rw [cfg_cells _ _ _ _ _ ht hb (by omega)]) (by rfl)
      (copy_step cap total base pos (by omega)) (ih (pos+1) (by omega))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem copy_run (cap total base : ℕ) (ht : total ≤ cap) (hb : base ≤ total) :
    ∃ receipt : ExecutionReceipt 2 2,
      runFrom machine (total+1) (cfg 0 cap total base 0) = some receipt ∧
      receipt.final = cfg 1 cap total base total ∧ receipt.steps = total+1 ∧
      receipt.peakTapeCells ≤ 2*(cap+2) := by
  have hp := copy_prefix total cap total base 0 ht (hb.trans ht) (by omega)
  simp only [Nat.zero_add] at hp
  have tail : Prefix machine (2*(cap+2)) 1 (cfg 0 cap total base total) (cfg 1 cap total base total) :=
    Prefix.step (by rw [cfg_cells _ _ _ _ _ ht (hb.trans ht) ht]) (by rfl)
      (stop_step cap total base) (Prefix.refl _ (by rw [cfg_cells _ _ _ _ _ ht (hb.trans ht) ht]))
  exact (hp.trans tail).run (by rfl) (by rw [cfg_cells _ _ _ _ _ ht (hb.trans ht) ht])

end NearCubicWires.RepairSource.VerifierDecoding.CopyMachine
