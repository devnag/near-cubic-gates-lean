import Proof.PCP.VerifierDecodingHeader
import Proof.PCP.VerifierDecodingSlice

/-! Actual cap-c arithmetic for the guarded verifier decoder. Every bounded
counter has a false left sentinel and explicitly charged c+2 cell backing.
Growth checks the retained cap tape before writing the next unary cell. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.CapMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def counter (cap value : ℕ) : List Bool :=
  ZeroPadding.pad (cap+2) (false :: List.replicate value true)

theorem counter_length (cap value : ℕ) (h : value ≤ cap) : (counter cap value).length = cap+2 := by
  simp [counter, ZeroPadding.pad_length, max_eq_left (show value+1 ≤ cap+2 by omega)]

theorem counter_read (cap value pos : ℕ) :
    readTapeBit (counter cap value) (pos+1) = decide (pos < value) := by
  rw [counter, ZeroPadding.read_pad]
  change readTapeBit (List.replicate value true) pos = _
  exact SliceMachine.read_unary value pos

theorem counter_write (cap value : ℕ) :
    writeTapeBit (counter cap value) (value+1) true = counter cap (value+1) := by
  rw [counter, ZeroPadding.write_pad]
  have h := Streaming.write_append (false :: List.replicate value true) true
  simp only [List.length_cons, List.length_replicate] at h
  rw [h]
  simp only [counter, List.cons_append, List.replicate_add, List.replicate_one]

def action (next : Fin 3) (grow : Bool) : Action 3 3 :=
  ⟨next, ![none, if grow then some true else none, none],
    fun _ => if grow then .right else .stay⟩

def machine : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val ≠ 0
  rule := fun state scanned =>
    if state.val = 0 then
      if scanned 0 then
        if scanned 2 then some (action 0 true) else some (action 2 false)
      else some (action 1 false)
    else none

def cfg (state : Fin 3) (cap total value pos : ℕ) : Configuration 3 3 :=
  ⟨state, ![pos+1,value+1,value+1],
    ![counter cap total, counter cap value, counter cap cap]⟩

theorem cfg_cells (state : Fin 3) (cap total value pos : ℕ)
    (ht : total ≤ cap) (hv : value ≤ cap) :
    (cfg state cap total value pos).tapeCells = 3*(cap+2) := by
  simp [cfg, Configuration.tapeCells, Fin.sum_univ_succ, counter_length _ _ ht,
    counter_length _ _ hv, counter_length cap cap (Nat.le_refl _)]
  omega

theorem grow_step (cap total value pos : ℕ) (ht : pos < total) (hv : value < cap) :
    step machine (cfg 0 cap total value pos) = some (cfg 0 cap total (value+1) (pos+1)) := by
  simp [step, machine, cfg, Configuration.scanned, counter_read, ht, hv]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, counter_write]

theorem accept_step (cap total value : ℕ) :
    step machine (cfg 0 cap total value total) = some (cfg 1 cap total value total) := by
  simp [step, machine, cfg, Configuration.scanned, counter_read]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem reject_step (cap total pos : ℕ) (ht : pos < total) :
    step machine (cfg 0 cap total cap pos) = some (cfg 2 cap total cap pos) := by
  simp [step, machine, cfg, Configuration.scanned, counter_read, ht]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem grow_prefix (n cap total value pos : ℕ) (ht : total ≤ cap)
    (hn : pos+n ≤ total) (hv : value+n ≤ cap) :
    Prefix machine (3*(cap+2)) n (cfg 0 cap total value pos)
      (cfg 0 cap total (value+n) (pos+n)) := by
  induction n generalizing value pos with
  | zero => simpa using Prefix.refl _ (by rw [cfg_cells _ _ _ _ _ ht (by omega)])
  | succ n ih =>
    have hp := ih (value+1) (pos+1) (by omega) (by omega)
    have h := Prefix.step (by rw [cfg_cells _ _ _ _ _ ht (by omega)]) (by rfl)
      (grow_step cap total value pos (by omega) (by omega)) hp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- A complete guarded addition, including overflow rejection. The returned
counter is clipped at c, and no write is made past its c-cell value region. -/
theorem capped_add_run (cap base extra : ℕ) (hb : base ≤ cap) (he : extra ≤ cap) :
    ∃ receipt : ExecutionReceipt 3 3,
      runFrom machine (min extra (cap-base)+1) (cfg 0 cap extra base 0) = some receipt ∧
      receipt.final = cfg (if base+extra ≤ cap then 1 else 2) cap extra
        (min cap (base+extra)) (min extra (cap-base)) ∧
      receipt.steps = min extra (cap-base)+1 ∧ receipt.peakTapeCells ≤ 3*(cap+2) := by
  let count := min extra (cap-base)
  have hc : count ≤ extra := Nat.min_le_left _ _
  have hbc : base+count ≤ cap := by have h := Nat.min_le_right extra (cap-base); dsimp [count]; omega
  have hp := grow_prefix count cap extra base 0 he (by omega) hbc
  simp only [Nat.zero_add] at hp
  by_cases hfit : base+extra ≤ cap
  · have hk : count = extra := Nat.min_eq_left (by omega)
    have hmin : min extra (cap-base) = extra := hk
    rw [hk] at hp
    have tail : Prefix machine (3*(cap+2)) 1 (cfg 0 cap extra (base+extra) extra)
        (cfg 1 cap extra (base+extra) extra) :=
      Prefix.step (by rw [cfg_cells _ _ _ _ _ he hfit]) (by rfl)
        (accept_step cap extra (base+extra)) (Prefix.refl _ (by rw [cfg_cells _ _ _ _ _ he hfit]))
    obtain ⟨r, hr, hf, hs, hpeak⟩ := (hp.trans tail).run (by rfl) (by rw [cfg_cells _ _ _ _ _ he hfit])
    refine ⟨r, ?_, ?_, ?_, hpeak⟩
    · rw [hmin]
      exact hr
    · simpa only [if_pos hfit, min_eq_right hfit, hmin] using hf
    · rw [hmin]
      exact hs
  · have hk : count = cap-base := Nat.min_eq_right (by omega)
    have hvalue : base+count = cap := by omega
    have hlt : count < extra := by omega
    rw [hvalue] at hp
    have tail : Prefix machine (3*(cap+2)) 1 (cfg 0 cap extra cap count) (cfg 2 cap extra cap count) :=
      Prefix.step (by rw [cfg_cells _ _ _ _ _ he (Nat.le_refl _)]) (by rfl)
        (reject_step cap extra count hlt) (Prefix.refl _ (by rw [cfg_cells _ _ _ _ _ he (Nat.le_refl _)]))
    obtain ⟨r, hr, hf, hs, hpeak⟩ := (hp.trans tail).run (by rfl)
      (by rw [cfg_cells _ _ _ _ _ he (Nat.le_refl _)])
    exact ⟨r, hr, by simpa [hfit, min_eq_left (by omega : cap ≤ base+extra)] using hf, hs, hpeak⟩

end NearCubicWires.RepairSource.VerifierDecoding.CapMachine
