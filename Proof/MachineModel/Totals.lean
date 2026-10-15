import Proof.MachineModel.Basic

/-! P25: the two count workers.

`TotalsAppend` walks one child-count template (`UnaryTemplate.tape count`, head 1)
and appends `count` marks to the growing total tape, then returns the template
head to 1. `FinalizeT` turns the accumulated total `false :: 1^B` into the exact
`UnaryTemplate.tape B` at head 1 and allocates the incidence scratch
`replicate B false` at head 0, walking the template three times. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace TotalsAppend

/-- Tape 0 count template, tape 1 total. States: 0 walk, 1 return, 2 halt. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q bits =>
    if q.val = 0 then some (if bits 0 then ⟨0, ![none, some true], ![.right, .right]⟩
      else ⟨1, fun _ => none, ![.left, .stay]⟩)
    else if q.val = 1 then some (if bits 0 then ⟨1, fun _ => none, ![.left, .stay]⟩
      else ⟨2, fun _ => none, ![.right, .stay]⟩)
    else none

def cfg (q : Fin 3) (count ch : ℕ) (t : List Bool) : Configuration 2 3 :=
  ⟨q, ![ch, t.length], ![UnaryTemplate.tape count, t]⟩

@[simp] theorem halted_two : machine.halted 2 = true := rfl

theorem walk_step (count k : ℕ) (hk : k < count) (t : List Bool) :
    step machine (cfg 0 count (k+1) t) = some (cfg 0 count (k+2) (t ++ [true])) := by
  simp [step, machine, cfg, Configuration.scanned, UnaryTemplate.tape_mark count k hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end]

theorem walk_end (count : ℕ) (t : List Bool) :
    step machine (cfg 0 count (count+1) t) = some (cfg 1 count count t) := by
  simp [step, machine, cfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · rfl

theorem back_step (count k : ℕ) (hk : k < count) (t : List Bool) :
    step machine (cfg 1 count (k+1) t) = some (cfg 1 count k t) := by
  simp [step, machine, cfg, Configuration.scanned, UnaryTemplate.tape_mark count k hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · rfl

theorem back_stop (count : ℕ) (t : List Bool) :
    step machine (cfg 1 count 0 t) = some (cfg 2 count 1 t) := by
  simp [step, machine, cfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · rfl

theorem walk_timed (count k r : ℕ) (hkr : k + r = count) (t : List Bool) :
    Timed machine r (cfg 0 count (k+1) (t ++ List.replicate k true))
      (cfg 0 count (count+1) (t ++ List.replicate count true)) := by
  induction r generalizing k with
  | zero =>
    have : k = count := by omega
    subst this; exact Timed.refl machine _
  | succ r ih =>
    have h1 := walk_step count k (by omega) (t ++ List.replicate k true)
    rw [List.append_assoc, ← List.replicate_succ'] at h1
    have h := (Timed.single (p := machine) (by rfl) h1).trans (ih (k+1) (by omega))
    have e : 1 + r = r + 1 := Nat.add_comm 1 r
    rw [e] at h; exact h

theorem back_timed (count k : ℕ) (hk : k ≤ count) (t : List Bool) :
    Timed machine (k+1) (cfg 1 count k t) (cfg 2 count 1 t) := by
  induction k with
  | zero => exact Timed.single (by rfl) (back_stop count t)
  | succ k ih =>
    have h := (Timed.single (p := machine) (by rfl) (back_step count k (by omega) t)).trans (ih (by omega))
    have e : 1 + (k+1) = k+1+1 := by omega
    rw [e] at h; exact h

def cost (count : ℕ) : ℕ := 2*count+2

theorem append_run (count : ℕ) (t : List Bool) :
    ∃ r : ExecutionReceipt 2 3, runFrom machine (2*count+2) (cfg 0 count 1 t) = some r ∧
      r.final = cfg 2 count 1 (t ++ List.replicate count true) ∧ r.steps = 2*count+2 := by
  have s1 := walk_timed count 0 count (by omega) t
  simp only [List.replicate_zero, List.append_nil] at s1
  have s2 := Timed.single (p := machine) (by rfl) (walk_end count (t ++ List.replicate count true))
  have s3 := back_timed count count le_rfl (t ++ List.replicate count true)
  have h := (s1.trans s2).trans s3
  have e : count + 1 + (count+1) = 2*count+2 := by omega
  rw [e] at h
  exact h.run rfl

end TotalsAppend

namespace FinalizeT

/-- Tape 0 total/template, tape 1 incidence scratch. States: 0 terminator, 1 back
appending scratch zeros, 2 forward returning the scratch head, 3 back to the mark, 4 halt. -/
def machine : Machine 2 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q bits =>
    if q.val = 0 then some ⟨1, ![some false, none], ![.left, .stay]⟩
    else if q.val = 1 then some (if bits 0 then ⟨1, ![none, some false], ![.left, .right]⟩
      else ⟨2, fun _ => none, ![.right, .stay]⟩)
    else if q.val = 2 then some (if bits 0 then ⟨2, fun _ => none, ![.right, .left]⟩
      else ⟨3, fun _ => none, ![.left, .stay]⟩)
    else if q.val = 3 then some (if bits 0 then ⟨3, fun _ => none, ![.left, .stay]⟩
      else ⟨4, fun _ => none, ![.right, .stay]⟩)
    else none

def cfg (q : Fin 5) (t : List Bool) (th : ℕ) (z zh : ℕ) : Configuration 2 5 :=
  ⟨q, ![th, zh], ![t, List.replicate z false]⟩

@[simp] theorem halted_four : machine.halted 4 = true := rfl

theorem terminator_step (B : ℕ) :
    step machine (cfg 0 (false :: List.replicate B true) (B+1) 0 0) =
      some (cfg 1 (UnaryTemplate.tape B) B 0 0) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i
    · change writeTapeBit (false :: List.replicate B true) (B+1) false = UnaryTemplate.tape B
      have h := write_end (false :: List.replicate B true) false
      simp only [List.length_cons, List.length_replicate] at h
      rw [h]; rfl
    · rfl

theorem back1_step (B k z : ℕ) (hk : k < B) :
    step machine (cfg 1 (UnaryTemplate.tape B) (k+1) z z) = some (cfg 1 (UnaryTemplate.tape B) k (z+1) (z+1)) := by
  simp [step, machine, cfg, Configuration.scanned, UnaryTemplate.tape_mark B k hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end_replicate]

theorem back1_stop (B z : ℕ) :
    step machine (cfg 1 (UnaryTemplate.tape B) 0 z z) = some (cfg 2 (UnaryTemplate.tape B) 1 z z) := by
  simp [step, machine, cfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · rfl

theorem fwd_step (B j z : ℕ) (hj : j < B) :
    step machine (cfg 2 (UnaryTemplate.tape B) (j+1) z (B-j)) = some (cfg 2 (UnaryTemplate.tape B) (j+2) z (B-j-1)) := by
  simp [step, machine, cfg, Configuration.scanned, UnaryTemplate.tape_mark B j hj]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · rfl

theorem fwd_stop (B z : ℕ) :
    step machine (cfg 2 (UnaryTemplate.tape B) (B+1) z 0) = some (cfg 3 (UnaryTemplate.tape B) B z 0) := by
  simp [step, machine, cfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · rfl

theorem back3_step (B k z : ℕ) (hk : k < B) :
    step machine (cfg 3 (UnaryTemplate.tape B) (k+1) z 0) = some (cfg 3 (UnaryTemplate.tape B) k z 0) := by
  simp [step, machine, cfg, Configuration.scanned, UnaryTemplate.tape_mark B k hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · rfl

theorem back3_stop (B z : ℕ) :
    step machine (cfg 3 (UnaryTemplate.tape B) 0 z 0) = some (cfg 4 (UnaryTemplate.tape B) 1 z 0) := by
  simp [step, machine, cfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · rfl

theorem back1_timed (B k z : ℕ) (hk : k ≤ B) :
    Timed machine (k+1) (cfg 1 (UnaryTemplate.tape B) k z z) (cfg 2 (UnaryTemplate.tape B) 1 (z+k) (z+k)) := by
  induction k generalizing z with
  | zero => simpa using Timed.single (p := machine) (by rfl) (back1_stop B z)
  | succ k ih =>
    have h := (Timed.single (p := machine) (by rfl) (back1_step B k z (by omega))).trans (ih (z+1) (by omega))
    have e1 : z+1+k = z+(k+1) := by omega
    have e2 : 1+(k+1) = k+1+1 := by omega
    rw [e1, e2] at h; exact h

theorem fwd_timed (B j r z : ℕ) (hjr : j + r = B) :
    Timed machine r (cfg 2 (UnaryTemplate.tape B) (j+1) z r) (cfg 2 (UnaryTemplate.tape B) (B+1) z 0) := by
  induction r generalizing j with
  | zero =>
    have : j = B := by omega
    subst this; exact Timed.refl machine _
  | succ r ih =>
    have h1 := fwd_step B j z (by omega)
    have e0 : B - j = r+1 := by omega
    rw [e0, Nat.add_sub_cancel] at h1
    have h := (Timed.single (p := machine) (by rfl) h1).trans (ih (j+1) (by omega))
    have e : 1 + r = r + 1 := Nat.add_comm 1 r
    rw [e] at h; exact h

theorem back3_timed (B k z : ℕ) (hk : k ≤ B) :
    Timed machine (k+1) (cfg 3 (UnaryTemplate.tape B) k z 0) (cfg 4 (UnaryTemplate.tape B) 1 z 0) := by
  induction k with
  | zero => exact Timed.single (by rfl) (back3_stop B z)
  | succ k ih =>
    have h := (Timed.single (p := machine) (by rfl) (back3_step B k z (by omega))).trans (ih (by omega))
    have e : 1+(k+1) = k+1+1 := by omega
    rw [e] at h; exact h

/-- From the accumulated total `false :: 1^B` (head at its end) and an empty scratch
to the exact template at head 1 and `replicate B false` at head 0, in `3B+4` steps. -/
theorem finalize_run (B : ℕ) :
    ∃ r : ExecutionReceipt 2 5,
      runFrom machine (3*B+4) (cfg 0 (false :: List.replicate B true) (B+1) 0 0) = some r ∧
      r.final = cfg 4 (UnaryTemplate.tape B) 1 B 0 ∧ r.steps = 3*B+4 := by
  have s0 := Timed.single (p := machine) (by rfl) (terminator_step B)
  have s1 := back1_timed B B 0 le_rfl
  simp only [Nat.zero_add] at s1
  have s2 := fwd_timed B 0 B B (by omega)
  simp only [Nat.zero_add] at s2
  have s3 := Timed.single (p := machine) (by rfl) (fwd_stop B B)
  have s4 := back3_timed B B B le_rfl
  have h := (((s0.trans s1).trans s2).trans s3).trans s4
  have e : 1 + (B+1) + B + 1 + (B+1) = 3*B+4 := by omega
  rw [e] at h
  exact h.run rfl

end FinalizeT

end NearCubicWires.ExtDecompositionBatch
