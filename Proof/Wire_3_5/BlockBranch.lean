import Proof.Wire_3_5.BlockCost
import Proof.Amplification.RecoveryCursorCalls

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.BlockPlatform

/-- The test point: a one-state program that has already halted. -/
def idle (t : ℕ) : Machine t 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none

section
variable {t : ℕ}

def branchSizes (b c : Block t) : Fin 3 → ℕ := ![1, b.states, c.states]

def branchPrograms (b c : Block t) : (j : Fin 3) → Machine t (branchSizes b c j)
  | 0 => idle t
  | 1 => b.machine
  | 2 => c.machine

/-- After the test point: the bit under head `i` picks the branch; each branch then stops. -/
def branchNext (b c : Block t) (i : Fin t) : (j : Fin 3) → Fin (branchSizes b c j) → (Fin t → Bool) → Option (Fin 3)
  | 0, _, bits => if bits i then some 1 else some 2
  | 1, _, _ => none
  | 2, _, _ => none

noncomputable def branchMachine (i : Fin t) (b c : Block t) :=
  RecoveryCalls.machine (branchSizes b c) (branchPrograms b c) 0 (branchNext b c i)

/-- The bit the branch reads: tape `i` under its head, at the entry bank. -/
def entryBit (H : Fin t → ℕ) (A : Fin t → List Bool) (i : Fin t) : Bool := readTapeBit (A i) (H i)

/-- One branch's receipt inside the call graph. -/
theorem branch_timed (i : Fin t) (b c : Block t) (l : Fin 3) (hl : l = 1 ∨ l = 2)
    (H : Fin t → ℕ) (A : Fin t → List Bool)
    (hpick : (if entryBit H A i then (1 : Fin 3) else 2) = l)
    (fuel : ℕ) (r : ExecutionReceipt t (branchSizes b c l))
    (hr : runFrom (branchPrograms b c l) fuel ⟨(branchPrograms b c l).start, H, A⟩ = some r) :
    ∃ n ≤ 0 + 1 + (fuel + 1), Timed (branchMachine i b c) n
      (controlConfig (RecoveryCalls.code (branchSizes b c) 0) ⟨(idle t).start, H, A⟩)
      (RecoveryCalls.stopped (branchSizes b c) r.final.heads r.final.tapes) := by
  have hidle := runFrom_zero_of_halted (idle t) ⟨(idle t).start, H, A⟩ rfl
  obtain ⟨u, hu, first⟩ := call_receipt (branchSizes b c) (branchPrograms b c) 0 (branchNext b c i) 0 l 0
    ⟨(idle t).start, H, A⟩ _ hidle (by
      change (if readTapeBit (A i) (H i) then some (1 : Fin 3) else some 2) = some l
      rw [← hpick]
      unfold entryBit
      split <;> rfl)
  obtain ⟨v, hv, tail⟩ := stop_receipt (branchSizes b c) (branchPrograms b c) 0 (branchNext b c i) l fuel _ r hr
    (by rcases hl with rfl | rfl <;> rfl)
  exact ⟨u + v, by omega, first.trans tail⟩

/-- **The conditional block.** Both branches start from the same entry bank. -/
noncomputable def branch (i : Fin t) (b c : Block t) (hH : b.entryH = c.entryH) (hA : b.entryA = c.entryA) :
    Block t where
  states := Fintype.card (RecoveryCalls.Control (branchSizes b c))
  machine := branchMachine i b c
  cost := (if entryBit b.entryH b.entryA i then b.cost else c.cost) + 2
  entryH := b.entryH
  entryA := b.entryA
  exitH := if entryBit b.entryH b.entryA i then b.exitH else c.exitH
  exitA := if entryBit b.entryH b.entryA i then b.exitA else c.exitA
  run := by
    by_cases hbit : entryBit b.entryH b.entryA i = true
    · obtain ⟨r, hr, hh, ht, _⟩ := b.run
      obtain ⟨n, hn, htimed⟩ := branch_timed i b c 1 (Or.inl rfl) b.entryH b.entryA (by rw [if_pos hbit]) b.cost r hr
      obtain ⟨actual, ha, haf, has⟩ := htimed.run (by simp [branchMachine, RecoveryCalls.machine, RecoveryCalls.stopped])
      have more := runFrom_moreFuel (branchMachine i b c) n (b.cost + 2 - n) _ actual ha
      rw [Nat.add_sub_of_le (by omega)] at more
      refine ⟨actual, ?_, ?_, ?_, ?_⟩
      · rw [if_pos hbit]; exact more
      · rw [if_pos hbit, haf, ← hh]; rfl
      · rw [if_pos hbit, haf, ← ht]; rfl
      · rw [if_pos hbit, has]; omega
    · have hbit' : entryBit b.entryH b.entryA i = false := by simpa using hbit
      obtain ⟨r, hr, hh, ht, _⟩ := c.run
      rw [← hH, ← hA] at hr
      obtain ⟨n, hn, htimed⟩ := branch_timed i b c 2 (Or.inr rfl) b.entryH b.entryA (by rw [if_neg hbit]) c.cost r hr
      obtain ⟨actual, ha, haf, has⟩ := htimed.run (by simp [branchMachine, RecoveryCalls.machine, RecoveryCalls.stopped])
      have more := runFrom_moreFuel (branchMachine i b c) n (c.cost + 2 - n) _ actual ha
      rw [Nat.add_sub_of_le (by omega)] at more
      refine ⟨actual, ?_, ?_, ?_, ?_⟩
      · rw [if_neg hbit]; exact more
      · rw [if_neg hbit, haf, ← hh]; rfl
      · rw [if_neg hbit, haf, ← ht]; rfl
      · rw [if_neg hbit, has]; omega

theorem branch_exit (i : Fin t) (b c : Block t) (hH : b.entryH = c.entryH) (hA : b.entryA = c.entryA) :
    ((branch i b c hH hA).exitA = if entryBit b.entryH b.entryA i then b.exitA else c.exitA) ∧
      ((branch i b c hH hA).exitH = if entryBit b.entryH b.entryA i then b.exitH else c.exitH) := ⟨rfl, rfl⟩

theorem branch_cost (i : Fin t) (b c : Block t) (hH : b.entryH = c.entryH) (hA : b.entryA = c.entryA) :
    (branch i b c hH hA).cost = (if entryBit b.entryH b.entryA i then b.cost else c.cost) + 2 := rfl

theorem branch_cost_le (i : Fin t) (b c : Block t) (hH : b.entryH = c.entryH) (hA : b.entryA = c.entryA) :
    (branch i b c hH hA).cost ≤ max b.cost c.cost + 2 := by
  rw [branch_cost]
  split <;> omega

end

/-! ## One-sided branches over fixed machines

A uniform program runs the SAME machine at every input, but only the taken branch has a run at a given
input (the other branch's preconditions may fail there). `branchM i p q` is the conditional over two
machines. `branchT` and `branchF` are its blocks when the bit is set, respectively clear: only the taken
branch needs a `Block`. -/

section
variable {t : ℕ}

def sizesM (s₁ s₂ : ℕ) : Fin 3 → ℕ := ![1, s₁, s₂]

def programsM {s₁ s₂ : ℕ} (p : Machine t s₁) (q : Machine t s₂) : (j : Fin 3) → Machine t (sizesM s₁ s₂ j)
  | 0 => idle t
  | 1 => p
  | 2 => q

def nextM (s₁ s₂ : ℕ) (i : Fin t) : (j : Fin 3) → Fin (sizesM s₁ s₂ j) → (Fin t → Bool) → Option (Fin 3)
  | 0, _, bits => if bits i then some 1 else some 2
  | 1, _, _ => none
  | 2, _, _ => none

/-- The conditional over two fixed machines. -/
noncomputable def branchM (i : Fin t) {s₁ s₂ : ℕ} (p : Machine t s₁) (q : Machine t s₂) :=
  RecoveryCalls.machine (sizesM s₁ s₂) (programsM p q) 0 (nextM s₁ s₂ i)

theorem branchM_timed (i : Fin t) {s₁ s₂ : ℕ} (p : Machine t s₁) (q : Machine t s₂) (l : Fin 3) (hl : l = 1 ∨ l = 2)
    (H : Fin t → ℕ) (A : Fin t → List Bool)
    (hpick : (if entryBit H A i then (1 : Fin 3) else 2) = l)
    (fuel : ℕ) (r : ExecutionReceipt t (sizesM s₁ s₂ l))
    (hr : runFrom (programsM p q l) fuel ⟨(programsM p q l).start, H, A⟩ = some r) :
    ∃ n ≤ 0 + 1 + (fuel + 1), Timed (branchM i p q) n
      (controlConfig (RecoveryCalls.code (sizesM s₁ s₂) 0) ⟨(idle t).start, H, A⟩)
      (RecoveryCalls.stopped (sizesM s₁ s₂) r.final.heads r.final.tapes) := by
  have hidle := runFrom_zero_of_halted (idle t) ⟨(idle t).start, H, A⟩ rfl
  obtain ⟨u, hu, first⟩ := call_receipt (sizesM s₁ s₂) (programsM p q) 0 (nextM s₁ s₂ i) 0 l 0
    ⟨(idle t).start, H, A⟩ _ hidle (by
      change (if readTapeBit (A i) (H i) then some (1 : Fin 3) else some 2) = some l
      rw [← hpick]
      unfold entryBit
      split <;> rfl)
  obtain ⟨v, hv, tail⟩ := stop_receipt (sizesM s₁ s₂) (programsM p q) 0 (nextM s₁ s₂ i) l fuel _ r hr
    (by rcases hl with rfl | rfl <;> rfl)
  exact ⟨u + v, by omega, first.trans tail⟩

/-- The taken branch is `b` (the bit is set); the other branch is only a machine. -/
noncomputable def branchT (i : Fin t) (b : Block t) {s₂ : ℕ} (q : Machine t s₂)
    (hbit : entryBit b.entryH b.entryA i = true) : Block t where
  states := Fintype.card (RecoveryCalls.Control (sizesM b.states s₂))
  machine := branchM i b.machine q
  cost := b.cost + 2
  entryH := b.entryH
  entryA := b.entryA
  exitH := b.exitH
  exitA := b.exitA
  run := by
    obtain ⟨r, hr, hh, ht, _⟩ := b.run
    obtain ⟨n, hn, htimed⟩ := branchM_timed i b.machine q 1 (Or.inl rfl) b.entryH b.entryA (by rw [if_pos hbit])
      b.cost r hr
    obtain ⟨actual, ha, haf, has⟩ := htimed.run (by simp [branchM, RecoveryCalls.machine, RecoveryCalls.stopped])
    have more := runFrom_moreFuel (branchM i b.machine q) n (b.cost + 2 - n) _ actual ha
    rw [Nat.add_sub_of_le (by omega)] at more
    refine ⟨actual, more, ?_, ?_, by omega⟩
    · rw [haf, ← hh]; rfl
    · rw [haf, ← ht]; rfl

/-- The taken branch is `c` (the bit is clear); the other branch is only a machine. -/
noncomputable def branchF (i : Fin t) {s₁ : ℕ} (p : Machine t s₁) (c : Block t)
    (hbit : entryBit c.entryH c.entryA i = false) : Block t where
  states := Fintype.card (RecoveryCalls.Control (sizesM s₁ c.states))
  machine := branchM i p c.machine
  cost := c.cost + 2
  entryH := c.entryH
  entryA := c.entryA
  exitH := c.exitH
  exitA := c.exitA
  run := by
    obtain ⟨r, hr, hh, ht, _⟩ := c.run
    obtain ⟨n, hn, htimed⟩ := branchM_timed i p c.machine 2 (Or.inr rfl) c.entryH c.entryA
      (by rw [if_neg (by simp [hbit])]) c.cost r hr
    obtain ⟨actual, ha, haf, has⟩ := htimed.run (by simp [branchM, RecoveryCalls.machine, RecoveryCalls.stopped])
    have more := runFrom_moreFuel (branchM i p c.machine) n (c.cost + 2 - n) _ actual ha
    rw [Nat.add_sub_of_le (by omega)] at more
    refine ⟨actual, more, ?_, ?_, by omega⟩
    · rw [haf, ← hh]; rfl
    · rw [haf, ← ht]; rfl

@[simp] theorem branchT_cost (i : Fin t) (b : Block t) {s₂ : ℕ} (q : Machine t s₂)
    (hbit : entryBit b.entryH b.entryA i = true) : (branchT i b q hbit).cost = b.cost + 2 := rfl
@[simp] theorem branchF_cost (i : Fin t) {s₁ : ℕ} (p : Machine t s₁) (c : Block t)
    (hbit : entryBit c.entryH c.entryA i = false) : (branchF i p c hbit).cost = c.cost + 2 := rfl

end

/-- A branch between two blocks within a class stays within that class (the two transfers are paid). -/
theorem Within.branch {E : Envelope} {cls : BudgetClass} {q k psi c₁ c₂ n₁ n₂ : ℕ} (hq : 1 ≤ q)
    (h₁ : Within E cls c₁ q k psi n₁) (h₂ : Within E cls c₂ q k psi n₂) :
    Within E cls (c₁ + c₂ + 2) q k psi (max n₁ n₂ + 2) := by
  have hmax : Within E cls (c₁ + c₂) q k psi (max n₁ n₂) :=
    (h₁.add h₂).mono (by omega)
  exact (hmax.add (Within.const (E := E) (cls := cls) (k := k) (psi := psi) hq 2)).mono (le_refl _)

/-- Executable check: the branch reads the bit under the head. -/
theorem entryBit_twin : entryBit (t := 2) ![1, 0] ![[false, true], [false]] 0 = true ∧
    entryBit (t := 2) ![0, 0] ![[false, true], [false]] 0 = false := by decide

end NearCubicWires.WireExponent3_5.Block
