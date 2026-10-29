import SourceAdapters.RAMTrace.Sorted

/-!
# The event-trace system over bits, and the objects of a trace

`app:event-trace` `def:event-trace` with every slot a bit (`HoldsB`), and the objects `thm:trace`'s proof reads off a trace:
the decoded configurations, the instructions, access values, time stamps and counters of the rows, the records of
the lanes, the memory sequence (`lem:trace-memory` (a)), and the arithmetic of keys (the record convention of `app:event-trace`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMTrace

open NearCubicGates.Adapters.ACSP Expr BitVec

/-- **`def:event-trace` over bits.** `ET(M, τ, x̄)` holds at a Boolean assignment (every slot is a bit, (G)). -/
def HoldsB (M : Ram) (kind : Fin M.ops → AluOp) (τ : ℕ) (xbar : List Bool) (b : Trace Bool) : Prop :=
  (∀ i < 2 ^ τ, ∀ q : TEq, q.Active (dims M τ) → (timeEq M kind τ q).evalB (b.timeRead i) = false) ∧
  (∀ c : TCopy, c.Active (dims M τ) → b.timeRead 0 c.dst = false) ∧
  (∀ i, i + 1 < 2 ^ τ → ∀ c : TCopy, c.Active (dims M τ) → b.timeRead (i + 1) c.dst = b.time i c.src) ∧
  (∀ i, i + 1 < 2 ^ τ → (outE M).evalB (b.timeRead i) = false) ∧
  (accE M).evalB (b.timeRead (2 ^ τ - 1)) = false ∧
  (∀ j < 2 ^ (τ + 1), ∀ q : SEq, q.Active (dims M τ) → (sortEq (dims M τ) q).evalB (b.sortRead j) = false) ∧
  (∀ f k, (SSlot.prev f k).Active (dims M τ) → b.sort 0 (.prev f k) = decide (f = .act)) ∧
  (∀ j, j + 1 < 2 ^ (τ + 1) → ∀ f k, (SSlot.prev f k).Active (dims M τ) →
    b.sort (j + 1) (.prev f k) = b.dst j f k) ∧
  (∀ c < xbar.length / M.w,
    b.src (2 ^ τ + c) .act 0 = true ∧ b.src (2 ^ τ + c) .rgn 0 = true ∧ b.src (2 ^ τ + c) .ph 0 = false ∧
    b.src (2 ^ τ + c) .st 0 = false ∧ (∀ j < τ, b.src (2 ^ τ + c) .ts j = false) ∧
    (∀ j < M.w, b.src (2 ^ τ + c) .ad j = c.testBit j) ∧
    (∀ k < M.w, b.src (2 ^ τ + c) .va k = xbar.getD (c * M.w + k) false)) ∧
  (∀ x, 2 ^ τ + xbar.length / M.w ≤ x → x < 2 ^ (τ + 1) → ∀ s : RecSlot, s.Active (dims M τ) →
    b.src x s.1 s.2 = false) ∧
  (∃ π : Equiv.Perm (Fin (2 ^ (τ + 1))), ∀ x : Fin (2 ^ (τ + 1)), ∀ s : RecSlot, s.Active (dims M τ) →
    b.dst (π x) s.1 s.2 = b.src x s.1 s.2)

/-! ## Configurations are read from active slots -/

section Congr

variable {M : Ram}

theorem decCur_congr (v v' : TVar → Bool) (hpc : ∀ j < M.w, v (.inl (.pc j)) = v' (.inl (.pc j)))
    (hfl : ∀ r < M.k, v (.inl (.fl r)) = v' (.inl (.fl r)))
    (hrg : ∀ r < M.k, ∀ j < M.w, v (.inl (.rg r j)) = v' (.inl (.rg r j))) :
    (decCur v : M.Config) = decCur v' := by
  simp only [decCur]
  rw [bvOf_congr _ _ _ hpc]
  congr 1
  funext r
  rw [hfl r.val r.isLt, bvOf_congr _ _ _ (hrg r.val r.isLt)]

theorem decNxt_congr (v v' : TVar → Bool) (hpc : ∀ j < M.w, v (.inl (.npc j)) = v' (.inl (.npc j)))
    (hfl : ∀ r < M.k, v (.inl (.nfl r)) = v' (.inl (.nfl r)))
    (hrg : ∀ r < M.k, ∀ j < M.w, v (.inl (.nrg r j)) = v' (.inl (.nrg r j))) :
    (decNxt v : M.Config) = decNxt v' := by
  simp only [decNxt]
  rw [bvOf_congr _ _ _ hpc]
  congr 1
  funext r
  rw [hfl r.val r.isLt, bvOf_congr _ _ _ (hrg r.val r.isLt)]

end Congr

/-! ## Memory (`lem:trace-memory` (a)) -/

section Memory

variable {M : Ram}

/-- The memory after executing `I` at `S`: only a `store j x` changes it, writing `val x` at `val (reg j)`. -/
def memNext (S : M.Config) (I : Instr M.w M.k M.ops) (mem : M.Memory) : M.Memory :=
  match I with
  | .store j x => Function.update mem (S.val (.reg j)) (S.val x)
  | _ => mem

/-- The address accessed by a load or a store (the `X` bus). -/
theorem memNext_ne (S : M.Config) (I : Instr M.w M.k M.ops) (mem : M.Memory) (A : BitVec M.w)
    (h : isSt I = true → xWord S I ≠ A) : memNext S I mem A = mem A := by
  cases I with
  | store j x =>
    have hne := h rfl
    simp only [xWord] at hne
    simp [memNext, Function.update_of_ne hne.symm]
  | _ => rfl

theorem memNext_store (S : M.Config) (I : Instr M.w M.k M.ops) (mem : M.Memory) (hI : isSt I = true) :
    memNext S I mem (xWord S I) = yWord S I := by
  cases I <;> simp_all [isSt, memNext, xWord, yWord]

/-- **One step** (`lem:trace-step` (iii) with `lem:trace-memory` (a)): a row whose instruction is not `out`, whose load reads the
memory, is a `Ram.Step` from `(S, mem)` to `(rowSucc S mv rd I, memNext S I mem)`. -/
theorem step_of_row (S : M.Config) (I : Instr M.w M.k M.ops) (mv : BitVec M.w) (rd : Option (BitVec M.w))
    (mem : M.Memory) (hI : M.instrAt S.pc = some I) (hout : isOut I = false)
    (hload : isLd I = true → mv = mem (xWord S I)) :
    M.Step S mem (rowSucc S mv rd I) (memNext S I mem) := by
  unfold Ram.Step
  rw [hI]
  cases I with
  | nop => exact ⟨rfl, rfl⟩
  | pload => exact ⟨rfl, rfl⟩
  | readA i => exact ⟨⟨rd, rfl⟩, rfl⟩
  | readB i => exact ⟨⟨rd, rfl⟩, rfl⟩
  | load i j => exact ⟨by simp [rowSucc, hload rfl, xWord], rfl⟩
  | store j x => exact ⟨rfl, rfl⟩
  | iseof i j => exact ⟨rfl, rfl⟩
  | out b => simp [isOut] at hout
  | arith op i x y => exact ⟨rfl, rfl⟩
  | je i c => exact ⟨rfl, rfl⟩
  | jne i c => exact ⟨rfl, rfl⟩
  | jmp c => exact ⟨rfl, rfl⟩

end Memory

/-! ## Keys (the record convention of `app:event-trace`) -/

section KeyArith

/-- `a·M + A < b·M + B` with `A, B < M` is the lexicographic order. -/
theorem lex_lt {M a b A B : ℕ} (hA : A < M) (hB : B < M) :
    A + M * a < B + M * b ↔ a < b ∨ (a = b ∧ A < B) := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy a b with hab | hab | hab
    · exact Or.inl hab
    · subst hab; right; exact ⟨rfl, by omega⟩
    · exfalso
      have : M * (b + 1) ≤ M * a := Nat.mul_le_mul_left _ hab
      rw [Nat.mul_succ] at this; omega
  · rintro (hab | ⟨rfl, hAB⟩)
    · have : M * (a + 1) ≤ M * b := Nat.mul_le_mul_left _ hab
      rw [Nat.mul_succ] at this; omega
    · omega

end KeyArith

end NearCubicGates.Adapters.RAMTrace
