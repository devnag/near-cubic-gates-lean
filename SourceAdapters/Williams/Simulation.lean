import NineInputs
import Proof.Amplification.RecoveryTimedExecution
import Proof.Foundations.OrdinaryMachine
import Proof.Wire_3_5.PrimTReadEq
import Mathlib.Tactic.DeriveFintype

/-!
# W03: the textbook multitape machine on the release's bit tapes, at constant overhead per step

Convert the source's fixed finite alphabet and tape/head convention to the repository's local bit
machine with constant overhead per step. Prove the state/tape relation, rather than assume a black-box general
compiler with an unspecified polynomial loss. Williams matrix multiplier | Constant/
polylogarithmic overhead plus near-linear I/O conversion.
`sec:prelim`, "Machine model": "Algorithms are deterministic or nondeterministic multitape Turing machines over a binary alphabet, and
time counts machine steps. This is the model of the imported algorithms (\cref{imp:batch,imp:ae-refuter})." This
module is the proof that a textbook machine over a finite alphabet (the leaf's model) is one over the binary
alphabet of `LocalBitMultitape` with a constant factor in time.

**Construction.** Source tape `i` is target tape `i`. Each source cell is a block of `w = extraSymbols + 4` target
cells holding the thermometer code of its symbol (`code s j = (j < s)`; the blank is all `false`, so unwritten target
cells read as blanks). One source step is `3w - 1` target steps: read the block left to right into the control
(`w` steps, the last one consults the source transition), write the new block right to left (`w` steps, the last
one is also the first head move), and `w - 1` further head moves. A halting source configuration costs `w` steps.

**Exported.** `simulator M : Machine M.tapes (Fintype.card (Phase M))`, `Holds` (the tape relation),
`simulator_run`: a source run of `t` steps that halts is a target run of exactly `(3w-1)·t + w` steps that halts,
with every final target tape holding the final source tape and every head at `w·h + (w-1)`.
-/

namespace NearCubicGates.Adapters.Williams

open NearCubicGates.Published.Williams
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.WireExponent3_5.PrimT.ReadEq (readTapeBit_write)

set_option autoImplicit false

instance : Fintype Move where
  elems := {Move.left, Move.stay, Move.right}
  complete := by intro x; cases x <;> simp

/-! ## The block code -/

/-- Thermometer code: bit `j` of the symbol `s` is `j < s`. -/
def code {x : ℕ} (s : Symbol x) (j : ℕ) : Bool := decide (j < s.val)

@[simp] theorem code_blank {x : ℕ} (j : ℕ) : code (Symbol.blank : Symbol x) j = false := by
  simp [code, Symbol.blank]

theorem code_injective {x : ℕ} :
    Function.Injective (fun (s : Symbol x) (j : Fin (x + 4)) => code s j.val) := by
  intro s s' h
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := congrFun h ⟨s.val, by omega⟩
    simp [code] at this
    omega
  · have := congrFun h ⟨s'.val, by omega⟩
    simp [code] at this
    omega

/-- Decoding a block (the code is injective; non-codes decode arbitrarily). -/
noncomputable def decode {x : ℕ} (bits : Fin (x + 4) → Bool) : Symbol x :=
  Function.invFun (fun (s : Symbol x) (j : Fin (x + 4)) => code s j.val) bits

theorem decode_code {x : ℕ} (s : Symbol x) : decode (fun j : Fin (x + 4) => code s j.val) = s :=
  Function.leftInverse_invFun code_injective s

/-- Target tape `L` holds source tape `T`: block `p` of `L` is the code of `T p`. -/
def Holds {x : ℕ} (T : ℕ → Symbol x) (L : List Bool) : Prop :=
  ∀ p j, j < x + 4 → readTapeBit L ((x + 4) * p + j) = code (T p) j

/-- A position lies in block `h` exactly when its block index is `h`. -/
theorem block_iff {w p h j : ℕ} (hj : j < w) : (w * h ≤ w * p + j ∧ w * p + j < w * h + w) ↔ p = h := by
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : w * (p + 1) ≤ w * h := Nat.mul_le_mul_left w hlt
      rw [Nat.mul_succ] at this
      omega
    · have : w * (h + 1) ≤ w * p := Nat.mul_le_mul_left w hlt
      rw [Nat.mul_succ] at this
      omega
  · rintro rfl; omega

/-! ## Head moves -/

/-- The release's head move of a source move. -/
def toHead : Move → HeadMove
  | .left => .left
  | .stay => .stay
  | .right => .right

theorem iterate_toHead (m : Move) (w h : ℕ) :
    ((toHead m).apply)^[w] (w * h) = w * m.apply h := by
  cases m with
  | left =>
    have hit : ∀ n x, (HeadMove.left.apply)^[n] x = x - n := by
      intro n; induction n with
      | zero => intro x; rfl
      | succ n ih => intro x; rw [Function.iterate_succ_apply', ih]; simp [HeadMove.apply]; omega
    simp only [toHead, Move.apply]
    rw [hit, Nat.mul_sub_one]
  | stay =>
    simp only [toHead, Move.apply]
    exact Function.iterate_fixed rfl w
  | right =>
    have hit : ∀ n x, (HeadMove.right.apply)^[n] x = x + n := by
      intro n; induction n with
      | zero => intro x; rfl
      | succ n ih => intro x; rw [Function.iterate_succ_apply', ih]; simp [HeadMove.apply]; omega
    simp only [toHead, Move.apply]
    rw [hit, Nat.mul_succ]

/-! ## The simulator -/

/-- Control phases: reading bit `j` of the current blocks into `buf`; writing bit `j` of the new blocks; the head
moves `r = 1, …, w-1` after the first one; halted. -/
inductive Phase (M : MultitapeTM) where
  | halt : Phase M
  | read (q : Fin M.states) (j : Fin (M.extraSymbols + 4))
      (buf : Fin M.tapes → Fin (M.extraSymbols + 4) → Bool) : Phase M
  | write (q : Fin M.states) (ws : Fin M.tapes → Symbol M.extraSymbols) (d : Fin M.tapes → Move)
      (j : Fin (M.extraSymbols + 4)) : Phase M
  | move (q : Fin M.states) (d : Fin M.tapes → Move) (r : Fin (M.extraSymbols + 4)) : Phase M
deriving Fintype

variable (M : MultitapeTM)

/-- The phases, numbered. -/
noncomputable def enc : Phase M ≃ Fin (Fintype.card (Phase M)) := by
  classical exact Fintype.equivFin (Phase M)

/-- The phase starting the simulation of a step in state `q`. -/
def readStart (q : Fin M.states) : Phase M := .read q ⟨0, by omega⟩ (fun _ _ => false)

/-- One target transition of a phase on the scanned bits. -/
noncomputable def phaseRule : Phase M → (Fin M.tapes → Bool) →
    Option (Phase M × (Fin M.tapes → Option Bool) × (Fin M.tapes → HeadMove))
  | .halt, _ => none
  | .read q j buf, sc =>
    if h : j.val + 1 < M.extraSymbols + 4 then
      some (.read q ⟨j.val + 1, h⟩ (fun i => Function.update (buf i) j (sc i)), fun _ => none, fun _ => .right)
    else
      match M.transition q (fun i => decode (Function.update (buf i) j (sc i))) with
      | none => some (.halt, fun _ => none, fun _ => .stay)
      | some a => some (.write a.1 a.2.1 a.2.2 j, fun _ => none, fun _ => .stay)
  | .write q ws d j, _ =>
    if h : 0 < j.val then
      some (.write q ws d ⟨j.val - 1, by omega⟩, fun i => some (code (ws i) j.val), fun _ => .left)
    else
      some (.move q d ⟨1, by omega⟩, fun i => some (code (ws i) 0), fun i => (toHead (d i)))
  | .move q d r, _ =>
    if h : r.val + 1 < M.extraSymbols + 4 then
      some (.move q d ⟨r.val + 1, h⟩, fun _ => none, fun i => (toHead (d i)))
    else
      some (readStart M q, fun _ => none, fun i => (toHead (d i)))

/-- Whether a phase is the halting phase. -/
def Phase.isHalt {M : MultitapeTM} : Phase M → Bool
  | .halt => true
  | _ => false

/-- **The simulator** (W03). -/
noncomputable def simulator : Machine M.tapes (Fintype.card (Phase M)) where
  descriptionBits := 0
  start := enc M (readStart M M.start)
  halted := fun s => ((enc M).symm s).isHalt
  rule := fun s sc => (phaseRule M ((enc M).symm s) sc).map fun a => ⟨enc M a.1, a.2.1, a.2.2⟩

/-- A target configuration in a given phase. -/
noncomputable def cfg (p : Phase M) (H : Fin M.tapes → ℕ) (T : Fin M.tapes → List Bool) :
    Configuration M.tapes (Fintype.card (Phase M)) :=
  ⟨enc M p, H, T⟩

theorem halted_cfg (p : Phase M) (H : Fin M.tapes → ℕ) (T : Fin M.tapes → List Bool) :
    (simulator M).halted (cfg M p H T).control = p.isHalt := by
  simp [simulator, cfg]

theorem step_cfg (p : Phase M) (H : Fin M.tapes → ℕ) (T : Fin M.tapes → List Bool)
    (p' : Phase M) (wr : Fin M.tapes → Option Bool) (mv : Fin M.tapes → HeadMove)
    (h : phaseRule M p (fun i => readTapeBit (T i) (H i)) = some (p', wr, mv)) :
    step (simulator M) (cfg M p H T) =
      some (cfg M p' (fun i => (mv i).apply (H i))
        (fun i => match wr i with
          | none => T i
          | some v => writeTapeBit (T i) (H i) v)) := by
  simp only [step, simulator, cfg, Equiv.symm_apply_apply]
  rw [show Configuration.scanned (⟨(enc M) p, H, T⟩ : Configuration M.tapes (Fintype.card (Phase M))) =
    fun i => readTapeBit (T i) (H i) from rfl, h]
  rfl

/-- One step, timed, of a non-halting phase. -/
theorem timed_cfg (p : Phase M) (hp : p.isHalt = false) (H : Fin M.tapes → ℕ) (T : Fin M.tapes → List Bool)
    (p' : Phase M) (wr : Fin M.tapes → Option Bool) (mv : Fin M.tapes → HeadMove)
    (h : phaseRule M p (fun i => readTapeBit (T i) (H i)) = some (p', wr, mv)) :
    Timed (simulator M) 1 (cfg M p H T)
      (cfg M p' (fun i => (mv i).apply (H i))
        (fun i => match wr i with
          | none => T i
          | some v => writeTapeBit (T i) (H i) v)) :=
  Timed.single (by rw [halted_cfg]; exact hp) (step_cfg M p H T p' wr mv h)

/-! ## The read phase -/

variable {M}

/-- The buffer after reading bits `0, …, j-1` of the scanned blocks of `c`. -/
def bufAt (c : M.Configuration) (j : ℕ) : Fin M.tapes → Fin (M.extraSymbols + 4) → Bool :=
  fun i j' => if j'.val < j then code (c.scanned i) j'.val else false

theorem bufAt_zero (c : M.Configuration) : bufAt c 0 = fun _ _ => false := by
  funext i j'; simp [bufAt]

theorem bufAt_succ (c : M.Configuration) (j : ℕ) (hj : j < M.extraSymbols + 4) (i : Fin M.tapes) :
    Function.update (bufAt c j i) ⟨j, hj⟩ (code (c.scanned i) j) = bufAt c (j + 1) i := by
  funext j'
  by_cases hjj : j' = ⟨j, hj⟩
  · subst hjj; simp [bufAt]
  · rw [Function.update_of_ne hjj]
    have hv : j'.val ≠ j := fun e => hjj (Fin.ext e)
    simp only [bufAt]
    by_cases hlt : j'.val < j
    · simp [hlt, show j'.val < j + 1 by omega]
    · simp [hlt, show ¬ j'.val < j + 1 by omega]

theorem bufAt_full (c : M.Configuration) (i : Fin M.tapes) :
    bufAt c (M.extraSymbols + 4) i = fun j' => code (c.scanned i) j'.val := by
  funext j'; simp [bufAt, j'.isLt]

/-- The target heads at the start of a simulated step. -/
def blockHeads (c : M.Configuration) : Fin M.tapes → ℕ := fun i => (M.extraSymbols + 4) * c.heads i

theorem scanned_read (c : M.Configuration) (T : Fin M.tapes → List Bool) (hT : ∀ i, Holds (c.contents i) (T i))
    (j : ℕ) (hj : j < M.extraSymbols + 4) (i : Fin M.tapes) :
    readTapeBit (T i) (blockHeads c i + j) = code (c.scanned i) j :=
  hT i (c.heads i) j hj

/-- Reading bits `0, …, j-1` takes `j` steps. -/
theorem read_run (c : M.Configuration) (T : Fin M.tapes → List Bool) (hT : ∀ i, Holds (c.contents i) (T i)) :
    ∀ j (hj : j < M.extraSymbols + 4),
      Timed (simulator M) j (cfg M (readStart M c.state) (blockHeads c) T)
        (cfg M (.read c.state ⟨j, hj⟩ (bufAt c j)) (fun i => blockHeads c i + j) T) := by
  intro j
  induction j with
  | zero =>
    intro hj
    have : (cfg M (readStart M c.state) (blockHeads c) T) =
        cfg M (.read c.state ⟨0, hj⟩ (bufAt c 0)) (fun i => blockHeads c i + 0) T := by
      simp [readStart, bufAt_zero]
    rw [this]; exact Timed.refl _ _
  | succ j ih =>
    intro hj
    have hj' : j < M.extraSymbols + 4 := by omega
    refine Timed.trans (ih hj') ?_
    have hrule : phaseRule M (.read c.state ⟨j, hj'⟩ (bufAt c j))
        (fun i => readTapeBit (T i) (blockHeads c i + j)) =
        some (.read c.state ⟨j + 1, hj⟩ (bufAt c (j + 1)), fun _ => none, fun _ => .right) := by
      simp only [phaseRule, dif_pos hj]
      congr 3
      funext i
      rw [scanned_read c T hT j hj' i]
      exact bufAt_succ c j hj' i
    have := timed_cfg M _ rfl _ _ _ _ _ hrule
    simpa [HeadMove.apply, Nat.add_assoc] using this

/-! ## The last read step -/

theorem last_rule (c : M.Configuration) (T : Fin M.tapes → List Bool) (hT : ∀ i, Holds (c.contents i) (T i)) :
    phaseRule M (.read c.state ⟨M.extraSymbols + 3, by omega⟩ (bufAt c (M.extraSymbols + 3)))
        (fun i => readTapeBit (T i) (blockHeads c i + (M.extraSymbols + 3))) =
      match M.transition c.state c.scanned with
      | none => some (.halt, fun _ => none, fun _ => .stay)
      | some a => some (.write a.1 a.2.1 a.2.2 ⟨M.extraSymbols + 3, by omega⟩, fun _ => none, fun _ => .stay) := by
  have hdec : (fun i => decode (Function.update (bufAt c (M.extraSymbols + 3) i)
      ⟨M.extraSymbols + 3, by omega⟩ (readTapeBit (T i) (blockHeads c i + (M.extraSymbols + 3))))) =
      c.scanned := by
    funext i
    rw [scanned_read c T hT _ (by omega) i, bufAt_succ c _ (by omega) i, bufAt_full, decode_code]
  simp only [phaseRule, dif_neg (show ¬ (M.extraSymbols + 3 + 1 < M.extraSymbols + 4) by omega)]
  rw [hdec]

/-! ## Halting -/

/-- A halting source configuration: `w` target steps to the halting phase, tapes unchanged. -/
theorem halt_run (c : M.Configuration) (hs : M.step c = none) (T : Fin M.tapes → List Bool)
    (hT : ∀ i, Holds (c.contents i) (T i)) :
    Timed (simulator M) (M.extraSymbols + 4) (cfg M (readStart M c.state) (blockHeads c) T)
      (cfg M .halt (fun i => blockHeads c i + (M.extraSymbols + 3)) T) := by
  have htr : M.transition c.state c.scanned = none := by
    simpa [MultitapeTM.step] using hs
  have hlast := last_rule c T hT
  rw [htr] at hlast
  have h1 := timed_cfg M _ rfl _ _ _ _ _ hlast
  have h0 := read_run c T hT (M.extraSymbols + 3) (by omega)
  have := Timed.trans h0 h1
  simpa [HeadMove.apply] using this

/-! ## The write phase -/

/-- The tape after writing the top `n` bits of the code of `s` into the block starting at `base`, top bit first. -/
def writeTop (w : ℕ) (L : List Bool) (base : ℕ) {x : ℕ} (s : Symbol x) : ℕ → List Bool
  | 0 => L
  | n + 1 => writeTapeBit (writeTop w L base s n) (base + (w - 1 - n)) (code s (w - 1 - n))

theorem writeTop_succ (w : ℕ) (L : List Bool) (base : ℕ) {x : ℕ} (s : Symbol x) (n : ℕ) :
    writeTop w L base s (n + 1) = writeTapeBit (writeTop w L base s n) (base + (w - 1 - n)) (code s (w - 1 - n)) :=
  rfl

theorem read_writeTop (w : ℕ) (L : List Bool) (base : ℕ) {x : ℕ} (s : Symbol x) :
    ∀ n, n ≤ w → ∀ pos, readTapeBit (writeTop w L base s n) pos =
      if base + (w - n) ≤ pos ∧ pos < base + w then code s (pos - base) else readTapeBit L pos := by
  intro n
  induction n with
  | zero => intro _ pos; simp [writeTop]
  | succ n ih =>
    intro hn pos
    simp only [writeTop, readTapeBit_write]
    rw [ih (by omega) pos]
    by_cases hp : pos = base + (w - 1 - n)
    · subst hp; simp [show base + (w - (n + 1)) ≤ base + (w - 1 - n) by omega,
        show base + (w - 1 - n) < base + w by omega, show base + (w - 1 - n) - base = w - 1 - n by omega]
    · simp only [hp, if_false]
      congr 1
      apply propext
      omega

/-- After the write phase, every target tape holds the updated source tape. -/
theorem holds_update {x : ℕ} (T : ℕ → Symbol x) (L : List Bool) (hL : Holds T L) (h : ℕ) (s : Symbol x) :
    Holds (Function.update T h s) (writeTop (x + 4) L ((x + 4) * h) s (x + 4)) := by
  intro p j hj
  rw [read_writeTop _ _ _ _ _ le_rfl]
  simp only [Nat.sub_self, Nat.add_zero]
  by_cases hph : p = h
  · subst hph
    rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left, Function.update_self]
  · have hnot : ¬ ((x + 4) * h ≤ (x + 4) * p + j ∧ (x + 4) * p + j < (x + 4) * h + (x + 4)) :=
      fun hb => hph ((block_iff hj).mp hb)
    rw [if_neg hnot, Function.update_of_ne hph]
    exact hL p j hj

/-! ## One step, with prescribed result -/

variable (M) in
theorem timed_cfg' (p : Phase M) (hp : p.isHalt = false) (H : Fin M.tapes → ℕ) (T : Fin M.tapes → List Bool)
    (p' : Phase M) (wr : Fin M.tapes → Option Bool) (mv : Fin M.tapes → HeadMove)
    (h : phaseRule M p (fun i => readTapeBit (T i) (H i)) = some (p', wr, mv))
    (H' : Fin M.tapes → ℕ) (T' : Fin M.tapes → List Bool) (hH : ∀ i, (mv i).apply (H i) = H' i)
    (hT : ∀ i, (match wr i with
          | none => T i
          | some v => writeTapeBit (T i) (H i) v) = T' i) :
    Timed (simulator M) 1 (cfg M p H T) (cfg M p' H' T') := by
  have := timed_cfg M p hp H T p' wr mv h
  rwa [show (fun i => (mv i).apply (H i)) = H' from funext hH, show (fun i => match wr i with
          | none => T i
          | some v => writeTapeBit (T i) (H i) v) = T' from funext hT] at this

/-! ## The write phase -/

/-- `n` steps of the write phase write the top `n` bits of every new block. -/
theorem write_run (q : Fin M.states) (ws : Fin M.tapes → Symbol M.extraSymbols) (d : Fin M.tapes → Move)
    (base : Fin M.tapes → ℕ) (T : Fin M.tapes → List Bool) :
    ∀ n (hn : n ≤ M.extraSymbols + 3),
      Timed (simulator M) n
        (cfg M (.write q ws d ⟨M.extraSymbols + 3, by omega⟩) (fun i => base i + (M.extraSymbols + 3)) T)
        (cfg M (.write q ws d ⟨M.extraSymbols + 3 - n, by omega⟩) (fun i => base i + (M.extraSymbols + 3 - n))
          (fun i => writeTop (M.extraSymbols + 4) (T i) (base i) (ws i) n)) := by
  intro n
  induction n with
  | zero => intro _; simpa [writeTop] using Timed.refl _ _
  | succ n ih =>
    intro hn
    refine Timed.trans (ih (by omega)) ?_
    have hrule : phaseRule M (.write q ws d ⟨M.extraSymbols + 3 - n, by omega⟩)
        (fun i => readTapeBit (writeTop (M.extraSymbols + 4) (T i) (base i) (ws i) n)
          (base i + (M.extraSymbols + 3 - n))) =
        some (.write q ws d ⟨M.extraSymbols + 3 - (n + 1), by omega⟩,
          fun i => some (code (ws i) (M.extraSymbols + 3 - n)), fun _ => .left) := by
      simp only [phaseRule, dif_pos (show 0 < M.extraSymbols + 3 - n by omega)]
      congr 3
    refine timed_cfg' M _ rfl _ _ _ _ _ hrule _ _ (fun i => ?_) (fun i => ?_)
    · simp only [HeadMove.apply]; omega
    · simp only [writeTop]
      rw [show M.extraSymbols + 4 - 1 - n = M.extraSymbols + 3 - n by omega]

/-- The last write step: bit `0`, and the first head move. -/
theorem write_last (q : Fin M.states) (ws : Fin M.tapes → Symbol M.extraSymbols) (d : Fin M.tapes → Move)
    (base : Fin M.tapes → ℕ) (T : Fin M.tapes → List Bool) :
    Timed (simulator M) 1
      (cfg M (.write q ws d ⟨M.extraSymbols + 3 - (M.extraSymbols + 3), by omega⟩)
        (fun i => base i + (M.extraSymbols + 3 - (M.extraSymbols + 3)))
        (fun i => writeTop (M.extraSymbols + 4) (T i) (base i) (ws i) (M.extraSymbols + 3)))
      (cfg M (.move q d ⟨1, by omega⟩) (fun i => ((toHead (d i)).apply)^[1] (base i))
        (fun i => writeTop (M.extraSymbols + 4) (T i) (base i) (ws i) (M.extraSymbols + 3 + 1))) := by
  have hrule : phaseRule M (.write q ws d ⟨M.extraSymbols + 3 - (M.extraSymbols + 3), by omega⟩)
      (fun i => readTapeBit (writeTop (M.extraSymbols + 4) (T i) (base i) (ws i) (M.extraSymbols + 3))
        (base i + (M.extraSymbols + 3 - (M.extraSymbols + 3)))) =
      some (.move q d ⟨1, by omega⟩, fun i => some (code (ws i) 0), fun i => toHead (d i)) := by
    simp only [phaseRule, Nat.sub_self, dif_neg (lt_irrefl 0)]
  refine timed_cfg' M _ rfl _ _ _ _ _ hrule _ _ (fun i => ?_) (fun i => ?_)
  · simp
  · rw [writeTop_succ _ _ _ _ (M.extraSymbols + 3), show M.extraSymbols + 4 - 1 - (M.extraSymbols + 3) = 0 by omega,
      Nat.sub_self]

/-! ## The move phase -/

/-- Moves `2, …, r` of the move phase. -/
theorem move_run (q : Fin M.states) (d : Fin M.tapes → Move) (base : Fin M.tapes → ℕ)
    (T : Fin M.tapes → List Bool) :
    ∀ n (hn : n + 1 < M.extraSymbols + 4),
      Timed (simulator M) n
        (cfg M (.move q d ⟨1, by omega⟩) (fun i => ((toHead (d i)).apply)^[1] (base i)) T)
        (cfg M (.move q d ⟨n + 1, hn⟩) (fun i => ((toHead (d i)).apply)^[n + 1] (base i)) T) := by
  intro n
  induction n with
  | zero => intro _; exact Timed.refl _ _
  | succ n ih =>
    intro hn
    refine Timed.trans (ih (by omega)) ?_
    have hrule : phaseRule M (.move q d ⟨n + 1, by omega⟩)
        (fun i => readTapeBit (T i) (((toHead (d i)).apply)^[n + 1] (base i))) =
        some (.move q d ⟨n + 1 + 1, hn⟩, fun _ => none, fun i => toHead (d i)) := by
      simp only [phaseRule, dif_pos hn]
    refine timed_cfg' M _ rfl _ _ _ _ _ hrule _ _ (fun i => ?_) (fun i => rfl)
    rw [Function.iterate_succ_apply' _ (n + 1)]

/-- The last move: back to reading, in the next source state. -/
theorem move_last (q : Fin M.states) (d : Fin M.tapes → Move) (base : Fin M.tapes → ℕ)
    (T : Fin M.tapes → List Bool) :
    Timed (simulator M) 1
      (cfg M (.move q d ⟨M.extraSymbols + 3, by omega⟩)
        (fun i => ((toHead (d i)).apply)^[M.extraSymbols + 3] (base i)) T)
      (cfg M (readStart M q) (fun i => ((toHead (d i)).apply)^[M.extraSymbols + 4] (base i)) T) := by
  have hrule : phaseRule M (.move q d ⟨M.extraSymbols + 3, by omega⟩)
      (fun i => readTapeBit (T i) (((toHead (d i)).apply)^[M.extraSymbols + 3] (base i))) =
      some (readStart M q, fun _ => none, fun i => toHead (d i)) := by
    simp only [phaseRule, dif_neg (show ¬ (M.extraSymbols + 3 + 1 < M.extraSymbols + 4) by omega)]
  refine timed_cfg' M _ rfl _ _ _ _ _ hrule _ _ (fun i => ?_) (fun i => rfl)
  rw [Function.iterate_succ_apply' _ (M.extraSymbols + 3)]

/-! ## One source step -/

/-- **One source step is `3w - 1` target steps** (`w = extraSymbols + 4`), and the tape relation is kept. -/
theorem step_run (c c' : M.Configuration) (hs : M.step c = some c') (T : Fin M.tapes → List Bool)
    (hT : ∀ i, Holds (c.contents i) (T i)) :
    ∃ T' : Fin M.tapes → List Bool, (∀ i, Holds (c'.contents i) (T' i)) ∧
      Timed (simulator M) (3 * (M.extraSymbols + 4) - 1)
        (cfg M (readStart M c.state) (blockHeads c) T) (cfg M (readStart M c'.state) (blockHeads c') T') := by
  cases hta : M.transition c.state c.scanned with
  | none => simp [MultitapeTM.step, hta] at hs
  | some a =>
  have hc' : c' = ⟨a.1, fun i => (a.2.2 i).apply (c.heads i),
      fun i => Function.update (c.contents i) (c.heads i) (a.2.1 i)⟩ := by
    simp only [MultitapeTM.step, hta, Option.map_some] at hs
    exact (Option.some.inj hs).symm
  subst hc'
  refine ⟨fun i => writeTop (M.extraSymbols + 4) (T i) (blockHeads c i) (a.2.1 i) (M.extraSymbols + 4),
    fun i => holds_update _ _ (hT i) _ _, ?_⟩
  -- read: w - 1 steps, then the last read step
  have h0 := read_run c T hT (M.extraSymbols + 3) (by omega)
  have hlast := last_rule c T hT
  rw [hta] at hlast
  have h1 := timed_cfg' M _ rfl _ _ _ _ _ hlast (fun i => blockHeads c i + (M.extraSymbols + 3)) T
    (fun i => rfl) (fun i => rfl)
  -- write: w - 1 steps, then the last write step
  have h2 := write_run a.1 a.2.1 a.2.2 (blockHeads c) T (M.extraSymbols + 3) le_rfl
  have h3 := write_last a.1 a.2.1 a.2.2 (blockHeads c) T
  -- move: w - 2 steps, then the last move
  have h4 := move_run a.1 a.2.2 (blockHeads c)
    (fun i => writeTop (M.extraSymbols + 4) (T i) (blockHeads c i) (a.2.1 i) (M.extraSymbols + 4))
    (M.extraSymbols + 2) (by omega)
  have h5 := move_last a.1 a.2.2 (blockHeads c)
    (fun i => writeTop (M.extraSymbols + 4) (T i) (blockHeads c i) (a.2.1 i) (M.extraSymbols + 4))
  have hheads : (fun i => ((toHead (a.2.2 i)).apply)^[M.extraSymbols + 4] (blockHeads c i)) =
      fun i => (M.extraSymbols + 4) * (a.2.2 i).apply (c.heads i) := by
    funext i
    exact iterate_toHead (a.2.2 i) (M.extraSymbols + 4) (c.heads i)
  rw [hheads] at h5
  have := ((((h0.trans h1).trans h2).trans h3).trans h4).trans h5
  rwa [show M.extraSymbols + 3 + 1 + (M.extraSymbols + 3) + 1 + (M.extraSymbols + 2) + 1 =
    3 * (M.extraSymbols + 4) - 1 by omega] at this

/-! ## Runs -/

/-- **W03, run form.** A source run of `t` steps from `c` that ends in a halting configuration `cf` is a target run
of exactly `(3w-1)·t + w` steps that ends in the halting phase, with every target tape holding the final source tape
and every head on the last cell of its block. -/
theorem simulator_run (t : ℕ) (c cf : M.Configuration) (hrun : M.run t c = some cf) (hf : M.step cf = none)
    (T : Fin M.tapes → List Bool) (hT : ∀ i, Holds (c.contents i) (T i)) :
    ∃ T' : Fin M.tapes → List Bool, (∀ i, Holds (cf.contents i) (T' i)) ∧
      ∃ r : ExecutionReceipt M.tapes (Fintype.card (Phase M)),
        runFrom (simulator M) ((3 * (M.extraSymbols + 4) - 1) * t + (M.extraSymbols + 4))
            (cfg M (readStart M c.state) (blockHeads c) T) = some r ∧
          r.final = cfg M .halt (fun i => blockHeads cf i + (M.extraSymbols + 3)) T' ∧
          r.steps = (3 * (M.extraSymbols + 4) - 1) * t + (M.extraSymbols + 4) := by
  have key : ∀ t (c : M.Configuration) (T : Fin M.tapes → List Bool), M.run t c = some cf →
      (∀ i, Holds (c.contents i) (T i)) →
      ∃ T' : Fin M.tapes → List Bool, (∀ i, Holds (cf.contents i) (T' i)) ∧
        Timed (simulator M) ((3 * (M.extraSymbols + 4) - 1) * t)
          (cfg M (readStart M c.state) (blockHeads c) T) (cfg M (readStart M cf.state) (blockHeads cf) T') := by
    intro t
    induction t with
    | zero =>
      intro c T h hT
      simp only [MultitapeTM.run, Option.some.injEq] at h
      subst h
      exact ⟨T, hT, by simpa using Timed.refl _ _⟩
    | succ t ih =>
      intro c T h hT
      simp only [MultitapeTM.run] at h
      cases hs : M.step c with
      | none => rw [hs] at h; simp at h
      | some c' =>
        rw [hs, Option.bind_some] at h
        obtain ⟨T1, hT1, h1⟩ := step_run c c' hs T hT
        obtain ⟨T2, hT2, h2⟩ := ih c' T1 h hT1
        refine ⟨T2, hT2, ?_⟩
        have := h1.trans h2
        rwa [show 3 * (M.extraSymbols + 4) - 1 + (3 * (M.extraSymbols + 4) - 1) * t =
          (3 * (M.extraSymbols + 4) - 1) * (t + 1) by ring] at this
  obtain ⟨T', hT', h1⟩ := key t c T hrun hT
  have h2 := halt_run cf hf T' hT'
  obtain ⟨r, hr, hfin, hsteps⟩ := (h1.trans h2).run (by rw [halted_cfg]; rfl)
  exact ⟨T', hT', r, hr, hfin, hsteps⟩

end NearCubicGates.Adapters.Williams
