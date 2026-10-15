import Proof.Packets.PacketsRoot
import Proof.MachineModel.BlockScrubEntry
import Proof.Circuits.DecompositionCountPosition

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

/-! ## The counter stamp -/

namespace NearCubicWires.PacketsGlue
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary.RecoveryExecution

theorem timedCongr {t s : ℕ} {p : Machine t s} {n n' : ℕ} {c c' d d' : Configuration t s} (h : Timed p n c d)
    (hn : n = n') (hc : c = c') (hd : d = d') : Timed p n' c' d' := by
  subst hn hc hd
  exact h

end NearCubicWires.PacketsGlue

namespace NearCubicWires.PacketsGlue.Stamp
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue.CeilSqrt (sentC read_sent write_sent read_rep)

/-- Tape 0: the unary source `1^m`; tapes `1..k+1`: the counters. -/
def machine (k : ℕ) : Machine (2 + k) 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q b =>
    if q.val = 0 then some ⟨1, fun i => if i.val = 0 then none else some false,
        fun i => if i.val = 0 then .stay else .right⟩
    else if q.val = 1 then (if b ⟨0, by omega⟩ then
        some ⟨1, fun i => if i.val = 0 then none else some true, fun _ => .right⟩
      else some ⟨2, fun _ => none, fun _ => .left⟩)
    else if q.val = 2 then (if b ⟨1, by omega⟩ then some ⟨2, fun _ => none, fun _ => .left⟩
      else some ⟨3, fun _ => none, fun _ => .stay⟩)
    else none

/-- All counters share one content and one head. -/
def cfg (k : ℕ) (q : Fin 4) (m uh : ℕ) (C : List Bool) (ch : ℕ) : Configuration (2 + k) 4 :=
  ⟨q, fun i => if i.val = 0 then uh else ch, fun i => if i.val = 0 then List.replicate m true else C⟩

section Steps
variable (k m uh : ℕ) (C : List Bool) (ch : ℕ)

theorem s0 : step (machine k) (cfg k 0 m uh C ch) = some (cfg k 1 m uh (writeTapeBit C ch false) (ch + 1)) := by
  simp only [step, machine, cfg]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, HeadMove.apply, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, HeadMove.apply, hi']
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, hi']

theorem s1t (h : readTapeBit (List.replicate m true) uh = true) :
    step (machine k) (cfg k 1 m uh C ch) = some (cfg k 1 m (uh + 1) (writeTapeBit C ch true) (ch + 1)) := by
  simp only [step, machine, cfg, Configuration.scanned]
  simp only [Fin.isValue, show ¬ ((1 : Fin 4).val = 0) from by decide, if_false, if_true, h]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, HeadMove.apply, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, HeadMove.apply, hi']
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, hi']

theorem s1f (h : readTapeBit (List.replicate m true) uh = false) :
    step (machine k) (cfg k 1 m uh C ch) = some (cfg k 2 m (uh - 1) C (ch - 1)) := by
  simp only [step, machine, cfg, Configuration.scanned]
  simp only [Fin.isValue, show ¬ ((1 : Fin 4).val = 0) from by decide, if_false, if_true, h]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, HeadMove.apply, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, HeadMove.apply, hi']
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, hi']

theorem s2t (h : readTapeBit C ch = true) :
    step (machine k) (cfg k 2 m uh C ch) = some (cfg k 2 m (uh - 1) C (ch - 1)) := by
  simp only [step, machine, cfg, Configuration.scanned]
  simp only [Fin.isValue, show ¬ ((2 : Fin 4).val = 0) from by decide, show ¬ ((2 : Fin 4).val = 1) from by decide,
    show ¬ ((1 : ℕ) = 0) from by decide, if_false, if_true, h]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, HeadMove.apply, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, HeadMove.apply, hi']
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, hi']

theorem s2f (h : readTapeBit C ch = false) :
    step (machine k) (cfg k 2 m uh C ch) = some (cfg k 3 m uh C ch) := by
  simp only [step, machine, cfg, Configuration.scanned]
  simp only [Fin.isValue, show ¬ ((2 : Fin 4).val = 0) from by decide, show ¬ ((2 : Fin 4).val = 1) from by decide,
    show ¬ ((1 : ℕ) = 0) from by decide, if_false, if_true, h]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, HeadMove.apply, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, HeadMove.apply, hi']
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, hi']

end Steps

theorem fill (k m : ℕ) : ∀ t j : ℕ, j + t = m →
    Timed (machine k) t (cfg k 1 m j (sentC j) (j + 1)) (cfg k 1 m m (sentC m) (m + 1)) := by
  intro t
  induction t with
  | zero => intro j hj; rw [show j = m by omega]; exact Timed.refl _ _
  | succ t ih =>
    intro j hj
    have h : readTapeBit (List.replicate m true) j = true := by rw [read_rep]; simp; omega
    have t1 := Timed.single (p := machine k) (by rfl) (s1t k m j (sentC j) (j + 1) h)
    rw [write_sent] at t1
    have t2 := ih (j + 1) (by omega)
    have tt := t1.trans t2
    rw [show 1 + t = t + 1 by omega] at tt
    exact tt

theorem rewind (k m : ℕ) : ∀ p : ℕ, p ≤ m →
    Timed (machine k) (p + 1) (cfg k 2 m (p - 1) (sentC m) p) (cfg k 3 m 0 (sentC m) 0) := by
  intro p
  induction p with
  | zero =>
    intro _
    have h : readTapeBit (sentC m) 0 = false := rfl
    simpa using Timed.single (p := machine k) (by rfl) (s2f k m (0 - 1) (sentC m) 0 h)
  | succ p ih =>
    intro hp
    have h : readTapeBit (sentC m) (p + 1) = true := by rw [read_sent]; simp; omega
    have t1 := Timed.single (p := machine k) (by rfl) (s2t k m (p + 1 - 1) (sentC m) (p + 1) h)
    rw [show p + 1 - 1 - 1 = p - 1 by omega, show p + 1 - 1 = p by omega] at t1
    have tt := t1.trans (ih (by omega))
    rw [show 1 + (p + 1) = p + 1 + 1 by omega] at tt
    exact tt

/-- **The stamp**: `k+1` counters `word m`, the source kept, all heads `0`, in `2m + 3` steps. -/
theorem run (k m : ℕ) :
    Step (machine k) (2 * m + 3) (fun _ => 0) (fun i => if i.val = 0 then List.replicate m true else [])
      (fun _ => 0)
      (fun i => if i.val = 0 then List.replicate m true else RepairSource.VerifierDecoding.CompareMachine.word m) := by
  have t0 := Timed.single (p := machine k) (by rfl) (s0 k m 0 [] 0)
  have e0 : writeTapeBit ([] : List Bool) 0 false = sentC 0 := rfl
  rw [e0] at t0
  have t1 := fill k m m 0 (by omega)
  have hf : readTapeBit (List.replicate m true) m = false := by rw [read_rep]; simp
  have t2 := Timed.single (p := machine k) (by rfl) (s1f k m m (sentC m) (m + 1) hf)
  have t3 := rewind k m m (le_refl _)
  rw [show m + 1 - 1 = m by omega] at t2
  have e := ((t0.trans t1).trans t2).trans t3
  have s := NatAt.Timed.toStep e rfl rfl
  have hh0 : (cfg k 0 m 0 [] 0).heads = fun _ => 0 := by funext i; simp [cfg]
  have hh3 : (cfg k 3 m 0 (sentC m) 0).heads = fun _ => 0 := by funext i; simp [cfg]
  rw [hh0, hh3, show 0 + 1 + m + 1 + (m + 1) = 2 * m + 3 by omega] at s
  exact s

end NearCubicWires.PacketsGlue.Stamp

/-! ## Write `c` trues -/

namespace NearCubicWires.PacketsGlue.WriteC
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch

def machine (c : ℕ) : Machine 1 (c + 1) where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == c
  rule := fun q _ => if h : q.val < c then some ⟨⟨q.val + 1, by omega⟩, fun _ => some true, fun _ => .right⟩
    else none

def cfg (c : ℕ) (j : ℕ) (hj : j ≤ c) (p : ℕ) (T : List Bool) : Configuration 1 (c + 1) :=
  ⟨⟨j, by omega⟩, ![p], ![T]⟩

theorem s (c j : ℕ) (hj : j < c) (p : ℕ) (T : List Bool) :
    step (machine c) (cfg c j (by omega) p T) = some (cfg c (j + 1) hj (p + 1) (writeTapeBit T p true)) := by
  simp only [step, machine, cfg, dif_pos hj]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i; simp [applyAction]

/-- The padded tail: one more true written at the end of `false :: out`. -/
theorem write_pad (out : List Bool) (K : ℕ) :
    writeTapeBit (false :: out ++ List.replicate K false) (out.length + 1) true =
      false :: (out ++ [true]) ++ List.replicate (K - 1) false := by
  have h := NatSum.write_tail (false :: out) K true
  simp only [List.length_cons] at h
  simpa using h

theorem writes (c : ℕ) : ∀ t j (hjt : j + t = c) (out : List Bool) (K : ℕ),
    Timed (machine c) t (cfg c j (by omega) (out.length + 1) (false :: out ++ List.replicate K false))
      (cfg c c le_rfl (out.length + 1 + t) (false :: (out ++ List.replicate t true) ++ List.replicate (K - t) false)) := by
  intro t
  induction t with
  | zero =>
    intro j hjt out K
    have hj : j = c := by omega
    subst hj
    simpa using Timed.refl (machine j) (cfg j j le_rfl (out.length + 1) (false :: out ++ List.replicate K false))
  | succ t ih =>
    intro j hjt out K
    have t1 := Timed.single (p := machine c) (by simp [machine, cfg]; omega)
      (s c j (by omega) (out.length + 1) (false :: out ++ List.replicate K false))
    rw [write_pad] at t1
    have t2 := ih (j + 1) (by omega) (out ++ [true]) (K - 1)
    have e0 : (out ++ [true]).length + 1 = out.length + 1 + 1 := by simp
    have e2 : out ++ [true] ++ List.replicate t true = out ++ List.replicate (t + 1) true := by
      simp [List.replicate_succ]
    have e3 : K - 1 - t = K - (t + 1) := by omega
    rw [e0, e2, e3] at t2
    exact timedCongr (t1.trans t2) (by omega) rfl
      (by rw [show out.length + 1 + 1 + t = out.length + 1 + (t + 1) by omega])

/-- **`c` trues appended** after `false :: out`, head following. -/
theorem run (c : ℕ) (out : List Bool) (K : ℕ) :
    Step (machine c) c ![out.length + 1] ![false :: out ++ List.replicate K false]
      ![out.length + 1 + c] ![false :: (out ++ List.replicate c true) ++ List.replicate (K - c) false] := by
  have t := writes c c 0 (by omega) out K
  exact NatAt.Timed.toStep t (by simp [machine, cfg]) rfl

end NearCubicWires.PacketsGlue.WriteC

/-! ## The nest of loops -/

namespace NearCubicWires.PacketsGlue.Nest
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform

/-- The newest counter's head, one cell right / left. -/
def advance (k : ℕ) : Fin (1 + k + 1) → HeadMove := fun i => if i.val = 1 + k then .right else .stay
def retreat (k : ℕ) : Fin (1 + k + 1) → HeadMove := fun i => if i.val = 1 + k then .left else .stay

/-- **Level `k`**: `k` nested loops around `WriteC c`. Tape 0 the log, tapes `1..k` the counters. -/
noncomputable def lvl (c : ℕ) : (k : ℕ) → Σ s, Machine (1 + k) s
  | 0 => ⟨c + 1, WriteC.machine c⟩
  | k + 1 => ⟨_, Composition.machine (DecompositionCountPosition.move (advance k))
      (Composition.machine (CloseoutRowsDegreeLoop.machine (lvl c k).2)
        (DecompositionCountPosition.move (retreat k)))⟩

/-- Heads: the log head after `false :: out`, counters at `0`. -/
def hd : (k : ℕ) → List Bool → Fin (1 + k) → ℕ
  | 0, out => ![out.length + 1]
  | k + 1, out => (Fin.addCases (m := 1 + k) (n := 1) (hd k out) (fun _ : Fin 1 => 0) : Fin (1 + k + 1) → ℕ)

/-- Tapes: the log `false :: out` padded to `P + 1`, the counters `word m`. -/
def tp (m P : ℕ) : (k : ℕ) → List Bool → Fin (1 + k) → List Bool
  | 0, out => ![false :: out ++ List.replicate (P - out.length) false]
  | k + 1, out => (Fin.addCases (m := 1 + k) (n := 1) (tp m P k out)
      (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word m) : Fin (1 + k + 1) → List Bool)

def cost (c m : ℕ) : ℕ → ℕ
  | 0 => c
  | k + 1 => 1 + 1 + ((m * (cost c m k + 3) + 3) + 1 + 1)

theorem flat_rep (n : ℕ) : ∀ m : ℕ,
    (List.range m).flatMap (fun _ => List.replicate n true) = List.replicate (m * n) true := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [← List.replicate_add]
    congr 1
    ring

theorem move_step {t : ℕ} (d : Fin t → HeadMove) (H : Fin t → ℕ) (A : Fin t → List Bool) :
    Step (DecompositionCountPosition.move d) 1 H A (fun i => (d i).apply (H i)) A := by
  obtain ⟨r, hr, hf, _⟩ := DecompositionCountPosition.move_run d H A
  exact Step.of_run hr (by rw [hf]) (by rw [hf])

/-- `Fin.addCases` of one extra entry, by value. -/
theorem ac1 {α : Type} {t : ℕ} (X : Fin t → α) (Y : Fin 1 → α) (i : Fin (t + 1)) :
    Fin.addCases X Y i = if h : i.val < t then X ⟨i.val, h⟩ else Y 0 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]
    have : ((Fin.castAdd 1 j) : Fin (t + 1)).val = j.val := rfl
    rw [dif_pos (by rw [this]; exact j.isLt)]
    rfl
  · rw [Fin.addCases_right]
    have : ((Fin.natAdd t j) : Fin (t + 1)).val = t + j.val := rfl
    rw [dif_neg (by rw [this]; omega), Fin.eq_zero j]

theorem adv_heads (k : ℕ) (out : List Bool) :
    (fun i => (advance k i).apply (hd (k + 1) out i)) =
      (Fin.addCases (m := 1 + k) (n := 1) (hd k out) (fun _ : Fin 1 => 1) : Fin (1 + k + 1) → ℕ) := by
  funext i
  have e : hd (k + 1) out i = Fin.addCases (m := 1 + k) (n := 1) (hd k out) (fun _ : Fin 1 => 0) i := rfl
  rw [e, ac1, ac1]
  unfold advance
  by_cases h : i.val < 1 + k
  · rw [dif_pos h, dif_pos h, if_neg (by omega)]; rfl
  · rw [dif_neg h, dif_neg h, if_pos (by omega)]; rfl

theorem ret_heads (k : ℕ) (out : List Bool) :
    (fun i => (retreat k i).apply (Fin.addCases (m := 1 + k) (n := 1) (hd k out) (fun _ : Fin 1 => 1) i)) =
      hd (k + 1) out := by
  funext i
  have e : hd (k + 1) out i = Fin.addCases (m := 1 + k) (n := 1) (hd k out) (fun _ : Fin 1 => 0) i := rfl
  rw [e, ac1, ac1]
  unfold retreat
  by_cases h : i.val < 1 + k
  · rw [dif_pos h, dif_pos h, if_neg (by omega)]; rfl
  · rw [dif_neg h, dif_neg h, if_pos (by omega)]; rfl

/-- **The nest**: level `k` appends `1^(c·m^k)` after `false :: out`, counters and their heads restored. -/
theorem run (c m P : ℕ) : ∀ (k : ℕ) (out : List Bool),
    Step (lvl c k).2 (cost c m k) (hd k out) (tp m P k out)
      (hd k (out ++ List.replicate (c * m ^ k) true)) (tp m P k (out ++ List.replicate (c * m ^ k) true)) := by
  intro k
  induction k with
  | zero =>
    intro out
    have h := WriteC.run c out (P - out.length)
    have e1 : out.length + 1 + c = (out ++ List.replicate (c * m ^ 0) true).length + 1 := by simp; omega
    have e2 : P - out.length - c = P - (out ++ List.replicate (c * m ^ 0) true).length := by simp; omega
    rw [e1, e2, show List.replicate c true = List.replicate (c * m ^ 0) true by simp] at h
    exact h
  | succ k ih =>
    intro out
    let cl : Cells (1 + k) (lvl c k).1 :=
      { body := (lvl c k).2
        cost := cost c m k
        bound := m
        source := fun _ o => ⟨(lvl c k).2.start, hd k o, tp m P k o⟩
        emit := fun _ => List.replicate (c * m ^ k) true
        entry := fun _ _ _ => rfl
        step := fun _ _ o => ih o }
    have s2 := Cells.loopStep cl out
    have s1 := move_step (advance k) (hd (k + 1) out) (tp m P (k + 1) out)
    rw [adv_heads] at s1
    have ef : out ++ (List.range m).flatMap (fun _ => List.replicate (c * m ^ k) true) =
        out ++ List.replicate (c * m ^ (k + 1)) true := by
      rw [flat_rep]; congr 2; ring
    have s2' : Step (CloseoutRowsDegreeLoop.machine (lvl c k).2) (m * (cost c m k + 3) + 3)
        (Fin.addCases (hd k out) (fun _ : Fin 1 => 1)) (tp m P (k + 1) out)
        (Fin.addCases (hd k (out ++ List.replicate (c * m ^ (k + 1)) true)) (fun _ : Fin 1 => 1))
        (tp m P (k + 1) (out ++ List.replicate (c * m ^ (k + 1)) true)) := by
      have := s2
      simp only [cl] at this
      rw [ef] at this
      exact this
    have s3 := move_step (retreat k) (Fin.addCases (hd k (out ++ List.replicate (c * m ^ (k + 1)) true))
      (fun _ : Fin 1 => 1)) (tp m P (k + 1) (out ++ List.replicate (c * m ^ (k + 1)) true))
    rw [ret_heads] at s3
    exact s1.seq (s2'.seq s3)

end NearCubicWires.PacketsGlue.Nest

/-! ## Drain the log into the driver -/

namespace NearCubicWires.PacketsGlue.Drain
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue.CeilSqrt (sentC read_sent read_rep write_rep)

def nw : Fin 2 → Option Bool := fun _ => none

def act (q : Fin 5) (w : Fin 2 → Option Bool) (m : Fin 2 → HeadMove) : Option (Action 2 5) :=
  some ⟨q, w, m⟩

/-- Tape 0 the log `false :: 1^R` (head at its end), tape 1 the driver. States: 0 step back, 1 rewind the log,
2 copy, 3 erase the log while rewinding both, 4 halt. -/
def machine : Machine 2 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q b =>
    if q.val = 0 then act 1 nw ![.left, .stay]
    else if q.val = 1 then (if b 0 then act 1 nw ![.left, .stay] else act 2 nw ![.right, .stay])
    else if q.val = 2 then (if b 0 then act 2 ![none, some true] ![.right, .right]
      else act 3 nw ![.left, .left])
    else if q.val = 3 then (if b 0 then act 3 ![some false, none] ![.left, .left]
      else act 4 nw ![.stay, .stay])
    else none

def cfg (q : Fin 5) (L : List Bool) (lh : ℕ) (D : List Bool) (dh : ℕ) : Configuration 2 5 :=
  ⟨q, ![lh, dh], ![L, D]⟩

section Steps
variable (L : List Bool) (lh : ℕ) (D : List Bool) (dh : ℕ)

theorem s0 : step machine (cfg 0 L lh D dh) = some (cfg 1 L (lh - 1) D dh) := by
  simp [step, machine, cfg, act]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s1t (h : readTapeBit L lh = true) : step machine (cfg 1 L lh D dh) = some (cfg 1 L (lh - 1) D dh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s1f (h : readTapeBit L lh = false) : step machine (cfg 1 L lh D dh) = some (cfg 2 L (lh + 1) D dh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s2t (h : readTapeBit L lh = true) :
    step machine (cfg 2 L lh D dh) = some (cfg 2 L (lh + 1) (writeTapeBit D dh true) (dh + 1)) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s2f (h : readTapeBit L lh = false) :
    step machine (cfg 2 L lh D dh) = some (cfg 3 L (lh - 1) D (dh - 1)) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s3t (h : readTapeBit L lh = true) :
    step machine (cfg 3 L lh D dh) = some (cfg 3 (writeTapeBit L lh false) (lh - 1) D (dh - 1)) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s3f (h : readTapeBit L lh = false) : step machine (cfg 3 L lh D dh) = some (cfg 4 L lh D dh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

end Steps

/-- The log during the erase: `p` ones left. -/
def E (R p : ℕ) : List Bool := false :: (List.replicate p true ++ List.replicate (R - p) false)

theorem E_top (R : ℕ) : E R R = sentC R := by simp [E, sentC]

theorem E_zero (R : ℕ) : E R 0 = List.replicate (R + 1) false := by simp [E, List.replicate_succ]

theorem read_E (R p i : ℕ) (_hp : p ≤ R) : readTapeBit (E R p) i = decide (1 ≤ i ∧ i ≤ p) := by
  cases i with
  | zero => rfl
  | succ i =>
    unfold E readTapeBit
    simp only [List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD]
    by_cases h : i < p
    · rw [List.getElem?_append_left (by simpa using h)]
      simp [h] <;> omega
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate]
      by_cases h2 : i - p < R - p
      · simp [h2] <;> omega
      · simp [h2] <;> omega

theorem write_E (R p : ℕ) (hp : p + 1 ≤ R) : writeTapeBit (E R (p + 1)) (p + 1) false = E R p := by
  unfold E
  have h := NatSum.write_mid (List.replicate p true) true (R - (p + 1)) false
  simp only [List.length_replicate] at h
  have e1 : List.replicate (p + 1) true ++ List.replicate (R - (p + 1)) false =
      List.replicate p true ++ true :: List.replicate (R - (p + 1)) false := by
    rw [List.replicate_succ', List.append_assoc]; rfl
  have e2 : List.replicate p true ++ false :: List.replicate (R - (p + 1)) false =
      List.replicate p true ++ List.replicate (R - p) false := by
    rw [show R - p = R - (p + 1) + 1 by omega, List.replicate_succ]
  simp only [writeTapeBit]
  rw [e1, h, e2]

theorem timed_congr {n n' : ℕ} {c c' d d' : Configuration 2 5} (h : Timed machine n c d)
    (hn : n = n') (hc : c = c') (hd : d = d') : Timed machine n' c' d' := by
  subst hn hc hd
  exact h

theorem rewind (R : ℕ) (D : List Bool) (dh : ℕ) : ∀ p : ℕ, p ≤ R →
    Timed machine (p + 1) (cfg 1 (sentC R) p D dh) (cfg 2 (sentC R) 1 D dh) := by
  intro p
  induction p with
  | zero =>
    intro _
    have h : readTapeBit (sentC R) 0 = false := rfl
    simpa using Timed.single (p := machine) (by rfl) (s1f (sentC R) 0 D dh h)
  | succ p ih =>
    intro hp
    have h : readTapeBit (sentC R) (p + 1) = true := by rw [read_sent]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s1t (sentC R) (p + 1) D dh h)
    rw [show p + 1 - 1 = p by omega] at t1
    exact timed_congr (t1.trans (ih (by omega))) (by omega) rfl rfl

theorem copy (R : ℕ) : ∀ t j : ℕ, j + t = R →
    Timed machine t (cfg 2 (sentC R) (j + 1) (List.replicate j true) j)
      (cfg 2 (sentC R) (R + 1) (List.replicate R true) R) := by
  intro t
  induction t with
  | zero => intro j hj; rw [show j = R by omega]; exact Timed.refl _ _
  | succ t ih =>
    intro j hj
    have h : readTapeBit (sentC R) (j + 1) = true := by rw [read_sent]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s2t (sentC R) (j + 1) (List.replicate j true) j h)
    rw [write_rep] at t1
    exact timed_congr (t1.trans (ih (j + 1) (by omega))) (by omega) rfl rfl

theorem erase (R : ℕ) (D : List Bool) : ∀ p : ℕ, p ≤ R →
    Timed machine (p + 1) (cfg 3 (E R p) p D (p - 1)) (cfg 4 (E R 0) 0 D 0) := by
  intro p
  induction p with
  | zero =>
    intro _
    have h : readTapeBit (E R 0) 0 = false := rfl
    simpa using Timed.single (p := machine) (by rfl) (s3f (E R 0) 0 D (0 - 1) h)
  | succ p ih =>
    intro hp
    have h : readTapeBit (E R (p + 1)) (p + 1) = true := by rw [read_E _ _ _ hp]; simp
    have t1 := Timed.single (p := machine) (by rfl) (s3t (E R (p + 1)) (p + 1) D (p + 1 - 1) h)
    rw [write_E R p hp, show p + 1 - 1 = p by omega] at t1
    rw [show p + 1 - 1 = p by omega]
    exact timed_congr (t1.trans (ih (by omega))) (by omega) rfl rfl

/-- **The drain**: log `false :: 1^R` (head `R+1`) and an empty driver ↦ log `0^(R+1)`, driver `1^R`, heads `0`. -/
theorem run (R : ℕ) :
    Step machine (3 * R + 4) ![R + 1, 0] ![sentC R, []] ![0, 0]
      ![List.replicate (R + 1) false, List.replicate R true] := by
  have t0 := Timed.single (p := machine) (by rfl) (s0 (sentC R) (R + 1) [] 0)
  rw [show R + 1 - 1 = R by omega] at t0
  have t1 := rewind R [] 0 R (le_refl _)
  have t2 := copy R R 0 (by omega)
  have hf : readTapeBit (sentC R) (R + 1) = false := by rw [read_sent]; simp
  have t3 := Timed.single (p := machine) (by rfl) (s2f (sentC R) (R + 1) (List.replicate R true) R hf)
  rw [show R + 1 - 1 = R by omega] at t3
  have t4 := erase R (List.replicate R true) R (le_refl _)
  rw [E_top] at t4
  have e := (((t0.trans t1).trans (timed_congr t2 rfl (by simp [cfg]) rfl)).trans t3).trans t4
  rw [E_zero] at e
  have s := NatAt.Timed.toStep e rfl rfl
  rw [show 1 + (R + 1) + R + 1 + (R + 1) = 3 * R + 4 by omega] at s
  exact s

end NearCubicWires.PacketsGlue.Drain

