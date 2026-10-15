import Proof.MachineModel.BlockLoop
import Proof.MachineModel.ClosureLocalSupport
import Proof.CaseAnalysis.WitnessSelectedErase

namespace NearCubicWires.BlockPlatform
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution
open RepairOrdinary.RecoveryRootRound NearCubicWires.ExtDecompositionBatch
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable {t : ℕ}

/-! ## 1. Existential stage to `Block`

A stage author proves only the ports a consumer reads (inside `P`) and the cost;
the exit bank itself is chosen, so nothing downstream can depend on it except
through `P`. -/

/-- A `Block` from an existential stage: machine, cost and entry bank are the
given ones; the exit bank is `Classical.choose`n and satisfies `P`. -/
def Block.ofExists {s n : ℕ} {M : Machine t s} {H : Fin t → ℕ} {A : Fin t → List Bool}
    {P : (Fin t → ℕ) → (Fin t → List Bool) → Prop}
    (h : ∃ H' A', Step M n H A H' A' ∧ P H' A') : Block t where
  states := s
  machine := M
  cost := n
  entryH := H
  entryA := A
  exitH := Classical.choose h
  exitA := Classical.choose (Classical.choose_spec h)
  run := (Classical.choose_spec (Classical.choose_spec h)).1

section ofExists
variable {s n : ℕ} {M : Machine t s} {H : Fin t → ℕ} {A : Fin t → List Bool}
    {P : (Fin t → ℕ) → (Fin t → List Bool) → Prop}
    (h : ∃ H' A', Step M n H A H' A' ∧ P H' A')

theorem Block.ofExists_spec : P (Block.ofExists h).exitH (Block.ofExists h).exitA :=
  (Classical.choose_spec (Classical.choose_spec h)).2

@[simp] theorem Block.ofExists_cost : (Block.ofExists h).cost = n := rfl
@[simp] theorem Block.ofExists_entryH : (Block.ofExists h).entryH = H := rfl
@[simp] theorem Block.ofExists_entryA : (Block.ofExists h).entryA = A := rfl
theorem Block.ofExists_machine : (Block.ofExists h).machine = M := rfl
end ofExists

/-! ## 2. The scrubbed layout `t+1+1` -/
namespace Scrub

/-- Stage tape `i` inside the scrubbed layout. -/
def inner (i : Fin t) : Fin (t+1+1) := (i.castAdd 1).castAdd 1
/-- The one log, shared by the masked reset and the erase. -/
def logTape : Fin (t+1+1) := ((0 : Fin 1).natAdd t).castAdd 1
/-- The unary erase driver. -/
def driverTape : Fin (t+1+1) := (0 : Fin 1).natAdd (t+1)

/-- Heads of the scrubbed layout: the stage's, then `0`, `0`. -/
def heads (H : Fin t → ℕ) : Fin (t+1+1) → ℕ :=
  Fin.addCases (Fin.addCases H (fun _ : Fin 1 => 0)) (fun _ : Fin 1 => 0)
/-- Tapes of the scrubbed layout: the stage's, the blank log `L`, the driver `R`. -/
def bank (A : Fin t → List Bool) (R L : ℕ) : Fin (t+1+1) → List Bool :=
  Fin.addCases (Fin.addCases A (fun _ : Fin 1 => List.replicate L false))
    (fun _ : Fin 1 => List.replicate R true)
/-- `A` with the selected tapes replaced by exactly `List.replicate R false`. -/
def blank {u : ℕ} (S : Fin u → Bool) (A : Fin u → List Bool) (R : ℕ) : Fin u → List Bool :=
  fun i => if S i then List.replicate R false else A i
/-- `H` with the selected heads returned to `0` (what `Step.mask` exports). -/
def rewound (reset : Fin t → Bool) (H : Fin t → ℕ) : Fin t → ℕ :=
  fun i => if reset i then 0 else H i
/-- The scratch selector extended by `false` on the log and the driver. -/
def wide (S : Fin t → Bool) : Fin (t+1+1) → Bool :=
  Fin.addCases (Fin.addCases S (fun _ : Fin 1 => false)) (fun _ : Fin 1 => false)

@[simp] theorem heads_inner (H : Fin t → ℕ) (i : Fin t) : heads H (inner i) = H i := by
  simp [heads, inner]
@[simp] theorem heads_log (H : Fin t → ℕ) : heads H logTape = 0 := by
  simp [heads, logTape]
@[simp] theorem heads_driver (H : Fin t → ℕ) : heads H driverTape = 0 := by
  simp [heads, driverTape]
@[simp] theorem bank_inner (A : Fin t → List Bool) (R L : ℕ) (i : Fin t) :
    bank A R L (inner i) = A i := by
  simp [bank, inner]
@[simp] theorem bank_log (A : Fin t → List Bool) (R L : ℕ) :
    bank A R L logTape = List.replicate L false := by
  simp [bank, logTape]
@[simp] theorem bank_driver (A : Fin t → List Bool) (R L : ℕ) :
    bank A R L driverTape = List.replicate R true := by
  simp [bank, driverTape]
@[simp] theorem wide_inner (S : Fin t → Bool) (i : Fin t) : wide S (inner i) = S i := by
  simp [wide, inner]
@[simp] theorem wide_log (S : Fin t → Bool) : wide S logTape = false := by
  simp [wide, logTape]
@[simp] theorem wide_driver (S : Fin t → Bool) : wide S driverTape = false := by
  simp [wide, driverTape]

theorem inner_val (i : Fin t) : (inner i).val = i.val := rfl
theorem log_val : (logTape : Fin (t+1+1)).val = t := rfl
theorem driver_val : (driverTape : Fin (t+1+1)).val = t+1 := rfl

theorem inner_ne_log (i : Fin t) : inner i ≠ logTape := by
  intro h; have := congrArg Fin.val h; rw [inner_val, log_val] at this; omega
theorem inner_ne_driver (i : Fin t) : inner i ≠ driverTape := by
  intro h; have := congrArg Fin.val h; rw [inner_val, driver_val] at this; omega
theorem driver_ne_log : (driverTape : Fin (t+1+1)) ≠ logTape := by
  intro h; have := congrArg Fin.val h; rw [driver_val, log_val] at this; omega

/-- Every tape of the scrubbed layout is a stage tape, the log, or the driver. -/
theorem cover {motive : Fin (t+1+1) → Prop} (hi : ∀ i, motive (inner i))
    (hl : motive logTape) (hd : motive driverTape) (j : Fin (t+1+1)) : motive j := by
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · refine Fin.addCases (fun i => ?_) (fun k => ?_) k
    · exact hi i
    · rw [Fin.eq_zero k]; exact hl
  · rw [Fin.eq_zero k]; exact hd

/-! ### The in-layout erase, with a loop-invariant log

`SelectedErase.erase_run` wants the log EMPTY and leaves it at `R+1` blanks; padding
the log to `L ≥ R+1` (`Step.pad`, i.e. `ZeroPadding.run_config`) makes the log enter
and leave as the same `List.replicate L false`. The driver is untouched. Heads are
kept, so the only head demand is `0` on the erased tapes, the driver and the log. -/
theorem erase_step {u : ℕ} (mask : Fin u → Bool) (driver log : Fin u)
    (hd : mask driver = false) (hl : mask log = false) (hne : driver ≠ log)
    (R L : ℕ) (hL : R + 1 ≤ L) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hh : ∀ i, mask i = true ∨ i = driver ∨ i = log → H i = 0)
    (hb : ∀ i, mask i = true → (A i).length ≤ R)
    (hdrv : A driver = List.replicate R true) (hlog : A log = List.replicate L false) :
    Step (CloseoutWitness.SelectedErase.machine mask driver log) (2*R+4) H A H (blank mask A R) := by
  let base : Fin u → List Bool := fun i => if i = log then [] else A i
  let cap : Fin u → ℕ := fun i => if i = log then L else 0
  have hbase : ∀ i, mask i = true → (base i).length ≤ R := by
    intro i hi
    have hil : i ≠ log := by
      rintro rfl
      rw [hl] at hi
      cases hi
    simp only [base, if_neg hil]
    exact hb i hi
  have hbd : base driver = List.replicate R true := by
    simp only [base, if_neg hne]
    exact hdrv
  have hbl : base log = [] := by simp [base]
  obtain ⟨r, hr, hs, hrh, hrt⟩ :=
    CloseoutWitness.SelectedErase.erase_run mask driver log hd hl hne R H base hh hbase hbd hbl
  have e : Step (CloseoutWitness.SelectedErase.machine mask driver log) (2*R+4) H base H
      (CloseoutWitness.SelectedErase.output mask log R base) := ⟨r, hr, hrh, hrt, hs⟩
  refine ((e.pad cap).congr_in rfl ?_).congr rfl ?_
  · funext i
    by_cases hi : i = log
    · subst hi
      simp [cap, base, hlog, ZeroPadding.pad]
    · simp [cap, base, hi]
  · funext i
    by_cases hi : i = log
    · subst hi
      have hpad : ZeroPadding.pad L (List.replicate (R+1) false) = List.replicate L false := by
        simp only [ZeroPadding.pad, List.length_replicate, List.replicate_append_replicate]
        congr 1
        omega
      simpa [cap, CloseoutWitness.SelectedErase.output, blank, hl, hlog] using hpad
    · by_cases hm : mask i = true
      · simp [cap, CloseoutWitness.SelectedErase.output, blank, hm, hi]
      · simp [cap, CloseoutWitness.SelectedErase.output, blank, hm, hi, base]

/-! ## 3. The scrub -/

/-- The scrubbed body: masked stage, one fresh driver tape, in-layout erase of `S`.
It depends on the stage's MACHINE and the two selectors only, never on `R`, `L` or
any bank, so a loop body built from it is one fixed machine. -/
def machine {s : ℕ} (M : Machine t s) (reset S : Fin t → Bool) : Machine (t+1+1) (s+2+4) :=
  Composition.machine (TapeEmbedding.machine 1 (MaskedReset.machine M reset))
    (CloseoutWitness.SelectedErase.machine (wide S) driverTape logTape)

/-- **The scrub.** For ANY stage `Step M n H A H' A'`: after the scrub, the scratch
set `S` holds exactly `List.replicate R false` with head `0`; every other tape holds
the stage's exit `A'` and its head the stage's head (or `0` where `reset`); the log
and driver are exactly as at entry. The stage's scratch exit `A' i` (`S i`) is used
only through `LocalSupport.step_fits`, i.e. the cost bound `n + 1 ≤ R`. -/
theorem step {s n : ℕ} {M : Machine t s} {H H' : Fin t → ℕ} {A A' : Fin t → List Bool}
    (h : Step M n H A H' A') (reset S : Fin t → Bool) (R L : ℕ)
    (hstart : ∀ i, reset i = true → H i = 0) (hSr : ∀ i, S i = true → reset i = true)
    (hA : ∀ i, S i = true → (A i).length ≤ R) (hR : n + 1 ≤ R) (hL : R + 1 ≤ L) :
    Step (machine M reset S) (2*n+2+1+(2*R+4)) (heads H) (bank A R L)
      (heads (rewound reset H')) (bank (blank S A' R) R L) := by
  have he : Step (TapeEmbedding.machine 1 (MaskedReset.machine M reset)) (2*n+2)
      (heads H) (bank A R L) (heads (rewound reset H')) (bank A' R L) :=
    (h.mask reset hstart (show n ≤ L by omega)).embed
      (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate R true)
  have hfit : ∀ i, S i = true → (A' i).length ≤ R := fun i hi =>
    P1Closure.LocalSupport.step_fits h i R (hA i hi) (by rw [hstart i (hSr i hi)]; omega)
  have hh : ∀ j, wide S j = true ∨ j = driverTape ∨ j = logTape →
      heads (rewound reset H') j = 0 := by
    intro j
    refine cover (motive := fun j => wide S j = true ∨ j = driverTape ∨ j = logTape →
      heads (rewound reset H') j = 0) (fun i hi => ?_) (fun _ => by simp) (fun _ => by simp) j
    rw [heads_inner]
    rcases hi with hi | hi | hi
    · rw [wide_inner] at hi
      simp [rewound, hSr i hi]
    · exact absurd hi (inner_ne_driver i)
    · exact absurd hi (inner_ne_log i)
  have hb : ∀ j, wide S j = true → (bank A' R L j).length ≤ R := by
    intro j
    refine cover (motive := fun j => wide S j = true → (bank A' R L j).length ≤ R)
      (fun i hi => ?_) (fun hl => by simp at hl) (fun hd => by simp at hd) j
    rw [wide_inner] at hi
    rw [bank_inner]
    exact hfit i hi
  have hr := erase_step (wide S) driverTape logTape (wide_driver S) (wide_log S) driver_ne_log
    R L hL (heads (rewound reset H')) (bank A' R L) hh hb (bank_driver A' R L) (bank_log A' R L)
  refine (Step.seq he hr).congr rfl ?_
  funext j
  refine cover (motive := fun j => blank (wide S) (bank A' R L) R j = bank (blank S A' R) R L j)
    (fun i => ?_) ?_ ?_ j
  · simp [blank]
  · simp [blank]
  · simp [blank]

/-- **The next-cell form** (what `Cells.step` consumes). Any target bank that agrees
with the stage's exit OFF `S`, is blank on `S`, and whose heads agree off `reset` and
are `0` on `reset`, is reached EXACTLY. `hblank` names only `R`; nothing names the
stage's scratch exit. -/
theorem step_into {s n : ℕ} {M : Machine t s} {H H' : Fin t → ℕ} {A A' : Fin t → List Bool}
    (h : Step M n H A H' A') (reset S : Fin t → Bool) (R L : ℕ)
    (hstart : ∀ i, reset i = true → H i = 0) (hSr : ∀ i, S i = true → reset i = true)
    (hA : ∀ i, S i = true → (A i).length ≤ R) (hR : n + 1 ≤ R) (hL : R + 1 ≤ L)
    {G : Fin t → ℕ} {B : Fin t → List Bool}
    (hkept : ∀ i, S i = false → A' i = B i)
    (hblank : ∀ i, S i = true → B i = List.replicate R false)
    (hheads : ∀ i, reset i = false → H' i = G i)
    (hzero : ∀ i, reset i = true → G i = 0) :
    Step (machine M reset S) (2*n+2+1+(2*R+4)) (heads H) (bank A R L) (heads G) (bank B R L) := by
  have hG : rewound reset H' = G := by
    funext i
    cases hr : reset i
    · simp [rewound, hr, hheads i hr]
    · simp [rewound, hr, hzero i hr]
  have hB : blank S A' R = B := by
    funext i
    cases hs : S i
    · simp [blank, hs, hkept i hs]
    · simp [blank, hs, hblank i hs]
  have hs := step h reset S R L hstart hSr hA hR hL
  rw [hG, hB] at hs
  exact hs

/-- **The cleared-state entry form.** A stage proved from blank scratch of length
`≤ R` (e.g. `[]` or `zeros c`) runs, by `ZeroPadding.run_config` (`Step.pad`), from
the scrub's cleared state `blank S A R` — so the next iteration can start. Kept
ports (`S i = false`) are padded by `0`, i.e. unchanged. -/
theorem cleared_entry {s n : ℕ} {M : Machine t s} {H H' : Fin t → ℕ} {A A' : Fin t → List Bool}
    (h : Step M n H A H' A') (S : Fin t → Bool) (R : ℕ)
    (hS : ∀ i, S i = true → ∃ k, k ≤ R ∧ A i = List.replicate k false) :
    Step M n H (blank S A R) H' (fun i => ZeroPadding.pad (if S i then R else 0) (A' i)) := by
  refine (h.pad (fun i => if S i then R else 0)).congr_in rfl ?_
  funext i
  cases hi : S i
  · simp [blank, hi]
  · obtain ⟨k, hk, he⟩ := hS i hi
    simp only [blank, hi, if_true, he, ZeroPadding.pad, List.length_replicate,
      List.replicate_append_replicate]
    congr 1
    omega

@[simp] theorem cleared_kept (S : Fin t → Bool) (R : ℕ) (A' : Fin t → List Bool) (i : Fin t)
    (hi : S i = false) : ZeroPadding.pad (if S i then R else 0) (A' i) = A' i := by
  simp [hi]

end Scrub

/-! ## 4. `Block.scrub` -/

/-- **`Block.scrub`.** Two extra tapes (one shared log, one driver); cost
`2*b.cost+2 + 1 + (2*R+4)`; exit exactly `List.replicate R false` on `S`. -/
def Block.scrub (b : Block t) (reset S : Fin t → Bool) (R L : ℕ)
    (hstart : ∀ i, reset i = true → b.entryH i = 0) (hSr : ∀ i, S i = true → reset i = true)
    (hA : ∀ i, S i = true → (b.entryA i).length ≤ R) (hR : b.cost + 1 ≤ R) (hL : R + 1 ≤ L) :
    Block (t+1+1) :=
  ofStep (Scrub.step b.run reset S R L hstart hSr hA hR hL)

section scrub
variable (b : Block t) (reset S : Fin t → Bool) (R L : ℕ)
    (hstart : ∀ i, reset i = true → b.entryH i = 0) (hSr : ∀ i, S i = true → reset i = true)
    (hA : ∀ i, S i = true → (b.entryA i).length ≤ R) (hR : b.cost + 1 ≤ R) (hL : R + 1 ≤ L)

@[simp] theorem Block.scrub_cost :
    (b.scrub reset S R L hstart hSr hA hR hL).cost = 2*b.cost+2+1+(2*R+4) := rfl
@[simp] theorem Block.scrub_entryH :
    (b.scrub reset S R L hstart hSr hA hR hL).entryH = Scrub.heads b.entryH := rfl
@[simp] theorem Block.scrub_entryA :
    (b.scrub reset S R L hstart hSr hA hR hL).entryA = Scrub.bank b.entryA R L := rfl
@[simp] theorem Block.scrub_exitH :
    (b.scrub reset S R L hstart hSr hA hR hL).exitH = Scrub.heads (Scrub.rewound reset b.exitH) := rfl
@[simp] theorem Block.scrub_exitA :
    (b.scrub reset S R L hstart hSr hA hR hL).exitA = Scrub.bank (Scrub.blank S b.exitA R) R L := rfl
theorem Block.scrub_machine :
    (b.scrub reset S R L hstart hSr hA hR hL).machine = Scrub.machine b.machine reset S := rfl

theorem Block.scrub_scratch (i : Fin t) (hi : S i = true) :
    (b.scrub reset S R L hstart hSr hA hR hL).exitA (Scrub.inner i) = List.replicate R false := by
  simp [Scrub.blank, hi]
theorem Block.scrub_scratch_head (i : Fin t) (hi : S i = true) :
    (b.scrub reset S R L hstart hSr hA hR hL).exitH (Scrub.inner i) = 0 := by
  simp [Scrub.rewound, hSr i hi]
theorem Block.scrub_kept (i : Fin t) (hi : S i = false) :
    (b.scrub reset S R L hstart hSr hA hR hL).exitA (Scrub.inner i) = b.exitA i := by
  simp [Scrub.blank, hi]
theorem Block.scrub_log :
    (b.scrub reset S R L hstart hSr hA hR hL).exitA Scrub.logTape = List.replicate L false := by
  simp
theorem Block.scrub_driver :
    (b.scrub reset S R L hstart hSr hA hR hL).exitA Scrub.driverTape = List.replicate R true := by
  simp
end scrub

/-! ## 5. A loop of scrubbed bodies

`Cells.ofScrub` is the consumer-facing constructor: a uniform stage (one machine
`M`, one cost `n`) given only EXISTENTIALLY per cell, with its kept ports and kept
heads, becomes a `Cells` whose body is `Scrub.machine M reset S`. The cell source
carries the stage's bank inside `Scrub.bank · R L`; `hclear` says the scratch
entry is the cleared state (use `Scrub.cleared_entry` for a stage proved from
`[]`/`zeros`). Nothing names the stage's scratch exit. -/
def Cells.ofScrub {s n : ℕ} (M : Machine t s) (reset S : Fin t → Bool) (R L bound : ℕ)
    (H : ℕ → List Bool → Fin t → ℕ) (A : ℕ → List Bool → Fin t → List Bool)
    (emit : ℕ → List Bool)
    (hSr : ∀ i, S i = true → reset i = true) (hR : n + 1 ≤ R) (hL : R + 1 ≤ L)
    (hstart : ∀ j, j ≤ bound → ∀ out i, reset i = true → H j out i = 0)
    (hclear : ∀ j, j ≤ bound → ∀ out i, S i = true → A j out i = List.replicate R false)
    (stage : ∀ j, j < bound → ∀ out, ∃ H' A', Step M n (H j out) (A j out) H' A' ∧
      (∀ i, S i = false → A' i = A (j+1) (out ++ emit j) i) ∧
      (∀ i, reset i = false → H' i = H (j+1) (out ++ emit j) i)) :
    Cells (t+1+1) (s+2+4) where
  body := Scrub.machine M reset S
  cost := 2*n+2+1+(2*R+4)
  bound := bound
  source := fun j out =>
    ⟨(Scrub.machine M reset S).start, Scrub.heads (H j out), Scrub.bank (A j out) R L⟩
  emit := emit
  entry := fun _ _ _ => rfl
  step := by
    intro j _hj out
    obtain ⟨H', A', h, hk, hh⟩ := stage j _hj out
    exact Scrub.step_into h reset S R L (hstart j (by omega) out) hSr
      (fun i hi => by rw [hclear j (by omega) out i hi, List.length_replicate]) hR hL hk
      (hclear (j+1) (by omega) (out ++ emit j)) hh (hstart (j+1) (by omega) (out ++ emit j))

@[simp] theorem Cells.ofScrub_cost {s n : ℕ} (M : Machine t s) (reset S : Fin t → Bool)
    (R L bound : ℕ) (H : ℕ → List Bool → Fin t → ℕ) (A : ℕ → List Bool → Fin t → List Bool)
    (emit : ℕ → List Bool)
    (hSr : ∀ i, S i = true → reset i = true) (hR : n + 1 ≤ R) (hL : R + 1 ≤ L)
    (hstart : ∀ j, j ≤ bound → ∀ out i, reset i = true → H j out i = 0)
    (hclear : ∀ j, j ≤ bound → ∀ out i, S i = true → A j out i = List.replicate R false)
    (stage : ∀ j, j < bound → ∀ out, ∃ H' A', Step M n (H j out) (A j out) H' A' ∧
      (∀ i, S i = false → A' i = A (j+1) (out ++ emit j) i) ∧
      (∀ i, reset i = false → H' i = H (j+1) (out ++ emit j) i)) :
    (Cells.ofScrub M reset S R L bound H A emit hSr hR hL hstart hclear stage).cost =
      2*n+2+1+(2*R+4) := rfl

end
end NearCubicWires.BlockPlatform
