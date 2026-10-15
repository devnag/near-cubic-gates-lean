import Proof.MachineModel.BlockUnaryCalc

namespace NearCubicWires.BlockPlatform
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution
open RepairOrdinary.RecoveryRootRound NearCubicWires.ExtDecompositionBatch
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem dockH_existing {t u : ℕ} (slots : Fin t → Fin u) (ambient : Fin u → ℕ)
    (local' : Fin t → ℕ) (h : ∀ j, ambient (slots j) = local' j) :
    dockH slots ambient local' = ambient := by
  funext i
  cases hp : RecoveryFocus.pick slots i with
  | none => simp [dockH, hp]
  | some j =>
    have he := RecoveryFocus.slot_of_pick slots hp
    simp only [dockH, hp]
    rw [← he]
    exact (h j).symm

namespace Scrub
variable {t : ℕ}

/-- The calc workspace: the polynomial run's tapes plus one blank tape for the copier. -/
abbrev wk (D : ℕ) : ℕ := UnaryCalc.tapes D + 1

/-- The calc input: the parsed unary dimension on the run's input tape, all else blank. -/
def calcIn (D n : ℕ) : Fin (wk D) → List Bool :=
  Fin.addCases (DimensionPolynomial.input D n) (fun _ : Fin 1 => [])

def stageTape (D : ℕ) (i : Fin t) : Fin (t+wk D+1+1) := inner (Fin.castAdd (wk D) i)
def workTape (D : ℕ) (j : Fin (wk D)) : Fin (t+wk D+1+1) := inner (Fin.natAdd t j)
def blankWork (D : ℕ) : Fin (wk D) := Fin.natAdd (UnaryCalc.tapes D) 0

def powSlots (D : ℕ) : Fin (UnaryCalc.tapes D) → Fin (t+wk D+1+1) :=
  fun k => workTape D (Fin.castAdd 1 k)
def copySlots (D : ℕ) : Fin 4 → Fin (t+wk D+1+1) :=
  ![workTape D (Fin.castAdd 1 (UnaryCalc.outputTape D)), workTape D (blankWork D),
    driverTape, logTape]

/-- The stage scratch, extended by `false` on the workspace. -/
def entryScratch (D : ℕ) (S : Fin t → Bool) : Fin (t+wk D) → Bool :=
  Fin.addCases S (fun _ => false)

/-- The entry machine: one fixed machine per `(t, D, C, S)`, independent of `n`, `A`, `H`. -/
def entryMachine (t D C : ℕ) (S : Fin t → Bool) :=
  Composition.machine
    (Composition.machine
      (RecoveryFocus.machine (powSlots (t := t) D) (PCPSerializerCapacity.Power.machine D C))
      (RecoveryFocus.machine (copySlots (t := t) D) ClockUnarySum.machine))
    (CloseoutWitness.SelectedErase.machine (wide (entryScratch D S)) driverTape logTape)

/-- The entry's cost. -/
def entryCost (D C n : ℕ) : ℕ :=
  PCPSerializerCapacity.Power.budget D C n+1+(2*UnaryCalc.value D C n+6)+1+
    (2*UnaryCalc.value D C n+4)

theorem wk_eq (D : ℕ) : wk D = UnaryCalc.tapes D+1 := rfl
theorem stageTape_val (D : ℕ) (i : Fin t) : (stageTape (t := t) D i).val = i.val := rfl
theorem workTape_val (D : ℕ) (j : Fin (wk D)) : (workTape (t := t) D j).val = t+j.val := rfl

theorem powSlots_injective (D : ℕ) : Function.Injective (powSlots (t := t) D) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [powSlots, workTape_val, Fin.val_castAdd] at hv
  exact Fin.ext (by omega)

theorem outputTape_lt (D : ℕ) : (UnaryCalc.outputTape D).val < UnaryCalc.tapes D :=
  (UnaryCalc.outputTape D).isLt

theorem copySlots_val (D : ℕ) (k : Fin 4) : (copySlots (t := t) D k).val =
    ![t+(UnaryCalc.outputTape D).val, t+UnaryCalc.tapes D, t+wk D+1, t+wk D] k := by
  fin_cases k <;> rfl

theorem copySlots_injective (D : ℕ) : Function.Injective (copySlots (t := t) D) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [copySlots_val (t := t) D a, copySlots_val (t := t) D b] at hv
  have ho := outputTape_lt D
  have hw := wk_eq D
  fin_cases a <;> fin_cases b <;> simp at hv ⊢ <;> omega

/-- **The scrub entry.** From the stage bank `A` (scratch `S` of length `≤ R`, heads `0`
there), the calc input and NO driver or log, the entry reaches exactly the scrubbed source:
stage scratch `replicate R false`, stage kept tapes unchanged, the workspace at some `W`
(still holding the dimension), the log `replicate (R+2) false`, the driver `replicate R true`,
all heads as at entry. `R = C*(n+1)^D` is computed, never supplied. -/
theorem entry_step (t D C n : ℕ) (S : Fin t → Bool) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (hS : ∀ i, S i = true → H i = 0)
    (hA : ∀ i, S i = true → (A i).length ≤ UnaryCalc.value D C n) :
    ∃ W : Fin (wk D) → List Bool,
      W (Fin.castAdd 1 (UnaryCalc.inputTape D)) = List.replicate n true ∧
      Step (entryMachine t D C S) (entryCost D C n)
        (heads (Fin.addCases H (fun _ => 0))) (bank (Fin.addCases A (calcIn D n)) 0 0)
        (heads (Fin.addCases H (fun _ => 0)))
        (bank (Fin.addCases (blank S A (UnaryCalc.value D C n)) W)
          (UnaryCalc.value D C n) (UnaryCalc.value D C n+2)) := by
  set R := UnaryCalc.value D C n with hRdef
  set H0 : Fin (t+wk D+1+1) → ℕ := heads (Fin.addCases H (fun _ => 0)) with hH0
  set B0 : Fin (t+wk D+1+1) → List Bool := bank (Fin.addCases A (calcIn D n)) 0 0 with hB0
  have ho := outputTape_lt D
  -- values of the initial bank / heads
  have B0_stage : ∀ i, B0 (stageTape D i) = A i := by
    intro i; simp [hB0, stageTape]
  have B0_work : ∀ j, B0 (workTape D j) = calcIn D n j := by
    intro j; simp [hB0, workTape]
  have H0_stage : ∀ i, H0 (stageTape D i) = H i := by
    intro i; simp [hH0, stageTape]
  have H0_work : ∀ j, H0 (workTape D j) = 0 := by
    intro j; simp [hH0, workTape]
  -- phase 1: the polynomial run on the workspace (heads: exit 0 where ambient is 0)
  have hw := wk_eq D
  obtain ⟨out, hp, hin, hout⟩ := UnaryCalc.poly_step D C n
  have p1 := hp.focus (powSlots D) (powSlots_injective D) H0 B0
  rw [install_existing (powSlots D) B0 _ (fun k => by
      rw [show powSlots D k = workTape D (Fin.castAdd 1 k) from rfl, B0_work]
      simp [calcIn]),
    dockH_existing (powSlots D) H0 _ (fun k => H0_work _)] at p1
  set B1 := install (powSlots (t := t) D) B0 out with hB1
  have notPow_stage : ∀ i k, powSlots (t := t) D k ≠ stageTape D i := by
    intro i k h; have hv := congrArg Fin.val h
    rw [stageTape_val] at hv; simp [powSlots, workTape_val] at hv; omega
  have notPow_blank : ∀ k, powSlots (t := t) D k ≠ workTape D (blankWork D) := by
    intro k h; have hv := congrArg Fin.val h
    have hk := k.isLt
    simp [powSlots, workTape_val, blankWork] at hv; omega
  have notPow_driver : ∀ k, powSlots (t := t) D k ≠ driverTape := by
    intro k h; have hv := congrArg Fin.val h
    have hk := k.isLt
    rw [driver_val] at hv; simp [powSlots, workTape_val] at hv; omega
  have notPow_log : ∀ k, powSlots (t := t) D k ≠ logTape := by
    intro k h; have hv := congrArg Fin.val h
    have hk := k.isLt
    rw [log_val] at hv; simp [powSlots, workTape_val] at hv; omega
  -- phase 2: copy the value onto the driver; its rewind log is the scrub log
  have p2 := (UnaryCalc.copy_step R).focus (copySlots D) (copySlots_injective D) H0 B1
  have B1_out : B1 (copySlots (t := t) D 0) = List.replicate R true := by
    change install (powSlots (t := t) D) B0 out (powSlots D (UnaryCalc.outputTape D)) = _
    rw [install_slot _ (powSlots_injective D)]; exact hout
  have B1_blank : B1 (copySlots (t := t) D 1) = [] := by
    change install (powSlots (t := t) D) B0 out (workTape D (blankWork D)) = _
    rw [install_other _ _ _ _ (notPow_blank), B0_work]
    simp [calcIn, blankWork]
  have B1_driver : B1 (copySlots (t := t) D 2) = [] := by
    change install (powSlots (t := t) D) B0 out driverTape = _
    rw [install_other _ _ _ _ notPow_driver]
    simp [hB0]
  have B1_log : B1 (copySlots (t := t) D 3) = [] := by
    change install (powSlots (t := t) D) B0 out logTape = _
    rw [install_other _ _ _ _ notPow_log]
    simp [hB0]
  have H0_copy : ∀ k, H0 (copySlots (t := t) D k) = 0 := by
    intro k
    fin_cases k
    · exact H0_work _
    · exact H0_work _
    · simp [hH0, copySlots]
    · simp [hH0, copySlots]
  rw [install_existing (copySlots D) B1 _ (fun k => by
      fin_cases k
      · exact B1_out
      · exact B1_blank
      · exact B1_driver
      · exact B1_log),
    dockH_existing (copySlots D) H0 _ H0_copy] at p2
  set B2 := install (copySlots (t := t) D) B1
    ![List.replicate R true, [], List.replicate R true, List.replicate (R+2) false] with hB2
  have notCopy_stage : ∀ i k, copySlots (t := t) D k ≠ stageTape D i := by
    intro i k h; have hv := congrArg Fin.val h
    rw [copySlots_val, stageTape_val] at hv
    have := i.isLt
    fin_cases k <;> simp at hv <;> omega
  have B2_driver : B2 driverTape = List.replicate R true := by
    change install (copySlots (t := t) D) B1 _ (copySlots D 2) = _
    rw [install_slot _ (copySlots_injective D)]; rfl
  have B2_log : B2 logTape = List.replicate (R+2) false := by
    change install (copySlots (t := t) D) B1 _ (copySlots D 3) = _
    rw [install_slot _ (copySlots_injective D)]; rfl
  have B2_stage : ∀ i, B2 (stageTape D i) = A i := by
    intro i
    rw [hB2, install_other _ _ _ _ (fun k => notCopy_stage i k), hB1,
      install_other _ _ _ _ (fun k => notPow_stage i k), B0_stage]
  -- phase 3: clear the stage scratch to exactly `R` blanks
  have hh : ∀ i, wide (entryScratch D S) i = true ∨ i = driverTape ∨ i = logTape → H0 i = 0 := by
    intro x hx
    rcases hx with hx | hx | hx
    · revert hx
      refine cover (motive := fun x => wide (entryScratch D S) x = true → H0 x = 0)
        (fun i hi => ?_) (fun _ => by simp [hH0]) (fun _ => by simp [hH0]) x
      rw [wide_inner] at hi
      refine Fin.addCases (motive := fun i => entryScratch D S i = true →
        H0 (inner i) = 0) (fun i0 hi0 => ?_) (fun j hj => ?_) i hi
      · have hs : S i0 = true := by simpa [entryScratch] using hi0
        simpa [hH0] using hS i0 hs
      · simp [entryScratch] at hj
    · subst hx; simp [hH0]
    · subst hx; simp [hH0]
  have hb : ∀ x, wide (entryScratch D S) x = true → (B2 x).length ≤ R := by
    intro x
    refine cover (motive := fun x => wide (entryScratch D S) x = true → (B2 x).length ≤ R)
      (fun i hi => ?_) (fun hl => by simp at hl) (fun hd => by simp at hd) x
    rw [wide_inner] at hi
    refine Fin.addCases (motive := fun i => entryScratch D S i = true →
      (B2 (inner i)).length ≤ R) (fun i0 hi0 => ?_) (fun j hj => ?_) i hi
    · have hs : S i0 = true := by simpa [entryScratch] using hi0
      have := B2_stage i0
      change (B2 (stageTape D i0)).length ≤ R
      rw [this]; exact hA i0 hs
    · simp [entryScratch] at hj
  have p3 := erase_step (wide (entryScratch D S)) driverTape logTape (wide_driver _) (wide_log _)
    driver_ne_log R (R+2) (by omega) H0 B2 hh hb B2_driver B2_log
  have whole := Step.seq (Step.seq p1 p2) p3
  refine ⟨fun j => B2 (workTape D j), ?_, ?_⟩
  · change install (copySlots (t := t) D) B1 _ (workTape D (Fin.castAdd 1 (UnaryCalc.inputTape D))) = _
    have hne : ∀ k, copySlots (t := t) D k ≠ workTape D (Fin.castAdd 1 (UnaryCalc.inputTape D)) := by
      intro k h; have hv := congrArg Fin.val h
      rw [copySlots_val, workTape_val] at hv
      have hio := UnaryCalc.output_ne_input D
      have hio' : (UnaryCalc.outputTape D).val ≠ 0 := fun h0 => hio (Fin.ext h0)
      have hnz : 0 < UnaryCalc.tapes D := by simp [UnaryCalc.tapes, DimensionPolynomial.tapes]
      fin_cases k <;> simp [UnaryCalc.inputTape] at hv <;> omega
    rw [install_other _ _ _ _ hne]
    change install (powSlots (t := t) D) B0 out (powSlots D (UnaryCalc.inputTape D)) = _
    rw [install_slot _ (powSlots_injective D)]; exact hin
  · refine whole.congr rfl ?_
    funext x
    refine cover (motive := fun x => blank (wide (entryScratch D S)) B2 R x =
      bank (Fin.addCases (blank S A R) (fun j => B2 (workTape D j))) R (R+2) x)
      (fun i => ?_) ?_ ?_ x
    · refine Fin.addCases (fun i0 => ?_) (fun j => ?_) i
      · have := B2_stage i0
        change blank (wide (entryScratch D S)) B2 R (stageTape D i0) = _
        simp only [blank, stageTape, wide_inner, entryScratch, Fin.addCases_left, bank_inner]
        change (if S i0 = true then List.replicate R false else B2 (stageTape D i0)) = _
        rw [this]
      · simp [blank, entryScratch, workTape]
    · simp [blank, B2_log]
    · simp [blank, B2_driver]

end Scrub

/-- **The whole loop as one `Step`**, so an entry composes with it by `Step.seq`. The loop's
own entry is `Cells.run`'s: the data bank extended by the counter `CompareMachine.word bound`
(head `1`); `RepeatMachine.cfg 0`'s control is the loop machine's start. -/
theorem Cells.loopStep {t s : ℕ} (c : Cells t s) (out : List Bool) :
    Step (CloseoutRowsDegreeLoop.machine c.body) (c.bound*(c.cost+3)+3)
      (Fin.addCases (c.source 0 out).heads (fun _ : Fin 1 => 1))
      (Fin.addCases (c.source 0 out).tapes (fun _ : Fin 1 => CompareMachine.word c.bound))
      (Fin.addCases (c.source c.bound (out ++ (List.range c.bound).flatMap c.emit)).heads
        (fun _ : Fin 1 => 1))
      (Fin.addCases (c.source c.bound (out ++ (List.range c.bound).flatMap c.emit)).tapes
        (fun _ : Fin 1 => CompareMachine.word c.bound)) := by
  obtain ⟨r, hr, hf, _⟩ := c.run out
  refine Step.of_run (r := r) hr ?_ ?_
  · rw [hf]; rfl
  · rw [hf]; rfl

end
end NearCubicWires.BlockPlatform
