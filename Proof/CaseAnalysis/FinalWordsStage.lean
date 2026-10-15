import Proof.CaseAnalysis.FinalWordEngines2
import Proof.CaseAnalysis.FinalWorkerLoaderPorts

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WordsStage

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10DimensionWords (dimensions_dock)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WordEngines (sum_dock copy_dock product_dock
  fixedWord_dock)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WordEngines2 (counter_dock normalize_dock)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock (DockReady joinScalarWidth)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape (EmitEntry)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerLoaderPorts (dockReady_of_ports
  emitEntry_of_ports)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairSource.VerifierDecoding

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The private block, measured -/

/-- The number of private tapes the seventeen stages consume.  `abbrev`, not `def`: the
bank numerals `83 : Fin (219 + s)` need the `NeZero (219 + s)` instance. -/
abbrev s : ℕ := 59

/-- **Constraint 32.**  The stage fits in the granted budget. -/
theorem s_le_64 : s ≤ 64 := by decide

/-! ## §2 The seventeen slot maps -/

def slots1 : Fin 19 → Fin (219 + s) :=
  ![218, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 83, 234,
      219, 235]
def slots2 : Fin 2 → Fin (219 + s) :=
  ![236, 237]
def slots3 : Fin 4 → Fin (219 + s) :=
  ![83, 236, 238, 239]
def slots4 : Fin 4 → Fin (219 + s) :=
  ![238, 90, 240, 241]
def slots5 : Fin 4 → Fin (219 + s) :=
  ![240, 238, 85, 242]
def slots6 : Fin 19 → Fin (219 + s) :=
  ![85, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 84, 257,
      86, 258]
def slots7 : Fin 4 → Fin (219 + s) :=
  ![84, 259, 98, 260]
def slots8 : Fin 4 → Fin (219 + s) :=
  ![85, 259, 176, 261]
def slots9 : Fin 4 → Fin (219 + s) :=
  ![85, 259, 187, 262]
def slots10 : Fin 4 → Fin (219 + s) :=
  ![86, 259, 182, 263]
def slots11 : Fin 4 → Fin (219 + s) :=
  ![236, 90, 264, 265]
def slots12 : Fin 4 → Fin (219 + s) :=
  ![264, 266, 186, 267]
def slots13 : Fin 2 → Fin (219 + s) :=
  ![268, 269]
def slots14 : Fin 5 → Fin (219 + s) :=
  ![85, 268, 213, 270, 271]
def slots15 : Fin 5 → Fin (219 + s) :=
  ![85, 268, 214, 272, 273]
def slots16 : Fin 4 → Fin (219 + s) :=
  ![85, 259, 274, 276]
def slots17 : Fin 4 → Fin (219 + s) :=
  ![84, 259, 275, 277]

theorem slots1_inj : Function.Injective slots1 := by decide
theorem slots2_inj : Function.Injective slots2 := by decide
theorem slots3_inj : Function.Injective slots3 := by decide
theorem slots4_inj : Function.Injective slots4 := by decide
theorem slots5_inj : Function.Injective slots5 := by decide
theorem slots6_inj : Function.Injective slots6 := by decide
theorem slots7_inj : Function.Injective slots7 := by decide
theorem slots8_inj : Function.Injective slots8 := by decide
theorem slots9_inj : Function.Injective slots9 := by decide
theorem slots10_inj : Function.Injective slots10 := by decide
theorem slots11_inj : Function.Injective slots11 := by decide
theorem slots12_inj : Function.Injective slots12 := by decide
theorem slots13_inj : Function.Injective slots13 := by decide
theorem slots14_inj : Function.Injective slots14 := by decide
theorem slots15_inj : Function.Injective slots15 := by decide
theorem slots16_inj : Function.Injective slots16 := by decide
theorem slots17_inj : Function.Injective slots17 := by decide

theorem slots1_scratch : ∀ j : Fin 19, j.val ≠ 0 → j.val ≠ 15 → 219 ≤ (slots1 j).val := by
  decide

theorem slots6_scratch :
    ∀ j : Fin 19, j.val ≠ 0 → j.val ≠ 15 → j.val ≠ 17 → 243 ≤ (slots6 j).val := by decide

/-! ## §3 The public ports, and the ports still pending after each stage -/

/-- The bank tapes the stage is allowed to disturb: the twelve words and the driver. -/
def pubTapes : Finset ℕ := {83, 84, 85, 86, 90, 98, 176, 182, 186, 187, 213, 214, 218}

def P0 : Finset ℕ := {83, 84, 85, 86, 98, 176, 182, 186, 187, 213, 214}
def P1 : Finset ℕ := {84, 85, 86, 98, 176, 182, 186, 187, 213, 214}
def P5 : Finset ℕ := {84, 86, 98, 176, 182, 186, 187, 213, 214}
def P6 : Finset ℕ := {98, 176, 182, 186, 187, 213, 214}
def P7 : Finset ℕ := {176, 182, 186, 187, 213, 214}
def P8 : Finset ℕ := {182, 186, 187, 213, 214}
def P9 : Finset ℕ := {182, 186, 213, 214}
def P10 : Finset ℕ := {186, 213, 214}
def P12 : Finset ℕ := {213, 214}
def P14 : Finset ℕ := {214}

theorem cover1 : ∀ k, 219 ≤ (slots1 k).val ∨ (slots1 k).val ∈ pubTapes := by decide
theorem cover2 : ∀ k, 219 ≤ (slots2 k).val ∨ (slots2 k).val ∈ pubTapes := by decide
theorem cover3 : ∀ k, 219 ≤ (slots3 k).val ∨ (slots3 k).val ∈ pubTapes := by decide
theorem cover4 : ∀ k, 219 ≤ (slots4 k).val ∨ (slots4 k).val ∈ pubTapes := by decide
theorem cover5 : ∀ k, 219 ≤ (slots5 k).val ∨ (slots5 k).val ∈ pubTapes := by decide
theorem cover6 : ∀ k, 219 ≤ (slots6 k).val ∨ (slots6 k).val ∈ pubTapes := by decide
theorem cover7 : ∀ k, 219 ≤ (slots7 k).val ∨ (slots7 k).val ∈ pubTapes := by decide
theorem cover8 : ∀ k, 219 ≤ (slots8 k).val ∨ (slots8 k).val ∈ pubTapes := by decide
theorem cover9 : ∀ k, 219 ≤ (slots9 k).val ∨ (slots9 k).val ∈ pubTapes := by decide
theorem cover10 : ∀ k, 219 ≤ (slots10 k).val ∨ (slots10 k).val ∈ pubTapes := by decide
theorem cover11 : ∀ k, 219 ≤ (slots11 k).val ∨ (slots11 k).val ∈ pubTapes := by decide
theorem cover12 : ∀ k, 219 ≤ (slots12 k).val ∨ (slots12 k).val ∈ pubTapes := by decide
theorem cover13 : ∀ k, 219 ≤ (slots13 k).val ∨ (slots13 k).val ∈ pubTapes := by decide
theorem cover14 : ∀ k, 219 ≤ (slots14 k).val ∨ (slots14 k).val ∈ pubTapes := by decide
theorem cover15 : ∀ k, 219 ≤ (slots15 k).val ∨ (slots15 k).val ∈ pubTapes := by decide
theorem cover16 : ∀ k, 219 ≤ (slots16 k).val ∨ (slots16 k).val ∈ pubTapes := by decide
theorem cover17 : ∀ k, 219 ≤ (slots17 k).val ∨ (slots17 k).val ∈ pubTapes := by decide

/-! ## §4 The four bookkeeping lemmas -/

/-- Carry an established port through a stage whose slot map misses it. -/
theorem keep {t : ℕ} (slots : Fin t → Fin (219 + s)) (A A' : Fin (219 + s) → List Bool)
    (f : ∀ i : Fin (219 + s), (∀ j, slots j ≠ i) → A' i = A i)
    (i : Fin (219 + s)) (hi : ∀ j, slots j ≠ i) {w : List Bool} (h : A i = w) : A' i = w :=
  (f i hi).trans h

/-- Everything from tape `n` on is still blank: the stage's slots all lie below `n`. -/
theorem scratch_advance {t : ℕ} (slots : Fin t → Fin (219 + s)) (A A' : Fin (219 + s) → List Bool)
    (f : ∀ i : Fin (219 + s), (∀ j, slots j ≠ i) → A' i = A i)
    (m n : ℕ) (hmn : m ≤ n) (hlt : ∀ j, (slots j).val < n)
    (sc : ∀ i : Fin (219 + s), m ≤ i.val → A i = []) :
    ∀ i : Fin (219 + s), n ≤ i.val → A' i = [] := by
  intro i hi
  refine (f i (fun j hj => ?_)).trans (sc i (le_trans hmn hi))
  have h := hlt j
  rw [hj] at h
  omega

/-- The public ports still blank after the stage: `Q` shrinks by the ports it writes. -/
theorem blank_advance {t : ℕ} (slots : Fin t → Fin (219 + s)) (P Q : Finset ℕ)
    (A A' : Fin (219 + s) → List Bool)
    (f : ∀ i : Fin (219 + s), (∀ j, slots j ≠ i) → A' i = A i)
    (hQP : Q ⊆ P) (hQ : ∀ j, (slots j).val ∉ Q)
    (hA : ∀ i : Fin (219 + s), i.val ∈ P → A i = []) :
    ∀ i : Fin (219 + s), i.val ∈ Q → A' i = [] := by
  intro i hi
  refine (f i (fun j hj => hQ j ?_)).trans (hA i (hQP hi))
  rw [hj]
  exact hi

/-- A bank tape below `219` that is not a public port is missed by every slot map. -/
theorem untouched {t : ℕ} (slots : Fin t → Fin (219 + s)) (P : Finset ℕ)
    (hr : ∀ k, 219 ≤ (slots k).val ∨ (slots k).val ∈ P)
    (i : Fin (219 + s)) (hi : i.val ∉ P) (hlt : i.val < 219) : ∀ j, slots j ≠ i := by
  intro j hj
  rcases hr j with h | h
  · rw [hj] at h; omega
  · exact hi (by rw [← hj]; exact h)

/-! ## §5 The machine and its fuel -/

noncomputable def stage1 := RecoveryFocus.machine slots1 CompetitorDimensions.machine
noncomputable def stage2 := RecoveryFocus.machine slots2 (HierarchyFixedWord.machine [true])
noncomputable def stage3 := RecoveryFocus.machine slots3 ClockUnarySum.machine
noncomputable def stage4 := RecoveryFocus.machine slots4 ClockUnaryProduct.machine
noncomputable def stage5 := RecoveryFocus.machine slots5 ClockUnarySum.machine
noncomputable def stage6 := RecoveryFocus.machine slots6 CompetitorDimensions.machine
noncomputable def stage7 := RecoveryFocus.machine slots7 ClockUnarySum.machine
noncomputable def stage8 := RecoveryFocus.machine slots8 ClockUnarySum.machine
noncomputable def stage9 := RecoveryFocus.machine slots9 ClockUnarySum.machine
noncomputable def stage10 := RecoveryFocus.machine slots10 ClockUnarySum.machine
noncomputable def stage11 := RecoveryFocus.machine slots11 ClockUnaryProduct.machine
noncomputable def stage12 := RecoveryFocus.machine slots12 NearCubicWires.RepairSource.ProjectionNormalization.Counter.machine
noncomputable def stage13 := RecoveryFocus.machine slots13 (HierarchyFixedWord.machine [true, true, false])
noncomputable def stage14 := RecoveryFocus.machine slots14 ClockNormalize.machine
noncomputable def stage15 := RecoveryFocus.machine slots15 ClockNormalize.machine
noncomputable def stage16 := RecoveryFocus.machine slots16 ClockUnarySum.machine
noncomputable def stage17 := RecoveryFocus.machine slots17 ClockUnarySum.machine

/-- The seventeen docked runs, composed left to right. -/
noncomputable def wordsMachine :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine (Composition.machine (Composition.machine stage1
    stage2) stage3) stage4) stage5) stage6) stage7) stage8) stage9) stage10) stage11) stage12)
    stage13) stage14) stage15) stage16) stage17

/-- The sum of the seventeen engine budgets and the sixteen paid bridge steps. -/
def wordsFuel (entryWidth callCount : ℕ) : ℕ :=
  CompetitorDimensions.budget entryWidth
  + 1 + (2 * ([true] : List Bool).length + 2)
  + 1 + (2 * (CompetitorRationalDecision.width entryWidth + 1) + 6)
  + 1 + (2 * ((CompetitorRationalDecision.width entryWidth + 1) * (2 * callCount + 3) + 2) + 2)
  + 1 + (2 * ((CompetitorRationalDecision.width entryWidth + 1) * callCount + (CompetitorRationalDecision.width entryWidth + 1)) + 6)
  + 1 + (CompetitorDimensions.budget (joinScalarWidth entryWidth callCount))
  + 1 + (2 * (CompetitorRationalDecision.width (joinScalarWidth entryWidth callCount) + 0) + 6)
  + 1 + (2 * (joinScalarWidth entryWidth callCount + 0) + 6)
  + 1 + (2 * (joinScalarWidth entryWidth callCount + 0) + 6)
  + 1 + (2 * (CompetitorReusableDecision.capacity (joinScalarWidth entryWidth callCount) + 0) + 6)
  + 1 + (2 * (1 * (2 * callCount + 3) + 2) + 2)
  + 1 + (NearCubicWires.RepairSource.ProjectionNormalization.Counter.budget callCount)
  + 1 + (2 * ([true, true, false] : List Bool).length + 2)
  + 1 + (4 * (joinScalarWidth entryWidth callCount) + 4)
  + 1 + (4 * (joinScalarWidth entryWidth callCount) + 4)
  + 1 + (2 * (joinScalarWidth entryWidth callCount + 0) + 6)
  + 1 + (2 * (CompetitorRationalDecision.width (joinScalarWidth entryWidth callCount) + 0) + 6)

/-! ## §6 The stage, port by port -/

/-- **The words stage.**  From the driver on tape `218`, the call counter on tape `90`,
eleven blank public ports and an empty private block, one machine run leaves the twelve
dimension words on their bank tapes, duplicates `85` and `84` onto `274` and `275`, and
changes no other tape of the `218` prefix.  The private block ends dirty, which is what
restricting the frame clause to `i.val < 219` says. -/
theorem words_step (entryWidth callCount : ℕ) (H : Fin (219 + s) → ℕ) (A : Fin (219 + s) → List Bool)
    (hH : ∀ i, H i = 0)
    (hdriver : A ⟨218, by omega⟩ = List.replicate entryWidth true)
    (hcount : A 90 = CompareMachine.word callCount)
    (hblank : ∀ i : Fin (219 + s),
      i.val ∈ ({83, 84, 85, 86, 98, 176, 182, 186, 187, 213, 214} : Finset ℕ) → A i = [])
    (hscratch : ∀ i : Fin (219 + s), 219 ≤ i.val → A i = []) :
    ∃ (H' : Fin (219 + s) → ℕ) (A' : Fin (219 + s) → List Bool),
      Step wordsMachine (wordsFuel entryWidth callCount) H A H' A' ∧ (∀ i, H' i = 0) ∧
      A' 83  = List.replicate (CompetitorRationalDecision.width entryWidth) true ∧
      A' 84  = List.replicate (CompetitorRationalDecision.width (joinScalarWidth entryWidth callCount)) true ∧
      A' 85  = List.replicate (joinScalarWidth entryWidth callCount) true ∧
      A' 86  = List.replicate (CompetitorReusableDecision.capacity (joinScalarWidth entryWidth callCount)) true ∧
      A' 90  = CompareMachine.word callCount ∧
      A' 98  = A' 84 ∧ A' 176 = A' 85 ∧ A' 182 = A' 86 ∧
      A' 186 = CompareMachine.word callCount ∧
      A' 187 = List.replicate (joinScalarWidth entryWidth callCount) true ∧
      A' 213 = frame (binary (joinScalarWidth entryWidth callCount) 1) ∧ A' 214 = A' 213 ∧
      A' ⟨274, by decide⟩ = A' 85 ∧ A' ⟨275, by decide⟩ = A' 84 ∧
      (∀ i : Fin (219 + s), i.val ∉ ({83, 84, 85, 86, 90, 98, 176, 182, 186, 187, 213, 214, 218} :
          Finset ℕ) → i.val < 219 → A' i = A i) := by
  have hB : joinScalarWidth entryWidth callCount
      = (CompetitorRationalDecision.width entryWidth + 1) * callCount + (CompetitorRationalDecision.width entryWidth + 1) := by
    unfold joinScalarWidth CompetitorSumWidth.width
    ring
  have hB1 : 1 ≤ joinScalarWidth entryWidth callCount := by rw [hB]; omega
  have hbits : ([true] : List Bool).length ≤ joinScalarWidth entryWidth callCount := by simpa using hB1
  have hdrv1 : A (slots1 0) = List.replicate entryWidth true := hdriver
  have hb1 : ∀ j : Fin 19, j.val ≠ 0 → A (slots1 j) = [] := by
    intro j hj
    by_cases h15 : j.val = 15
    · have hj15 : slots1 j = (83 : Fin (219 + s)) := by
        have h : j = (15 : Fin 19) := Fin.ext h15
        rw [h]; rfl
      rw [hj15]
      exact hblank 83 (by decide)
    · exact hscratch (slots1 j) (slots1_scratch j hj h15)
  obtain ⟨H1, A1, st1, hH1, _q1_0, q1_15, _q1_17, f1⟩ :=
    dimensions_dock entryWidth slots1 slots1_inj H A hH hdrv1 hb1
  have a1_90 := keep slots1 _ _ f1 90 (by decide) hcount
  have sc1 := scratch_advance slots1 _ _ f1 219 236 (by omega) (by decide) hscratch
  have pend1 := blank_advance slots1 P0 P1 _ _ f1 (by decide) (by decide) hblank
  obtain ⟨H2, A2, st2, hH2, q2_0, f2⟩ :=
    fixedWord_dock [true] slots2 slots2_inj H1 A1 hH1 (sc1 236 (by decide)) (sc1 237 (by decide))
  have a2_83 := keep slots2 _ _ f2 83 (by decide) q1_15
  have a2_90 := keep slots2 _ _ f2 90 (by decide) a1_90
  have sc2 := scratch_advance slots2 _ _ f2 236 238 (by omega) (by decide) sc1
  have pend2 := blank_advance slots2 P1 P1 _ _ f2 (fun _ hx => hx) (by decide) pend1
  obtain ⟨H3, A3, st3, hH3, q3_0, q3_1, q3_2, f3⟩ :=
    sum_dock (CompetitorRationalDecision.width entryWidth) 1 slots3 slots3_inj H2 A2 hH2
      a2_83 q2_0 (sc2 238 (by decide)) (sc2 239 (by decide))
  have a3_90 := keep slots3 _ _ f3 90 (by decide) a2_90
  have sc3 := scratch_advance slots3 _ _ f3 238 240 (by omega) (by decide) sc2
  have pend3 := blank_advance slots3 P1 P1 _ _ f3 (fun _ hx => hx) (by decide) pend2
  obtain ⟨H4, A4, st4, hH4, q4_0, q4_1, q4_2, f4⟩ :=
    product_dock (CompetitorRationalDecision.width entryWidth + 1) callCount slots4 slots4_inj H3 A3 hH3
      q3_2 a3_90 (sc3 240 (by decide)) (sc3 241 (by decide))
  have a4_83 := keep slots4 _ _ f4 83 (by decide) q3_0
  have a4_236 := keep slots4 _ _ f4 236 (by decide) q3_1
  have sc4 := scratch_advance slots4 _ _ f4 240 242 (by omega) (by decide) sc3
  have pend4 := blank_advance slots4 P1 P1 _ _ f4 (fun _ hx => hx) (by decide) pend3
  obtain ⟨H5, A5, st5, hH5, _q5_0, _q5_1, q5_2, f5⟩ :=
    sum_dock ((CompetitorRationalDecision.width entryWidth + 1) * callCount) (CompetitorRationalDecision.width entryWidth + 1) slots5 slots5_inj H4 A4 hH4
      q4_2 q4_0 (pend4 85 (by decide)) (sc4 242 (by decide))
  have a5_85 : A5 (85 : Fin (219 + s)) = List.replicate (joinScalarWidth entryWidth callCount) true := by
    rw [hB]
    exact q5_2
  have a5_83 := keep slots5 _ _ f5 83 (by decide) a4_83
  have a5_90 := keep slots5 _ _ f5 90 (by decide) q4_1
  have a5_236 := keep slots5 _ _ f5 236 (by decide) a4_236
  have sc5 := scratch_advance slots5 _ _ f5 242 243 (by omega) (by decide) sc4
  have pend5 := blank_advance slots5 P1 P5 _ _ f5 (by decide) (by decide) pend4
  have hb6 : ∀ j : Fin 19, j.val ≠ 0 → A5 (slots6 j) = [] := by
    intro j hj
    by_cases h15 : j.val = 15
    · have hj15 : slots6 j = (84 : Fin (219 + s)) := by
        have h : j = (15 : Fin 19) := Fin.ext h15
        rw [h]; rfl
      rw [hj15]
      exact pend5 84 (by decide)
    by_cases h17 : j.val = 17
    · have hj17 : slots6 j = (86 : Fin (219 + s)) := by
        have h : j = (17 : Fin 19) := Fin.ext h17
        rw [h]; rfl
      rw [hj17]
      exact pend5 86 (by decide)
    exact sc5 (slots6 j) (slots6_scratch j hj h15 h17)
  obtain ⟨H6, A6, st6, hH6, q6_0, q6_15, q6_17, f6⟩ :=
    dimensions_dock (joinScalarWidth entryWidth callCount) slots6 slots6_inj H5 A5 hH5 a5_85 hb6
  have a6_83 := keep slots6 _ _ f6 83 (by decide) a5_83
  have a6_90 := keep slots6 _ _ f6 90 (by decide) a5_90
  have a6_236 := keep slots6 _ _ f6 236 (by decide) a5_236
  have sc6 := scratch_advance slots6 _ _ f6 243 259 (by omega) (by decide) sc5
  have pend6 := blank_advance slots6 P5 P6 _ _ f6 (by decide) (by decide) pend5
  obtain ⟨H7, A7, st7, hH7, q7_0, q7_1, q7_2, f7⟩ :=
    copy_dock (CompetitorRationalDecision.width (joinScalarWidth entryWidth callCount)) slots7 slots7_inj H6 A6 hH6
      q6_15 (sc6 259 (by decide)) (pend6 98 (by decide)) (sc6 260 (by decide))
  have a7_83 := keep slots7 _ _ f7 83 (by decide) a6_83
  have a7_85 := keep slots7 _ _ f7 85 (by decide) q6_0
  have a7_86 := keep slots7 _ _ f7 86 (by decide) q6_17
  have a7_90 := keep slots7 _ _ f7 90 (by decide) a6_90
  have a7_236 := keep slots7 _ _ f7 236 (by decide) a6_236
  have sc7 := scratch_advance slots7 _ _ f7 259 261 (by omega) (by decide) sc6
  have pend7 := blank_advance slots7 P6 P7 _ _ f7 (by decide) (by decide) pend6
  obtain ⟨H8, A8, st8, hH8, q8_0, q8_1, q8_2, f8⟩ :=
    copy_dock (joinScalarWidth entryWidth callCount) slots8 slots8_inj H7 A7 hH7
      a7_85 q7_1 (pend7 176 (by decide)) (sc7 261 (by decide))
  have a8_83 := keep slots8 _ _ f8 83 (by decide) a7_83
  have a8_84 := keep slots8 _ _ f8 84 (by decide) q7_0
  have a8_86 := keep slots8 _ _ f8 86 (by decide) a7_86
  have a8_90 := keep slots8 _ _ f8 90 (by decide) a7_90
  have a8_98 := keep slots8 _ _ f8 98 (by decide) q7_2
  have a8_236 := keep slots8 _ _ f8 236 (by decide) a7_236
  have sc8 := scratch_advance slots8 _ _ f8 261 262 (by omega) (by decide) sc7
  have pend8 := blank_advance slots8 P7 P8 _ _ f8 (by decide) (by decide) pend7
  obtain ⟨H9, A9, st9, hH9, q9_0, q9_1, q9_2, f9⟩ :=
    copy_dock (joinScalarWidth entryWidth callCount) slots9 slots9_inj H8 A8 hH8
      q8_0 q8_1 (pend8 187 (by decide)) (sc8 262 (by decide))
  have a9_83 := keep slots9 _ _ f9 83 (by decide) a8_83
  have a9_84 := keep slots9 _ _ f9 84 (by decide) a8_84
  have a9_86 := keep slots9 _ _ f9 86 (by decide) a8_86
  have a9_90 := keep slots9 _ _ f9 90 (by decide) a8_90
  have a9_98 := keep slots9 _ _ f9 98 (by decide) a8_98
  have a9_176 := keep slots9 _ _ f9 176 (by decide) q8_2
  have a9_236 := keep slots9 _ _ f9 236 (by decide) a8_236
  have sc9 := scratch_advance slots9 _ _ f9 262 263 (by omega) (by decide) sc8
  have pend9 := blank_advance slots9 P8 P9 _ _ f9 (by decide) (by decide) pend8
  obtain ⟨H10, A10, st10, hH10, q10_0, q10_1, q10_2, f10⟩ :=
    copy_dock (CompetitorReusableDecision.capacity (joinScalarWidth entryWidth callCount)) slots10 slots10_inj H9 A9 hH9
      a9_86 q9_1 (pend9 182 (by decide)) (sc9 263 (by decide))
  have a10_83 := keep slots10 _ _ f10 83 (by decide) a9_83
  have a10_84 := keep slots10 _ _ f10 84 (by decide) a9_84
  have a10_85 := keep slots10 _ _ f10 85 (by decide) q9_0
  have a10_90 := keep slots10 _ _ f10 90 (by decide) a9_90
  have a10_98 := keep slots10 _ _ f10 98 (by decide) a9_98
  have a10_176 := keep slots10 _ _ f10 176 (by decide) a9_176
  have a10_187 := keep slots10 _ _ f10 187 (by decide) q9_2
  have a10_236 := keep slots10 _ _ f10 236 (by decide) a9_236
  have sc10 := scratch_advance slots10 _ _ f10 263 264 (by omega) (by decide) sc9
  have pend10 := blank_advance slots10 P9 P10 _ _ f10 (by decide) (by decide) pend9
  obtain ⟨H11, A11, st11, hH11, _q11_0, q11_1, q11_2, f11⟩ :=
    product_dock 1 callCount slots11 slots11_inj H10 A10 hH10
      a10_236 a10_90 (sc10 264 (by decide)) (sc10 265 (by decide))
  have a11_83 := keep slots11 _ _ f11 83 (by decide) a10_83
  have a11_84 := keep slots11 _ _ f11 84 (by decide) a10_84
  have a11_85 := keep slots11 _ _ f11 85 (by decide) a10_85
  have a11_86 := keep slots11 _ _ f11 86 (by decide) q10_0
  have a11_98 := keep slots11 _ _ f11 98 (by decide) a10_98
  have a11_176 := keep slots11 _ _ f11 176 (by decide) a10_176
  have a11_182 := keep slots11 _ _ f11 182 (by decide) q10_2
  have a11_187 := keep slots11 _ _ f11 187 (by decide) a10_187
  have a11_259 := keep slots11 _ _ f11 259 (by decide) q10_1
  have sc11 := scratch_advance slots11 _ _ f11 264 266 (by omega) (by decide) sc10
  have pend11 := blank_advance slots11 P10 P10 _ _ f11 (fun _ hx => hx) (by decide) pend10
  have h12in : A11 (264 : Fin (219 + s)) = List.replicate callCount true := by
    have h : A11 (264 : Fin (219 + s)) = List.replicate (1 * callCount) true := q11_2
    simpa using h
  obtain ⟨H12, A12, st12, hH12, _q12_0, q12_2, f12⟩ :=
    counter_dock callCount slots12 slots12_inj H11 A11 hH11
      h12in (sc11 266 (by decide)) (pend11 186 (by decide)) (sc11 267 (by decide))
  have a12_83 := keep slots12 _ _ f12 83 (by decide) a11_83
  have a12_84 := keep slots12 _ _ f12 84 (by decide) a11_84
  have a12_85 := keep slots12 _ _ f12 85 (by decide) a11_85
  have a12_86 := keep slots12 _ _ f12 86 (by decide) a11_86
  have a12_90 := keep slots12 _ _ f12 90 (by decide) q11_1
  have a12_98 := keep slots12 _ _ f12 98 (by decide) a11_98
  have a12_176 := keep slots12 _ _ f12 176 (by decide) a11_176
  have a12_182 := keep slots12 _ _ f12 182 (by decide) a11_182
  have a12_187 := keep slots12 _ _ f12 187 (by decide) a11_187
  have a12_259 := keep slots12 _ _ f12 259 (by decide) a11_259
  have sc12 := scratch_advance slots12 _ _ f12 266 268 (by omega) (by decide) sc11
  have pend12 := blank_advance slots12 P10 P12 _ _ f12 (by decide) (by decide) pend11
  obtain ⟨H13, A13, st13, hH13, q13_0, f13⟩ :=
    fixedWord_dock [true, true, false] slots13 slots13_inj H12 A12 hH12
      (sc12 268 (by decide)) (sc12 269 (by decide))
  have a13_83 := keep slots13 _ _ f13 83 (by decide) a12_83
  have a13_84 := keep slots13 _ _ f13 84 (by decide) a12_84
  have a13_85 := keep slots13 _ _ f13 85 (by decide) a12_85
  have a13_86 := keep slots13 _ _ f13 86 (by decide) a12_86
  have a13_90 := keep slots13 _ _ f13 90 (by decide) a12_90
  have a13_98 := keep slots13 _ _ f13 98 (by decide) a12_98
  have a13_176 := keep slots13 _ _ f13 176 (by decide) a12_176
  have a13_182 := keep slots13 _ _ f13 182 (by decide) a12_182
  have a13_186 := keep slots13 _ _ f13 186 (by decide) q12_2
  have a13_187 := keep slots13 _ _ f13 187 (by decide) a12_187
  have a13_259 := keep slots13 _ _ f13 259 (by decide) a12_259
  have sc13 := scratch_advance slots13 _ _ f13 268 270 (by omega) (by decide) sc12
  have pend13 := blank_advance slots13 P12 P12 _ _ f13 (fun _ hx => hx) (by decide) pend12
  obtain ⟨H14, A14, st14, hH14, q14_0, q14_1, q14_2, f14⟩ :=
    normalize_dock (joinScalarWidth entryWidth callCount) [true] hbits slots14 slots14_inj H13 A13 hH13
      a13_85 q13_0 (pend13 213 (by decide)) (sc13 270 (by decide)) (sc13 271 (by decide))
  have a14_213 : A14 (213 : Fin (219 + s)) = frame (binary (joinScalarWidth entryWidth callCount) 1) := q14_2
  have a14_83 := keep slots14 _ _ f14 83 (by decide) a13_83
  have a14_84 := keep slots14 _ _ f14 84 (by decide) a13_84
  have a14_86 := keep slots14 _ _ f14 86 (by decide) a13_86
  have a14_90 := keep slots14 _ _ f14 90 (by decide) a13_90
  have a14_98 := keep slots14 _ _ f14 98 (by decide) a13_98
  have a14_176 := keep slots14 _ _ f14 176 (by decide) a13_176
  have a14_182 := keep slots14 _ _ f14 182 (by decide) a13_182
  have a14_186 := keep slots14 _ _ f14 186 (by decide) a13_186
  have a14_187 := keep slots14 _ _ f14 187 (by decide) a13_187
  have a14_259 := keep slots14 _ _ f14 259 (by decide) a13_259
  have sc14 := scratch_advance slots14 _ _ f14 270 272 (by omega) (by decide) sc13
  have pend14 := blank_advance slots14 P12 P14 _ _ f14 (by decide) (by decide) pend13
  obtain ⟨H15, A15, st15, hH15, q15_0, _q15_1, q15_2, f15⟩ :=
    normalize_dock (joinScalarWidth entryWidth callCount) [true] hbits slots15 slots15_inj H14 A14 hH14
      q14_0 q14_1 (pend14 214 (by decide)) (sc14 272 (by decide)) (sc14 273 (by decide))
  have a15_214 : A15 (214 : Fin (219 + s)) = frame (binary (joinScalarWidth entryWidth callCount) 1) := q15_2
  have a15_83 := keep slots15 _ _ f15 83 (by decide) a14_83
  have a15_84 := keep slots15 _ _ f15 84 (by decide) a14_84
  have a15_86 := keep slots15 _ _ f15 86 (by decide) a14_86
  have a15_90 := keep slots15 _ _ f15 90 (by decide) a14_90
  have a15_98 := keep slots15 _ _ f15 98 (by decide) a14_98
  have a15_176 := keep slots15 _ _ f15 176 (by decide) a14_176
  have a15_182 := keep slots15 _ _ f15 182 (by decide) a14_182
  have a15_186 := keep slots15 _ _ f15 186 (by decide) a14_186
  have a15_187 := keep slots15 _ _ f15 187 (by decide) a14_187
  have a15_213 := keep slots15 _ _ f15 213 (by decide) a14_213
  have a15_259 := keep slots15 _ _ f15 259 (by decide) a14_259
  have sc15 := scratch_advance slots15 _ _ f15 272 274 (by omega) (by decide) sc14
  have a15_275 := (sc15 275 (by decide))
  obtain ⟨H16, A16, st16, hH16, q16_0, q16_1, q16_2, f16⟩ :=
    copy_dock (joinScalarWidth entryWidth callCount) slots16 slots16_inj H15 A15 hH15
      q15_0 a15_259 (sc15 274 (by decide)) (sc15 276 (by decide))
  have a16_83 := keep slots16 _ _ f16 83 (by decide) a15_83
  have a16_84 := keep slots16 _ _ f16 84 (by decide) a15_84
  have a16_86 := keep slots16 _ _ f16 86 (by decide) a15_86
  have a16_90 := keep slots16 _ _ f16 90 (by decide) a15_90
  have a16_98 := keep slots16 _ _ f16 98 (by decide) a15_98
  have a16_176 := keep slots16 _ _ f16 176 (by decide) a15_176
  have a16_182 := keep slots16 _ _ f16 182 (by decide) a15_182
  have a16_186 := keep slots16 _ _ f16 186 (by decide) a15_186
  have a16_187 := keep slots16 _ _ f16 187 (by decide) a15_187
  have a16_213 := keep slots16 _ _ f16 213 (by decide) a15_213
  have a16_214 := keep slots16 _ _ f16 214 (by decide) a15_214
  have a16_275 := keep slots16 _ _ f16 275 (by decide) a15_275
  have sc16 := scratch_advance slots16 _ _ f16 274 277 (by omega) (by decide) sc15
  obtain ⟨H17, A17, st17, hH17, q17_0, _q17_1, q17_2, f17⟩ :=
    copy_dock (CompetitorRationalDecision.width (joinScalarWidth entryWidth callCount)) slots17 slots17_inj H16 A16 hH16
      a16_84 q16_1 a16_275 (sc16 277 (by decide))
  have a17_83 := keep slots17 _ _ f17 83 (by decide) a16_83
  have a17_85 := keep slots17 _ _ f17 85 (by decide) q16_0
  have a17_86 := keep slots17 _ _ f17 86 (by decide) a16_86
  have a17_90 := keep slots17 _ _ f17 90 (by decide) a16_90
  have a17_98 := keep slots17 _ _ f17 98 (by decide) a16_98
  have a17_176 := keep slots17 _ _ f17 176 (by decide) a16_176
  have a17_182 := keep slots17 _ _ f17 182 (by decide) a16_182
  have a17_186 := keep slots17 _ _ f17 186 (by decide) a16_186
  have a17_187 := keep slots17 _ _ f17 187 (by decide) a16_187
  have a17_213 := keep slots17 _ _ f17 213 (by decide) a16_213
  have a17_214 := keep slots17 _ _ f17 214 (by decide) a16_214
  have a17_274 := keep slots17 _ _ f17 274 (by decide) q16_2
  refine ⟨H17, A17, ?_, hH17, a17_83, q17_0, a17_85, a17_86, a17_90,
    a17_98.trans q17_0.symm, a17_176.trans a17_85.symm, a17_182.trans a17_86.symm,
    a17_186, a17_187, a17_213, a17_214.trans a17_213.symm,
    a17_274.trans a17_85.symm, q17_2.trans q17_0.symm, ?_⟩
  · exact (((((((((((((((st1.seq st2).seq st3).seq st4).seq st5).seq st6).seq st7).seq st8).seq st9).seq st10).seq st11).seq st12).seq st13).seq st14).seq st15).seq st16).seq st17
  · intro i hi hlt
    rw [f17 i (untouched slots17 pubTapes cover17 i hi hlt),
      f16 i (untouched slots16 pubTapes cover16 i hi hlt),
      f15 i (untouched slots15 pubTapes cover15 i hi hlt),
      f14 i (untouched slots14 pubTapes cover14 i hi hlt),
      f13 i (untouched slots13 pubTapes cover13 i hi hlt),
      f12 i (untouched slots12 pubTapes cover12 i hi hlt),
      f11 i (untouched slots11 pubTapes cover11 i hi hlt),
      f10 i (untouched slots10 pubTapes cover10 i hi hlt),
      f9 i (untouched slots9 pubTapes cover9 i hi hlt),
      f8 i (untouched slots8 pubTapes cover8 i hi hlt),
      f7 i (untouched slots7 pubTapes cover7 i hi hlt),
      f6 i (untouched slots6 pubTapes cover6 i hi hlt),
      f5 i (untouched slots5 pubTapes cover5 i hi hlt),
      f4 i (untouched slots4 pubTapes cover4 i hi hlt),
      f3 i (untouched slots3 pubTapes cover3 i hi hlt),
      f2 i (untouched slots2 pubTapes cover2 i hi hlt),
      f1 i (untouched slots1 pubTapes cover1 i hi hlt)]

/-! ## §7 The stage's output, as the loader's obligation -/

theorem ready_of_words (entryWidth : ℕ) (entries : List Entry) (bank : Fin 218 → List Bool)
    (h81 : bank 81 = CloseoutRowsEstimatorCoefficients.Stream.words entryWidth entries)
    (hwords :
      bank 83 = List.replicate (CompetitorRationalDecision.width entryWidth) true ∧
      bank 84 = List.replicate
        (CompetitorRationalDecision.width (joinScalarWidth entryWidth entries.length)) true ∧
      bank 85 = List.replicate (joinScalarWidth entryWidth entries.length) true ∧
      bank 86 = List.replicate
        (CompetitorReusableDecision.capacity (joinScalarWidth entryWidth entries.length)) true ∧
      bank 90 = CompareMachine.word entries.length ∧
      bank 98 = bank 84 ∧ bank 176 = bank 85 ∧ bank 182 = bank 86 ∧
      bank 186 = CompareMachine.word entries.length ∧
      bank 187 = List.replicate (joinScalarWidth entryWidth entries.length) true ∧
      bank 213 = frame (binary (joinScalarWidth entryWidth entries.length) 1) ∧
      bank 214 = bank 213)
    (hblank : ∀ i : Fin 218, 2 ≤ i.val → i.val < 187 →
      i.val ≠ 81 → i.val ≠ 83 → i.val ≠ 84 → i.val ≠ 85 → i.val ≠ 86 → i.val ≠ 90 →
      i.val ≠ 98 → i.val ≠ 176 → i.val ≠ 182 → i.val ≠ 186 → bank i = [])
    (hanswer : ∀ i : Fin 218, 187 < i.val → i.val < 216 →
      i.val ≠ 213 → i.val ≠ 214 → bank i = []) :
    DockReady entryWidth entries bank ∧
      EmitEntry (joinScalarWidth entryWidth entries.length) bank := by
  obtain ⟨h83, h84, h85, h86, h90, h98, h176, h182, h186, h187, h213, h214⟩ := hwords
  exact ⟨dockReady_of_ports entryWidth entries bank h81 h83 h84 h85 h86 h90 (h98.trans h84)
      (h176.trans h85) (h182.trans h86) h186 hblank,
    emitEntry_of_ports _ bank h187 h213 (h214.trans h213) hanswer⟩

-- The two std3-FREE results (`keep`, `s_le_64`) are printed last on purpose: Lean prints

-- non-greedy `'(.+?)' depends on axioms: [...]` pattern would otherwise absorb the NEXT
-- declaration's name into that line.
end NearCubicWires.RepairOrdinary.CloseoutFinalC10WordsStage
