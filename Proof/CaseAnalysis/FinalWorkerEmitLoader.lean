import Proof.CaseAnalysis.FinalWorkerEmitShape
import Proof.MachineModel.ClockScalarFields

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader

open Finset
open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_value)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The three slot maps -/

/-- The positive numerator's re-encoding: driver `98`, source `92`, output
`210 = answerSlot 23`, flag `181`, counter `183`. -/
def slotsP : Fin 5 → Fin 218 := ![98, 92, 210, 181, 183]

/-- The negative numerator's re-encoding: flag `184`, same counter. -/
def slotsN : Fin 5 → Fin 218 := ![98, 93, 211, 184, 183]

/-- The denominator's WIDTH CHANGE: source `96` carries `binary b d`, the
driver `98` carries the wide width, so the output is `binary (width b) d`. -/
def slotsD : Fin 5 → Fin 218 := ![98, 96, 212, 185, 183]

theorem slotsP_injective : Function.Injective slotsP := by decide
theorem slotsN_injective : Function.Injective slotsN := by decide
theorem slotsD_injective : Function.Injective slotsD := by decide

theorem slotsP_vals (k : Fin 5) :
    (slotsP k).val = 98 ∨ (slotsP k).val = 92 ∨ (slotsP k).val = 210 ∨
      (slotsP k).val = 181 ∨ (slotsP k).val = 183 := by revert k; decide
theorem slotsN_vals (k : Fin 5) :
    (slotsN k).val = 98 ∨ (slotsN k).val = 93 ∨ (slotsN k).val = 211 ∨
      (slotsN k).val = 184 ∨ (slotsN k).val = 183 := by revert k; decide
theorem slotsD_vals (k : Fin 5) :
    (slotsD k).val = 98 ∨ (slotsD k).val = 96 ∨ (slotsD k).val = 212 ∨
      (slotsD k).val = 185 ∨ (slotsD k).val = 183 := by revert k; decide

/-! ## §2 One re-encoding stage, docked -/

/-- The blank-padding profile: the framed source and the flag tape at the
fold's capacity, the counter tape one longer, the driver and the output tape
unpadded. -/
def capVec (cap : ℕ) : Fin 5 → ℕ := fun i =>
  if i.val = 1 then cap else if i.val = 3 then cap
  else if i.val = 4 then cap + 1 else 0

/-- The stage's exit, at its own five tapes. -/
def widenOut (width cap : ℕ) (bits : List Bool) : Fin 5 → List Bool := fun i =>
  if i.val = 0 then List.replicate width true
  else if i.val = 1 then ZeroPadding.pad cap (frame bits)
  else if i.val = 2 then frame (binary width (value bits))
  else if i.val = 3 then ZeroPadding.pad cap [true]
  else List.replicate (cap + 1) false

theorem input_zero (width : ℕ) (bits : List Bool) :
    ClockNormalize.input width bits 0 = List.replicate width true := rfl
theorem input_one (width : ℕ) (bits : List Bool) :
    ClockNormalize.input width bits 1 = frame bits := rfl
theorem input_two (width : ℕ) (bits : List Bool) :
    ClockNormalize.input width bits 2 = [] := rfl
theorem input_three (width : ℕ) (bits : List Bool) :
    ClockNormalize.input width bits 3 = [] := rfl
theorem input_four (width : ℕ) (bits : List Bool) :
    ClockNormalize.input width bits 4 = [] := rfl

theorem pad_nil (cap : ℕ) : ZeroPadding.pad cap [] = List.replicate cap false := by
  simp [ZeroPadding.pad]

theorem widen_step (slots : Fin 5 → Fin 218) (hslots : Function.Injective slots)
    (width cap : ℕ) (bits : List Bool) (hbits : bits.length ≤ width)
    (hcap : 2 * width + 1 ≤ cap + 1)
    (H : Fin 218 → ℕ) (A : Fin 218 → List Bool)
    (hH : ∀ j : Fin 5, H (slots j) = 0)
    (hA0 : A (slots 0) = List.replicate width true)
    (hA1 : A (slots 1) = ZeroPadding.pad cap (frame bits))
    (hA2 : A (slots 2) = [])
    (hA3 : A (slots 3) = List.replicate cap false)
    (hA4 : A (slots 4) = List.replicate (cap + 1) false) :
    Step (RecoveryFocus.machine slots ClockNormalize.machine) (4 * width + 4) H A
      (dockH slots H (fun _ => 0)) (install slots A (widenOut width cap bits)) := by
  obtain ⟨r, hrun, h0, h1, h2, h3, h4, hheads, _hsteps⟩ :=
    ClockScalarFields.scalar_run width bits hbits
  have hstep : Step ClockNormalize.machine (4 * width + 4) (fun _ => 0)
      (ClockNormalize.input width bits) (fun _ => 0) r.final.tapes :=
    Step.of_run hrun (funext hheads) rfl
  have hpad := hstep.pad (capVec cap)
  have hout : (fun i => ZeroPadding.pad (capVec cap i) (r.final.tapes i)) =
      widenOut width cap bits := by
    funext i
    fin_cases i
    · show ZeroPadding.pad 0 (r.final.tapes 0) = List.replicate width true
      rw [ZeroPadding.pad_zero, h0]
    · show ZeroPadding.pad cap (r.final.tapes 1) = ZeroPadding.pad cap (frame bits)
      rw [h1]
    · show ZeroPadding.pad 0 (r.final.tapes 2) = frame (binary width (value bits))
      rw [ZeroPadding.pad_zero, h2]
    · show ZeroPadding.pad cap (r.final.tapes 3) = ZeroPadding.pad cap [true]
      rw [h3]
    · show ZeroPadding.pad (cap + 1) (r.final.tapes 4) = List.replicate (cap + 1) false
      rw [h4]
      exact pad_replicate_false (cap + 1) (2 * width + 1) hcap
  rw [hout] at hpad
  refine hpad.dock slots hslots H A hH ?_
  intro j
  fin_cases j
  · show A (slots 0) = ZeroPadding.pad 0 (ClockNormalize.input width bits 0)
    rw [ZeroPadding.pad_zero, input_zero]
    exact hA0
  · show A (slots 1) = ZeroPadding.pad cap (ClockNormalize.input width bits 1)
    rw [input_one]
    exact hA1
  · show A (slots 2) = ZeroPadding.pad 0 (ClockNormalize.input width bits 2)
    rw [ZeroPadding.pad_zero, input_two]
    exact hA2
  · show A (slots 3) = ZeroPadding.pad cap (ClockNormalize.input width bits 3)
    rw [input_three, pad_nil]
    exact hA3
  · show A (slots 4) = ZeroPadding.pad (cap + 1) (ClockNormalize.input width bits 4)
    rw [input_four, pad_nil]
    exact hA4

/-! ## §3 The emit loader -/

noncomputable def stage (slots : Fin 5 → Fin 218) : Machine 218 6 :=
  RecoveryFocus.machine slots ClockNormalize.machine

noncomputable def emitLoader :=
  Composition.machine (Composition.machine (stage slotsP) (stage slotsN)) (stage slotsD)

/-- The emit loader's fuel: three copies of the normalizer's own budget at the
wide scalar width, plus the two paid bridge steps.  No summand mentions the
witness. -/
def emitFuel (b : ℕ) : ℕ :=
  (4 * CompetitorRationalDecision.width b + 4) + 1 +
    (4 * CompetitorRationalDecision.width b + 4) + 1 +
    (4 * CompetitorRationalDecision.width b + 4)

/-! ## §4 The head invariant -/

/-- The dock's exit heads are zero away from the fold's source tape `76` and
its unread counter tape `186`; a docked stage whose own heads return to zero
preserves that. -/
theorem dockH_zero (slots : Fin 5 → Fin 218) (H : Fin 218 → ℕ)
    (hH : ∀ i : Fin 218, i.val ≠ 76 → i.val ≠ 186 → H i = 0) :
    ∀ i : Fin 218, i.val ≠ 76 → i.val ≠ 186 → dockH slots H (fun _ => 0) i = 0 := by
  intro i h76 h186
  cases hp : RecoveryFocus.pick slots i with
  | none => simp only [dockH, hp]; exact hH i h76 h186
  | some j => simp only [dockH, hp]

theorem heads_at_slots (slots : Fin 5 → Fin 218) (H : Fin 218 → ℕ)
    (hH : ∀ i : Fin 218, i.val ≠ 76 → i.val ≠ 186 → H i = 0)
    (hs : ∀ k : Fin 5, (slots k).val ≠ 76 ∧ (slots k).val ≠ 186) :
    ∀ k : Fin 5, H (slots k) = 0 := fun k => hH _ (hs k).1 (hs k).2

/-- The three data ports the emit loader fills start empty. -/
theorem entry_data (b : ℕ) (A : Fin 218 → List Bool) (hentry : EmitEntry b A)
    (j : Fin 29) (hj : j.val = 23 ∨ j.val = 24 ∨ j.val = 25) : A (answerSlot j) = [] := by
  have h := hentry j
  rw [if_pos hj] at h
  exact h

theorem slotsP_fresh : ∀ k : Fin 5, (slotsP k).val ≠ 76 ∧ (slotsP k).val ≠ 186 := by decide
theorem slotsN_fresh : ∀ k : Fin 5, (slotsN k).val ≠ 76 ∧ (slotsN k).val ≠ 186 := by decide
theorem slotsD_fresh : ∀ k : Fin 5, (slotsD k).val ≠ 76 ∧ (slotsD k).val ≠ 186 := by decide

/-! ## §5 The fold's stored fields, as bank ports -/

theorem store_ports (b : ℕ) (a : CompetitorValidity.Estimate) (source : List Bool)
    (A : Fin 218 → List Bool)
    (h : CompetitorSumFold.Store b a source (fun i : Fin 94 => A (foldSlot (i.castAdd 1)))) :
    A 92 = ZeroPadding.pad (CompetitorReusableDecision.capacity b)
        (frame (binary (CompetitorRationalDecision.width b) a.positive)) ∧
      A 93 = ZeroPadding.pad (CompetitorReusableDecision.capacity b)
        (frame (binary (CompetitorRationalDecision.width b) a.negative)) ∧
      A 96 = ZeroPadding.pad (CompetitorReusableDecision.capacity b)
        (frame (binary b a.denominator)) ∧
      A 98 = List.replicate (CompetitorRationalDecision.width b) true ∧
      A 181 = List.replicate (CompetitorReusableDecision.capacity b) false ∧
      A 183 = List.replicate (CompetitorReusableDecision.capacity b + 1) false ∧
      A 184 = List.replicate (CompetitorReusableDecision.capacity b) false ∧
      A 185 = List.replicate (CompetitorReusableDecision.capacity b) false :=
  ⟨h.positive, h.negative, h.denominator, h.wideWidth, h.loaderReset, h.eraseReset,
    h.copyCounter, h.copyReset⟩

/-! ## §6 The emit loader's receipt -/

theorem width_bound (b : ℕ) :
    2 * CompetitorRationalDecision.width b + 1 ≤ CompetitorReusableDecision.capacity b + 1 := by
  unfold CompetitorRationalDecision.width CompetitorReusableDecision.capacity
  nlinarith [sq_nonneg (b + 1), Nat.zero_le b]

theorem short_le_wide (b : ℕ) : b ≤ CompetitorRationalDecision.width b := by
  unfold CompetitorRationalDecision.width
  omega

/-- **The emit loader runs, and its three data ports are the emitter's.**
Premise: the fold's stored accumulator on the bank (`CompetitorSumFold.Store`
through the frozen `foldSlot` map), the loader's constant ports (`EmitEntry`),
the dock's head invariant, and the answer's validity at the fold's own width.
Conclusion: one `Step` of `emitLoader`, all twenty-nine operand heads at zero,
and all twenty-nine operand ports equal to
`CloseoutRowsEstimatorCoefficients.Append.input`. -/
theorem emit_loader_step (b : ℕ) (q : CompetitorValidity.Estimate) (source : List Bool)
    (H : Fin 218 → ℕ) (A : Fin 218 → List Bool)
    (hstore : CompetitorSumFold.Store b q source (fun i : Fin 94 => A (foldSlot (i.castAdd 1))))
    (hvalid : CompetitorValidity.Estimate.Valid q b)
    (hH : ∀ i : Fin 218, i.val ≠ 76 → i.val ≠ 186 → H i = 0)
    (hentry : EmitEntry b A) :
    ∃ (operandHeads : Fin 218 → ℕ) (operands : Fin 218 → List Bool),
      Step emitLoader (emitFuel b) H A operandHeads operands ∧
      (∀ j : Fin 29, operandHeads (answerSlot j) = 0) ∧
      (∀ j : Fin 29,
        operands (answerSlot j) =
          CloseoutRowsEstimatorCoefficients.Append.input b q 1 1 j) := by
  classical
  obtain ⟨p92, p93, p96, p98, p181, p183, p184, p185⟩ := store_ports b q source A hstore
  -- the three empty data ports
  have p210 : A 210 = [] := entry_data b A hentry 23 (by decide)
  have p211 : A 211 = [] := entry_data b A hentry 24 (by decide)
  have p212 : A 212 = [] := entry_data b A hentry 25 (by decide)
  set W := CompetitorRationalDecision.width b with hW
  set C := CompetitorReusableDecision.capacity b with hC
  -- stage P
  have hP := widen_step slotsP slotsP_injective W C (binary W q.positive) (by simp)
    (width_bound b) H A (heads_at_slots slotsP H hH slotsP_fresh) p98 p92 p210 p181 p183
  set H1 := dockH slotsP H (fun _ => 0) with hH1def
  set A1 := install slotsP A (widenOut W C (binary W q.positive)) with hA1def
  have hH1 : ∀ i : Fin 218, i.val ≠ 76 → i.val ≠ 186 → H1 i = 0 := dockH_zero slotsP H hH
  have a1_98 : A1 98 = List.replicate W true := by
    have := install_slot slotsP slotsP_injective A (widenOut W C (binary W q.positive)) 0
    exact this
  have a1_183 : A1 183 = List.replicate (C + 1) false := by
    have := install_slot slotsP slotsP_injective A (widenOut W C (binary W q.positive)) 4
    exact this
  have a1_210 : A1 210 = frame (binary W (value (binary W q.positive))) := by
    have := install_slot slotsP slotsP_injective A (widenOut W C (binary W q.positive)) 2
    exact this
  have a1_93 : A1 93 = A 93 := install_other slotsP _ _ 93 (by decide)
  have a1_211 : A1 211 = A 211 := install_other slotsP _ _ 211 (by decide)
  have a1_184 : A1 184 = A 184 := install_other slotsP _ _ 184 (by decide)
  have a1_96 : A1 96 = A 96 := install_other slotsP _ _ 96 (by decide)
  have a1_212 : A1 212 = A 212 := install_other slotsP _ _ 212 (by decide)
  have a1_185 : A1 185 = A 185 := install_other slotsP _ _ 185 (by decide)
  -- stage N
  have hN := widen_step slotsN slotsN_injective W C (binary W q.negative) (by simp)
    (width_bound b) H1 A1 (heads_at_slots slotsN H1 hH1 slotsN_fresh) a1_98
    (a1_93.trans p93) (a1_211.trans p211) (a1_184.trans p184) a1_183
  set H2 := dockH slotsN H1 (fun _ => 0) with hH2def
  set A2 := install slotsN A1 (widenOut W C (binary W q.negative)) with hA2def
  have hH2 : ∀ i : Fin 218, i.val ≠ 76 → i.val ≠ 186 → H2 i = 0 := dockH_zero slotsN H1 hH1
  have a2_98 : A2 98 = List.replicate W true := by
    have := install_slot slotsN slotsN_injective A1 (widenOut W C (binary W q.negative)) 0
    exact this
  have a2_183 : A2 183 = List.replicate (C + 1) false := by
    have := install_slot slotsN slotsN_injective A1 (widenOut W C (binary W q.negative)) 4
    exact this
  have a2_211 : A2 211 = frame (binary W (value (binary W q.negative))) := by
    have := install_slot slotsN slotsN_injective A1 (widenOut W C (binary W q.negative)) 2
    exact this
  have a2_96 : A2 96 = A1 96 := install_other slotsN _ _ 96 (by decide)
  have a2_212 : A2 212 = A1 212 := install_other slotsN _ _ 212 (by decide)
  have a2_185 : A2 185 = A1 185 := install_other slotsN _ _ 185 (by decide)
  have a2_210 : A2 210 = A1 210 := install_other slotsN _ _ 210 (by decide)
  -- stage D
  have hD := widen_step slotsD slotsD_injective W C (binary b q.denominator)
    (by simpa using short_le_wide b) (width_bound b) H2 A2
    (heads_at_slots slotsD H2 hH2 slotsD_fresh) a2_98
    ((a2_96.trans a1_96).trans p96) ((a2_212.trans a1_212).trans p212)
    ((a2_185.trans a1_185).trans p185) a2_183
  set H3 := dockH slotsD H2 (fun _ => 0) with hH3def
  set A3 := install slotsD A2 (widenOut W C (binary b q.denominator)) with hA3def
  have hH3 : ∀ i : Fin 218, i.val ≠ 76 → i.val ≠ 186 → H3 i = 0 := dockH_zero slotsD H2 hH2
  have a3_212 : A3 212 = frame (binary W (value (binary b q.denominator))) := by
    have := install_slot slotsD slotsD_injective A2 (widenOut W C (binary b q.denominator)) 2
    exact this
  have a3_211 : A3 211 = A2 211 := install_other slotsD _ _ 211 (by decide)
  have a3_210 : A3 210 = A2 210 := install_other slotsD _ _ 210 (by decide)
  -- the value of each data port
  have hpos : q.positive < 2 ^ W := lt_of_lt_of_le hvalid.positive
    (Nat.pow_le_pow_right (by omega) (short_le_wide b))
  have hneg : q.negative < 2 ^ W := lt_of_lt_of_le hvalid.negative
    (Nat.pow_le_pow_right (by omega) (short_le_wide b))
  have h23 : A3 (answerSlot 23) = frame (binary W q.positive) := by
    have h : A3 210 = frame (binary W q.positive) := by
      rw [a3_210, a2_210, a1_210, binary_value W q.positive hpos]
    exact h
  have h24 : A3 (answerSlot 24) = frame (binary W q.negative) := by
    have h : A3 211 = frame (binary W q.negative) := by
      rw [a3_211, a2_211, binary_value W q.negative hneg]
    exact h
  have h25 : A3 (answerSlot 25) = frame (binary W q.denominator) := by
    have h : A3 212 = frame (binary W q.denominator) := by
      rw [a3_212, binary_value b q.denominator hvalid.denominator]
    exact h
  -- the untouched ports
  have hrest : ∀ j : Fin 29, ¬ (j.val = 23 ∨ j.val = 24 ∨ j.val = 25) →
      A3 (answerSlot j) = A (answerSlot j) := by
    intro j hj
    have hval : (answerSlot j).val = 187 + j.val := answerSlot_val j
    have hD' : A3 (answerSlot j) = A2 (answerSlot j) := by
      refine install_other slotsD _ _ _ ?_
      intro k hk
      have hv := congrArg Fin.val hk
      rw [hval] at hv
      rcases slotsD_vals k with h | h | h | h | h <;> omega
    have hN' : A2 (answerSlot j) = A1 (answerSlot j) := by
      refine install_other slotsN _ _ _ ?_
      intro k hk
      have hv := congrArg Fin.val hk
      rw [hval] at hv
      rcases slotsN_vals k with h | h | h | h | h <;> omega
    have hP' : A1 (answerSlot j) = A (answerSlot j) := by
      refine install_other slotsP _ _ _ ?_
      intro k hk
      have hv := congrArg Fin.val hk
      rw [hval] at hv
      rcases slotsP_vals k with h | h | h | h | h <;> omega
    rw [hD', hN', hP']
  refine ⟨H3, A3, ?_, ?_, ?_⟩
  · have hchain := (hP.seq hN).seq hD
    have hfuel : (4 * W + 4) + 1 + (4 * W + 4) + 1 + (4 * W + 4) = emitFuel b := by
      unfold emitFuel
      rw [← hW]
    rw [hfuel] at hchain
    exact hchain
  · intro j
    refine hH3 (answerSlot j) ?_ ?_ <;> rw [answerSlot_val] <;> have := j.isLt <;> omega
  · intro j
    exact emitEntry_append b q A hentry A3 h23 h24 h25 hrest j

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader
