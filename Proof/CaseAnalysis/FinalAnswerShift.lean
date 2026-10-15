import Proof.Hierarchy.CompetitorDenominator
import Proof.CaseAnalysis.FinalSupplierCountStage
import Proof.CaseAnalysis.FinalCostAtTable

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10AnswerShift

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
  (rowAnswer rowDenominator)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth
  (answer denominator seedExponent rowCount_eq_two_pow rowAnswer_le_rowDenominator)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage
  (bank_scratch_apply scratchOf scratchOf_apply round_step_of_dock)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
  (widthAt widthPower one_le_widthPower widthPower_le_logScale widthConst thresholdFloor
    entryWidthSchedule partsOnset width_ge_floor)
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin
  (polyFuel poly_polylog_le_polyFuel repinOnset partsOnset_le_repinOnset)
open NearCubicWires.RepairSource.CloseoutFinal.C10CostAtTable (hotFuel polyFuel_le_hotFuel)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierWalk

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 A.13.9's rescaling IS a left shift

`answer` is a floor quotient by definition.  Under the fit condition
`seedExponent <= scale` both parts of the quotient are powers of two, and the
quotient is exact: the whole answer channel is `rowAnswer` shifted left by
`scale - seedExponent` places. -/

/-- The shift amount: A.13.9's `2 ^ (arity+scale) / (|\mathcal E| * 2 ^ arity)`. -/
def shiftAmount (_spectrum : ExpanderSpectrumContract) (liveScale : ℕ) (target : ℕ → ℕ)
    (arity scale : ℕ) (factors : List (NormalizedSymmetricThresholdCircuit arity)) : ℕ :=
  scale - seedExponent ⟨arity, factors⟩ liveScale (target arity)

/-- The per-request denominator in closed form: `|\mathcal E| * 2 ^ q
= 2 ^ (seedExponent + arity)`, from `rowCount_eq_two_pow`
(`Proof/CaseAnalysis/FinalSupplierWidth.lean`). -/
theorem rowDenominator_eq_two_pow (spectrum : ExpanderSpectrumContract) (liveScale : ℕ)
    (target : ℕ → ℕ) (arity : ℕ)
    (factors : List (NormalizedSymmetricThresholdCircuit arity)) :
    rowDenominator (symmetricFourfoldRows spectrum liveScale target) arity factors
      = 2 ^ (seedExponent ⟨arity, factors⟩ liveScale (target arity) + arity) := by
  rw [rowDenominator, rowCount_eq_two_pow spectrum liveScale target ⟨arity, factors⟩,
    ← Nat.pow_add]

theorem answer_eq_shift (spectrum : ExpanderSpectrumContract) (liveScale : ℕ)
    (target : ℕ → ℕ) (arity scale : ℕ)
    (factors : List (NormalizedSymmetricThresholdCircuit arity))
    (hfit : seedExponent ⟨arity, factors⟩ liveScale (target arity) ≤ scale) :
    answer (symmetricFourfoldRows spectrum liveScale target) arity scale factors
      = rowAnswer (symmetricFourfoldRows spectrum liveScale target) arity factors
          * 2 ^ shiftAmount spectrum liveScale target arity scale factors := by
  have hrow := rowDenominator_eq_two_pow spectrum liveScale target arity factors
  have hsplit : denominator arity scale
      = 2 ^ (seedExponent ⟨arity, factors⟩ liveScale (target arity) + arity)
        * 2 ^ shiftAmount spectrum liveScale target arity scale factors := by
    rw [denominator, shiftAmount, ← Nat.pow_add]
    congr 1
    omega
  have hpos : 0 < (2 : ℕ) ^ (seedExponent ⟨arity, factors⟩ liveScale (target arity) + arity) :=
    Nat.two_pow_pos _
  show rowAnswer (symmetricFourfoldRows spectrum liveScale target) arity factors
      * denominator arity scale
      / rowDenominator (symmetricFourfoldRows spectrum liveScale target) arity factors = _
  rw [hrow, hsplit, show rowAnswer (symmetricFourfoldRows spectrum liveScale target) arity factors
      * (2 ^ (seedExponent ⟨arity, factors⟩ liveScale (target arity) + arity)
        * 2 ^ shiftAmount spectrum liveScale target arity scale factors)
      = 2 ^ (seedExponent ⟨arity, factors⟩ liveScale (target arity) + arity)
        * (rowAnswer (symmetricFourfoldRows spectrum liveScale target) arity factors
          * 2 ^ shiftAmount spectrum liveScale target arity scale factors) by ring,
    Nat.mul_div_cancel_left _ hpos]

/-- **The shifted answer fits in `arity + scale + 1` bits, with a bit to spare.**
This is `multiply_run`'s own `hfit` at the channel's arguments: `rowAnswer`
never exceeds A.13.9's denominator (`rowAnswer_le_rowDenominator`,
`Proof/CaseAnalysis/FinalSupplierWidth.lean`), so the product with the shift
word `powerBits` -- whose length is the shift amount PLUS ONE -- is below
`2 ^ (arity + scale + 1)`. -/
theorem answer_hfit (spectrum : ExpanderSpectrumContract) (liveScale : ℕ)
    (target : ℕ → ℕ) (arity scale w : ℕ)
    (factors : List (NormalizedSymmetricThresholdCircuit arity))
    (hfit : seedExponent ⟨arity, factors⟩ liveScale (target arity) ≤ scale)
    (hw : arity + scale + 2 ≤ w) :
    rowAnswer (symmetricFourfoldRows spectrum liveScale target) arity factors
        * 2 ^ (CompetitorDenominator.powerBits
            (shiftAmount spectrum liveScale target arity scale factors)).length
      < 2 ^ w := by
  have hlen : (CompetitorDenominator.powerBits
      (shiftAmount spectrum liveScale target arity scale factors)).length
      = shiftAmount spectrum liveScale target arity scale factors + 1 := by
    simp [CompetitorDenominator.powerBits]
  have hle := rowAnswer_le_rowDenominator (symmetricFourfoldRows spectrum liveScale target)
    arity factors
  rw [rowDenominator_eq_two_pow spectrum liveScale target arity factors] at hle
  have hmul : rowAnswer (symmetricFourfoldRows spectrum liveScale target) arity factors
      * 2 ^ (shiftAmount spectrum liveScale target arity scale factors + 1)
      ≤ 2 ^ (seedExponent ⟨arity, factors⟩ liveScale (target arity) + arity)
        * 2 ^ (shiftAmount spectrum liveScale target arity scale factors + 1) :=
    Nat.mul_le_mul_right _ hle
  have hpow : (2 : ℕ) ^ (seedExponent ⟨arity, factors⟩ liveScale (target arity) + arity)
      * 2 ^ (shiftAmount spectrum liveScale target arity scale factors + 1)
      = 2 ^ (arity + scale + 1) := by
    rw [← Nat.pow_add]
    congr 1
    unfold shiftAmount
    omega
  have hlt : (2 : ℕ) ^ (arity + scale + 1) < 2 ^ w :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [hlen]
  omega

/-! ## §2 The ROUTE-SIDE width floor

`entryWidth_floor_answer` (`Proof/CaseAnalysis/FinalSupplierWidth.lean`) is a
fact about `C10SupplierWidth.entryWidth`.  The live route's record width is
`entryWidthSchedule` (`Proof/CaseAnalysis/FinalPartsSchedule.lean`), a
DIFFERENT width, so that lemma is off-route.  These are the on-route versions,
and they carry the `+ 2` that §1's `answer_hfit` actually consumes. -/

/-- **The route-side answer floor.**  `entryWidthSchedule sources k r N =
thresholdFloor sources + (q(N)+1) ^ r`, so as soon as the answer channel's own
`arity + scale + 2` is under the SQUARE of `q(N)+1`, every schedule at `r >= 2`
carries it.  The threshold floor is pure slack. -/
theorem entryWidthSchedule_floor_answer (sources : RepairSource.EightSources) (k r N : ℕ)
    (arity scale : ℕ → ℕ) (hr : 2 ≤ r)
    (hbudget : arity N + scale N + 2 ≤ widthPower sources k 2 N) :
    arity N + scale N + 2 ≤ entryWidthSchedule sources k r N := by
  have hmono : widthPower sources k 2 N ≤ widthPower sources k r N := by
    unfold widthPower
    exact Nat.pow_le_pow_right (by omega) hr
  have hfloor : widthPower sources k r N ≤ entryWidthSchedule sources k r N := by
    unfold entryWidthSchedule
    omega
  omega

theorem entryWidthSchedule_floor_at_width (sources : RepairSource.EightSources) (k r degree N m : ℕ)
    (scale : ℕ → ℕ) (hr : 2 ≤ r) (hN : partsOnset sources k r degree ≤ N)
    (hm : m ≤ widthAt sources k N)
    (hscale : scale N ≤ widthAt sources k N * widthAt sources k N) :
    max (widthAt sources k N) m + scale N + 2 ≤ entryWidthSchedule sources k r N := by
  have hq : thresholdFloor sources + 2 ≤ widthAt sources k N :=
    width_ge_floor sources k r degree N hN
  have hmax : max (widthAt sources k N) m = widthAt sources k N := Nat.max_eq_left hm
  refine entryWidthSchedule_floor_answer sources k r N
    (fun n => max (widthAt sources k n) m) scale hr ?_
  have hsq : widthPower sources k 2 N
      = widthAt sources k N * widthAt sources k N + 2 * widthAt sources k N + 1 := by
    unfold widthPower
    ring
  rw [hmax, hsq]
  omega

/-- The multiplier's own budget at a power-of-two multiplier word. -/
def answerShiftFuel (w shift : ℕ) : ℕ :=
  HierarchyMultiplyEntry.budget w (CompetitorDenominator.powerBits shift)

theorem answerShiftFuel_eq (w shift : ℕ) :
    answerShiftFuel w shift = 128 * (w + 1) * (shift + 2) := by
  unfold answerShiftFuel HierarchyMultiplyEntry.budget
  simp [CompetitorDenominator.powerBits]

/-- **The binary multiplier, docked.**  Slot `0` carries the multiplier word,
slot `8` the multiplicand in binary at width `w`, slot `9` the paid width; the
other eleven slots start blank.  On exit slot `3` carries
`frame (binary w (a * value bits))`, the three input slots are restored, every
head is parked at `0` and every tape outside the slot map is untouched.  The
budget is `HierarchyMultiplyEntry.budget w bits` -- polynomial in the WIDTHS. -/
theorem multiply_dock {m : ℕ} (w a : ℕ) (bits : List Bool)
    (hfit : a * 2 ^ bits.length < 2 ^ w)
    (slots : Fin 14 → Fin m) (hinj : Function.Injective slots)
    (H : Fin m → ℕ) (A : Fin m → List Bool) (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = frame bits)
    (h8 : A (slots 8) = frame (binary w a))
    (h9 : A (slots 9) = List.replicate w true)
    (hblank : ∀ j : Fin 14, j.val ≠ 0 → j.val ≠ 8 → j.val ≠ 9 → A (slots j) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (RecoveryFocus.machine slots HierarchyMultiplyEntry.machine)
        (HierarchyMultiplyEntry.budget w bits) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 3) = frame (binary w (a * value bits)) ∧
      A' (slots 0) = frame bits ∧
      A' (slots 8) = frame (binary w a) ∧
      A' (slots 9) = List.replicate w true ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨rc, hrun, h3, hf0, hf8, hf9, _h12, hheads, hsteps⟩ :=
    HierarchyMultiplyEntry.multiply_run w a bits hfit
  have hstep : Step HierarchyMultiplyEntry.machine (HierarchyMultiplyEntry.budget w bits)
      (fun _ => 0) (HierarchyMultiplyEntry.input14 w a bits) (fun _ => 0) rc.final.tapes :=
    ⟨rc, hrun, funext hheads, rfl, hsteps⟩
  have hA : ∀ j : Fin 14, A (slots j) = HierarchyMultiplyEntry.input14 w a bits j := by
    intro j
    rw [CompetitorRationalProducts.input14_cases]
    by_cases e0 : j.val = 0
    · have hj : j = 0 := Fin.ext e0
      subst hj
      simpa using h0
    · by_cases e8 : j.val = 8
      · have hj : j = 8 := Fin.ext e8
        subst hj
        simpa using h8
      · by_cases e9 : j.val = 9
        · have hj : j = 9 := Fin.ext e9
          subst hj
          simpa using h9
        · rw [if_neg e0, if_neg e8, if_neg e9]
          exact hblank j e0 e8 e9
  have hdock := hstep.dock slots hinj H A (fun j => hH (slots j)) hA
  refine ⟨_, _, hdock, CloseoutFinalC10WordEngines.dockH_all_zero slots H hH, ?_, ?_, ?_, ?_, ?_⟩
  · exact (RecoveryRootRound.install_slot slots hinj A rc.final.tapes 3).trans h3
  · exact (RecoveryRootRound.install_slot slots hinj A rc.final.tapes 0).trans hf0
  · exact (RecoveryRootRound.install_slot slots hinj A rc.final.tapes 8).trans hf8
  · exact (RecoveryRootRound.install_slot slots hinj A rc.final.tapes 9).trans hf9
  · intro i hi
    exact RecoveryRootRound.install_other slots A rc.final.tapes i hi

/-! ## §4 The answer channel, on the C.10 bank, in BINARY

`round_step_of_dock` (`Proof/CaseAnalysis/FinalSupplierCountStage.lean`) lifts
any docked stage whose slots lie on the scratch band to a `Step` between two
banks.  `answer_bank_dock` (`Proof/CaseAnalysis/FinalSupplierCountStage.lean`)
is that at the UNARY `answer_dock`; this is that at the binary multiplier. -/

theorem answer_shift_bank_dock (extra : ℕ) (spectrum : ExpanderSpectrumContract)
    (liveScale : ℕ) (target : ℕ → ℕ) (arity scale w : ℕ)
    (factors : List (NormalizedSymmetricThresholdCircuit arity))
    (hfit : seedExponent ⟨arity, factors⟩ liveScale (target arity) ≤ scale)
    (hw : arity + scale + 2 ≤ w)
    (slots : Fin 14 → Fin (218 + (60 + extra))) (hinj : Function.Injective slots)
    (hband : ∀ j, 278 ≤ (slots j).val)
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (h0 : s (slots 0).val
      = frame (CompetitorDenominator.powerBits
          (shiftAmount spectrum liveScale target arity scale factors)))
    (h8 : s (slots 8).val
      = frame (binary w (rowAnswer (symmetricFourfoldRows spectrum liveScale target)
          arity factors)))
    (h9 : s (slots 9).val = List.replicate w true)
    (hblank : ∀ j : Fin 14, j.val ≠ 0 → j.val ≠ 8 → j.val ≠ 9 → s (slots j).val = []) :
    ∃ s' : ℕ → List Bool,
      Step (RecoveryFocus.machine slots HierarchyMultiplyEntry.machine)
        (answerShiftFuel w (shiftAmount spectrum liveScale target arity scale factors))
        (fun _ => 0) (bank stream count driver input witness s)
        (fun _ => 0) (bank stream count driver input witness s') ∧
      s' (slots 3).val
        = frame (binary w (answer (symmetricFourfoldRows spectrum liveScale target)
            arity scale factors)) := by
  have hA : ∀ j : Fin 14,
      bank stream count driver input witness s (slots j) = s (slots j).val :=
    fun j => bank_scratch_apply stream count driver input witness s (slots j) (hband j)
  obtain ⟨H', A', hstep, hzero, h3, _r0, _r8, _r9, hframe⟩ :=
    multiply_dock w (rowAnswer (symmetricFourfoldRows spectrum liveScale target) arity factors)
      (CompetitorDenominator.powerBits
        (shiftAmount spectrum liveScale target arity scale factors))
      (answer_hfit spectrum liveScale target arity scale w factors hfit hw)
      slots hinj (fun _ => 0) (bank stream count driver input witness s) (fun _ => rfl)
      ((hA 0).trans h0) ((hA 8).trans h8) ((hA 9).trans h9)
      (fun j e0 e8 e9 => (hA j).trans (hblank j e0 e8 e9))
  refine ⟨scratchOf extra A' s, ?_, ?_⟩
  · exact round_step_of_dock extra
      (answerShiftFuel w (shiftAmount spectrum liveScale target arity scale factors))
      stream count driver input witness s slots hband H' A' hstep hzero hframe
  · rw [scratchOf_apply extra A' s (slots 3), h3,
      CompetitorDenominator.power_value,
      ← answer_eq_shift spectrum liveScale target arity scale factors hfit]

/-- **§5.1 -- the channel's fuel is a FIXED POWER of `q(N)+1`.**  `paper.tex:1383-1385`'s
`q ^ {O(1)}`.  Compare `answerFuel` (`Proof/CaseAnalysis/FinalSupplierCountStage.lean`),
which is `Theta(2 ^ (2*arity))`. -/
theorem answerShiftFuel_le_widthPower (sources : RepairSource.EightSources) (k r degree N shift : ℕ)
    (hr : 1 ≤ r) (hN : partsOnset sources k r degree ≤ N)
    (hshift : shift + 2 ≤ widthPower sources k 2 N) :
    answerShiftFuel (entryWidthSchedule sources k r N) shift
      ≤ 256 * widthPower sources k (r + 2) N := by
  have hq : thresholdFloor sources + 2 ≤ widthAt sources k N :=
    width_ge_floor sources k r degree N hN
  have hqp : widthAt sources k N ≤ widthPower sources k r N := by
    unfold widthPower
    calc widthAt sources k N ≤ widthAt sources k N + 1 := Nat.le_succ _
      _ = (widthAt sources k N + 1) ^ 1 := (pow_one _).symm
      _ ≤ (widthAt sources k N + 1) ^ r := Nat.pow_le_pow_right (by omega) hr
  have hwidth : entryWidthSchedule sources k r N + 1 ≤ 2 * widthPower sources k r N := by
    unfold entryWidthSchedule
    omega
  have hsplit : widthPower sources k (r + 2) N
      = widthPower sources k r N * widthPower sources k 2 N := by
    unfold widthPower
    rw [← pow_add]
  rw [answerShiftFuel_eq, hsplit]
  calc 128 * (entryWidthSchedule sources k r N + 1) * (shift + 2)
      ≤ 128 * (2 * widthPower sources k r N) * (widthPower sources k 2 N) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hwidth) hshift
    _ = 256 * (widthPower sources k r N * widthPower sources k 2 N) := by ring

theorem answerShiftFuel_le_hotFuel (sources : RepairSource.EightSources) (k r degree : ℕ) (hr : 1 ≤ r)
    (shift : ℕ → ℕ) (hshift : ∀ N, shift N + 2 ≤ widthPower sources k 2 N) :
    ∃ onset : ℕ, ∀ N, onset ≤ N →
      answerShiftFuel (entryWidthSchedule sources k r N) (shift N)
        ≤ hotFuel sources k r degree N := by
  obtain ⟨onset0, honset0⟩ :=
    poly_polylog_le_polyFuel 0 (256 * widthConst sources k ^ (r + 2)) (r + 2) 1 1
      (le_refl 1) (by omega)
  refine ⟨max onset0 (repinOnset sources k r degree 1), fun N hN => ?_⟩
  have hN0 : onset0 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : repinOnset sources k r degree 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNp : partsOnset sources k r degree ≤ N :=
    le_trans (partsOnset_le_repinOnset sources k r degree 1) hN1
  have hstep1 := answerShiftFuel_le_widthPower sources k r degree N (shift N) hr hNp (hshift N)
  have hstep2 : 256 * widthPower sources k (r + 2) N
      ≤ 256 * (widthConst sources k ^ (r + 2) * logScale N ^ (r + 2)) :=
    Nat.mul_le_mul_left _ (widthPower_le_logScale sources k (r + 2) N)
  have hstep3 := honset0 N hN0
  have hstep4 := polyFuel_le_hotFuel sources k r degree 1 1 N (by omega) hN1
  have hre : (N + 1) ^ 0 * (256 * widthConst sources k ^ (r + 2) * logScale N ^ (r + 2))
      = 256 * (widthConst sources k ^ (r + 2) * logScale N ^ (r + 2)) := by ring
  rw [hre] at hstep3
  omega

end NearCubicWires.RepairOrdinary.CloseoutFinalC10AnswerShift
