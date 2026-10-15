import Proof.SourceAssembly.SourceRequestTermSegC
import Proof.CaseAnalysis.RowsIntegerFields
import Proof.CaseAnalysis.WitnessNat
import Proof.CaseAnalysis.WitnessCoefficientRecord

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.TermCoef
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceRequest.TermSeg

/-! ## Layout on `Fin 543`
`0` the coefficient code; `1 + i` pair parser (149); `150` log; `151 + i` integer fields (203); `354` log;
`355 + i` natural decoder (178); `533` log; `534` resident `1^cw`; `535..537` / `538..540` the two normalizers' tapes 2–4;
`541` the record; `542` its rewind log. -/

def pS (i : Fin 149) : Fin 543 := ⟨1 + i.val, by omega⟩
def iS (i : Fin 203) : Fin 543 := ⟨151 + i.val, by omega⟩
def dS (i : Fin 178) : Fin 543 := ⟨355 + i.val, by omega⟩
def c1S : Fin 3 → Fin 543 := ![0, 2, 150]
def c3S : Fin 3 → Fin 543 := ![39, 151, 354]
def c5S : Fin 3 → Fin 543 := ![79, 355, 533]
def n1S : Fin 5 → Fin 543 := ![534, 345, 535, 536, 537]
def n2S : Fin 5 → Fin 543 := ![534, 529, 538, 539, 540]
def rS : Fin 6 → Fin 543 := ![168, 535, 538, 541, 537, 542]

theorem pS_inj : Function.Injective pS := by
  intro i j h; exact Fin.ext (by have := congrArg Fin.val h; simp only [pS] at this; omega)
theorem iS_inj : Function.Injective iS := by
  intro i j h; exact Fin.ext (by have := congrArg Fin.val h; simp only [iS] at this; omega)
theorem dS_inj : Function.Injective dS := by
  intro i j h; exact Fin.ext (by have := congrArg Fin.val h; simp only [dS] at this; omega)
theorem c1S_inj : Function.Injective c1S := by decide
theorem c3S_inj : Function.Injective c3S := by decide
theorem c5S_inj : Function.Injective c5S := by decide
theorem n1S_inj : Function.Injective n1S := by decide
theorem n2S_inj : Function.Injective n2S := by decide
theorem rS_inj : Function.Injective rS := by decide

theorem off {t : Nat} (slots : Fin t → Fin 543) (A : Fin 543 → List Bool) (T : Fin t → List Bool) (x : Fin 543)
    (h : ∀ j, (slots j).val ≠ x.val) : install slots A T x = A x :=
  install_other _ _ _ _ (fun j e => h j (congrArg Fin.val e))

def entry (a : List Bool) (cw : Nat) : Fin 543 → List Bool := fun x =>
  if x.val = 0 then frame a else if x.val = 1 then [false] else if x.val = 534 then List.replicate cw true else []

/-- The CoefficientRecord stage with its rewind log. -/
noncomputable def recordMachine := Rewind.machine CloseoutWitness.CoefficientRecord.machine

noncomputable def machine :=
  Composition.machine
   (Composition.machine
    (Composition.machine
     (Composition.machine
      (Composition.machine
       (Composition.machine
        (Composition.machine
         (Composition.machine (RecoveryFocus.machine c1S copyMachine)
          (RecoveryFocus.machine pS CloseoutWitness.PairHeader.machine))
         (RecoveryFocus.machine c3S copyMachine))
        (RecoveryFocus.machine iS CloseoutRowsIntegerFields.machine))
       (RecoveryFocus.machine c5S copyMachine))
      (RecoveryFocus.machine dS CloseoutWitness.NatCold.machine))
     (RecoveryFocus.machine n1S ClockNormalize.machine))
    (RecoveryFocus.machine n2S ClockNormalize.machine))
   (RecoveryFocus.machine rS recordMachine)

/-- The integer and natural code words of the coefficient code. -/
noncomputable def intW (a : List Bool) : List Bool := CloseoutWitness.PairHeader.codeWord a 0
noncomputable def natW (a : List Bool) : List Bool := CloseoutWitness.PairHeader.codeWord a 1
noncomputable def nb (a : List Bool) (cw : Nat) : List Bool :=
  ClockNormalize.resize cw (CloseoutWitness.BitFields.payload (RecoveryFixedUnpair.rightWord (intW a)))
noncomputable def db (a : List Bool) (cw : Nat) : List Bool :=
  ClockNormalize.resize cw (CloseoutWitness.BitFields.payload (natW a))

/-- The machine's word: sign bit, then the two normalized fields. -/
noncomputable def recordWord (a : List Bool) (cw : Nat) : List Bool :=
  CloseoutWitness.CoefficientRecord.produced (frame (RecoveryFixedUnpair.leftWord (intW a))) (nb a cw) (db a cw)

noncomputable def cost (a : List Bool) (cw : Nat) : Nat :=
  ((((((((2 * (2 * a.length + 1) + 2) + 1 + CloseoutWitness.PairHeader.budget a) + 1 +
    (2 * (2 * (intW a).length + 1) + 2)) + 1 + CloseoutRowsIntegerFields.budget (intW a)) + 1 +
    (2 * (2 * (natW a).length + 1) + 2)) + 1 + CloseoutWitness.NatCold.budget (natW a)) + 1 +
    (4 * cw + 4)) + 1 + (4 * cw + 4)) + 1 +
    (2 * CloseoutWitness.CoefficientRecord.budget (nb a cw) (db a cw) + 2)

theorem entry_fresh (a : List Bool) (cw : Nat) (x : Fin 543) (h0 : x.val ≠ 0) (h1 : x.val ≠ 1) (h2 : x.val ≠ 534) :
    entry a cw x = [] := by
  unfold entry; rw [if_neg h0, if_neg h1, if_neg h2]

theorem intInput_eq (w : List Bool) (i : Fin 203) :
    CloseoutRowsIntegerFields.input w i = if i.val = 0 then frame w else [] := by
  by_cases h : i.val < 21
  · have e : i = Fin.castAdd 182 (⟨i.val, h⟩ : Fin 21) := Fin.ext rfl
    rw [e, CloseoutRowsIntegerFields.input, Fin.addCases_left]
    rfl
  · have e : i = Fin.natAdd 21 (⟨i.val - 21, by omega⟩ : Fin 182) := Fin.ext (by simp; omega)
    rw [e, CloseoutRowsIntegerFields.input, Fin.addCases_right]
    simp

theorem natInput_eq (w : List Bool) (i : Fin 178) :
    CloseoutWitness.NatCold.input w i = if i.val = 0 then frame w else [] := by
  by_cases h : i.val < 174
  · have e : i = Fin.castAdd 4 (⟨i.val, h⟩ : Fin 174) := Fin.ext rfl
    rw [e, CloseoutWitness.NatCold.input, Fin.addCases_left]
    rfl
  · have e : i = Fin.natAdd 174 (⟨i.val - 174, by omega⟩ : Fin 4) := Fin.ext (by simp; omega)
    rw [e, CloseoutWitness.NatCold.input, Fin.addCases_right]
    simp

theorem normInput_eq (cw : Nat) (w : List Bool) (i : Fin 5) :
    ClockNormalize.input cw w i =
      if i.val = 0 then List.replicate cw true else if i.val = 1 then frame w else [] := by
  fin_cases i <;> rfl

theorem coef_run (a : List Bool) (cw : Nat) : ∃ X : Fin 543 → List Bool,
    Step machine (cost a cw) (fun _ => 0) (entry a cw) (fun _ => 0) X ∧
    X 0 = frame a ∧ X 534 = List.replicate cw true ∧ X 541 = recordWord a cw := by
  -- 1. copy
  obtain ⟨l1, s1⟩ := copy_run a
  have d1 := dock s1 c1S c1S_inj (fun _ => 0) (entry a cw) (fun _ => rfl) (by intro i; fin_cases i <;> rfl)
  -- 2. pair parser
  have gh := stepOfReady (CloseoutWitness.PairHeader.header_run a).1
  have hA2 : ∀ i, install c1S (entry a cw) (copyOut a l1) (pS i) = CloseoutWitness.PairHeader.input a i := by
    intro i
    rw [TermSegB.pairInput_eq]
    by_cases h1 : i.val = 1
    · have e : pS i = c1S 1 := Fin.ext (by simp [pS, c1S]; omega)
      rw [e, install_slot _ c1S_inj, if_neg (by omega), if_pos h1]
      rfl
    · rw [off _ _ _ _ (by intro j; fin_cases j <;> simp [c1S, pS] <;> omega)]
      by_cases h0 : i.val = 0
      · rw [if_pos h0]
        unfold entry; simp only [pS]; rw [if_neg (by omega), if_pos (by omega)]; rfl
      · rw [if_neg h0, if_neg h1, entry_fresh _ _ _ (by simp [pS]) (by simp [pS]; omega) (by simp [pS]; omega)]
  have d2 := dock gh pS pS_inj (fun _ => 0) _ (fun _ => rfl) hA2
  have h38 := (CloseoutWitness.PairHeader.header_run a).2.2.1
  have h78 := (CloseoutWitness.PairHeader.header_run a).2.2.2
  -- facts after stage 2
  let B2 := install pS (install c1S (entry a cw) (copyOut a l1)) (CloseoutWitness.PairHeader.output a)
  have B2_39 : B2 39 = frame (intW a) := by
    show install pS _ _ (pS 38) = _; rw [install_slot _ pS_inj, h38]; rfl
  have B2_79 : B2 79 = frame (natW a) := by
    show install pS _ _ (pS 78) = _; rw [install_slot _ pS_inj, h78]; rfl
  have B2_hi : ∀ x : Fin 543, 151 ≤ x.val → x.val ≠ 534 → B2 x = [] := by
    intro x hx hx2
    show install pS _ _ x = _
    rw [off _ _ _ _ (by intro j; simp [pS]; omega), off _ _ _ _ (by intro j; fin_cases j <;> simp [c1S] <;> omega),
      entry_fresh _ _ _ (by omega) (by omega) hx2]
  have B2_534 : B2 534 = List.replicate cw true := by
    show install pS _ _ _ = _
    rw [off _ _ _ _ (by intro j; simp [pS]; omega), off _ _ _ _ (by intro j; fin_cases j <;> simp [c1S])]
    rfl
  have B2_0 : B2 0 = frame a := by
    show install pS _ _ _ = _
    rw [off _ _ _ _ (by intro j; simp [pS])]
    show install c1S _ _ (c1S 0) = _
    rw [install_slot _ c1S_inj]; rfl
  -- 3. copy the integer code
  obtain ⟨l3, s3⟩ := copy_run (intW a)
  have d3 := dock s3 c3S c3S_inj (fun _ => 0) B2 (fun _ => rfl) (by
    intro i; fin_cases i
    · exact B2_39
    · exact B2_hi 151 (by decide) (by decide)
    · exact B2_hi 354 (by decide) (by decide))
  let B3 := install c3S B2 (copyOut (intW a) l3)
  -- 4. integer fields
  obtain ⟨out4, ready4, h17, _, h174, _, _⟩ := CloseoutRowsIntegerFields.fields_run (intW a)
  have st4 := stepOfReady ready4
  have d4 := dock st4 iS iS_inj (fun _ => 0) B3 (fun _ => rfl) (by
    intro i
    rw [intInput_eq]
    by_cases h0 : i.val = 0
    · have e : iS i = c3S 1 := Fin.ext (by simp [iS, c3S]; omega)
      rw [if_pos h0, e]
      show install c3S _ _ (c3S 1) = _
      rw [install_slot _ c3S_inj]; rfl
    · rw [if_neg h0]
      show install c3S _ _ _ = _
      rw [off _ _ _ _ (by intro j; fin_cases j <;> simp [c3S, iS] <;> omega)]
      exact B2_hi _ (by simp [iS]) (by simp [iS]; omega))
  let B4 := install iS B3 out4
  have B4_168 : B4 168 = frame (RecoveryFixedUnpair.leftWord (intW a)) := by
    show install iS _ _ (iS 17) = _; rw [install_slot _ iS_inj, h17]
  have B4_345 : B4 345 = frame (CloseoutWitness.BitFields.payload (RecoveryFixedUnpair.rightWord (intW a))) := by
    show install iS _ _ (iS (CloseoutRowsIntegerFields.nativeSlots 174)) = _
    rw [install_slot _ iS_inj, h174]
  have B4_lo : ∀ x : Fin 543, (x.val < 151 ∨ 354 ≤ x.val) → B4 x = B3 x := by
    intro x hx; exact off _ _ _ _ (by intro j; simp [iS]; omega)
  -- 5. copy the natural code
  obtain ⟨l5, s5⟩ := copy_run (natW a)
  have B3_79 : B3 79 = frame (natW a) := by
    show install c3S _ _ _ = _; rw [off _ _ _ _ (by intro j; fin_cases j <;> simp [c3S])]; exact B2_79
  have B3_hi : ∀ x : Fin 543, 355 ≤ x.val → x.val ≠ 534 → B3 x = [] := by
    intro x hx hx2
    show install c3S _ _ _ = _
    rw [off _ _ _ _ (by intro j; fin_cases j <;> simp [c3S] <;> omega)]
    exact B2_hi x (by omega) hx2
  have d5 := dock s5 c5S c5S_inj (fun _ => 0) B4 (fun _ => rfl) (by
    intro i; fin_cases i
    · show B4 79 = _; rw [B4_lo _ (by decide), B3_79]; rfl
    · show B4 355 = _; rw [B4_lo _ (by decide), B3_hi _ (by decide) (by decide)]; rfl
    · show B4 533 = _; rw [B4_lo _ (by decide), B3_hi _ (by decide) (by decide)]; rfl)
  let B5 := install c5S B4 (copyOut (natW a) l5)
  -- 6. natural decoder
  obtain ⟨out6, ready6, h6, _, _, _⟩ := CloseoutWitness.NatCold.nat_run (natW a)
  have st6 := stepOfReady ready6
  have B5_hi : ∀ x : Fin 543, 356 ≤ x.val → x.val ≠ 533 → x.val ≠ 534 → B5 x = [] := by
    intro x hx hx1 hx2
    show install c5S _ _ _ = _
    rw [off _ _ _ _ (by intro j; fin_cases j <;> simp [c5S] <;> omega), B4_lo _ (by omega)]
    exact B3_hi x (by omega) hx2
  have d6 := dock st6 dS dS_inj (fun _ => 0) B5 (fun _ => rfl) (by
    intro i
    rw [natInput_eq]
    by_cases h0 : i.val = 0
    · have e : dS i = c5S 1 := Fin.ext (by simp [dS, c5S]; omega)
      rw [if_pos h0, e]
      show install c5S _ _ (c5S 1) = _
      rw [install_slot _ c5S_inj]; rfl
    · rw [if_neg h0]
      exact B5_hi _ (by simp [dS]; omega) (by simp [dS]; omega) (by simp [dS]; omega))
  let B6 := install dS B5 out6
  have B6_529 : B6 529 = frame (CloseoutWitness.BitFields.payload (natW a)) := by
    show install dS _ _ (dS 174) = _; rw [install_slot _ dS_inj, h6]
  have B6_out : ∀ x : Fin 543, (x.val < 355 ∨ 533 ≤ x.val) → B6 x = B5 x := by
    intro x hx; exact off _ _ _ _ (by intro j; simp [dS]; omega)
  have B5_out : ∀ x : Fin 543, (x.val ≠ 79 ∧ x.val ≠ 355 ∧ x.val ≠ 533) → B5 x = B4 x := by
    intro x hx; exact off _ _ _ _ (by intro j; fin_cases j <;> simp [c5S] <;> omega)
  -- 7. normalize the magnitude
  obtain ⟨r7, hr7, t70, _, t72, _, t74, hh7, _⟩ := ClockNormalize.normalize_run cw
    (CloseoutWitness.BitFields.payload (RecoveryFixedUnpair.rightWord (intW a)))
  have st7 : Step ClockNormalize.machine (4 * cw + 4) (fun _ => 0)
      (ClockNormalize.input cw (CloseoutWitness.BitFields.payload (RecoveryFixedUnpair.rightWord (intW a))))
      (fun _ => 0) r7.final.tapes := Step.of_run hr7 (funext hh7) rfl
  have B6_534 : B6 534 = List.replicate cw true := by
    rw [B6_out _ (by decide), B5_out _ (by decide), B4_lo _ (by decide)]
    show install c3S _ _ _ = _
    rw [off _ _ _ _ (by intro j; fin_cases j <;> simp [c3S])]; exact B2_534
  have B6_fresh : ∀ x : Fin 543, 535 ≤ x.val → B6 x = [] := by
    intro x hx
    rw [B6_out _ (by omega), B5_out _ (by omega), B4_lo _ (by omega)]
    exact B3_hi _ (by omega) (by omega)
  have d7 := dock st7 n1S n1S_inj (fun _ => 0) B6 (fun _ => rfl) (by
    intro i
    rw [normInput_eq]
    fin_cases i
    · exact B6_534
    · show B6 345 = _
      rw [B6_out _ (by decide), B5_out _ (by decide)]; exact B4_345
    · exact B6_fresh _ (by decide)
    · exact B6_fresh _ (by decide)
    · exact B6_fresh _ (by decide))
  let B7 := install n1S B6 r7.final.tapes
  -- 8. normalize the denominator
  obtain ⟨r8, hr8, t80, _, t82, _, _, hh8, _⟩ := ClockNormalize.normalize_run cw
    (CloseoutWitness.BitFields.payload (natW a))
  have st8 : Step ClockNormalize.machine (4 * cw + 4) (fun _ => 0)
      (ClockNormalize.input cw (CloseoutWitness.BitFields.payload (natW a))) (fun _ => 0) r8.final.tapes :=
    Step.of_run hr8 (funext hh8) rfl
  have B7_out : ∀ x : Fin 543, (x.val ≠ 534 ∧ x.val ≠ 345 ∧ x.val ≠ 535 ∧ x.val ≠ 536 ∧ x.val ≠ 537) →
      B7 x = B6 x := by
    intro x hx; exact off _ _ _ _ (by intro j; fin_cases j <;> simp [n1S] <;> omega)
  have d8 := dock st8 n2S n2S_inj (fun _ => 0) B7 (fun _ => rfl) (by
    intro i
    rw [normInput_eq]
    fin_cases i
    · show install n1S _ _ (n1S 0) = _; rw [install_slot _ n1S_inj, t70]; rfl
    · show B7 529 = _; rw [B7_out _ (by decide)]; exact B6_529
    · show B7 538 = _; rw [B7_out _ (by decide)]; exact B6_fresh _ (by decide)
    · show B7 539 = _; rw [B7_out _ (by decide)]; exact B6_fresh _ (by decide)
    · show B7 540 = _; rw [B7_out _ (by decide)]; exact B6_fresh _ (by decide))
  let B8 := install n2S B7 r8.final.tapes
  -- 9. the record
  have hnb : (nb a cw).length = cw := ClockNormalize.resize_length _ _
  have hdb : (db a cw).length = cw := ClockNormalize.resize_length _ _
  obtain ⟨r9, hr9, rs9, rh9, rt9⟩ := CloseoutWitness.CoefficientRecord.record_run (2 * cw + 1)
    (frame (RecoveryFixedUnpair.leftWord (intW a))) (nb a cw) (db a cw) [] (by omega) (by omega)
  have hz : CloseoutWitness.CoefficientRecord.heads [] = fun _ => 0 := by funext i; fin_cases i <;> rfl
  rw [hz] at hr9
  have st9 : Step CloseoutWitness.CoefficientRecord.machine
      (CloseoutWitness.CoefficientRecord.budget (nb a cw) (db a cw)) (fun _ => 0)
      (CloseoutWitness.CoefficientRecord.tapes (2 * cw + 1) (frame (RecoveryFixedUnpair.leftWord (intW a)))
        (nb a cw) (db a cw) []) r9.final.heads r9.final.tapes := ⟨r9, hr9, rfl, rfl, by omega⟩
  obtain ⟨l9, s9⟩ := rewound st9
  have B8_out : ∀ x : Fin 543, (x.val ≠ 534 ∧ x.val ≠ 529 ∧ x.val ≠ 538 ∧ x.val ≠ 539 ∧ x.val ≠ 540) →
      B8 x = B7 x := by
    intro x hx; exact off _ _ _ _ (by intro j; fin_cases j <;> simp [n2S] <;> omega)
  have hpad : ∀ w : List Bool, w.length = cw → ZeroPadding.pad (2 * cw + 1) (frame w) = frame w := by
    intro w hw
    simp [ZeroPadding.pad, frame_length, hw]
  have d9 := dock s9 rS rS_inj (fun _ => 0) B8 (fun _ => rfl) (by
    intro i
    fin_cases i
    · show B8 168 = _
      rw [B8_out _ (by decide), B7_out _ (by decide), B6_out _ (by decide), B5_out _ (by decide)]
      exact B4_168
    · show B8 535 = _
      rw [B8_out _ (by decide)]
      show install n1S _ _ (n1S 2) = _
      rw [install_slot _ n1S_inj, t72]
      show frame (nb a cw) = ZeroPadding.pad (2 * cw + 1) (frame (nb a cw))
      rw [hpad _ hnb]
    · show install n2S _ _ (n2S 2) = _
      rw [install_slot _ n2S_inj, t82]
      show frame (db a cw) = ZeroPadding.pad (2 * cw + 1) (frame (db a cw))
      rw [hpad _ hdb]
    · show B8 541 = _
      rw [B8_out _ (by decide), B7_out _ (by decide)]; exact B6_fresh _ (by decide)
    · show B8 537 = _
      rw [B8_out _ (by decide)]
      show install n1S _ _ (n1S 4) = _
      rw [install_slot _ n1S_inj, t74]
      rfl
    · show B8 542 = _
      rw [B8_out _ (by decide), B7_out _ (by decide)]; exact B6_fresh _ (by decide))
  have whole := ((((((((d1.seq d2).seq d3).seq d4).seq d5).seq d6).seq d7).seq d8).seq d9)
  refine ⟨_, whole, ?_, ?_, ?_⟩
  · show install rS B8 _ 0 = _
    rw [off _ _ _ _ (by intro j; fin_cases j <;> simp [rS]), B8_out _ (by decide), B7_out _ (by decide),
      B6_out _ (by decide), B5_out _ (by decide), B4_lo _ (by decide)]
    show install c3S _ _ _ = _
    rw [off _ _ _ _ (by intro j; fin_cases j <;> simp [c3S])]
    exact B2_0
  · show install rS B8 _ 534 = _
    rw [off _ _ _ _ (by intro j; fin_cases j <;> simp [rS])]
    show install n2S _ _ (n2S 0) = _
    rw [install_slot _ n2S_inj, t80]
  · show install rS B8 _ (rS 3) = _
    rw [install_slot _ rS_inj]
    show r9.final.tapes 3 = _
    rw [rt9]
    show [] ++ _ = _
    rfl

/-! ## The word is the compact coefficient record -/

open RadixSemantics CanonicalBinary CanonicalWitnessCodec in
/-- The fixed-width-unpair magnitude of a canonical integer code decodes to `|num|`. -/
theorem payload_of_int (I : List Bool) (num : ℤ) (h : value I = encodeInt num) :
    value (CloseoutWitness.BitFields.payload (RecoveryFixedUnpair.rightWord I)) = num.natAbs := by
  have hr : value (RecoveryFixedUnpair.rightWord I) = encodeNat num.natAbs := by
    unfold RecoveryFixedUnpair.rightWord
    rw [h]
    unfold encodeInt
    rw [Nat.unpair_pair]
    apply SignedSortKey.binary_value
    have hl := value_lt I
    rw [h] at hl
    unfold encodeInt at hl
    exact lt_of_le_of_lt (Nat.right_le_pair _ _) hl
  have hd : decodeNat (value (RecoveryFixedUnpair.rightWord I)) = some num.natAbs := by rw [hr, decodeNat_encode]
  have hp := CloseoutWitness.BitFields.decode_of_passes _
    ((CloseoutWitness.BitFields.passes_iff _).mpr (by rw [hd]; rfl))
  rw [hd] at hp
  exact (Option.some.inj hp).symm

open RadixSemantics CanonicalBinary in
theorem payload_of_nat (D : List Bool) (d : Nat) (h : value D = encodeNat d) :
    value (CloseoutWitness.BitFields.payload D) = d := by
  have hd : decodeNat (value D) = some d := by rw [h, decodeNat_encode]
  have hp := CloseoutWitness.BitFields.decode_of_passes _
    ((CloseoutWitness.BitFields.passes_iff _).mpr (by rw [hd]; rfl))
  rw [hd] at hp
  exact (Option.some.inj hp).symm

theorem resize_payload (cw : Nat) (p : List Bool) :
    ClockNormalize.resize cw p = SignedSortKey.binary cw (RadixSemantics.value p) := by
  conv_lhs => rw [← BoundedCounter.binary_of_value p]
  exact TermSegC.resize_binary_eq cw p.length _ (RadixSemantics.value_lt p)

open RadixSemantics CanonicalBinary CanonicalWitnessCodec in
/-- **The machine's word is `Product.record cw coef`** whenever the coefficient code decodes canonically. -/
theorem recordWord_eq (a : List Bool) (cw : Nat) (coef : ℚ) (hdec : decodeCanonicalRational (value a) = some coef) :
    recordWord a cw = CloseoutRowsEstimatorCoefficients.Product.record cw coef := by
  have henc := encodeCanonicalRational_of_decode hdec
  have hx := CloseoutWitness.PairHeader.extracted_values a (encodeInt coef.num) (encodeNat coef.den)
    (by rw [← henc]; rfl)
  obtain ⟨_, hI, hD⟩ := hx
  have hIv : value (intW a) = encodeInt coef.num := hI
  have hDv : value (natW a) = encodeNat coef.den := hD
  unfold recordWord CloseoutWitness.CoefficientRecord.produced CloseoutRowsEstimatorCoefficients.Product.record
  rw [nb, db, resize_payload, resize_payload, payload_of_int _ _ hIv, payload_of_nat _ _ hDv]
  congr 2
  -- the sign bit
  have hsign : readTapeBit (frame (RecoveryFixedUnpair.leftWord (intW a))) 1 = decide (coef.num < 0) := by
    unfold RecoveryFixedUnpair.leftWord
    rw [hIv]
    unfold encodeInt
    rw [Nat.unpair_pair]
    cases hw : (intW a).length with
    | zero =>
      have h0 : value (intW a) = 0 := by
        have := value_lt (intW a); rw [hw] at this; omega
      rw [hIv] at h0
      unfold encodeInt at h0
      have hs : (if coef.num < 0 then 1 else 0) = 0 := by
        have := Nat.left_le_pair (if coef.num < 0 then 1 else 0) (encodeNat coef.num.natAbs); omega
      by_cases hn : coef.num < 0
      · rw [if_pos hn] at hs; omega
      · rw [decide_eq_false hn]; rfl
    | succ k =>
      by_cases hn : coef.num < 0
      · rw [if_pos hn, decide_eq_true hn]; rfl
      · rw [if_neg hn, decide_eq_false hn]; rfl
  rw [hsign]

end NearCubicWires.SourceRequest.TermCoef

