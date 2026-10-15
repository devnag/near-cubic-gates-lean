import Proof.Wire_3_5.PrimTCarStages
import Proof.Wire_3_5.PrimTCarGate

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.CarRound
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.CarWM
open NearCubicWires.WireExponent3_5.PrimT.CarStages
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## Readiness and Steps -/

theorem step_of_ready {t s : ℕ} {p : Machine t s} {b : ℕ} {inp out : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p b inp out) : Step p b (fun _ => 0) inp (fun _ => 0) out := by
  obtain ⟨r, hr, ht, hh, _⟩ := h
  exact Step.of_run hr (funext hh) ht

theorem ready_of_step {t s : ℕ} {p : Machine t s} {b : ℕ} {inp out : Fin t → List Bool}
    (h : Step p b (fun _ => 0) inp (fun _ => 0) out) : ClockJoin.ReadyRun p b inp out := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  exact ⟨r, hr, ht, fun i => congrFun hh i, hs⟩

theorem zeroH {t : ℕ} (sl : Fin t → Fin 1041) : dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
  dockH_existing sl _ _ (fun _ => rfl)

/-! ## The layout -/

def cellSlR : Fin 1 → Fin 1041 := fun _ => 3
def cropSlR : Fin 5 → Fin 1041 := ![0, 3, 1, 7, 4]
def gcSl (j : Fin 1035) : Fin 1041 := ⟨j.val + 6, by omega⟩
def appSlR : Fin 4 → Fin 1041 := ![1039, 3, 2, 5]

theorem cellSlR_inj : Function.Injective cellSlR := fun a b _ => Subsingleton.elim a b
theorem cropSlR_inj : Function.Injective cropSlR := by decide
theorem gcSl_inj : Function.Injective gcSl := fun a b h => Fin.ext (by have := congrArg Fin.val h; simp [gcSl] at this; omega)
theorem appSlR_inj : Function.Injective appSlR := by decide

noncomputable def cellR := RecoveryFocus.machine cellSlR cellM
noncomputable def cropR := RecoveryFocus.machine cropSlR (Rewind.machine cropW.toProg.compile)
noncomputable def gateR := RecoveryFocus.machine gcSl CarGate.gateM
noncomputable def appR := RecoveryFocus.machine appSlR (Rewind.machine appendW.toProg.compile)

/-- **The round's worker.** -/
noncomputable def worker := Composition.machine cellR (Composition.machine cropR (Composition.machine gateR appR))

/-- The round's entry: the atom stream, the counter, the accumulator; every other tape blank. -/
def roundIn (S K A : List Bool) : Fin 1041 → List Bool :=
  fun t => if t.val = 0 then S else if t.val = 1 then K else if t.val = 2 then A else []

theorem cropSlR_val (j : Fin 5) : (cropSlR j).val = [0, 3, 1, 7, 4].getD j.val 0 := by fin_cases j <;> rfl
theorem appSlR_val (j : Fin 4) : (appSlR j).val = [1039, 3, 2, 5].getD j.val 0 := by fin_cases j <;> rfl

theorem gcIn_val (bits : List Bool) (j : Fin 1035) :
    CloseoutRowsGateCold.input bits j = if j.val = 1 then frame bits else [] := by
  refine Fin.addCases (m := 998) (n := 37) (fun a => ?_) (fun b => ?_) j
  · simp only [CloseoutRowsGateCold.input, Fin.addCases_left, CloseoutRowsGateFields.input, Fin.val_castAdd]; rfl
  · simp only [CloseoutRowsGateCold.input, Fin.addCases_right, Fin.val_natAdd]
    rw [if_neg (by omega)]

/-! ## One round -/

/-- The atoms' raw words at width `W`. -/
def rawAtoms {n : ℕ} (W : ℕ) (X : List (NormalizedThresholdGate n)) : List (List Bool) :=
  X.map fun g => binary W (CarrierFormat.gateCode g)

/-- The round's fuel. -/
noncomputable def roundCost {n : ℕ} (W : ℕ) (X : List (NormalizedThresholdGate n)) (i : ℕ) (g : NormalizedThresholdGate n) :
    ℕ :=
  1 + 1 + ((2 * cropCost i W + 2) + 1 + (CloseoutRowsGateRawRun.budget (binary W (CarrierFormat.gateCode g)) + 1 +
    (2 * appendCost (X.take i) (tabGW g) + 2)))

/-- **One round**: atom `i`'s native word joins the accumulator; the counter advances; the atom stream is kept. -/
theorem round_run {n : ℕ} (W : ℕ) (X : List (NormalizedThresholdGate n))
    (hW : ∀ g ∈ X, CarrierFormat.gateCode g < 2 ^ W) (i : ℕ) (hi : i < X.length) (rest : List Bool) :
    ∃ out, ClockJoin.ReadyRun worker (roundCost W X i X[i])
        (roundIn ((rawAtoms W X).flatMap frame) (List.replicate i true ++ (false :: rest))
          (accHdr ++ tabSeg (X.take i))) out ∧
      out 0 = (rawAtoms W X).flatMap frame ∧ out 1 = List.replicate (i + 1) true ++ rest ∧
      out 2 = accHdr ++ tabSeg (X.take (i + 1)) := by
  set ys := rawAtoms W X with hys
  set S := ys.flatMap frame with hS
  set g := X[i] with hg
  have hys_len : ∀ y ∈ ys, y.length = W := by
    intro y hy; obtain ⟨g', -, rfl⟩ := List.mem_map.mp hy; exact binary_length _ _
  have hiy : i < ys.length := by simp [hys, rawAtoms, hi]
  have hyi : ys[i] = binary W (CarrierFormat.gateCode g) := by simp [hys, rawAtoms, hg]
  set B0 := roundIn S (List.replicate i true ++ (false :: rest)) (accHdr ++ tabSeg (X.take i)) with hB0
  -- 1: the cell
  have d1 := cell_step.dock cellSlR cellSlR_inj (fun _ => 0) B0 (fun _ => rfl) (fun _ => by simp [hB0, roundIn, cellSlR])
  rw [zeroH] at d1
  set B1 := install cellSlR B0 (fun _ => [false]) with hB1
  have b1 : ∀ t : Fin 1041, t.val ≠ 3 → B1 t = B0 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have b13 : B1 3 = [false] := install_slot cellSlR cellSlR_inj _ _ 0
  -- 2: the crop
  obtain ⟨o2, s2, c0, c1, c2, c3⟩ := cropStage W ys hys_len [] i hiy rest
  have d2 := s2.dock cropSlR cropSlR_inj (fun _ => 0) B1 (fun _ => rfl) (by
    intro j; rw [cropIn_val]
    fin_cases j
    · rw [show cropSlR ⟨0, by decide⟩ = (0 : Fin 1041) from rfl, b1 _ (by decide)]; simp [hB0, roundIn, hS]
    · rw [show cropSlR ⟨1, by decide⟩ = (3 : Fin 1041) from rfl, b13]; rfl
    · rw [show cropSlR ⟨2, by decide⟩ = (1 : Fin 1041) from rfl, b1 _ (by decide)]; simp [hB0, roundIn]
    · rw [show cropSlR ⟨3, by decide⟩ = (7 : Fin 1041) from rfl, b1 _ (by decide)]; simp [hB0, roundIn]
    · rw [show cropSlR ⟨4, by decide⟩ = (4 : Fin 1041) from rfl, b1 _ (by decide)]; simp [hB0, roundIn])
  rw [zeroH] at d2
  set B2 := install cropSlR B1 o2 with hB2
  have b2 : ∀ t : Fin 1041, (∀ j, (cropSlR j).val ≠ t.val) → B2 t = B1 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have b2hit : ∀ j, B2 (cropSlR j) = o2 j := fun j => install_slot _ cropSlR_inj _ _ _
  -- 3: the atom's worker
  set bits := binary W (CarrierFormat.gateCode g) with hbits
  have hgm : g ∈ X := List.getElem_mem hi
  obtain ⟨o3, r3, t3⟩ := CarGate.gate_run g bits (binary_value _ _ (hW g hgm))
  have d3 := (step_of_ready r3).dock gcSl gcSl_inj (fun _ => 0) B2 (fun _ => rfl) (by
    intro j; rw [gcIn_val]
    by_cases hj : j.val = 1
    · rw [if_pos hj, show gcSl j = cropSlR 3 from Fin.ext (by simp [gcSl, hj]; rfl), b2hit, c3, hyi]
    · rw [if_neg hj, b2 _ (by intro k; rw [cropSlR_val]; fin_cases k <;> simp [gcSl] <;> omega),
        b1 _ (by simp [gcSl])]
      simp only [hB0, roundIn, gcSl]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)])
  rw [zeroH] at d3
  set B3 := install gcSl B2 o3 with hB3
  have b3 : ∀ t : Fin 1041, t.val < 6 → B3 t = B2 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by have := congrArg Fin.val e; simp [gcSl] at this; omega)
  have b3N : B3 1039 = frame (tabGW g) := (install_slot gcSl gcSl_inj B2 o3 1033).trans t3
  -- 4: the append
  obtain ⟨o4, s4, a0, a1, a2⟩ := appendStage (X.take i) (tabGW g) []
  have d4 := s4.dock appSlR appSlR_inj (fun _ => 0) B3 (fun _ => rfl) (by
    intro j; rw [appIn_val]
    fin_cases j
    · show B3 1039 = _; rw [b3N]; simp
    · show B3 3 = _; rw [b3 _ (by decide), show (3 : Fin 1041) = cropSlR 1 from rfl, b2hit, c1]; rfl
    · show B3 2 = _; rw [b3 _ (by decide), b2 _ (by intro k; rw [cropSlR_val]; fin_cases k <;> decide),
        b1 _ (by decide)]; simp [hB0, roundIn]
    · show B3 5 = _; rw [b3 _ (by decide), b2 _ (by intro k; rw [cropSlR_val]; fin_cases k <;> decide),
        b1 _ (by decide)]; simp [hB0, roundIn])
  rw [zeroH] at d4
  set B4 := install appSlR B3 o4 with hB4
  have b4 : ∀ t : Fin 1041, (∀ j, (appSlR j).val ≠ t.val) → B4 t = B3 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have run := d1.seq (d2.seq (d3.seq d4))
  have run' : Step worker _ (fun _ => 0) B0 (fun _ => 0) B4 := run
  refine ⟨B4, ready_of_step (run'.enlarge (by unfold roundCost; exact le_refl _)), ?_, ?_, ?_⟩
  · rw [b4 _ (by intro k; rw [appSlR_val]; fin_cases k <;> decide), b3 _ (by decide),
      show (0 : Fin 1041) = cropSlR 0 from rfl, b2hit, c0, List.append_nil]
  · rw [b4 _ (by intro k; rw [appSlR_val]; fin_cases k <;> decide), b3 _ (by decide),
      show (1 : Fin 1041) = cropSlR 2 from rfl, b2hit, c2]
  · have e2 : B4 2 = o4 2 := install_slot appSlR appSlR_inj B3 o4 2
    rw [e2, a2, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, tabSeg_append]
    simp [tabSeg, hg]

end NearCubicWires.WireExponent3_5.PrimT.CarRound
