import Proof.Wire_3_5.PrimTCarWM
import Proof.Wire_3_5.PrimTCarMask
import Proof.Wire_3_5.PrimTTabDock

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.CarStages
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.CarWM
open NearCubicWires.WireExponent3_5.PrimT.CarMask NearCubicWires.WireExponent3_5.FinalPass.Corner

/-! ## The crop -/

def σC (S K : List Bool) : WState 2 0 := ⟨fun _ => 0, ![S, K, []], fun r => r.elim0, false⟩

/-- The crop's entry bank: the atom stream, the cell, the counter, the empty input, the log. -/
def cropIn (S K : List Bool) : Fin 5 → List Bool :=
  Fin.addCases (m := 2 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σC S K)).A (fun _ => [])

theorem cropIn_val (S K : List Bool) (j : Fin 5) :
    cropIn S K j = if j.val = 0 then S else if j.val = 1 then [false] else if j.val = 2 then K else [] := by
  fin_cases j <;> rfl

theorem cropStage (W : ℕ) (ys : List (List Bool)) (hys : ∀ y ∈ ys, y.length = W) (tail : List Bool) (i : ℕ)
    (hi : i < ys.length) (rest : List Bool) : ∃ o : Fin 5 → List Bool,
    Step (Rewind.machine cropW.toProg.compile) (2 * cropCost i W + 2) (fun _ => 0)
      (cropIn (ys.flatMap frame ++ tail) (List.replicate i true ++ (false :: rest))) (fun _ => 0) o ∧
    o 0 = ys.flatMap frame ++ tail ∧ o 1 = [false] ∧ o 2 = List.replicate (i + 1) true ++ rest ∧
    o 3 = frame ys[i] := by
  set σ := σC (ys.flatMap frame ++ tail) (List.replicate i true ++ (false :: rest)) with hσ
  obtain ⟨τ, hw, e0, e1, e2, ec⟩ := cropW_spec 0 W ys hys tail i hi rest σ (fun _ => rfl) rfl rfl rfl
  obtain ⟨o, st, ho⟩ := wm_step 0 cropW σ τ _ hw (wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 5) = Fin.castAdd 1 (0 : Fin 4) from rfl, ho]; exact e0
  · rw [show (1 : Fin 5) = Fin.castAdd 1 (1 : Fin 4) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 5) = Fin.castAdd 1 (2 : Fin 4) from rfl, ho]; exact e1
  · rw [show (3 : Fin 5) = Fin.castAdd 1 (3 : Fin 4) from rfl, ho]; exact e2

/-! ## The append -/

def σA (N A : List Bool) : WState 1 0 := ⟨fun _ => 0, ![N, A], fun r => r.elim0, false⟩

/-- The append's entry bank: the native output, the cell, the accumulator, the log. -/
def appIn (N A : List Bool) : Fin 4 → List Bool :=
  Fin.addCases (m := 1 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σA N A)).A (fun _ => [])

theorem appIn_val (N A : List Bool) (j : Fin 4) :
    appIn N A j = if j.val = 0 then N else if j.val = 1 then [false] else if j.val = 2 then A else [] := by
  fin_cases j <;> rfl

theorem appendStage {n : ℕ} (G : List (NormalizedThresholdGate n)) (y rest : List Bool) : ∃ o : Fin 4 → List Bool,
    Step (Rewind.machine appendW.toProg.compile) (2 * appendCost G y + 2) (fun _ => 0)
      (appIn (frame y ++ rest) (accHdr ++ tabSeg G)) (fun _ => 0) o ∧
    o 0 = frame y ++ rest ∧ o 1 = [false] ∧ o 2 = accHdr ++ tabSeg G ++ frame y := by
  set σ := σA (frame y ++ rest) (accHdr ++ tabSeg G) with hσ
  obtain ⟨τ, hw, e0, e1, ec⟩ := appendW_spec 0 G y rest σ (fun _ => rfl) rfl rfl
  obtain ⟨o, st, ho⟩ := wm_step 0 appendW σ τ _ hw (wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 4) = Fin.castAdd 1 (0 : Fin 3) from rfl, ho]; exact e0
  · rw [show (1 : Fin 4) = Fin.castAdd 1 (1 : Fin 3) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 4) = Fin.castAdd 1 (2 : Fin 3) from rfl, ho]; exact e1

/-! ## The header -/

def σI : WState 0 0 := ⟨fun _ => 0, fun _ => [], fun r => r.elim0, false⟩

def initIn : Fin 3 → List Bool :=
  Fin.addCases (m := 0 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 σI).A (fun _ => [])

theorem initIn_val (j : Fin 3) : initIn j = if j.val = 1 then [false] else [] := by
  fin_cases j <;> rfl

theorem initStage : ∃ o : Fin 3 → List Bool,
    Step (Rewind.machine initW.toProg.compile) (2 * 15 + 2) (fun _ => 0) initIn (fun _ => 0) o ∧
    o 0 = accHdr ∧ o 1 = [false] := by
  obtain ⟨τ, hw, e0, ec⟩ := initW_spec 0 σI rfl rfl
  obtain ⟨o, st, ho⟩ := wm_step 0 initW σI τ _ hw (wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_⟩
  · rw [show (0 : Fin 3) = Fin.castAdd 1 (0 : Fin 2) from rfl, ho]; exact e0
  · rw [show (1 : Fin 3) = Fin.castAdd 1 (1 : Fin 2) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl

/-! ## The mask table -/

/-- Stream roles of the mask stage: `0` `A`, `1` `B`, `2` `1^n`, `3` the ruler, `4` the table, `5` `1^h`, `6` `C`,
`7` `D`. -/
def scM : Fin 6 ↪ Fin 8 := ⟨fun i => Fin.castLE (by omega) i, fun a b h => Fin.castLE_injective _ h⟩
def smM : Fin 5 ↪ Fin 8 := ⟨fun i => Fin.castLE (by omega) i, fun a b h => Fin.castLE_injective _ h⟩
def snM : Fin 5 ↪ Fin 8 := ⟨![6, 7, 2, 3, 4], by decide⟩
def rgM : Fin 3 ↪ Fin 3 := ⟨id, fun _ _ h => h⟩

/-- The last word stage: the unary width, then the mask table. -/
def mskW2 : WM 7 3 := .seq (onesW scM) (maskTableW smM snM rgM)

/-- The mask stage's entry: the four copies, `1^n`, the ruler, blank outputs, registers `0`. -/
def σM (seg : List Bool) (n h : ℕ) : WState 7 3 :=
  ⟨fun _ => 0, fun i => if i.val = 0 ∨ i.val = 1 ∨ i.val = 6 ∨ i.val = 7 then seg else if i.val = 2 then
    List.replicate n true else if i.val = 3 then false :: List.replicate h true else [], fun _ => 0, false⟩

def mskIn (cap : ℕ) (seg : List Bool) (n h : ℕ) : Fin 13 → List Bool :=
  Fin.addCases (m := 7 + 2 + 3) (n := 1) (motive := fun _ => List Bool) (wenc cap (σM seg n h)).A (fun _ => [])

theorem mskIn_val (cap : ℕ) (seg : List Bool) (n h : ℕ) (j : Fin 13) :
    mskIn cap seg n h j = if j.val = 0 ∨ j.val = 2 ∨ j.val = 7 ∨ j.val = 8 then seg else if j.val = 1 then [false]
      else if j.val = 3 then List.replicate n true else if j.val = 4 then false :: List.replicate h true
      else if 9 ≤ j.val ∧ j.val ≤ 11 then List.replicate (cap + 1) false else [] := by
  fin_cases j <;> simp [mskIn, σM, wenc, role, regTape] <;> rfl

def mskCost (n h m : ℕ) : ℕ := 10 * h + 7 + 1 + (m * (maskCost n h + 2) + 5)

theorem maskStage {n : ℕ} (cap h : ℕ) (X : List (NormalizedThresholdGate n)) (hok : ∀ g ∈ X, GateOk cap h g) :
    ∃ o : Fin 13 → List Bool,
    Step (Rewind.machine mskW2.toProg.compile) (2 * mskCost n h X.length + 2) (fun _ => 0)
      (mskIn cap (tabSeg X) n h) (fun _ => 0) o ∧
    o 3 = List.replicate n true ∧ o 5 = gatesW h (maskGates X) ∧ o 6 = List.replicate h true := by
  obtain ⟨τ1, s1, eO, -, eR, eRh, oth1, v1, c1⟩ := onesW_spec cap scM h (σM (tabSeg X) n h) (by simp [σM, scM])
    rfl rfl
  have hs1 : Std smM rgM τ1 h n := by
    have o2 := oth1 2 (by decide) (by decide); have o4 := oth1 4 (by decide) (by decide)
    refine ⟨?_, ?_, ?_, eRh, ?_, ?_, ?_, ?_⟩
    · show τ1.st 2 = _; rw [o2.1]; rfl
    · show τ1.sh 2 = _; rw [o2.2]; rfl
    · show τ1.st 3 = _; exact eR
    · show τ1.sh 4 = (τ1.st 4).length; rw [o4.1, o4.2]; rfl
    · show τ1.val 0 = 0; rw [v1]; rfl
    · show τ1.val 1 = 0; rw [v1]; rfl
    · show τ1.val 2 = 0; rw [v1]; rfl
  have o0 := oth1 0 (by decide) (by decide); have o1 := oth1 1 (by decide) (by decide)
  have o6 := oth1 6 (by decide) (by decide); have o7 := oth1 7 (by decide) (by decide)
  obtain ⟨τ, s2, eT, eA, eB, eC, eD, eN, eH, -, -, -, fr⟩ := maskTableW_spec cap smM snM rgM rfl rfl rfl
    (by decide) (by decide) (by decide) (by decide) h n X τ1 hs1
    (by show τ1.st 0 = _; rw [o0.1]; rfl) (by show τ1.sh 0 = _; rw [o0.2]; rfl)
    (by show τ1.st 1 = _; rw [o1.1]; rfl) (by show τ1.sh 1 = _; rw [o1.2]; rfl)
    (by show τ1.st 6 = _; rw [o6.1]; rfl) (by show τ1.sh 6 = _; rw [o6.2]; rfl)
    (by show τ1.st 7 = _; rw [o7.1]; rfl) (by show τ1.sh 7 = _; rw [o7.2]; rfl) hok
  have run : WExec cap mskW2 (σM (tabSeg X) n h) τ (mskCost n h X.length) :=
    WExec.mono (WExec.seq s1 s2) (by unfold mskCost; omega)
  obtain ⟨o, st, ho⟩ := wm_step cap mskW2 (σM (tabSeg X) n h) τ _ run
    (wenc_H_zero cap _ (fun _ => rfl) (fun _ => rfl))
  have o5 := fr.1 5 (by
    simp only [MaskS]; intro hh
    rcases hh with e | e | e | e | e | e | e <;> revert e <;> decide)
  have o4 := oth1 4 (by decide) (by decide)
  refine ⟨o, st, ?_, ?_, ?_⟩
  · rw [show (3 : Fin 13) = Fin.castAdd 1 (3 : Fin 12) from rfl, ho]; show τ.st 2 = _
    exact eN.trans hs1.1
  · rw [show (5 : Fin 13) = Fin.castAdd 1 (5 : Fin 12) from rfl, ho]; show τ.st 4 = _
    have e4 : τ.st 4 = τ1.st 4 ++ gatesW h (maskGates X) := eT
    rw [e4, o4.1]; rfl
  · rw [show (6 : Fin 13) = Fin.castAdd 1 (6 : Fin 12) from rfl, ho]; show τ.st 5 = _
    rw [o5.1]; exact eO.trans (by simp [σM, scM])

end NearCubicWires.WireExponent3_5.PrimT.CarStages
