import Proof.Wire_3_5.PrimAsmCellUnit
import Proof.MachineModel.BlockScrubEntry

/-! # PA (d), the writers' loop (base `Cells.ofScrub` over the unit machine)

The writer's loop runs the unit machine (`CellUnit.unitM`, embedded next to `e` workspace tapes) once per unit index
`j < bound`, scrubbing every tape but the request, the output and the counter between units (base
`Cells.ofScrub`: the scrub's capacity `R` above the unit's cost; `L = R + 2`). A unit starts at its blank cell state
(`CellState.blankCell`), padded to the scrub's cleared state (base `Scrub.cleared_entry`: empty streams, the register
tapes `regTape cap 0 = 0^(cap+1)` and the cell `[false]` are cleared tapes of length at most `R`).

* `loopH`, `loopA`: the loop's banks before unit `j`; `blank_H`, `blank_scratch`;
* **`loop_stage`**: from the decode spec at `j`, one unit as a loop stage (kept ports and the output head advanced);
* **`loopCells`**, **`loop_step`**: the whole loop as one `Step` (base `Cells.loopStep`), the output `flatMap emit`.

Paper quantity of the main type: the writer's output `(List.range bound).flatMap emit ++ [false]` (for the SYM writer
`SymFlat.symTape_flat`: C4's `BAT` word of the call). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.CellLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.PopPipe NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.CellUnit NearCubicWires.WireExponent3_5.PrimT.WalkBank

section Loop
variable (cap : ℕ)

/-- The cell layout's tape count. -/
abbrev TT (x : ℕ) : ℕ := LNS x + 2 + LNR

/-- The kept tapes of a cell: the request, the output, the counter. -/
def kept (x : ℕ) (i : Fin (TT x)) : Bool :=
  decide (i = sTape (sk x 0)) || decide (i = sTape (sk x 1)) || decide (i = sTape (sk x 2))

/-- The loop's scrubbed tapes: every cell tape but the kept ones; the workspace is kept. -/
def scrS (x e : ℕ) : Fin (TT x + e) → Bool := Fin.addCases (fun i => !kept x i) (fun _ => false)

/-- The loop's reset tapes: every head but the output's. -/
def scrReset (x e : ℕ) : Fin (TT x + e) → Bool := Fin.addCases (fun i => !decide (i = sTape (sk x 1))) (fun _ => true)

/-- The loop's heads after the output `out`. -/
def loopH (x e : ℕ) (out : List Bool) : Fin (TT x + e) → ℕ :=
  Fin.addCases (fun i => if i = sTape (sk x 1) then out.length else 0) (fun _ => 0)

/-- The loop's tapes before unit `j` after the output `out`: the kept ports of the blank cell, the rest cleared. -/
def loopA (x e R : ℕ) (w : List Bool) (Wk : Fin e → List Bool) (j : ℕ) (out : List Bool) :
    Fin (TT x + e) → List Bool :=
  Fin.addCases (fun i => if kept x i then (wenc cap (blankCell x w out j)).A i else List.replicate R false) Wk

theorem blank_H (x : ℕ) (w out : List Bool) (j : ℕ) :
    (wenc cap (blankCell x w out j)).H = fun i => if i = sTape (sk x 1) then out.length else 0 := by
  funext i
  rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [wenc_H_s]
    by_cases hs : s = sk x 1
    · subst hs
      rw [if_pos rfl]
      simp [blankCell]
    · rw [if_neg (fun h => hs (sTape_inj h))]
      simp [blankCell, hs]
  · rw [wenc_H_c, if_neg (fun h => sTape_ne_c _ h.symm)]
  · rw [wenc_H_r, if_neg (fun h => sTape_ne_r _ _ h.symm)]
    rfl

theorem blank_scratch (x : ℕ) (w out : List Bool) (j : ℕ) (i : Fin (TT x)) (hi : kept x i = false) :
    ∃ k, k ≤ cap + 1 ∧ (wenc cap (blankCell x w out j)).A i = List.replicate k false := by
  rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
  · have h0 : s ≠ sk x 0 := fun h => by subst h; simp [kept] at hi
    have h1 : s ≠ sk x 1 := fun h => by subst h; simp [kept] at hi
    have h2 : s ≠ sk x 2 := fun h => by subst h; simp [kept] at hi
    refine ⟨0, by omega, ?_⟩
    rw [wenc_A_s]
    simp [blankCell, h0, h1, h2]
  · exact ⟨1, by omega, by rw [wenc_A_c]; rfl⟩
  · refine ⟨cap + 1, le_rfl, ?_⟩
    rw [wenc_A_r]
    exact regTape_zero cap

/-- **One unit as a loop stage**: from the decode's spec at `j` (a `DecOK` state reached from the blank cell, the
request and counter kept, the unit's cost within `nU`), the embedded unit machine runs from the loop's bank before `j`
to a bank whose kept ports and output head are the loop's bank before `j + 1`. -/
theorem loop_stage (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) {e : ℕ} (R nU : ℕ) (w : List Bool)
    (Wk : Fin e → List Bool) (emit : ℕ → List Bool) (j : ℕ) (out : List Bool) (hcap : cap + 1 ≤ R)
    (hdec : ∃ σD m Bp, WExec cap decW (blankCell W.x w out j) σD m ∧ DecOK cap W σD out (emit j) Bp ∧
      σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧ σD.sh (sk W.x 2) = 0 ∧
      m + 1 + (Bp + 4) + 1 + (3 * j + 3) ≤ nU) :
    ∃ H' A', Step (TapeEmbedding.machine e (unitM W decW)) nU (loopH W.x e out) (loopA cap W.x e R w Wk j out) H' A' ∧
      (∀ i, scrS W.x e i = false → A' i = loopA cap W.x e R w Wk (j + 1) (out ++ emit j) i) ∧
      (∀ i, scrReset W.x e i = false → H' i = loopH W.x e (out ++ emit j) i) := by
  obtain ⟨σD, m, Bp, hd, hok, hIN, hC, hCh, hn⟩ := hdec
  obtain ⟨σE, sU, e0, e1, e1h, e2⟩ := unit_step cap W decW (blankCell W.x w out j) σD m j Bp out (emit j) w hd hok hIN
    hC hCh
  have c := Scrub.cleared_entry sU (fun i => !kept W.x i) R (fun i hi => by
    obtain ⟨k, hk, he⟩ := blank_scratch cap W.x w out j i (by simpa using hi)
    exact ⟨k, by omega, he⟩)
  have ce := (c.embed (fun _ : Fin e => 0) Wk).enlarge hn
  have eH : Fin.addCases (motive := fun _ => ℕ) (wenc cap (blankCell W.x w out j)).H (fun _ : Fin e => 0) =
      loopH W.x e out := by
    rw [blank_H]
    rfl
  have eA : Fin.addCases (motive := fun _ => List Bool)
      (Scrub.blank (fun i => !kept W.x i) (wenc cap (blankCell W.x w out j)).A R) Wk =
      loopA cap W.x e R w Wk j out := by
    unfold loopA
    congr 1
    funext i
    unfold Scrub.blank
    cases hk : kept W.x i <;> simp [hk]
  rw [eH, eA] at ce
  refine ⟨_, _, ce, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun a => ?_) (fun k => ?_) i
    · intro hi
      have hk : kept W.x a = true := by simpa [scrS] using hi
      simp only [Fin.addCases_left, loopA, hk, if_true, Bool.not_true, Bool.false_eq_true, if_false,
        ZeroPadding.pad_zero]
      have hk' := hk
      simp only [kept, Bool.or_eq_true, decide_eq_true_eq] at hk'
      rcases hk' with (rfl | rfl) | rfl
      · rw [wenc_A_s, wenc_A_s, e0, blankCell_st0]
      · rw [wenc_A_s, wenc_A_s, e1, blankCell_st1]
      · rw [wenc_A_s, wenc_A_s, e2, blankCell_st2]
    · intro _
      simp only [Fin.addCases_right, loopA]
  · intro i
    refine Fin.addCases (fun a => ?_) (fun k => ?_) i
    · intro hi
      have ha : a = sTape (sk W.x 1) := by simpa [scrReset] using hi
      subst ha
      simp only [Fin.addCases_left, loopH, if_true]
      rw [wenc_H_s, e1h]
    · intro hi
      simp [scrReset] at hi

/-- **The writer's loop** as base `Cells`: the embedded unit machine under the scrub, `bound` units. -/
noncomputable def loopCells (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) {e : ℕ} (R nU bound : ℕ) (w : List Bool)
    (Wk : Fin e → List Bool) (emit : ℕ → List Bool) (hcap : cap + 1 ≤ R) (hR : nU + 1 ≤ R)
    (hdec : ∀ j < bound, ∀ out : List Bool, ∃ σD m Bp, WExec cap decW (blankCell W.x w out j) σD m ∧
      DecOK cap W σD out (emit j) Bp ∧ σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧
      σD.sh (sk W.x 2) = 0 ∧ m + 1 + (Bp + 4) + 1 + (3 * j + 3) ≤ nU) :=
  Cells.ofScrub (TapeEmbedding.machine e (unitM W decW)) (scrReset W.x e) (scrS W.x e) R (R + 2) bound
    (fun _ out => loopH W.x e out) (fun j out => loopA cap W.x e R w Wk j out) emit
    (fun i => by
      refine Fin.addCases (fun a => ?_) (fun k => ?_) i
      · intro hi
        have hk : kept W.x a = false := by simpa [scrS] using hi
        have hne : a ≠ sTape (sk W.x 1) := fun h => by subst h; simp [kept] at hk
        simp [scrReset, hne]
      · intro hi
        simp [scrS] at hi)
    hR (by omega)
    (fun j _ out i => by
      refine Fin.addCases (fun a => ?_) (fun k => ?_) i
      · intro hi
        have hne : a ≠ sTape (sk W.x 1) := by simpa [scrReset] using hi
        simp [loopH, hne]
      · intro _
        simp [loopH])
    (fun j _ out i => by
      refine Fin.addCases (fun a => ?_) (fun k => ?_) i
      · intro hi
        have hk : kept W.x a = false := by simpa [scrS] using hi
        simp [loopA, hk]
      · intro hi
        simp [scrS] at hi)
    (fun j hj out => loop_stage cap W decW R nU w Wk emit j out hcap (hdec j hj out))

/-- **The writer's loop as one `Step`** (base `Cells.loopStep`): from the loop's bank before unit `0` (empty output)
and the counter `CompareMachine.word bound`, to the bank before unit `bound` after all units' emissions. -/
theorem loop_step (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) {e : ℕ} (R nU bound : ℕ) (w : List Bool)
    (Wk : Fin e → List Bool) (emit : ℕ → List Bool) (hcap : cap + 1 ≤ R) (hR : nU + 1 ≤ R)
    (hdec : ∀ j < bound, ∀ out : List Bool, ∃ σD m Bp, WExec cap decW (blankCell W.x w out j) σD m ∧
      DecOK cap W σD out (emit j) Bp ∧ σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧
      σD.sh (sk W.x 2) = 0 ∧ m + 1 + (Bp + 4) + 1 + (3 * j + 3) ≤ nU) :
    Step (CloseoutRowsDegreeLoop.machine (Scrub.machine (TapeEmbedding.machine e (unitM W decW)) (scrReset W.x e)
        (scrS W.x e)))
      (bound * ((2 * nU + 2 + 1 + (2 * R + 4)) + 3) + 3)
      (Fin.addCases (Scrub.heads (loopH W.x e [])) (fun _ : Fin 1 => 1))
      (Fin.addCases (Scrub.bank (loopA cap W.x e R w Wk 0 []) R (R + 2))
        (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word bound))
      (Fin.addCases (Scrub.heads (loopH W.x e ([] ++ (List.range bound).flatMap emit))) (fun _ : Fin 1 => 1))
      (Fin.addCases (Scrub.bank (loopA cap W.x e R w Wk bound ([] ++ (List.range bound).flatMap emit)) R (R + 2))
        (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word bound)) :=
  Cells.loopStep (loopCells cap W decW R nU bound w Wk emit hcap hR hdec) []

end Loop

end NearCubicWires.WireExponent3_5.PrimAsm.CellLoop
