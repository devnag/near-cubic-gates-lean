import Proof.Wire_3_5.BlockArith

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.RecoveryRootRound

/-- For `j < 2^w`, the `(w+1)`-bit counter is the `w`-bit string followed by a clear top bit. -/
theorem binary_succ_low (w j : ℕ) (hj : j < 2 ^ w) : binary (w + 1) j = binary w j ++ [false] := by
  induction w generalizing j with
  | zero =>
    have : j = 0 := by simpa using hj
    subst this
    rfl
  | succ w ih =>
    have hj' : j / 2 < 2 ^ w := by rw [pow_succ] at hj; omega
    have e : binary (w + 1 + 1) j = (j % 2 == 1) :: binary (w + 1) (j / 2) := rfl
    rw [e, ih (j / 2) hj']
    rfl

/-- The counter bank: `binary (w+1) j` and the increment's `w+1`-cell workspace. -/
def counterTapes (w j : ℕ) : Fin 2 → List Bool := ![binary (w + 1) j, List.replicate (w + 1) false]

/-- The layout of an enumeration cell: `t` user tapes, then the counter bank. -/
def enumTapes {t : ℕ} (D : Fin t → List Bool) (w j : ℕ) : Fin (t + 2) → List Bool :=
  Fin.addCases (m := t) (n := 2) (motive := fun _ => List Bool) D (counterTapes w j)

def enumHeads {t : ℕ} (H : Fin t → ℕ) : Fin (t + 2) → ℕ :=
  Fin.addCases (m := t) (n := 2) (motive := fun _ => ℕ) H (fun _ => 0)

/-- The counter bank's two tapes. -/
def counterSlots (t : ℕ) : Fin 2 → Fin (t + 2) := fun i => i.natAdd t

theorem counterSlots_injective (t : ℕ) : Function.Injective (counterSlots t) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [counterSlots] at this
  omega

/-- The counter increment, docked on the counter bank. -/
noncomputable def counterIncrement (t : ℕ) :=
  RecoveryFocus.machine (counterSlots t) (Rewind.machine BinaryIncrement.machine)

/-- A uniform enumeration body: the work machine on the enumeration layout. At every `j < 2^w` it runs
from the cell with user data `data j out` and counter `j` to the cell with user data
`data (j+1) (out ++ emit j)` and the counter unchanged. -/
structure EnumBody (t s w : ℕ) where
  work : Machine (t + 2) s
  cost : ℕ
  heads : Fin t → ℕ
  data : ℕ → List Bool → Fin t → List Bool
  emit : ℕ → List Bool
  step : ∀ j, j < 2 ^ w → ∀ out, Step work cost (enumHeads heads) (enumTapes (data j out) w j)
    (enumHeads heads) (enumTapes (data (j + 1) (out ++ emit j)) w j)

namespace EnumBody
variable {t s w : ℕ}

/-- The cell body: the work, then the increment. -/
noncomputable def body (B : EnumBody t s w) := Composition.machine B.work (counterIncrement t)

/-- The cost of one cell. -/
def cellCost (B : EnumBody t s w) : ℕ := B.cost + 1 + (2 * (w + 1) + 2)

theorem increment_step (w j : ℕ) (hj : j < 2 ^ w) :
    Step (Rewind.machine BinaryIncrement.machine) (2 * (w + 1) + 2) (fun _ => 0) (counterTapes w j)
      (fun _ => 0) (counterTapes w (j + 1)) := by
  have hj' : j + 1 < 2 ^ (w + 1) := by rw [pow_succ]; omega
  obtain ⟨hA, hH, hA', hH', _⟩ := incrementBlock_spec (w + 1) j hj'
  have h := (incrementBlock (w + 1) j hj').run
  rw [hA, hH, hA', hH'] at h
  exact h

theorem counter_heads {H : Fin t → ℕ} :
    dockH (counterSlots t) (enumHeads H) (fun _ => 0) = enumHeads H := by
  funext i
  refine Fin.addCases (m := t) (n := 2) (motive := fun i =>
    dockH (counterSlots t) (enumHeads H) (fun _ => 0) i = enumHeads H i) ?_ ?_ i
  · intro j
    exact dockH_other _ _ _ _ (fun k h => by
      have := congrArg Fin.val h
      simp [counterSlots] at this
      omega)
  · intro j
    change dockH (counterSlots t) (enumHeads H) (fun _ => 0) (counterSlots t j) = _
    rw [dockH_slot _ (counterSlots_injective t)]
    simp [enumHeads]

theorem counter_tapes (D : Fin t → List Bool) (j : ℕ) :
    install (counterSlots t) (enumTapes D w j) (counterTapes w (j + 1)) = enumTapes D w (j + 1) := by
  funext i
  refine Fin.addCases (m := t) (n := 2) (motive := fun i =>
    install (counterSlots t) (enumTapes D w j) (counterTapes w (j + 1)) i = enumTapes D w (j + 1) i) ?_ ?_ i
  · intro k
    rw [install_other _ _ _ _ (fun l h => by
      have := congrArg Fin.val h
      simp [counterSlots] at this
      omega)]
    simp [enumTapes]
  · intro k
    change install (counterSlots t) (enumTapes D w j) (counterTapes w (j + 1)) (counterSlots t k) = _
    rw [install_slot _ (counterSlots_injective t)]
    simp [enumTapes]

/-- One cell: the work at `j`, then the counter moves from `j` to `j+1`. -/
theorem cell (B : EnumBody t s w) (j : ℕ) (hj : j < 2 ^ w) (out : List Bool) :
    Step B.body B.cellCost (enumHeads B.heads) (enumTapes (B.data j out) w j)
      (enumHeads B.heads) (enumTapes (B.data (j + 1) (out ++ B.emit j)) w (j + 1)) := by
  have hinc := (increment_step w j hj).dock (counterSlots t) (counterSlots_injective t)
    (enumHeads B.heads) (enumTapes (B.data (j + 1) (out ++ B.emit j)) w j)
    (fun k => by simp [enumHeads, counterSlots])
    (fun k => by simp [enumTapes, counterSlots])
  rw [counter_heads, counter_tapes] at hinc
  exact Step.seq (B.step j hj out) hinc

/-- The enumeration as a bounded loop of cells over `j < 2^w`. -/
noncomputable def cells (B : EnumBody t s w) : Cells (t + 2) (s + 4) where
  body := B.body
  cost := B.cellCost
  bound := 2 ^ w
  source := fun j out => ⟨B.body.start, enumHeads B.heads, enumTapes (B.data j out) w j⟩
  emit := B.emit
  entry := fun _ _ _ => rfl
  step := fun j hj out => B.cell j hj out

/-- **The whole enumeration as one `Step`.** From iteration 0 (counter 0, the loop's own counter word
`CompareMachine.word (2^w)` with head 1), it reaches the data after all `2^w` strings, with output
`out ++ (List.range (2^w)).flatMap emit` and counter `2^w`. -/
theorem enumerate (B : EnumBody t s w) (out : List Bool) :
    Step (CloseoutRowsDegreeLoop.machine B.body) (2 ^ w * (B.cellCost + 3) + 3)
      (Fin.addCases (enumHeads B.heads) (fun _ : Fin 1 => 1))
      (Fin.addCases (enumTapes (B.data 0 out) w 0)
        (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word (2 ^ w)))
      (Fin.addCases (enumHeads B.heads) (fun _ : Fin 1 => 1))
      (Fin.addCases (enumTapes (B.data (2 ^ w) (out ++ (List.range (2 ^ w)).flatMap B.emit)) w (2 ^ w))
        (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word (2 ^ w))) :=
  B.cells.loopStep out

/-- The enumeration's cost is within any class whose exponent is at least `w`, given a body cost
`≤ c·q^a` (`a ≥ 1`) and `w + 1 ≤ q`. -/
theorem within {E : Envelope} {cls : BudgetClass} {q k psi : ℕ} (B : EnumBody t s w) (hq : 1 ≤ q)
    {c a : ℕ} (ha : 1 ≤ a) (hcost : B.cost ≤ c * q ^ a) (hw : w + 1 ≤ q)
    (he : w ≤ classExp E cls q k psi) (hd : a ≤ classDeg E cls) :
    Within E cls (c + 13) q k psi (2 ^ w * (B.cellCost + 3) + 3) := by
  have hqa : q ≤ q ^ a := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ a := Nat.pow_le_pow_right hq ha
  have hcell : B.cellCost ≤ (c + 7) * q ^ a := by
    unfold cellCost
    nlinarith
  exact Within.enumerate hq hcell he hd

end EnumBody

/-! ## Executable twin -/

/-- Enumerating the 2-bit strings and emitting each: the counter's low bits run through all strings. -/
theorem enumerate_twin :
    (List.range (2 ^ 2)).flatMap (binary 2) = [false, false, true, false, false, true, true, true] ∧
      binary 3 2 = binary 2 2 ++ [false] := by decide

end NearCubicWires.WireExponent3_5.Block
