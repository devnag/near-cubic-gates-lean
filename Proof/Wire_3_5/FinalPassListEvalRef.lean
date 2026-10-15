import Mathlib

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ListEval

/-- `1^n 0`. -/
def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]

def pow (W : ℕ) : ℕ := 2 ^ Nat.clog 2 (2 * W + 1)

theorem pow_pos (W : ℕ) : 0 < pow W := by unfold pow; positivity

/-- The count `Σ_i [row_i ∧ Z_i]` over the common prefix. -/
def hits : List Bool → List Bool → ℕ
  | a :: as, b :: bs => (if a && b then 1 else 0) + hits as bs
  | _, _ => 0

/-- The residue `x mod P` in `[0, P)`. -/
def cyc (P : ℕ) (x : ℤ) : ℕ := (x % (P : ℤ)).toNat

/-- One level of the followed state: from `s_{j+1}` to `s_j` with window `W`, counts `c_{j+1} = cp` and `c_j = c`. -/
def levelStep (M W cp c : ℕ) : Option ℕ → Option ℕ
  | none => none
  | some t =>
    if t ≤ M ∧ W ≤ 2 * t + cyc (pow W) ((c : ℤ) + W - 2 * cp) then some (2 * t + cyc (pow W) ((c : ℤ) + W - 2 * cp) - W)
    else none

/-- The windows with the dummy top record: `W'_J = 0`. -/
def topW (J : ℕ) (W : ℕ → ℕ) (j : ℕ) : ℕ := if j = J then 0 else W j

/-- The levels in processing order: `J, J−1, …, 0`. -/
def levels (J : ℕ) : List ℕ := (List.range (J + 1)).reverse

/-- The fold over the processed levels: the followed state and the last count. -/
def levelFold (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) (init : Option ℕ × ℕ)
    (js : List ℕ) : Option ℕ × ℕ :=
  js.foldl (fun acc j => (levelStep M (topW J W j) acc.2 (hits (row j) Z) acc.1, hits (row j) Z)) init

def reportRef (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) : ℕ :=
  match (levelFold M J W row Z (some 0, 0) (levels J)).1 with
  | some v => if v ≤ M then v else 0
  | none => 0

/-- One record of the table word. -/
def record (J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (j : ℕ) : List Bool :=
  true :: (unary (pow (topW J W j)) ++ unary (topW J W j) ++ row j)

/-- **The table word** read by stage 5: `M`, then the records of levels `J, …, 0`, then `false`. -/
def levelWord (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) : List Bool :=
  unary M ++ ((levels J).flatMap (record J W row)) ++ [false]

/-- The register capacity of the stage-5 machine for a table word and a point length. -/
def capOf (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (L : ℕ) : ℕ :=
  4 * ((levelWord M J W row).length + L + 1)

/-! ## Executable check -/

/-- A two-level table on three coordinates: `𝓛_0` all, `𝓛_1 = {0, 1}`, `𝓛_2 = ∅`, windows `2, 1`, `M = 5`. -/
def tinyRow : ℕ → List Bool
  | 0 => [true, true, true]
  | 1 => [true, true, false]
  | _ => [false, false, false]

def tinyW : ℕ → ℕ
  | 0 => 2
  | _ => 1

/-- All eight points of three coordinates. -/
def allZ : List (List Bool) := [[false, false, false], [true, false, false], [false, true, false], [true, true, false],
  [false, false, true], [true, false, true], [false, true, true], [true, true, true]]

/-- With `𝓛_2 = ∅` the report is the count `c_0` when it is at most `M`, and `0` (the repair) above `M`. -/
theorem tiny_reports :
    allZ.map (fun Z => reportRef 5 2 tinyW tinyRow Z) = [0, 1, 1, 2, 1, 2, 2, 3] ∧
      allZ.map (fun Z => reportRef 1 2 tinyW tinyRow Z) = [0, 1, 1, 0, 1, 0, 0, 0] := by decide

end NearCubicWires.WireExponent3_5.FinalPass.ListEval
