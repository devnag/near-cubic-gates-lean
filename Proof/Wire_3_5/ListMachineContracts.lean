import Proof.Wire_3_5.ListMachineNormal
import Proof.Wire_3_5.Contracts

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Machine
open NearCubicWires.WireExponent3_5.ListMachine.Ref Finset

/-- The finite list description the C2d machine reads (the nested hash as its level-membership table). -/
structure ListTable where
  /-- the states are `P_0, …, P_M` -/
  M : ℕ
  /-- the depth `J` -/
  J : ℕ
  /-- the population: coordinates `Z_0, …, Z_{L−1}` -/
  L : ℕ
  /-- the windows `W_0, …, W_{J−1}` -/
  windows : List ℕ
  /-- `cells[j][i]`: coordinate `i` lies in `𝓛_j` (`j ≤ J`) -/
  cells : List (List Bool)

namespace ListTable
variable (T : ListTable)

/-- The list data the table describes. -/
def data : ListData := ⟨T.M, T.J, fun j => T.windows.getD j 1, fun j i => (T.cells.getD j []).getD i false⟩

/-- The paper's degree bound `Σ_{j<J}(H_j − 1)`. -/
def degreeBound : ℕ := ∑ j ∈ range T.J, (2 ^ T.data.ell j - 1)

/-- The admissible tables: a nested hash (`𝓛_{j+1} ⊆ 𝓛_j`). -/
def Nested : Prop := ∀ j i, T.data.inLevel (j + 1) i = true → T.data.inLevel j i = true

/-- **The reference output**: the reduced repaired states `P_0, …, P_M`. -/
def printed : List Poly := (List.range (T.M + 1)).map (stateRefN T.data T.L)

def Correct (out : List Poly) : Prop :=
  out.length = T.M + 1 ∧ ∀ s ≤ T.M,
    (∀ z : Fin T.L → Bool, bitF2 (F2Poly.eval (out.getD s []) (ext z)) = T.data.listStates (List.ofFn z) s) ∧
    DegLe (out.getD s []) T.degreeBound ∧ AtomsLt (out.getD s []) T.L ∧
    (out.getD s []).length ≤ (T.L + 1) ^ T.degreeBound

/-- **The reference is correct** on every admissible table (the `Certified.err` field of `c2d`). -/
theorem printed_correct (hT : T.Nested) : T.Correct T.printed := by
  refine ⟨by simp [printed], fun s hs => ?_⟩
  have hget : T.printed.getD s [] = stateRefN T.data T.L s := by
    unfold printed
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  rw [hget]
  obtain ⟨h1, h2, h3⟩ := stateRefN_size T.data T.L s
  exact ⟨fun z => stateRefN_eval T.data hT T.L s z, h1, h2, h3⟩

end ListTable

/-! ## Tape encodings -/

/-- A natural number in unary, `1^n 0`. -/
def encodeNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- A list, its length first. -/
def encodeList {α : Type} (f : α → List Bool) (l : List α) : List Bool := encodeNat l.length ++ l.flatMap f

/-- The output tape: the printed states, each a list of monomials, each a list of coordinates. -/
def encodePolys (out : List Poly) : List Bool := encodeList (encodeList (encodeList encodeNat)) out

/-- The input tape: the table's fields in order. -/
def encodeTable (T : ListTable) : List Bool :=
  encodeNat T.M ++ encodeNat T.J ++ encodeNat T.L ++ encodeList encodeNat T.windows ++
    encodeList (encodeList fun b => [b]) T.cells

def c2d (E : Envelope) (psi : ListTable → ℕ) (coef : ℕ) : MachineContract E where
  Req := ListTable
  input := fun T => NearCubicWires.RepairOrdinary.frame (encodeTable T)
  pre := ListTable.Nested
  Out := List Poly
  ref := ListTable.printed
  encode := encodePolys
  cls := .preprocessing
  q := fun T => T.L
  k := fun _ => 0
  psi := psi
  coef := coef
  errSpec := fun T out => T.Correct out

/-- The error half of `Certified (c2d E psi coef)`: the reference meets the contract's error field. -/
theorem c2d_err (E : Envelope) (psi : ListTable → ℕ) (coef : ℕ) :
    ∀ T, (c2d E psi coef).pre T → (c2d E psi coef).errSpec T ((c2d E psi coef).ref T) :=
  fun T hT => T.printed_correct hT

end NearCubicWires.WireExponent3_5.ListMachine
