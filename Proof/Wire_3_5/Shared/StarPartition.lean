import Proof.Wire_3_5.Shared.S0

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open NearCubicWires

abbrev SyndromeVec (s : ℕ) := Fin s → Fin 2

namespace StarParams
variable (P : StarParams)

theorem one_le_s : 1 ≤ P.s := by
  unfold s
  have h4 : 4 ≤ P.n / P.r := (Nat.le_div_iff_mul_le P.r_pos).mpr (by have := P.four_r_le_n; omega)
  exact Nat.le_log_of_pow_le (by norm_num) (by omega)

theorem b_pos : 0 < P.b := by
  have h := P.b_succ
  have : 2 ^ 1 ≤ 2 ^ P.s := Nat.pow_le_pow_right (by norm_num) P.one_le_s
  omega

theorem column_lt (i : Fin P.b) : i.val + 1 < 2 ^ P.s := by have := P.b_succ; omega

def column (i : Fin P.b) : SyndromeVec P.s := finFunctionFinEquiv.symm ⟨i.val + 1, P.column_lt i⟩

def syndrome (y : Fin P.b → Bool) : SyndromeVec P.s := ∑ i, if y i then P.column i else 0

def errorOf (σ : SyndromeVec P.s) (y : Fin P.b → Bool) : Option (Fin P.b) :=
  if P.syndrome y + σ = 0 then none
  else some ⟨(finFunctionFinEquiv (P.syndrome y + σ)).val - 1, by
    have := (finFunctionFinEquiv (P.syndrome y + σ)).isLt
    have := P.b_succ; have := P.b_pos; omega⟩

def blockBits (x : BitInput P.n) (j : Fin P.r) : Fin P.b → Bool := fun i => x (P.blockCoord j i)

abbrev Translation := Fin P.r → SyndromeVec P.s

def IsCenter (σ : P.Translation) (c : BitInput P.n) : Prop := ∀ j, P.syndrome (P.blockBits c j) = σ j

instance (σ : P.Translation) : DecidablePred (P.IsCenter σ) := fun c =>
  inferInstanceAs (Decidable (∀ j, P.syndrome (P.blockBits c j) = σ j))

def leftErrors (σ : P.Translation) (x : BitInput P.n) : P.Errors :=
  fun j => P.errorOf (σ (P.leftBlock j)) (P.blockBits x (P.leftBlock j))

/-- The right block errors `v` of the input `x` in the partition `σ`. -/
def rightErrors (σ : P.Translation) (x : BitInput P.n) : P.Errors :=
  fun j => P.errorOf (σ (P.rightBlock j)) (P.blockBits x (P.rightBlock j))

def center (σ : P.Translation) (x : BitInput P.n) : BitInput P.n :=
  xorInput (xorInput x (P.errorVector P.leftBlock (P.leftErrors σ x))) (P.errorVector P.rightBlock (P.rightErrors σ x))

def point (c : BitInput P.n) (u v : P.Errors) : BitInput P.n :=
  xorInput (xorInput c (P.errorVector P.leftBlock u)) (P.errorVector P.rightBlock v)

/-- A translation read from syndrome codes (block `j` gets the binary expansion of the `j`-th code modulo `2^s`),
the form in which a request's word carries it. -/
def translationOfCodes (codes : List ℕ) : P.Translation :=
  fun j => finFunctionFinEquiv.symm ⟨codes.getD j.val 0 % 2 ^ P.s, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

end StarParams

end NearCubicWires.WireExponent3_5.Shared
