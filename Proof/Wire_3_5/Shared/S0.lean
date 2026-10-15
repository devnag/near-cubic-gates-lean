import Proof.Foundations.Semantics

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open NearCubicWires

structure StarParams where
  n : ℕ
  r : ℕ
  r_even : Even r
  two_le_r : 2 ≤ r
  four_r_le_n : 4 * r ≤ n

namespace StarParams
variable (P : StarParams)

def s : ℕ := Nat.log 2 (P.n / P.r + 1)

def b : ℕ := 2 ^ P.s - 1

def k : ℕ := P.r * P.s

theorem r_pos : 0 < P.r := lt_of_lt_of_le (by norm_num) P.two_le_r

theorem b_succ : P.b + 1 = 2 ^ P.s := by
  unfold b; have := Nat.one_le_two_pow (n := P.s); omega

theorem r_mul_b_le : P.r * P.b ≤ P.n := by
  have h1 : 2 ^ P.s ≤ P.n / P.r + 1 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
  have h2 : P.b ≤ P.n / P.r := by have := P.b_succ; omega
  calc P.r * P.b ≤ P.r * (P.n / P.r) := Nat.mul_le_mul_left _ h2
    _ ≤ P.n := Nat.mul_div_le P.n P.r

theorem n_add_r_lt : P.n + P.r < 2 * (P.b + 1) * P.r := by
  have h1 : P.n / P.r + 1 < 2 ^ (P.s + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : P.n < P.r * (P.n / P.r + 1) := by
    have := Nat.lt_mul_div_succ P.n P.r_pos; simpa [Nat.mul_comm] using this
  rw [P.b_succ]
  have h3 : P.r * (P.n / P.r + 1) + P.r ≤ P.r * 2 ^ (P.s + 1) := by
    have : P.n / P.r + 1 + 1 ≤ 2 ^ (P.s + 1) := h1
    calc P.r * (P.n / P.r + 1) + P.r = P.r * (P.n / P.r + 1 + 1) := by ring
      _ ≤ P.r * 2 ^ (P.s + 1) := Nat.mul_le_mul_left _ this
  have h4 : P.r * 2 ^ (P.s + 1) = 2 * 2 ^ P.s * P.r := by ring
  omega

def blockCoord (j : Fin P.r) (i : Fin P.b) : Fin P.n :=
  ⟨j.val * P.b + i.val, by
    have hj : j.val + 1 ≤ P.r := j.isLt
    have hb := P.r_mul_b_le
    have : j.val * P.b + i.val < (j.val + 1) * P.b := by
      have := i.isLt; nlinarith
    calc j.val * P.b + i.val < (j.val + 1) * P.b := this
      _ ≤ P.r * P.b := Nat.mul_le_mul_right _ hj
      _ ≤ P.n := hb⟩

def leftBlock (j : Fin (P.r / 2)) : Fin P.r := ⟨j.val, by have := j.isLt; omega⟩
def rightBlock (j : Fin (P.r / 2)) : Fin P.r :=
  ⟨P.r / 2 + j.val, by have := j.isLt; have := P.r_even; omega⟩

abbrev Errors := Fin (P.r / 2) → Option (Fin P.b)

def errorVector (side : Fin (P.r / 2) → Fin P.r) (e : P.Errors) : BitInput P.n :=
  fun x => decide (∃ j : Fin (P.r / 2), ∃ i : Fin P.b, e j = some i ∧ P.blockCoord (side j) i = x)

end StarParams

def xorInput {n : ℕ} (x y : BitInput n) : BitInput n := fun i => xor (x i) (y i)

/-- `0/1` as an integer. -/
def bitZ (b : Bool) : ℤ := if b then 1 else 0

def mixedDifference {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) : ℤ :=
  bitZ (T (xorInput (xorInput c u) v)) - bitZ (T (xorInput c u)) - bitZ (T (xorInput c v)) + bitZ (T c)

def residualPlus {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) : Bool := decide (mixedDifference T c u v = 1)
def residualMinus {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) : Bool := decide (mixedDifference T c u v = -1)

structure SeparatedEquation (ZL ZR : Type) where
  left : ZL → ℤ
  right : ZR → ℤ

def SeparatedEquation.holds {ZL ZR : Type} (E : SeparatedEquation ZL ZR) (zl : ZL) (zr : ZR) : Bool :=
  decide (E.left zl + E.right zr = 0)

abbrev SignedOccurrenceList (ZL ZR : Type) := List (ℤ × SeparatedEquation ZL ZR)

def SignedOccurrenceList.value {ZL ZR : Type} (S : SignedOccurrenceList ZL ZR) (zl : ZL) (zr : ZR) : ℤ :=
  (S.map fun p => p.1 * bitZ (p.2.holds zl zr)).sum

abbrev F2Poly (Atom : Type) := List (List Atom)

def F2Poly.eval {Atom : Type} (p : F2Poly Atom) (ρ : Atom → Bool) : Bool :=
  p.foldl (fun acc m => xor acc (m.all ρ)) false

def F2Poly.degree {Atom : Type} (p : F2Poly Atom) : ℕ := (p.map List.length).foldl max 0

abbrev IntExpression (Atom : Type) := List (ℤ × List (F2Poly Atom))

def IntExpression.eval {Atom : Type} (V : IntExpression Atom) (ρ : Atom → Bool) : ℤ :=
  (V.map fun t => t.1 * (t.2.map fun p => bitZ (p.eval ρ)).prod).sum

def IntExpression.termCount {Atom : Type} (V : IntExpression Atom) : ℕ := V.length
def IntExpression.maxFactors {Atom : Type} (V : IntExpression Atom) : ℕ := (V.map fun t => t.2.length).foldl max 0
def IntExpression.maxDegree {Atom : Type} (V : IntExpression Atom) : ℕ :=
  (V.map fun t => (t.2.map F2Poly.degree).foldl max 0).foldl max 0

abbrev NamedFilter (Seed Input : Type) := Seed → Input → Bool

def callMask {Seed Input Name : Type} (filter : Name → NamedFilter Seed Input) (names : List Name)
    (e : Seed) (x : Input) : Bool :=
  names.all fun X => filter X e x

abbrev GF2Word (ℓ : ℕ) := Fin ℓ → Bool

abbrev PolyHashSeed (ℓ t : ℕ) := Fin t → GF2Word ℓ

abbrev SeedPrefix := List Bool

/-! ## Executable twins (P25) of two B items -/

/-- `ref` for `star:delta`: all four corners of one gate, evaluated directly. -/
def mixedDifferenceRef {n : ℕ} (g : NormalizedThresholdGate n) (c u v : BitInput n) : ℤ :=
  mixedDifference g.eval c u v

def decoderBit (delta W : ℤ) (h : ℕ) : Bool := Int.testBit (delta + W) h

def repairedList (M : ℕ) (c : List ℕ) (W : List ℕ) : List Bool :=
  let J := W.length
  let step : Option ℕ → ℕ → Option ℕ := fun child j =>
    match child with
    | none => none
    | some t =>
      let ell := Nat.clog 2 (2 * W.getD j 0 + 1)
      let H := 2 ^ ell
      let delta : ℤ := (c.getD j 0 : ℤ) - 2 * (c.getD (j+1) 0 : ℤ)
      let x : ℤ := (delta + W.getD j 0) % (H : ℤ)
      let d : ℤ := x - W.getD j 0
      let s : ℤ := 2 * t + d
      if 0 ≤ s ∧ s ≤ M then some s.toNat else none
  let top := (List.range J).reverse.foldl step (some 0)
  let _ := c.getD J 0
  (List.range (M + 1)).map fun s =>
    match top with
    | none => decide (s = 0)
    | some t => decide (s = t)

def levelCounts (J : ℕ) (Z : List Bool) (labels : List ℕ) : List ℕ :=
  (List.range (J + 1)).map fun j =>
    ((List.zip Z labels).filter fun p => p.1 && labels.length > 0 && p.2 % 2 ^ j == 0).length

/-- One-hotness of the reference on every input of a tiny window, checked by `decide`
(the `P19` "test before prove" gate for B2). -/
theorem repairedList_oneHot_tiny :
    ∀ z : Fin 8, ∀ lab : Fin 64,
      let Z := [z.val.testBit 0, z.val.testBit 1, z.val.testBit 2]
      let labels := [lab.val % 4, (lab.val / 4) % 4, (lab.val / 16) % 4]
      ((repairedList 3 (levelCounts 2 Z labels) [1, 1]).filter id).length = 1 := by
  decide

end NearCubicWires.WireExponent3_5.Shared
