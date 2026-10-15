import Mathlib

namespace NearCubicWires.WireExponent3_5.JoinElimination
set_option autoImplicit false

/-! ## P1 -/

structure HalfScore where
  const : ℤ
  terms : List (ℤ × List ℕ × Bool)

def parityOf (z : ℕ) (mask : List ℕ) : Bool := mask.foldl (fun b i => xor b (z.testBit i)) false

def HalfScore.eval (h : HalfScore) (z : ℕ) : ℤ :=
  h.const + (h.terms.map (fun t => if xor (parityOf z t.2.1) t.2.2 then t.1 else 0)).sum

def joinBrute (a b : HalfScore) (dL dR : ℕ) : ℕ :=
  ((List.range (2 ^ dL)).map (fun zL =>
    ((List.range (2 ^ dR)).filter (fun zR => decide (a.eval zL + b.eval zR = 0))).length)).sum

/-- What sort + merge computes: Σ over distinct left values `v` of `#left(v) · #right(-v)`. -/
def joinByCounts (a b : HalfScore) (dL dR : ℕ) : ℕ :=
  let A := (List.range (2 ^ dL)).map a.eval
  let B := (List.range (2 ^ dR)).map (fun z => -b.eval z)
  (A.dedup.map (fun v => A.count v * B.count v)).sum

def pa : HalfScore := ⟨-1, [(2, [0, 1], false), (3, [2], false)]⟩
def pb : HalfScore := ⟨0, [(1, [0], true), (-2, [1, 2], false)]⟩

theorem pilot1_agree : joinBrute pa pb 3 3 = joinByCounts pa pb 3 3 := by decide
theorem pilot1_value : joinBrute pa pb 3 3 = 12 := by decide

/-! ## P2 -/

/-- Carry-less product of GF(2) polynomials (bit masks). -/
def clmul (x y : ℕ) (w : ℕ) : ℕ :=
  (List.range w).foldl (fun acc i => if y.testBit i then acc ^^^ (x <<< i) else acc) 0

/-- Reduction modulo a degree-`ℓ` modulus `p` (bit mask with bit `ℓ` set), for inputs below `2^(2ℓ)`. -/
def reduce (p ℓ x : ℕ) : ℕ :=
  (List.range ℓ).reverse.foldl (fun acc i => if acc.testBit (i + ℓ) then acc ^^^ (p <<< i) else acc) x

def fmul (p ℓ x y : ℕ) : ℕ := reduce p ℓ (clmul x y ℓ)

def fpow (p ℓ x : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => fmul p ℓ (fpow p ℓ x n) x

def gen (p ℓ twoH seed lam : ℕ) : ℕ :=
  (List.range twoH).foldl (fun acc i =>
    acc ^^^ fmul p ℓ ((seed >>> (i * ℓ)) % 2 ^ ℓ) (fpow p ℓ lam i)) 0

def proj (k v : ℕ) : ℕ := v % 2 ^ k

/-- Brute force: the fraction of completions of `prefix` (its low `plen` bits fixed) satisfying all
constraints, as (count, total). -/
def condProbBrute (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) : ℕ × ℕ :=
  let S := twoH * ℓ
  let rest := S - plen
  (((List.range (2 ^ rest)).filter (fun r =>
      let seed := pre % 2 ^ plen + (r <<< plen)
      cons.all (fun c => decide (proj k (gen p ℓ twoH seed c.1) = c.2)))).length, 2 ^ rest)

/-- One GF(2) row: variable bits (mask over the remaining seed bits) and the right-hand side. -/
abbrev Row := ℕ × Bool

def system (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) : List Row :=
  cons.flatMap (fun con => (List.range k).map (fun c =>
    let coeff : ℕ → Bool := fun j => (fmul p ℓ (2 ^ (j % ℓ)) (fpow p ℓ con.1 (j / ℓ))).testBit c
    let fixed := (List.range plen).foldl (fun acc j => xor acc (coeff j && pre.testBit j)) false
    let mask := (List.range (twoH * ℓ - plen)).foldl
      (fun acc j => if coeff (plen + j) then acc ||| (1 <<< j) else acc) 0
    (mask, xor (con.2.testBit c) fixed)))

/-- Gaussian elimination over GF(2): returns `(consistent, rank)`. -/
def gauss (nvars : ℕ) (rows : List Row) : Bool × ℕ :=
  let step := fun (st : List Row × ℕ) (col : ℕ) =>
    let (rs, rank) := st
    match rs.find? (fun r => r.1.testBit col) with
    | none => (rs, rank)
    | some piv =>
      let rs' := (rs.erase piv).map (fun r => if r.1.testBit col then (r.1 ^^^ piv.1, xor r.2 piv.2) else r)
      (rs', rank + 1)
  let (rest, rank) := (List.range nvars).foldl step (rows, 0)
  (rest.all (fun r => !(r.1 == 0 && r.2)), rank)

/-- Elimination form: probability `2^{-rank}` if consistent, else 0, as (count, total). -/
def condProbGauss (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) : ℕ × ℕ :=
  let rest := twoH * ℓ - plen
  let (ok, rank) := gauss rest (system p ℓ twoH k plen pre cons)
  (if ok then 2 ^ (rest - rank) else 0, 2 ^ rest)

/-- GF(16) with `x^4 + x + 1` (mask 19), `2h = 2` (pairwise), `k = 2`, empty prefix: two distinct
labels are independent and uniform, so `1/16` of the 256 seeds. -/
theorem pilot2_pairwise : condProbGauss 19 4 2 2 0 0 [(1, 1), (2, 2)] = (16, 256) := by decide
theorem pilot2_agree : condProbGauss 19 4 2 2 0 0 [(1, 1), (2, 2)] =
    condProbBrute 19 4 2 2 0 0 [(1, 1), (2, 2)] := by decide
/-- With a 3-bit prefix: a consistent case (4 of 32 completions), an inconsistent one (the prefix
forces `a0.0 = 1` against `a1.0 = 1`, `a0.0 ⊕ a1.0 = 1`), and three labels beyond pairwise. -/
theorem pilot2_prefix : condProbGauss 19 4 2 2 3 5 [(1, 1), (2, 2)] = (4, 32) := by decide
theorem pilot2_prefix_agree : condProbGauss 19 4 2 2 3 5 [(1, 1), (2, 2)] =
    condProbBrute 19 4 2 2 3 5 [(1, 1), (2, 2)] := by decide
theorem pilot2_inconsistent : condProbGauss 19 4 2 2 3 5 [(1, 3), (3, 1)] = (0, 32) := by decide
theorem pilot2_inconsistent_agree : condProbGauss 19 4 2 2 3 5 [(1, 3), (3, 1)] =
    condProbBrute 19 4 2 2 3 5 [(1, 3), (3, 1)] := by decide
theorem pilot2_three_agree : condProbGauss 19 4 2 2 3 5 [(1, 1), (2, 2), (3, 0)] =
    condProbBrute 19 4 2 2 3 5 [(1, 1), (2, 2), (3, 0)] := by decide

end NearCubicWires.WireExponent3_5.JoinElimination
