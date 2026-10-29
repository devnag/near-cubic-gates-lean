import Proof.Gates.Interfaces.Counter
import Proof.Gates.Counter.Params
import Proof.Gates.CountingCore
import Proof.Gates.ScoreBox
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ModEq

/-!
# Counter module 2/9 — the pure counter (`sec:algorithm`: witnesses, tables, reconstruction in a cell) and the witness codec

Parts: `counterOnCall` (admission guard, `W = 0` branch, parameters, witness decoding, eq:output); the codec
`encodeWitness`/`decodeWitness` with `decode_encode` and `encodeWitness_length`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open scoped BigOperators
open NearCubicGates NearCubicGates.Close.Interfaces NearCubicWires

/-! ## Roles, header, lookups -/

/-- Number of scores reconstructed jointly: two for a pair call, one otherwise. -/
def roleCount : CallKind → ℕ
  | .pair => 2
  | _ => 1

theorem roleCount_pos (κ : CallKind) : 0 < roleCount κ := by cases κ <;> decide

abbrev Role (c : Call) := Fin (roleCount c.kind)

/-- Circuit of role `r`: `C¹` for role 0, `C²` otherwise. -/
def circ (c : Call) (r : ℕ) : NCircuit c.n := if r = 0 then c.first else c.second

/-- The public header of a call. -/
def header (c : Call) : Header := ⟨c.n, c.W, decide (c.kind = .pair), c.radius⟩

/-- `f^r(s)`: the table entry at score `s` (the same lookup as `NCircuit.eval`). -/
def topLookup {n : ℕ} (C : NCircuit n) (s : ℤ) : Bool := C.table.getD (s + C.topWeight).toNat false

theorem eval_eq_topLookup {n : ℕ} (C : NCircuit n) (z : BitInput n) : C.eval z = topLookup C (C.score z) := rfl

def coord0 {c : Call} (u : Role c → ℤ) : ℤ := u ⟨0, roleCount_pos c.kind⟩
def coord1 {c : Call} (u : Role c → ℤ) : ℤ := if h : 1 < roleCount c.kind then u ⟨1, h⟩ else 0

/-- The requested Boolean predicate on a score vector (`sec:algorithm`, "Reconstruction inside a certified cell");
`outerParity` is
`PAR_{Σ∖I}(y) ⊕ b` for a parity call and ignored otherwise. -/
def scorePredicate (c : Call) (outerParity : Bool) (u : Role c → ℤ) : Bool :=
  match c.kind with
  | .single => topLookup c.first (coord0 u)
  | .pair => xor (topLookup c.first (coord0 u)) (topLookup c.second (coord1 u))
  | .parity => xor (topLookup c.first (coord0 u)) outerParity

/-! ## The `W = 0` branch -/

/-- The parity's effective coordinates: indices below `n` occurring an odd number of times. -/
def oddIndices (c : Call) : List ℕ := (List.range c.n).filter fun i => c.parity.count i % 2 = 1

/-- Exact value when `W = 0` (`sec:finite`): both circuits are constant, a nonempty parity has probability 1/2. -/
def zeroWeightValue (c : Call) : ℚ × ℚ :=
  let t1 := topLookup c.first 0
  let t2 := topLookup c.second 0
  match c.kind with
  | .single => (if t1 then 1 else 0, 0)
  | .pair => (if xor t1 t2 then 1 else 0, 0)
  | .parity => if oddIndices c = [] then (if t1 then 1 else 0, 0) else (1 / 2, 0)

/-! ## The witness codec (`sec:algorithm`, "Witnesses and the tables to be computed") -/

/-- Little-endian value of a bit list. -/
def bitsValue : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * bitsValue bs

/-- Little-endian bits of `v` of the given width. -/
def bitsOf : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, v => (v % 2 == 1) :: bitsOf w (v / 2)

/-- Read consecutive fields of the given widths; missing bits are zeros (`sec:algorithm`,
"Witnesses and the tables to be computed"). Returns the values and the
unread bits. -/
def readBlock : List Bool → List ℕ → List ℕ × List Bool
  | bits, [] => ([], bits)
  | bits, wd :: ws => ((bitsValue (bits.take wd)) :: (readBlock (bits.drop wd) ws).1,
      (readBlock (bits.drop wd) ws).2)

/-- Read consecutive blocks of fields. -/
def readSegments : List Bool → List (List ℕ) → List (List ℕ) × List Bool
  | bits, [] => ([], bits)
  | bits, seg :: segs => ((readBlock bits seg).1 :: (readSegments (readBlock bits seg).2 segs).1,
      (readSegments (readBlock bits seg).2 segs).2)

/-- Write consecutive fields of the given widths and values. -/
def writeBlock (ws vs : List ℕ) : List Bool := (ws.zip vs).flatMap fun f => bitsOf f.1 f.2

/-- Offset width `⌈lg(2|a|+1)⌉` of the coefficient field of a gate with top weight `a`. -/
def coefWidth (a : ℤ) : ℕ := Nat.clog 2 (2 * a.natAbs + 1)

/-- The position of the block of stage `s` (`K_{s+1}` of `sec:algorithm`) and role `r`. -/
def segmentIndex (c : Call) (s r : ℕ) : ℕ := s * roleCount c.kind + r

/-- Field widths of the coefficient blocks, stage-major then role (`sec:algorithm`,
"Witnesses and the tables to be computed"). -/
def segmentWidths (c : Call) (p : Params) : List (List ℕ) :=
  (List.range p.J).flatMap fun _ => (List.range (roleCount c.kind)).map fun r => (circ c r).coeffs.map coefWidth

/-- The decoded coefficient from an offset `v` for a gate of top weight `a` (valid iff `v ≤ 2|a|`). -/
def coefOf (a : ℤ) (v : ℕ) : ℤ := (v : ℤ) - a.natAbs

/-- A decoded witness: the inner coordinates and the coefficient list of stage `s` (`K_{s+1}` of `sec:algorithm`),
role `r`. -/
structure Wit (n : ℕ) where
  I : Finset (Fin n)
  coef : ℕ → ℕ → List ℤ

/-- Decoding (`sec:algorithm`, "Witnesses and the tables to be computed"): `k` coordinates of `λ_n` bits, then the
coefficient blocks; `none` on an invalid
encoding (a coordinate `≥ n`, a repeated coordinate, or an offset `> 2|w|`). Only the prefix of length
`k λ_n + J Σ_{r,i} ⌈lg(2|w_i^r|+1)⌉` is read; missing bits are zeros. -/
def decodeWitness (c : Call) (p : Params) (w : List Bool) : Option (Wit c.n) :=
  let coords := (readBlock w (List.replicate p.k (Target.lambda c.n))).1
  let segs := (readSegments (readBlock w (List.replicate p.k (Target.lambda c.n))).2 (segmentWidths c p)).1
  let ok : Bool := coords.all (· < c.n) && coords.Nodup &&
    (List.range p.J).all fun s => (List.range (roleCount c.kind)).all fun r =>
      ((circ c r).coeffs.zip (segs.getD (segmentIndex c s r) [])).all fun av => decide (av.2 ≤ 2 * av.1.natAbs)
  if ok then
    some ⟨(coords.filterMap fun i => if h : i < c.n then some (⟨i, h⟩ : Fin c.n) else none).toFinset,
      fun s r => ((circ c r).coeffs.zip (segs.getD (segmentIndex c s r) [])).map fun av => coefOf av.1 av.2⟩
  else none

/-- The length of the witness prefix that is read. -/
def prefixLength (c : Call) (p : Params) : ℕ :=
  p.k * Target.lambda c.n + p.J * ((List.range (roleCount c.kind)).map fun r =>
    ((circ c r).coeffs.map coefWidth).sum).sum

/-! ## Cells, points, forms -/

abbrev Points {n : ℕ} (I : Finset (Fin n)) := {i // i ∈ I} → Bool
abbrev Cells {n : ℕ} (I : Finset (Fin n)) := {i // i ∉ I} → Bool

/-- `(y, x)` as a full input. -/
def extend {n : ℕ} (I : Finset (Fin n)) (y : Cells I) (x : Points I) : BitInput n :=
  fun i => if hi : i ∈ I then x ⟨i, hi⟩ else y ⟨i, hi⟩

/-- `0^I`, so that `z_y = extend I y (zeroPoint I)`. -/
def zeroPoint {n : ℕ} (I : Finset (Fin n)) : Points I := fun _ => false

/-- A linear form `Σ_i a_i g_i(z)` over the gate list, with coefficient list `a`. -/
def linForm {n : ℕ} (gates : List (NormalizedThresholdGate n)) (a : List ℤ) (z : BitInput n) : ℤ :=
  ((gates.zip a).map fun gc => gc.2 * if gc.1.eval z then 1 else 0).sum

theorem score_eq_linForm {n : ℕ} (C : NCircuit n) (z : BitInput n) : C.score z = linForm C.gates C.coeffs z := rfl

section Forms

variable (c : Call) (p : Params) (wt : Wit c.n)

/-- `K_{s+1}^r(z)` (0-based stage `s`). -/
def stageForm (r s : ℕ) (z : BitInput c.n) : ℤ := linForm (circ c r).gates (wt.coef s r) z

/-- `X^r(z)`. -/
def scoreForm (r : ℕ) (z : BitInput c.n) : ℤ := (circ c r).score z

/-- `a_{j+1}` as an integer (0-based), so that `E_{j+1} = K_{j+2} − a_{j+1} K_{j+1}`. -/
def rateOf (j : ℕ) : ℤ := (p.factors.getD j 0 : ℤ)

/-- The digit `E_j^r(z)` (`E_0 = K_1`, `E_j = K_{j+1} − a_j K_j`), for an arbitrary proposal. -/
def digit (r j : ℕ) (z : BitInput c.n) : ℤ :=
  CountingCore.proposedDigit (rateOf p) (fun s => stageForm c wt r s z) j

/-- `Φ^r = M₁ K_J^r − A X^r` (`sec:algorithm`, "Witnesses and the tables to be computed"). -/
def phi (r : ℕ) (z : BitInput c.n) : ℤ :=
  (p.M1 : ℤ) * stageForm c wt r (p.J - 1) z - (p.A : ℤ) * scoreForm c r z

/-- `A_j = ∏_{i=j+1}^{J−1} a_i` (`A_0 = A`); `rateOf p t = a_{t+1}`. -/
def tailProd (j : ℕ) : ℤ := ∏ t ∈ Finset.Ico j (p.J - 1), rateOf p t

/-! ### The tables (a) and (b) of `sec:algorithm`, "Witnesses and the tables to be computed" -/

/-- Membership in the part `H` of a cell: all points, or `H_b = {x : PAR_{Σ∩I}(x) = b}` for a parity call. -/
def innerParity (x : Points wt.I) : Bool :=
  (c.parity.map fun i => if h : i < c.n then
    (if hI : (⟨i, h⟩ : Fin c.n) ∈ wt.I then x ⟨⟨i, h⟩, hI⟩ else false) else false).foldl xor false

def outerParity (y : Cells wt.I) : Bool :=
  (c.parity.map fun i => if h : i < c.n then
    (if hI : (⟨i, h⟩ : Fin c.n) ∈ wt.I then false else y ⟨⟨i, h⟩, hI⟩) else false).foldl xor false

/-- The parts of a cell: `[none]`, or `[some false, some true]` (the parity split) for a parity call. -/
def parts : List (Option Bool) := if c.kind = .parity then [some false, some true] else [none]

def inPart (part : Option Bool) (x : Points wt.I) : Bool :=
  match part with
  | none => true
  | some b => innerParity c wt x == b

/-- Table (a): the joint count of all digits `≡ κ` and scores `≡ σ` modulo `p` on a part of the cell `y`. -/
def jointCount (q : ℕ) (part : Option Bool) (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ) (σ : Role c → ℤ) : ℕ :=
  ((Finset.univ : Finset (Points wt.I)).filter fun x => inPart c wt part x = true ∧
    (∀ rj : Role c × Fin p.J, digit c p wt rj.1.val rj.2.val (extend wt.I y x) ≡ κ rj [ZMOD (q : ℤ)]) ∧
    ∀ r : Role c, scoreForm c r.val (extend wt.I y x) ≡ σ r [ZMOD (q : ℤ)]).card

/-- Table (b): `M_{E,j}^r(y) = Σ_x (ΔE_j^r(y,x))^{2k}`. -/
def digitMoment (r j : ℕ) (y : Cells wt.I) : ℤ :=
  ∑ x : Points wt.I, (digit c p wt r j (extend wt.I y x) -
    digit c p wt r j (extend wt.I y (zeroPoint wt.I))) ^ (2 * p.k)

/-- Table (b): `M_Φ^r(y) = Σ_x (ΔΦ^r(y,x))^{2k}`. -/
def phiMoment (r : ℕ) (y : Cells wt.I) : ℤ :=
  ∑ x : Points wt.I, (phi c p wt r (extend wt.I y x) - phi c p wt r (extend wt.I y (zeroPoint wt.I))) ^ (2 * p.k)

/-! ### Reconstruction inside a cell (`sec:algorithm`, "Reconstruction inside a certified cell") -/

/-- The strict tests eq:tests. -/
def CellTests (y : Cells wt.I) : Prop :=
  (∀ (r : Role c) (j : Fin p.J), digitMoment c p wt r.val j.val y < (p.hE : ℤ) ^ (2 * p.k)) ∧
    ∀ r : Role c, phiMoment c p wt r.val y < (p.Lambda : ℤ) ^ (2 * p.k)

/-- All integer digit vectors with `|κ_j^r − E_j^r(z_y)| < h_E` (`sec:algorithm`,
"Reconstruction inside a certified cell"). -/
noncomputable def digitVectors (y : Cells wt.I) : Finset (Role c × Fin p.J → ℤ) :=
  Fintype.piFinset fun rj => Finset.Ioo
    (digit c p wt rj.1.val rj.2.val (extend wt.I y (zeroPoint wt.I)) - p.hE)
    (digit c p wt rj.1.val rj.2.val (extend wt.I y (zeroPoint wt.I)) + p.hE)

/-- `M₁(K^r(κ) − K_J^r(z_y))`, with `K^r(κ) = Σ_{j<J} A_j κ_j^r`. -/
def boxCenter (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ) (r : Role c) : ℤ :=
  (p.M1 : ℤ) * ((∑ j : Fin p.J, tailProd p j.val * κ (r, j)) -
    stageForm c wt r.val (p.J - 1) (extend wt.I y (zeroPoint wt.I)))

/-- Lower end of eq:box, intersected with `[−W^r, W^r]`. -/
def boxLo (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ) (r : Role c) : ℤ :=
  let lo := ScoreBox.lower (boxCenter c p wt y κ r) p.A (scoreForm c r.val (extend wt.I y (zeroPoint wt.I))) p.Lambda
  if lo ≤ -((circ c r.val).topWeight : ℤ) then -((circ c r.val).topWeight : ℤ) else lo

/-- Upper end of eq:box, intersected with `[−W^r, W^r]`. -/
def boxHi (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ) (r : Role c) : ℤ :=
  let hi := ScoreBox.upper (boxCenter c p wt y κ r) p.A (scoreForm c r.val (extend wt.I y (zeroPoint wt.I))) p.Lambda
  if hi ≤ ((circ c r.val).topWeight : ℤ) then hi else ((circ c r.val).topWeight : ℤ)

/-- The reconstruction box `B(κ) = ∏_r B^r(κ)`. -/
noncomputable def box (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ) : Finset (Role c → ℤ) :=
  Fintype.piFinset fun r => Finset.Icc (boxLo c p wt y κ r) (boxHi c p wt y κ r)

/-- `F` solves the push-forward equations of `κ` on a part: for every prime and every score-residue vector, the box
mass in that residue class equals the tabulated joint count at `κ mod p` (`sec:algorithm`,
"Reconstruction inside a certified cell"). -/
def Solves (part : Option Bool) (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ) (F : (Role c → ℤ) → ℚ) : Prop :=
  ∀ q ∈ p.primes, ∀ σ : Role c → Fin q,
    (∑ u ∈ (box c p wt y κ).filter (fun u => ∀ r, u r ≡ (σ r : ℤ) [ZMOD (q : ℤ)]), F u) =
      (jointCount c p wt q part y κ (fun r => (σ r : ℤ)) : ℚ)

open Classical in
/-- Exact solution over `ℚ` (`none` = inconsistent). Solutions are unique on the box (`Sound.lean`). -/
noncomputable def solveSystem (part : Option Bool) (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ) :
    Option ((Role c → ℤ) → ℚ) :=
  if h : ∃ F, Solves c p wt part y κ F then some (Classical.choose h) else none

/-- `Σ_u F_κ(u)·[predicate(u)]` for one part and one digit vector (`sec:algorithm`,
"Reconstruction inside a certified cell"). -/
noncomputable def partAnswer (part : Option Bool) (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ) : ℚ :=
  match solveSystem c p wt part y κ with
  | none => 0
  | some F => ∑ u ∈ box c p wt y κ,
      F u * (if scorePredicate c (xor (outerParity c wt y) (part.getD false)) u then 1 else 0)

/-- Every system of the cell is consistent. -/
def AllSolved (y : Cells wt.I) : Prop :=
  ∀ part ∈ parts c, ∀ κ ∈ digitVectors c p wt y, ∃ F, Solves c p wt part y κ F

/-- `N_y` (`sec:algorithm`, "Reconstruction inside a certified cell"). -/
noncomputable def cellCount (y : Cells wt.I) : ℚ :=
  ((parts c).map fun part => ∑ κ ∈ digitVectors c p wt y, partAnswer c p wt part y κ).sum

/-- A certain cell: tests pass, every system is consistent, and `N_y` is an integer in `[0, 2^k]`. -/
def Certain (y : Cells wt.I) : Prop :=
  CellTests c p wt y ∧ AllSolved c p wt y ∧ (cellCount c p wt y).den = 1 ∧ 0 ≤ cellCount c p wt y ∧
    cellCount c p wt y ≤ 2 ^ p.k

open Classical in
/-- eq:output. -/
noncomputable def outputOf : ℚ × ℚ :=
  let unc : ℕ := ((Finset.univ : Finset (Cells wt.I)).filter fun y => ¬ Certain c p wt y).card
  let certainSum : ℚ := ∑ y ∈ (Finset.univ : Finset (Cells wt.I)).filter (fun y => Certain c p wt y),
    cellCount c p wt y
  ((certainSum + 2 ^ (p.k - 1) * unc) / 2 ^ c.n, 2 ^ (p.k - 1) * unc / 2 ^ c.n)

end Forms

/-! ## The counter -/

/-- The sound default `(1/2, 1/2)`. -/
def defaultValue : ℚ × ℚ := (1 / 2, 1 / 2)

open Classical in
/-- The pure counter on a decoded call. -/
noncomputable def counterOnCall (B1 B2 cT : ℕ) (c : Call) (w : List Bool) : ℚ × ℚ :=
  if c.Admitted B1 B2 then
    if c.W = 0 then zeroWeightValue c
    else match selectParams cT (header c) with
      | none => defaultValue
      | some p => match decodeWitness c p w with
        | none => defaultValue
        | some wt => outputOf c p wt
  else defaultValue

end NearCubicGates.Close.Counter

/-!
# The witness codec: encoding, decoding, length (`sec:algorithm`, "Witnesses and the tables to be computed")

`encodeWitness` writes an inner coordinate list (`k` fields of `λ_n` bits) and the coefficient offsets (stage-major,
then role, then gate; `⌈lg(2|w|+1)⌉` bits each). `decode_encode`: every `k`-subset and every family of coefficient
vectors in the witness ranges `[−|w_i^r|, |w_i^r|]` is recovered exactly by `decodeWitness`, from a word of length
`prefixLength` (the paper's `kλ_n + J Σ ⌈lg(2|w_i^r|+1)⌉`).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open scoped BigOperators
open NearCubicGates NearCubicGates.Close.Interfaces NearCubicWires

theorem length_bitsOf (w v : ℕ) : (bitsOf w v).length = w := by
  induction w generalizing v with
  | zero => rfl
  | succ w ih => simp [bitsOf, ih]

theorem bitsValue_bitsOf (w v : ℕ) (hv : v < 2 ^ w) : bitsValue (bitsOf w v) = v := by
  induction w generalizing v with
  | zero => simp at hv; simp [bitsOf, bitsValue, hv]
  | succ w ih =>
    have h2 : v / 2 < 2 ^ w := by rw [pow_succ] at hv; omega
    simp only [bitsOf, bitsValue, ih (v / 2) h2]
    rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h] <;> omega

theorem length_writeBlock (ws vs : List ℕ) (h : ws.length = vs.length) :
    (writeBlock ws vs).length = ws.sum := by
  induction ws generalizing vs with
  | nil => simp [writeBlock]
  | cons w ws ih =>
    cases vs with
    | nil => simp at h
    | cons v vs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have := ih vs h
      simp only [writeBlock, List.zip_cons_cons, List.flatMap_cons, List.length_append, length_bitsOf,
        List.sum_cons] at this ⊢
      omega

theorem readBlock_writeBlock (ws vs : List ℕ) (tail : List Bool)
    (hfit : List.Forall₂ (fun w v => v < 2 ^ w) ws vs) :
    readBlock (writeBlock ws vs ++ tail) ws = (vs, tail) := by
  induction hfit generalizing tail with
  | nil => simp [readBlock, writeBlock]
  | @cons w v ws vs hv _ ih =>
    have hw : writeBlock (w :: ws) (v :: vs) = bitsOf w v ++ writeBlock ws vs := by
      simp [writeBlock]
    rw [hw, List.append_assoc]
    simp only [readBlock]
    have htake : (bitsOf w v ++ (writeBlock ws vs ++ tail)).take w = bitsOf w v := by
      rw [List.take_append_of_le_length (by rw [length_bitsOf]), List.take_of_length_le (by rw [length_bitsOf])]
    have hdrop : (bitsOf w v ++ (writeBlock ws vs ++ tail)).drop w = writeBlock ws vs ++ tail := by
      rw [List.drop_append_of_le_length (by rw [length_bitsOf]), List.drop_of_length_le (by rw [length_bitsOf]),
        List.nil_append]
    rw [htake, hdrop, ih tail, bitsValue_bitsOf w v hv]

theorem readSegments_write (segs : List (List ℕ × List ℕ)) (tail : List Bool)
    (hfit : ∀ sg ∈ segs, List.Forall₂ (fun w v => v < 2 ^ w) sg.1 sg.2) :
    readSegments ((segs.flatMap fun sg => writeBlock sg.1 sg.2) ++ tail) (segs.map Prod.fst) =
      (segs.map Prod.snd, tail) := by
  induction segs generalizing tail with
  | nil => simp [readSegments]
  | cons sg segs ih =>
    simp only [List.flatMap_cons, List.map_cons, List.append_assoc]
    simp only [readSegments]
    rw [readBlock_writeBlock sg.1 sg.2 _ (hfit sg (by simp)),
      ih tail (fun s hs => hfit s (by simp [hs]))]

theorem getD_flatMap_range {α : Type*} (J d : ℕ) (g : ℕ → ℕ → α) (s r : ℕ) (hs : s < J) (hr : r < d) (x : α) :
    ((List.range J).flatMap fun s => (List.range d).map (g s)).getD (s * d + r) x = g s r := by
  induction J with
  | zero => omega
  | succ J ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hlen : ((List.range J).flatMap fun s => (List.range d).map (g s)).length = J * d := by
      simp [List.length_flatMap, List.sum_replicate]
    by_cases hsJ : s < J
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith), ih hsJ]
    · have hs' : s = J := by omega
      subst hs'
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, show s * d + r - s * d = r by omega]
      simp [List.getD_eq_getElem?_getD, hr]

/-! ## The encoding -/

/-- The coordinate list of a coordinate set (sorted). -/
def coordsOf {n : ℕ} (I : Finset (Fin n)) : List ℕ := (I.sort (· ≤ ·)).map Fin.val

/-- The offsets `coefficient + |w|` of one block. -/
def offsetsOf (a : List ℤ) (cf : List ℤ) : List ℕ := (a.zip cf).map fun ab => (ab.2 + ab.1.natAbs).toNat

/-- The witness word of a coordinate set and coefficient vectors. -/
def encodeWitness (c : Call) (p : Params) (I : Finset (Fin c.n)) (coefs : ℕ → ℕ → List ℤ) : List Bool :=
  writeBlock (List.replicate p.k (Target.lambda c.n)) (coordsOf I) ++
    (((List.range p.J).flatMap fun s => (List.range (roleCount c.kind)).map fun r =>
      ((circ c r).coeffs.map coefWidth, offsetsOf (circ c r).coeffs (coefs s r))).flatMap
        fun sg => writeBlock sg.1 sg.2)

theorem coordsOf_length {n : ℕ} (I : Finset (Fin n)) : (coordsOf I).length = I.card := by
  simp [coordsOf]

theorem coordsOf_nodup {n : ℕ} (I : Finset (Fin n)) : (coordsOf I).Nodup := by
  unfold coordsOf
  exact (Finset.sort_nodup _ _).map Fin.val_injective

theorem coordsOf_lt {n : ℕ} (I : Finset (Fin n)) : ∀ i ∈ coordsOf I, i < n := by
  intro i hi
  simp only [coordsOf, List.mem_map] at hi
  obtain ⟨j, _, rfl⟩ := hi
  exact j.isLt

theorem coordsOf_toFinset {n : ℕ} (I : Finset (Fin n)) :
    ((coordsOf I).filterMap fun i => if h : i < n then some (⟨i, h⟩ : Fin n) else none).toFinset = I := by
  ext j
  simp only [coordsOf, List.mem_toFinset, List.mem_filterMap, List.mem_map, Finset.mem_sort]
  constructor
  · rintro ⟨i, ⟨j', hj', rfl⟩, h⟩
    rw [dif_pos j'.isLt] at h
    cases h
    exact hj'
  · intro hj
    exact ⟨j.val, ⟨j, hj, rfl⟩, by rw [dif_pos j.isLt]⟩

theorem coordsOf_fit {n : ℕ} (I : Finset (Fin n)) (k : ℕ) (hk : I.card = k) :
    List.Forall₂ (fun w v => v < 2 ^ w) (List.replicate k (Target.lambda n)) (coordsOf I) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [coordsOf_length, hk], ?_⟩
  intro i h1 h2
  simp only [List.get_eq_getElem, List.getElem_replicate]
  have hlt := coordsOf_lt I _ (List.getElem_mem h2)
  exact hlt.trans_le (Nat.le_pow_clog (by decide) n)

theorem offsets_fit (a cf : List ℤ) (hlen : cf.length = a.length)
    (hrange : List.Forall₂ (fun x y => |y| ≤ |x|) a cf) :
    List.Forall₂ (fun w v => v < 2 ^ w) (a.map coefWidth) (offsetsOf a cf) := by
  induction hrange with
  | nil => simp [offsetsOf]
  | @cons x y xs ys hxy _ ih =>
    simp only [List.map_cons, offsetsOf, List.zip_cons_cons]
    refine List.Forall₂.cons ?_ (by simpa [offsetsOf] using ih (by simpa using hlen))
    unfold coefWidth
    have h1 : (y + x.natAbs).toNat ≤ 2 * x.natAbs := by
      have := abs_le.mp (hxy.trans (le_of_eq (Int.abs_eq_natAbs x)))
      omega
    exact lt_of_le_of_lt h1 (Nat.lt_of_succ_le (Nat.le_pow_clog (by decide) _))

theorem decode_offsets (a cf : List ℤ) (hrange : List.Forall₂ (fun x y => |y| ≤ |x|) a cf) :
    ((a.zip (offsetsOf a cf)).map fun av => coefOf av.1 av.2) = cf ∧
      ((a.zip (offsetsOf a cf)).all fun av => decide (av.2 ≤ 2 * av.1.natAbs)) = true := by
  induction hrange with
  | nil => simp [offsetsOf]
  | @cons x y xs ys hxy _ ih =>
    have hb := abs_le.mp (hxy.trans (le_of_eq (Int.abs_eq_natAbs x)))
    simp only [offsetsOf, List.zip_cons_cons, List.map_cons, List.all_cons] at ih ⊢
    refine ⟨?_, ?_⟩
    · rw [ih.1]
      congr 1
      unfold coefOf
      omega
    · rw [ih.2, Bool.and_true, decide_eq_true_eq]
      omega

theorem segmentWidths_eq (c : Call) (p : Params) (coefs : ℕ → ℕ → List ℤ) :
    segmentWidths c p = ((List.range p.J).flatMap fun s => (List.range (roleCount c.kind)).map fun r =>
      ((circ c r).coeffs.map coefWidth, offsetsOf (circ c r).coeffs (coefs s r))).map Prod.fst := by
  simp [segmentWidths, List.map_flatMap, Function.comp_def]

/-- Every coordinate set and every family of coefficient vectors in the witness ranges is decoded exactly. -/
theorem decode_encode (c : Call) (p : Params) (I : Finset (Fin c.n)) (hk : I.card = p.k)
    (coefs : ℕ → ℕ → List ℤ)
    (hrange : ∀ s r, List.Forall₂ (fun x y => |y| ≤ |x|) (circ c r).coeffs (coefs s r)) :
    ∃ wt : Wit c.n, decodeWitness c p (encodeWitness c p I coefs) = some wt ∧ wt.I = I ∧
      ∀ s r, s < p.J → r < roleCount c.kind → wt.coef s r = coefs s r := by
  set segs := (List.range p.J).flatMap fun s => (List.range (roleCount c.kind)).map fun r =>
      ((circ c r).coeffs.map coefWidth, offsetsOf (circ c r).coeffs (coefs s r)) with hsegs
  have hfitSegs : ∀ sg ∈ segs, List.Forall₂ (fun w v => v < 2 ^ w) sg.1 sg.2 := by
    intro sg hsg
    simp only [hsegs, List.mem_flatMap, List.mem_range, List.mem_map] at hsg
    obtain ⟨s, _, r, _, rfl⟩ := hsg
    exact offsets_fit _ _ (hrange s r).length_eq.symm (hrange s r)
  have hread1 := readBlock_writeBlock (List.replicate p.k (Target.lambda c.n)) (coordsOf I)
    (segs.flatMap fun sg => writeBlock sg.1 sg.2) (coordsOf_fit I p.k hk)
  have hread2 := readSegments_write segs [] hfitSegs
  rw [List.append_nil] at hread2
  have hsegsEq := segmentWidths_eq c p coefs
  rw [← hsegs] at hsegsEq
  have hget : ∀ s r, s < p.J → r < roleCount c.kind →
      (segs.map Prod.snd).getD (segmentIndex c s r) [] = offsetsOf (circ c r).coeffs (coefs s r) := by
    intro s r hs hr
    rw [hsegs, List.map_flatMap]
    simp only [List.map_map, Function.comp_def]
    exact getD_flatMap_range p.J (roleCount c.kind) (fun s r => offsetsOf (circ c r).coeffs (coefs s r)) s r hs hr []
  unfold decodeWitness encodeWitness
  rw [← hsegs]
  simp only [hread1, hsegsEq, hread2]
  have hok : ((coordsOf I).all (· < c.n) && (coordsOf I).Nodup &&
      (List.range p.J).all fun s => (List.range (roleCount c.kind)).all fun r =>
        ((circ c r).coeffs.zip ((segs.map Prod.snd).getD (segmentIndex c s r) [])).all
          fun av => decide (av.2 ≤ 2 * av.1.natAbs)) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range]
    refine ⟨⟨coordsOf_lt I, coordsOf_nodup I⟩, ?_⟩
    intro s hs r hr
    rw [hget s r hs hr]
    simpa using (decode_offsets _ _ (hrange s r)).2
  rw [if_pos hok]
  refine ⟨_, rfl, coordsOf_toFinset I, ?_⟩
  intro s r hs hr
  simp only
  rw [hget s r hs hr]
  exact (decode_offsets _ _ (hrange s r)).1

theorem sum_flatMap_nat {α : Type*} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem encodeWitness_length (c : Call) (p : Params) (I : Finset (Fin c.n)) (hk : I.card = p.k)
    (coefs : ℕ → ℕ → List ℤ)
    (hrange : ∀ s r, List.Forall₂ (fun x y => |y| ≤ |x|) (circ c r).coeffs (coefs s r)) :
    (encodeWitness c p I coefs).length = prefixLength c p := by
  unfold encodeWitness prefixLength
  rw [List.length_append, length_writeBlock _ _ (by simp [coordsOf_length, hk]), List.length_flatMap,
    List.sum_replicate, smul_eq_mul, List.map_flatMap, sum_flatMap_nat]
  congr 1
  have hconst : ∀ s ∈ List.range p.J, (((List.range (roleCount c.kind)).map fun r =>
      ((circ c r).coeffs.map coefWidth, offsetsOf (circ c r).coeffs (coefs s r))).map
        fun a => (writeBlock a.1 a.2).length).sum =
      ((List.range (roleCount c.kind)).map fun r => ((circ c r).coeffs.map coefWidth).sum).sum := by
    intro s _
    simp only [List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro r _
    exact length_writeBlock _ _ (by simp [offsetsOf, (hrange s r).length_eq])
  rw [List.map_congr_left hconst, List.map_const', List.sum_replicate, smul_eq_mul, List.length_range]

end NearCubicGates.Close.Counter
