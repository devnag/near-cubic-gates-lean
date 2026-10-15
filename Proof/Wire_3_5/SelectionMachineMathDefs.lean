import Proof.Wire_3_5.SelectionMachineContract
import Proof.MachineModel.OrdinarySignedSortKey

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Defs
open NearCubicWires.WireExponent3_5.SelectionMachine

/-- The coset with counter value `N`: its `r` syndrome codes are the `s`-bit digits of `N`, most significant first
(`allCodes`' order: the first code varies slowest). -/
def codesOfIdx (s : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | r + 1, N => N / 2 ^ (s * r) % 2 ^ s :: codesOfIdx s r (N % 2 ^ (s * r))

/-- The strict-`<` running minimum over the counter values `0, …, M−1`, starting from `0` (a later value replaces
the current best only when strictly smaller: the first minimizer). -/
def argminIdx {κ : Type} (lt : κ → κ → Bool) (key : ℕ → κ) (M : ℕ) : ℕ :=
  (List.range M).foldl (fun best N => if lt (key N) (key best) then N else best) 0

/-- A nonnegative rational as numerator and denominator, never normalized. -/
abbrev RegRat := ℕ × ℕ

/-- Its value. -/
def ratVal (x : RegRat) : ℚ := (x.1 : ℚ) / x.2

/-- Add `(a/b)·T` for `x = (a, b, T)`: `(N, D) ↦ (N·b + a·T·D, D·b)`. -/
def ratAccStep (acc : RegRat) (x : ℕ × ℕ × ℕ) : RegRat :=
  (acc.1 * x.2.1 + x.1 * x.2.2 * acc.2, acc.2 * x.2.1)

/-- The accumulated `Σ (a/b)·T` from `0/1`. -/
def ratAcc (xs : List (ℕ × ℕ × ℕ)) : RegRat := xs.foldl ratAccStep (0, 1)

/-- The cross-multiplied strict compare (no gcd). -/
def ratLt (x y : RegRat) : Bool := decide (x.1 * y.2 < y.1 * x.2)

/-- A gate's row counts at the partition `σ`: `Σ_{u,v} rowCount σ g u v` over the `2^k` error rows. -/
def gateRows (P : StarParams) (σ : P.Translation) (g : NormalizedThresholdGate P.n) : ℕ :=
  ∑ u : P.Errors, ∑ v : P.Errors, P.rowCount σ g u v

/-- A population's row count `T_X(l)` at the coset `l`: its gate occurrences' row counts (an index outside the gate
list reads the default gate, whose row counts vanish). -/
def popRows (R : SelectionReq) (h : ParamsOk R) (l : List ℕ) (X : List ℕ × ℚ) : ℕ :=
  (X.1.map fun i => if hi : i < R.gates.length then
      gateRows (starParamsOf R h) ((starParamsOf R h).translationOfCodes l) (gateOf R.gates[i]) else 0).sum

/-- **The objective's key** at the coset `l`: `Σ_X p_X · T_X(l)` accumulated exactly, `p_X = num/den`. -/
def objKey (R : SelectionReq) (h : ParamsOk R) (l : List ℕ) : RegRat :=
  ratAcc (R.pops.map fun X => (X.2.num.toNat, X.2.den, popRows R h l X))

/-- The four corner predicates of the pair of half points `p = (a, a')`, `q = (b, b')` (`cornerLeft = ![a',a',a,a]`,
`cornerRight = ![b',b,b',b]`). -/
def cutCorners (θ : ℤ) (p q : ℤ × ℤ) : Fin 4 → Bool :=
  ![decide (θ ≤ p.2 + q.2), decide (θ ≤ p.2 + q.1), decide (θ ≤ p.1 + q.2), decide (θ ≤ p.1 + q.1)]

/-- The pairs whose corner pattern has a nonzero mixed difference. -/
def pairCount (θ : ℤ) (L R : List (ℤ × ℤ)) : ℕ :=
  (L.map fun p => R.countP fun q => decide (cornerDelta (cutCorners θ p q) ≠ 0)).sum

/-- A list enumerating a predicate exactly once. -/
def Enumerates {α : Type} (l : List α) (p : α → Prop) : Prop := l.Nodup ∧ ∀ x, x ∈ l ↔ p x

/-- The left half point of `(u, z_L)`: the left half scores `(a, a')` at the corners without and with the left
error `u`. -/
def ptL (P : StarParams) (g : NormalizedThresholdGate P.n) (p : P.Errors × (P.SideL → Bool)) : ℤ × ℤ :=
  (P.halfScoreL g p.2, P.halfScoreL g (StarParams.xorHalf p.2 (P.leftPart (P.errorVector P.leftBlock p.1))))

/-- The right half point of `(v, z_R)`: `(b, b')`. -/
def ptR (P : StarParams) (g : NormalizedThresholdGate P.n) (q : P.Errors × (P.SideR → Bool)) : ℤ × ℤ :=
  (P.halfScoreR g q.2, P.halfScoreR g (StarParams.xorHalf q.2 (P.rightPart (P.errorVector P.rightBlock q.1))))

/-- The left point the machine writes for `(u, z_L)`: the half point when `z_L` lies in the coset, else the null
point `(0, 0)` (its interval is empty, so it pairs with nothing). -/
def ptLz (P : StarParams) (σ : P.Translation) (g : NormalizedThresholdGate P.n) (p : P.Errors × (P.SideL → Bool)) :
    ℤ × ℤ :=
  if P.LeftOK σ p.2 then ptL P g p else (0, 0)

/-- The right point the machine writes for `(v, z_R)`: the half point, or the null point `(0, 0)`. -/
def ptRz (P : StarParams) (σ : P.Translation) (g : NormalizedThresholdGate P.n) (q : P.Errors × (P.SideR → Bool)) :
    ℤ × ℤ :=
  if P.RightOK σ q.2 then ptR P g q else (0, 0)

/-- `J = [lo, hi)` of a left point: `lo = min(θ−a, θ−a')`. -/
def loOf (θ : ℤ) (p : ℤ × ℤ) : ℤ := min (θ - p.1) (θ - p.2)

/-- `hi = max(θ−a, θ−a')`. -/
def hiOf (θ : ℤ) (p : ℤ × ℤ) : ℤ := max (θ - p.1) (θ - p.2)

/-- The 1-d interval count `Σ_{[lo,hi) ∈ I} #{y ∈ Y : lo ≤ y < hi}`. -/
def inCount {α : Type} [LinearOrder α] (I : List (α × α)) (Y : List α) : ℕ :=
  (I.map fun J => Y.countP fun y => decide (J.1 ≤ y ∧ y < J.2)).sum

/-- The 2-d dominance count `Σ_{[lo,hi) ∈ I} #{(m, M) ∈ D : lo ≤ m ∧ M < hi}`. -/
def dom2 {α : Type} [LinearOrder α] (I D : List (α × α)) : ℕ :=
  (I.map fun J => D.countP fun d => decide (J.1 ≤ d.1 ∧ d.2 < J.2)).sum

/-- **The `<`-join** `Σ_{b ∈ B} #{a ∈ A : a < b}` (S5 `BlockJoin`'s pass `<`, `rel false`). -/
def joinLt {α : Type} [LinearOrder α] (A B : List α) : ℕ :=
  (B.map fun b => A.countP fun a => decide (a < b)).sum

/-- Level `ℓ`, left keys: `(hi >> (ℓ+1))·2^W + lo` when `hi` has bit `ℓ` set, else the null query `0` (no key is
below it). Every list keeps its length, so the machine overwrites fixed stream regions. -/
def lvlK1 (W ℓ : ℕ) (I : List (ℕ × ℕ)) : List ℕ :=
  I.map fun J => if J.2.testBit ℓ then J.2 / 2 ^ (ℓ + 1) * 2 ^ W + J.1 else 0

/-- Level `ℓ`, left keys `(hi >> (ℓ+1) + 1)·2^W`, or the null query `0`. -/
def lvlK3 (W ℓ : ℕ) (I : List (ℕ × ℕ)) : List ℕ :=
  I.map fun J => if J.2.testBit ℓ then (J.2 / 2 ^ (ℓ + 1) + 1) * 2 ^ W else 0

/-- Level `ℓ`, right keys `(M >> (ℓ+1))·2^W + m` when `M` has bit `ℓ` clear, else the sentinel `2^(2W) − 1`
(never below a query). -/
def lvlK2 (W ℓ : ℕ) (D : List (ℕ × ℕ)) : List ℕ :=
  D.map fun d => if d.2.testBit ℓ then 2 ^ (2 * W) - 1 else d.2 / 2 ^ (ℓ + 1) * 2 ^ W + d.1

/-- The offset-binary key of a value `|z| < 2^V` (base `SignedSortKey.shifted`: `z + 2^V`, below `2^(V+1)`). -/
def keyOf (V : ℕ) (z : ℤ) : ℕ := RepairOrdinary.SignedSortKey.shifted V z

/-- The plus side of `gateJoin`: `J<(Y; hi) + 2·Σ_ℓ J<(K2_ℓ; K1_ℓ)`. -/
def joinPlus (V : ℕ) (θ : ℤ) (L R : List (ℤ × ℤ)) : ℕ :=
  joinLt (R.map (fun q => keyOf V q.1) ++ R.map (fun q => keyOf V q.2)) (L.map fun p => keyOf V (hiOf θ p)) +
    2 * ((List.range (V + 1)).map fun ℓ =>
      joinLt (lvlK2 (V + 1) ℓ (R.map fun q => (keyOf V (min q.1 q.2), keyOf V (max q.1 q.2))))
        (lvlK1 (V + 1) ℓ (L.map fun p => (keyOf V (loOf θ p), keyOf V (hiOf θ p))))).sum

/-- The minus side of `gateJoin`: `J<(Y; lo) + 2·Σ_ℓ J<(K2_ℓ; K3_ℓ)`. -/
def joinMinus (V : ℕ) (θ : ℤ) (L R : List (ℤ × ℤ)) : ℕ :=
  joinLt (R.map (fun q => keyOf V q.1) ++ R.map (fun q => keyOf V q.2)) (L.map fun p => keyOf V (loOf θ p)) +
    2 * ((List.range (V + 1)).map fun ℓ =>
      joinLt (lvlK2 (V + 1) ℓ (R.map fun q => (keyOf V (min q.1 q.2), keyOf V (max q.1 q.2))))
        (lvlK3 (V + 1) ℓ (L.map fun p => (keyOf V (loOf θ p), keyOf V (hiOf θ p))))).sum

/-- **The pair count by joins**: `pairCount = joinPlus − joinMinus` (keys of width `V + 1`). -/
def gateJoin (V : ℕ) (θ : ℤ) (L R : List (ℤ × ℤ)) : ℕ := joinPlus V θ L R - joinMinus V θ L R

/-- The key width a gate needs: `|θ| + Σ_i |w_i| < 2^V`. -/
def KeyBound {n : ℕ} (g : NormalizedThresholdGate n) (V : ℕ) : Prop :=
  g.threshold.natAbs + ∑ i, (g.weight i).natAbs < 2 ^ V

end NearCubicWires.WireExponent3_5.SelectionMachine.Math
