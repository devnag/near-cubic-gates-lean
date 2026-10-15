import Proof.Wire_3_5.FinalPassPopBridge
import Proof.Wire_3_5.FinalPassWordAux
import Proof.MachineModel.CanonicalSignedGateEvaluationProgram

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.CanonicalSignedGateEvaluationProgram

/-! ## Formats -/

/-- A signed integer as the P/N pair of framed `h`-bit words. -/
def pairW (h : ℕ) (z : ℤ) : List Bool := frame (binary h z.toNat) ++ frame (binary h (-z).toNat)

/-- One gate: a marker, the pair of `−θ`, the pairs of the weights. -/
def gateW (h : ℕ) {n : ℕ} (g : NormalizedThresholdGate n) : List Bool :=
  true :: (pairW h (-g.threshold) ++ (List.ofFn g.weight).flatMap (pairW h))

/-- A gate list, then `false`. -/
def gatesW (h : ℕ) {n : ℕ} (G : List (NormalizedThresholdGate n)) : List Bool := G.flatMap (gateW h) ++ [false]

/-! ## The accumulators -/

/-- The P sum of the weights at the selected coordinates. -/
def posAcc : List ℤ → List Bool → ℕ
  | w :: ws, x :: xs => (if x then w.toNat else 0) + posAcc ws xs
  | _, _ => 0

/-- The N sum of the weights at the selected coordinates. -/
def negAcc : List ℤ → List Bool → ℕ
  | w :: ws, x :: xs => (if x then (-w).toNat else 0) + negAcc ws xs
  | _, _ => 0

theorem posAcc_ofFn : ∀ (n : ℕ) (w : Fin n → ℤ) (x : Fin n → Bool),
    posAcc (List.ofFn w) (List.ofFn x) = maskedPositiveSum w x
  | 0, _, _ => by simp [posAcc, maskedPositiveSum]
  | n + 1, w, x => by
    rw [List.ofFn_succ, List.ofFn_succ, posAcc, posAcc_ofFn n]
    unfold maskedPositiveSum positivePart
    rw [Fin.sum_univ_succ]

theorem negAcc_ofFn : ∀ (n : ℕ) (w : Fin n → ℤ) (x : Fin n → Bool),
    negAcc (List.ofFn w) (List.ofFn x) = maskedNegativeSum w x
  | 0, _, _ => by simp [negAcc, maskedNegativeSum]
  | n + 1, w, x => by
    rw [List.ofFn_succ, List.ofFn_succ, negAcc, negAcc_ofFn n]
    unfold maskedNegativeSum negativePart
    rw [Fin.sum_univ_succ]

/-- **The gate from the two accumulators**: `N = θ⁺ + N(x)` against `P = θ⁻ + P(x)`, where `θ⁻ = (−θ)⁺` is the
P word and `θ⁺ = (−θ)⁻` the N word of the pair of `−θ`. -/
theorem eval_acc {n : ℕ} (g : NormalizedThresholdGate n) (x : BitInput n) :
    g.eval x = decide ((-(-g.threshold)).toNat + negAcc (List.ofFn g.weight) (List.ofFn x) ≤
      (-g.threshold).toNat + posAcc (List.ofFn g.weight) (List.ofFn x)) := by
  rw [gate_eval_eq_decide, posAcc_ofFn, negAcc_ofFn, neg_neg]
  unfold positivePart negativePart
  apply decide_eq_decide.mpr
  omega

theorem posAcc_le (ws : List ℤ) (xs : List Bool) : posAcc ws xs ≤ (ws.map Int.natAbs).sum := by
  induction ws generalizing xs with
  | nil => simp [posAcc]
  | cons w ws ih =>
    cases xs with
    | nil => simp [posAcc]
    | cons x xs =>
      simp only [posAcc, List.map_cons, List.sum_cons]
      have := ih xs
      split <;> omega

theorem negAcc_le (ws : List ℤ) (xs : List Bool) : negAcc ws xs ≤ (ws.map Int.natAbs).sum := by
  induction ws generalizing xs with
  | nil => simp [negAcc]
  | cons w ws ih =>
    cases xs with
    | nil => simp [negAcc]
    | cons x xs =>
      simp only [negAcc, List.map_cons, List.sum_cons]
      have := ih xs
      split <;> omega

/-! ## The adder and the comparator -/

/-- The sum bit. -/
def addOut (x y c : Bool) : Bool := xor (xor x y) c

/-- The carry bit. -/
def addNxt (x y c : Bool) : Bool := (x && y) || (c && xor x y)

/-- The borrow comparator's carry: `x + ¬y + c`. -/
def cmpNxt (x y c : Bool) : Bool := addNxt x (!y) c

theorem binary_length' : ∀ (h x : ℕ), (binary h x).length = h
  | 0, _ => rfl
  | h + 1, x => by simp [binary, binary_length' h (x / 2)]

/-- **The ripple-carry pass is addition** of `h`-bit words. -/
theorem mapS_add : ∀ (h x y : ℕ) (c : Bool),
    (mapS addOut addNxt (binary h x) (binary h y) c).1 = binary h (x + y + c.toNat)
  | 0, _, _, _ => rfl
  | h + 1, x, y, c => by
    simp only [binary, mapS]
    have key : ∀ (x y : ℕ) (c : Bool),
        addOut (x % 2 == 1) (y % 2 == 1) c = ((x + y + c.toNat) % 2 == 1) ∧
        (x / 2 + y / 2 + (addNxt (x % 2 == 1) (y % 2 == 1) c).toNat) = (x + y + c.toNat) / 2 := by
      intro x y c
      have hx := Nat.mod_two_eq_zero_or_one x
      have hy := Nat.mod_two_eq_zero_or_one y
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> cases c <;>
        simp [addOut, addNxt, hx, hy, Bool.toNat] <;> omega
    obtain ⟨k1, k2⟩ := key x y c
    rw [k1, mapS_add h (x / 2) (y / 2), k2]

/-- The kept word of a pass that writes its own bits back. -/
theorem mapS_keep (nxt : Bool → Bool → Bool → Bool) : ∀ (as bs : List Bool) (c : Bool), as.length = bs.length →
    (mapS keepA nxt as bs c).1 = as
  | [], [], _, _ => rfl
  | a :: as, b :: bs, c, h => by
    simp only [mapS, keepA]
    rw [mapS_keep nxt as bs _ (by simpa using h)]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- **The borrow pass compares**: its final carry is `[y + [¬c] ≤ x]` on the low `h` bits. -/
theorem mapS_cmp : ∀ (h x y : ℕ) (c : Bool),
    (mapS keepA cmpNxt (binary h x) (binary h y) c).2 = decide (y % 2 ^ h + (!c).toNat ≤ x % 2 ^ h)
  | 0, x, y, c => by show c = _; cases c <;> simp [Nat.mod_one]
  | h + 1, x, y, c => by
    simp only [binary, mapS]
    rw [mapS_cmp h (x / 2) (y / 2)]
    have ex : x % 2 ^ (h + 1) = 2 * (x / 2 % 2 ^ h) + x % 2 := by
      rw [pow_succ, mul_comm, Nat.mod_mul]; omega
    have ey : y % 2 ^ (h + 1) = 2 * (y / 2 % 2 ^ h) + y % 2 := by
      rw [pow_succ, mul_comm, Nat.mod_mul]; omega
    rw [ex, ey]
    generalize x / 2 % 2 ^ h = x'
    generalize y / 2 % 2 ^ h = y'
    have hx := Nat.mod_two_eq_zero_or_one x
    have hy := Nat.mod_two_eq_zero_or_one y
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> cases c <;>
      simp [cmpNxt, addNxt, hx, hy, Bool.toNat] <;> omega

/-! ## The corner inputs -/

/-- The input of corner `(bu,bv)`: `c + [bu]u + [bv]v`, coordinatewise. -/
def cornerIn (bu bv : Bool) : List Bool → List Bool → List Bool → List Bool
  | c :: cs, u :: us, v :: vs => xor (xor c (bu && u)) (bv && v) :: cornerIn bu bv cs us vs
  | _, _, _ => []

theorem cornerIn_ofFn {n : ℕ} (bu bv : Bool) (c u v : BitInput n) :
    cornerIn bu bv (List.ofFn c) (List.ofFn u) (List.ofFn v) =
      List.ofFn (xorInput (xorInput c (fun i => bu && u i)) (fun i => bv && v i)) := by
  induction n with
  | zero => simp [cornerIn]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, cornerIn]
    have := ih (fun i => c i.succ) (fun i => u i.succ) (fun i => v i.succ)
    rw [this]
    rfl

theorem corner_in {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) :
    corners T c u v 0 = T (xorInput (xorInput c (fun i => true && u i)) (fun i => true && v i)) ∧
    corners T c u v 1 = T (xorInput (xorInput c (fun i => true && u i)) (fun i => false && v i)) ∧
    corners T c u v 2 = T (xorInput (xorInput c (fun i => false && u i)) (fun i => true && v i)) ∧
    corners T c u v 3 = T (xorInput (xorInput c (fun i => false && u i)) (fun i => false && v i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | (show T _ = T _; congr 1; funext i; simp [xorInput])

/-! ## The accumulator width -/

/-- The largest accumulator value of a gate: `max(θ⁻, θ⁺) + Σ|w_i|`. -/
def accMax {n : ℕ} (g : NormalizedThresholdGate n) : ℕ :=
  max (-g.threshold).toNat (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum

/-- **The accumulator width of a gate list**: enough bits for every gate's accumulators. -/
def accBits {n : ℕ} (G : List (NormalizedThresholdGate n)) : ℕ :=
  (G.map fun g => Nat.clog 2 (accMax g + 1)).foldr max 0

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact (ih h).trans (Nat.le_max_right _ _)

theorem accBits_ok {n : ℕ} (G : List (NormalizedThresholdGate n)) :
    ∀ g ∈ G, (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ accBits G ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ accBits G := by
  intro g hg
  have h1 : accMax g + 1 ≤ 2 ^ Nat.clog 2 (accMax g + 1) := Nat.le_pow_clog (by norm_num) _
  have h2 : Nat.clog 2 (accMax g + 1) ≤ accBits G := le_foldr_max (List.mem_map.mpr ⟨g, hg, rfl⟩)
  have h3 : 2 ^ Nat.clog 2 (accMax g + 1) ≤ 2 ^ accBits G := Nat.pow_le_pow_right (by norm_num) h2
  have h0 : (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum ≤ accMax g ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum ≤ accMax g := by
    unfold accMax; omega
  constructor <;> omega

end NearCubicWires.WireExponent3_5.FinalPass.Corner
