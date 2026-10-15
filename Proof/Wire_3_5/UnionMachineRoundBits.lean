import Proof.Wire_3_5.UnionMachineSlack
import Proof.Wire_3_5.FinalPassWordAux

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Round
open NearCubicWires NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WilliamsPublishedForm (framedNatBits fixedWidthNatBits)

/-! ## Binary words -/

theorem binary_succ (w n : ℕ) : binary (w + 1) n = (n % 2 == 1) :: binary w (n / 2) := rfl

theorem binary_mod : ∀ (w n : ℕ), binary w (n % 2 ^ w) = binary w n
  | 0, _ => rfl
  | w + 1, n => by
    rw [binary_succ, binary_succ]
    have h1 : n % 2 ^ (w + 1) % 2 = n % 2 := by
      rw [pow_succ', Nat.mod_mul_right_mod]
    have h2 : n % 2 ^ (w + 1) / 2 = n / 2 % 2 ^ w := by
      rw [pow_succ', Nat.mod_mul_right_div_self]
    rw [h1, h2, binary_mod w (n / 2)]

theorem binary_add_pow (w n : ℕ) : binary w (2 ^ w + n) = binary w n := by
  rw [← binary_mod w (2 ^ w + n), Nat.add_mod_left, binary_mod]

/-- The bitwise complement of a word. -/
theorem binary_not : ∀ (w y : ℕ), (binary w y).map (fun b => !b) = binary w (2 ^ w - 1 - y % 2 ^ w)
  | 0, _ => rfl
  | w + 1, y => by
    rw [binary_succ, binary_succ, List.map_cons, binary_not w (y / 2)]
    have hy : y % 2 ^ (w + 1) = 2 * (y / 2 % 2 ^ w) + y % 2 := by
      rw [pow_succ, mul_comm, Nat.mod_mul]; omega
    have hlt : y / 2 % 2 ^ w < 2 ^ w := Nat.mod_lt _ (by positivity)
    have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
    rw [hy, hp]
    have hX1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    generalize y / 2 % 2 ^ w = y' at hlt ⊢
    generalize 2 ^ w = X at hlt hX1 ⊢
    have hb := Nat.mod_two_eq_zero_or_one y
    congr 1
    · rcases hb with hb | hb <;> simp [hb] <;> omega
    · congr 1; rcases hb with hb | hb <;> rw [hb] <;> omega

/-! ## The passes -/

/-- The sum bit and the carry. -/
def addO (a b c : Bool) : Bool := xor (xor a b) c
def addN (a b c : Bool) : Bool := (a && b) || (c && xor a b)
/-- The borrow subtractor `a + ¬b + c` (sum bit) and the comparator/borrow carry. -/
def subO (a b c : Bool) : Bool := addO a (!b) c
def geN (a b c : Bool) : Bool := addN a (!b) c
/-- The or-pass carry. -/
def anyN (a _ c : Bool) : Bool := a || c

theorem mapS_add' : ∀ (w x y : ℕ) (c : Bool),
    (mapS addO addN (binary w x) (binary w y) c).1 = binary w (x + y + c.toNat)
  | 0, _, _, _ => rfl
  | w + 1, x, y, c => by
    simp only [binary_succ, mapS]
    have key : ∀ (x y : ℕ) (c : Bool),
        addO (x % 2 == 1) (y % 2 == 1) c = ((x + y + c.toNat) % 2 == 1) ∧
        (x / 2 + y / 2 + (addN (x % 2 == 1) (y % 2 == 1) c).toNat) = (x + y + c.toNat) / 2 := by
      intro x y c
      have hx := Nat.mod_two_eq_zero_or_one x
      have hy := Nat.mod_two_eq_zero_or_one y
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> cases c <;>
        simp [addO, addN, hx, hy, Bool.toNat] <;> omega
    obtain ⟨k1, k2⟩ := key x y c
    rw [k1, mapS_add' w (x / 2) (y / 2), k2]

theorem mapS_neg : ∀ (as bs : List Bool) (c : Bool),
    mapS subO geN as bs c = mapS addO addN as (bs.map fun b => !b) c
  | [], _, _ => by cases ‹List Bool› <;> rfl
  | _ :: _, [], _ => rfl
  | a :: as, b :: bs, c => by
    simp only [mapS, List.map_cons, subO, geN]
    rw [mapS_neg as bs]

/-- **The borrow subtractor**: `x − y` when `y ≤ x < 2^w`. -/
theorem mapS_sub (w x y : ℕ) (hyx : y ≤ x) (hx : x < 2 ^ w) :
    (mapS subO geN (binary w x) (binary w y) true).1 = binary w (x - y) := by
  rw [mapS_neg, binary_not, mapS_add']
  have hy : y % 2 ^ w = y := Nat.mod_eq_of_lt (by omega)
  have hp : 0 < 2 ^ w := by positivity
  rw [hy, show x + (2 ^ w - 1 - y) + true.toNat = 2 ^ w + (x - y) by simp [Bool.toNat]; omega, binary_add_pow]

/-- **The borrow comparator** (C5's `mapS_cmp` at the subtractor's carry): the final carry is `[y + [¬c] ≤ x]` on the
low `w` bits. -/
theorem mapS_ge : ∀ (w x y : ℕ) (c : Bool),
    (mapS keepA geN (binary w x) (binary w y) c).2 = decide (y % 2 ^ w + (!c).toNat ≤ x % 2 ^ w)
  | 0, x, y, c => by show c = _; cases c <;> simp [Nat.mod_one]
  | w + 1, x, y, c => by
    simp only [binary_succ, mapS]
    rw [mapS_ge w (x / 2) (y / 2)]
    have ex : x % 2 ^ (w + 1) = 2 * (x / 2 % 2 ^ w) + x % 2 := by
      rw [pow_succ, mul_comm, Nat.mod_mul]; omega
    have ey : y % 2 ^ (w + 1) = 2 * (y / 2 % 2 ^ w) + y % 2 := by
      rw [pow_succ, mul_comm, Nat.mod_mul]; omega
    rw [ex, ey]
    generalize x / 2 % 2 ^ w = x'
    generalize y / 2 % 2 ^ w = y'
    have hx := Nat.mod_two_eq_zero_or_one x
    have hy := Nat.mod_two_eq_zero_or_one y
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> cases c <;>
      simp [geN, addN, hx, hy, Bool.toNat] <;> omega

/-- The comparator keeps its word. -/
theorem mapS_keepA (nxt : Bool → Bool → Bool → Bool) : ∀ (as bs : List Bool) (c : Bool), as.length = bs.length →
    (mapS keepA nxt as bs c).1 = as
  | [], [], _, _ => rfl
  | a :: as, b :: bs, c, h => by
    simp only [mapS, keepA]
    rw [mapS_keepA nxt as bs _ (by simpa using h)]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- **The shift pass doubles.** -/
theorem mapS_shl : ∀ (w x : ℕ) (bs : List Bool) (c : Bool), bs.length = w →
    (mapS shOut shNxt (binary w x) bs c).1 = binary w (2 * x + c.toNat)
  | 0, _, [], _, _ => rfl
  | w + 1, x, b :: bs, c, h => by
    simp only [binary_succ, mapS, shOut, shNxt]
    rw [mapS_shl w (x / 2) bs _ (by simpa using h)]
    have h1 : (2 * x + c.toNat) % 2 = c.toNat := by cases c <;> simp [Bool.toNat]
    have h2 : (2 * x + c.toNat) / 2 = x := by have := Bool.toNat_lt c; omega
    have h3 : 2 * (x / 2) + (x % 2 == 1).toNat = x := by
      have := Nat.mod_two_eq_zero_or_one x
      rcases this with h | h <;> simp [h] <;> omega
    rw [h1, h2, h3]
    cases c <;> rfl
  | 0, _, _ :: _, _, h => by simp at h
  | _ + 1, _, [], _, h => by simp at h

/-- **The or-pass** decides `x ≠ 0` on the low `w` bits. -/
theorem mapS_any : ∀ (w x : ℕ) (bs : List Bool) (c : Bool), bs.length = w →
    (mapS keepA anyN (binary w x) bs c).2 = (c || decide (x % 2 ^ w ≠ 0))
  | 0, x, [], c, _ => by show c = _; simp [Nat.mod_one]
  | w + 1, x, b :: bs, c, h => by
    simp only [binary_succ, mapS, anyN]
    rw [mapS_any w (x / 2) bs _ (by simpa using h)]
    have ex : x % 2 ^ (w + 1) = 2 * (x / 2 % 2 ^ w) + x % 2 := by
      rw [pow_succ, mul_comm, Nat.mod_mul]; omega
    rw [ex]
    have hx := Nat.mod_two_eq_zero_or_one x
    rcases hx with hx | hx <;> cases c <;> simp [hx]
  | 0, _, _ :: _, _, h => by simp at h
  | _ + 1, _, [], _, h => by simp at h

/-! ## The division -/

/-- One integer-part round: subtract `den` once if it fits. -/
def intStep (den : ℕ) (rq : ℕ × ℕ) : ℕ × ℕ := if den ≤ rq.1 then (rq.1 - den, rq.2 + 1) else rq

/-- One fractional round: double, then subtract `den` once if it fits. -/
def fracStep (den : ℕ) (rq : ℕ × ℕ) : ℕ × ℕ :=
  if den ≤ 2 * rq.1 then (2 * rq.1 - den, 2 * rq.2 + 1) else (2 * rq.1, 2 * rq.2)

/-- **The division the machine runs**: three integer rounds, then `p` fractional rounds; `(remainder, quotient)`. -/
def divRef (num den p : ℕ) : ℕ × ℕ := (fracStep den)^[p] ((intStep den)^[3] (num, 0))

theorem intStep_inv (num den : ℕ) (rq : ℕ × ℕ) (h : num = rq.2 * den + rq.1) :
    num = (intStep den rq).2 * den + (intStep den rq).1 := by
  unfold intStep
  split
  · next hle =>
    simp only
    rw [h, Nat.add_mul, one_mul]; omega
  · exact h

theorem fracStep_inv (num den k : ℕ) (rq : ℕ × ℕ) (h : num * 2 ^ k = rq.2 * den + rq.1) :
    num * 2 ^ (k + 1) = (fracStep den rq).2 * den + (fracStep den rq).1 := by
  have e : num * 2 ^ (k + 1) = 2 * (rq.2 * den + rq.1) := by rw [pow_succ, ← h]; ring
  unfold fracStep
  split
  · next hle =>
    simp only
    rw [e]
    have : (2 * rq.2 + 1) * den = 2 * (rq.2 * den) + den := by ring
    rw [this]; omega
  · simp only
    rw [e]; ring

theorem fracStep_lt (den : ℕ) (rq : ℕ × ℕ) (h : rq.1 < den) : (fracStep den rq).1 < den := by
  unfold fracStep
  split
  · simp only; omega
  · next hlt => simp only; omega

theorem intStep3 (num den : ℕ) (hd : 0 < den) (h : num < 4 * den) :
    (intStep den)^[3] (num, 0) = (num % den, num / den) := by
  have hq : num / den < 4 := by rw [Nat.div_lt_iff_lt_mul hd]; omega
  have hm : num % den < den := Nat.mod_lt _ hd
  have hdm := Nat.div_add_mod num den
  simp only [Function.iterate_succ, Function.comp, Function.iterate_zero, id, intStep]
  interval_cases hq' : num / den
  · have : num < den := by omega
    have e : num % den = num := Nat.mod_eq_of_lt this
    simp [Nat.not_le.mpr this, e]
  · have h1 : den ≤ num := by omega
    have h2 : ¬ den ≤ num - den := by omega
    simp [h1, h2]; omega
  · have h1 : den ≤ num := by omega
    have h2 : den ≤ num - den := by omega
    have h3 : ¬ den ≤ num - den - den := by omega
    simp [h1, h2, h3]; omega
  · have h1 : den ≤ num := by omega
    have h2 : den ≤ num - den := by omega
    have h3 : den ≤ num - den - den := by omega
    simp [h1, h2, h3]; omega

theorem divRef_inv (num den : ℕ) (hd : 0 < den) (h : num < 4 * den) :
    ∀ p, num * 2 ^ p = (divRef num den p).2 * den + (divRef num den p).1 ∧ (divRef num den p).1 < den
  | 0 => by
    simp only [divRef, Function.iterate_zero, id, intStep3 num den hd h, pow_zero, mul_one]
    exact ⟨(Nat.div_add_mod' num den).symm, Nat.mod_lt _ hd⟩
  | p + 1 => by
    obtain ⟨h1, h2⟩ := divRef_inv num den hd h p
    have e : divRef num den (p + 1) = fracStep den (divRef num den p) := by
      simp only [divRef, Function.iterate_succ_apply']
    rw [e]
    exact ⟨fracStep_inv num den p _ h1, fracStep_lt den _ h2⟩

/-- **The division is exact**: `(num·2^p mod den, ⌊num·2^p/den⌋)`. -/
theorem divRef_spec (num den p : ℕ) (hd : 0 < den) (h : num < 4 * den) :
    divRef num den p = (num * 2 ^ p % den, num * 2 ^ p / den) := by
  obtain ⟨h1, h2⟩ := divRef_inv num den hd h p
  have hq : num * 2 ^ p / den = (divRef num den p).2 := by
    rw [h1, Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt h2, zero_add]
  have hr : num * 2 ^ p % den = (divRef num den p).1 := by
    rw [h1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  rw [hq, hr]

/-! ## The sign -/

/-- **The machine's rounded answer** from the sign, the division's remainder and quotient: `Q` for a nonnegative
answer, `−(Q + [r ≠ 0])` for a negative one. -/
def floorVal (neg : Bool) (rq : ℕ × ℕ) : ℤ := if neg then -((rq.2 : ℤ) + if rq.1 = 0 then 0 else 1) else rq.2

theorem floorVal_eq (v : ℚ) (p : ℕ) (h : v.num.natAbs < 4 * v.den) :
    floorVal (decide (v.num < 0)) (divRef v.num.natAbs v.den p) = ⌊v * 2 ^ p⌋ := by
  have hd : 0 < v.den := v.den_pos
  rw [divRef_spec _ _ _ hd h]
  have hv : v * 2 ^ p = ((v.num * 2 ^ p : ℤ) : ℚ) / (v.den : ℕ) := by
    conv_lhs => rw [← Rat.num_div_den v]
    push_cast; ring
  rw [hv, Rat.floor_intCast_div_natCast]
  set a := v.num.natAbs * 2 ^ p with ha
  have hda : (0 : ℤ) < (v.den : ℤ) := by exact_mod_cast hd
  have hml : ((a % v.den : ℕ) : ℤ) < v.den := by exact_mod_cast Nat.mod_lt a hd
  have hdm : (v.den : ℤ) * ((a / v.den : ℕ) : ℤ) + ((a % v.den : ℕ) : ℤ) = (a : ℤ) := by
    exact_mod_cast Nat.div_add_mod a v.den
  unfold floorVal
  dsimp only
  by_cases hn : v.num < 0
  · rw [if_pos (by simpa using hn)]
    have hA : (v.num.natAbs : ℤ) = -v.num := Int.ofNat_natAbs_of_nonpos (le_of_lt hn)
    have hnum : v.num * 2 ^ p = -(a : ℤ) := by
      rw [ha]; push_cast; rw [abs_of_neg hn]; ring
    rw [hnum]
    by_cases hr : a % v.den = 0
    · rw [if_pos hr]
      have hr' : ((a % v.den : ℕ) : ℤ) = 0 := by exact_mod_cast hr
      refine (((Int.ediv_emod_unique hda).mpr ⟨?_, le_refl 0, hda⟩).1).symm
      rw [hr'] at hdm; linarith
    · rw [if_neg hr]
      have hr' : (0 : ℤ) < ((a % v.den : ℕ) : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hr
      refine (((Int.ediv_emod_unique (r := (v.den : ℤ) - ((a % v.den : ℕ) : ℤ)) hda).mpr
        ⟨?_, by linarith, by linarith⟩).1).symm
      linarith
  · rw [if_neg (by simpa using hn)]
    have hA : (v.num.natAbs : ℤ) = v.num := Int.natAbs_of_nonneg (by omega)
    have hnum : v.num * 2 ^ p = (a : ℤ) := by
      rw [ha]; push_cast; rw [abs_of_nonneg (by omega)]
    rw [hnum]
    norm_cast

/-- The rounded answer as a rational: `roundQ p v = floorVal … / 2^p`. -/
theorem roundQ_eq (v : ℚ) (p : ℕ) (h : v.num.natAbs < 4 * v.den) :
    roundQ p v = (floorVal (decide (v.num < 0)) (divRef v.num.natAbs v.den p) : ℚ) / 2 ^ p := by
  rw [floorVal_eq v p h]; rfl

/-! ## The raw fields of `ratWord` -/

theorem natBitLength_lt (n : ℕ) : n < 2 ^ natBitLength n := Nat.lt_pow_succ_log_self (by norm_num) n

theorem testBit_eq_binary : ∀ (w n : ℕ), fixedWidthNatBits w n = binary w n
  | 0, _ => rfl
  | w + 1, n => by
    unfold fixedWidthNatBits
    rw [List.ofFn_succ, binary_succ]
    congr 1
    · simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
    · have := testBit_eq_binary w (n / 2)
      unfold fixedWidthNatBits at this
      rw [← this]
      congr 1
      funext i
      simp [Nat.testBit_succ]

theorem binary_append_zero : ∀ (w k n : ℕ), n < 2 ^ w →
    binary w n ++ List.replicate k false = binary (w + k) n
  | 0, k, n, h => by
    have : n = 0 := by simpa using h
    subst this
    simp [binary_zero]
  | w + 1, k, n, h => by
    rw [binary_succ, show w + 1 + k = (w + k) + 1 by omega, binary_succ, List.cons_append,
      binary_append_zero w k (n / 2) (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at h; omega)]

/-- `natWord n = 1^ℓ 0 bits`, with `ℓ = natBitLength n` and the bits `binary ℓ n`. -/
theorem natWord_eq (n : ℕ) :
    natWord n = List.replicate (natBitLength n) true ++ false :: binary (natBitLength n) n := by
  rw [natWord, framedNatBits, testBit_eq_binary]

/-- The low `ℓ` bits of `n`, padded with `k` zeros, are its `ℓ + k`-bit word. -/
theorem bits_pad (n k : ℕ) : binary (natBitLength n) n ++ List.replicate k false = binary (natBitLength n + k) n :=
  binary_append_zero _ k n (natBitLength_lt n)

/-- On an answer with `|num| < 4·den`, the numerator has at most `natBitLength den + 2` bits. -/
theorem natBitLength_num_le (a d : ℕ) (h : a < 4 * d) : natBitLength a ≤ natBitLength d + 2 := by
  unfold natBitLength
  have h1 : a < 2 ^ (Nat.log 2 d + 3) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) d
    rw [pow_succ, pow_succ, pow_succ] at *
    omega
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp
  · have := Nat.log_lt_of_lt_pow (by omega) h1
    omega

end NearCubicWires.WireExponent3_5.UnionMachine.Round
