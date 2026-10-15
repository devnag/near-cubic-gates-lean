import Proof.Wire_3_5.FinalPassMask
import Proof.Wire_3_5.FinalPassFiltTabRef

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sample
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Filt (binary_add)

/-- One block: bit `i < b` is `[d = i+1]`. -/
def oneHot (b d : ℕ) : List Bool := List.ofFn fun i : Fin b => decide (d = i.val + 1)

/-- The value of a low-bit-first word. -/
def chunkVal : List Bool → ℕ
  | [] => 0
  | x :: xs => x.toNat + 2 * chunkVal xs

theorem chunkVal_binary : ∀ (s x : ℕ), chunkVal (binary s x) = x % 2 ^ s
  | 0, x => by simp [binary, chunkVal, Nat.mod_one]
  | s + 1, x => by
    simp only [binary, chunkVal, chunkVal_binary s (x / 2)]
    rw [pow_succ, mul_comm (2 ^ s) 2, Nat.mod_mul]
    have h := Nat.mod_two_eq_zero_or_one x
    rcases h with h | h <;> simp [h]

/-- The `h` digits: the `s`-bit chunks of a word. -/
def digitsOf (s : ℕ) : ℕ → List Bool → List ℕ
  | 0, _ => []
  | h + 1, w => chunkVal (w.take s) :: digitsOf s h (w.drop s)

theorem binary_length'' : ∀ (h x : ℕ), (binary h x).length = h
  | 0, _ => rfl
  | h + 1, x => by simp [binary, binary_length'' h (x / 2)]

theorem digitsOf_binary (s : ℕ) : ∀ (h k : ℕ),
    digitsOf s h (binary (s * h) k) = List.ofFn fun j : Fin h => k / 2 ^ (s * j) % 2 ^ s
  | 0, _ => rfl
  | h + 1, k => by
    rw [show s * (h + 1) = s + s * h by ring, binary_add, digitsOf, List.ofFn_succ]
    have e1 : (binary s k ++ binary (s * h) (k / 2 ^ s)).take s = binary s k := by
      rw [List.take_left' (binary_length'' s k)]
    have e2 : (binary s k ++ binary (s * h) (k / 2 ^ s)).drop s = binary (s * h) (k / 2 ^ s) := by
      rw [List.drop_left' (binary_length'' s k)]
    rw [e1, e2, chunkVal_binary, digitsOf_binary s h (k / 2 ^ s)]
    congr 1
    · simp
    · congr 1
      funext j
      rw [Nat.div_div_eq_div_mul, ← pow_add]
      congr 3
      simp [Fin.val_succ]; ring

/-- **The half's error vector** in the order of the coordinates: `h` one-hot blocks on its side, zeros elsewhere. -/
def decWord (b h tail : ℕ) (right : Bool) (ds : List ℕ) : List Bool :=
  if right then List.replicate (h * b) false ++ ds.flatMap (oneHot b) ++ List.replicate tail false
  else ds.flatMap (oneHot b) ++ List.replicate (h * b + tail) false

theorem length_flatMap_oneHot (b : ℕ) (ds : List ℕ) : (ds.flatMap (oneHot b)).length = ds.length * b := by
  induction ds with
  | nil => simp
  | cons d ds ih => simp [ih, oneHot]; ring

theorem getElem_flatMap_oneHot (b : ℕ) : ∀ (ds : List ℕ) (q : ℕ) (hq : q < (ds.flatMap (oneHot b)).length),
    (ds.flatMap (oneHot b))[q] = decide (ds[q / b]'(by
      rw [length_flatMap_oneHot] at hq
      have hb : 0 < b := by rcases Nat.eq_zero_or_pos b with h | h <;> [simp [h] at hq; exact h]
      exact (Nat.div_lt_iff_lt_mul hb).mpr hq) = q % b + 1)
  | [], q, hq => by simp at hq
  | d :: ds, q, hq => by
    have hb : 0 < b := by
      rw [length_flatMap_oneHot] at hq
      rcases Nat.eq_zero_or_pos b with h | h
      · simp [h] at hq
      · exact h
    simp only [List.flatMap_cons]
    by_cases hqb : q < b
    · rw [List.getElem_append_left (by simp [oneHot]; omega)]
      simp only [oneHot, List.getElem_ofFn]
      have e1 : q / b = 0 := Nat.div_eq_of_lt hqb
      have e2 : q % b = q := Nat.mod_eq_of_lt hqb
      simp [e1, e2]
    · rw [List.getElem_append_right (by simp [oneHot]; omega)]
      have hq' : q - b < (ds.flatMap (oneHot b)).length := by
        simp only [List.flatMap_cons, List.length_append] at hq
        simp [oneHot] at hq ⊢; omega
      have ih := getElem_flatMap_oneHot b ds (q - b) (by simpa [oneHot] using hq')
      simp only [oneHot, List.length_ofFn] at ih ⊢
      rw [ih]
      have e1 : q / b = (q - b) / b + 1 := by
        rw [show q = (q - b) + b * 1 by omega, Nat.add_mul_div_left _ _ hb]; simp
      have e2 : q % b = (q - b) % b := by
        conv_lhs => rw [show q = (q - b) + b * 1 by omega]
        rw [Nat.add_mul_mod_self_left]
      simp only [e1, e2, List.getElem_cons_succ]

/-- The entries of `decWord` at the digits `d 0, …, d (h−1)`. -/
def decAt (b h : ℕ) (right : Bool) (d : ℕ → ℕ) (p : ℕ) : Prop :=
  if right then h * b ≤ p ∧ p < h * b + h * b ∧ d ((p - h * b) / b) = (p - h * b) % b + 1
  else p < h * b ∧ d (p / b) = p % b + 1

instance (b h : ℕ) (right : Bool) (d : ℕ → ℕ) (p : ℕ) : Decidable (decAt b h right d p) := by
  unfold decAt; split <;> infer_instance

theorem flat_get (b : ℕ) (hb : 0 < b) : ∀ (ds : List ℕ) (q : ℕ),
    (ds.flatMap (oneHot b))[q]? = if q < ds.length * b then some (decide (ds.getD (q / b) 0 = q % b + 1)) else none
  | [], q => by simp
  | d :: ds, q => by
    rw [List.flatMap_cons]
    by_cases hq : q < b
    · rw [List.getElem?_append_left (by simp [oneHot]; exact hq)]
      simp only [oneHot, List.getElem?_ofFn, List.length_cons]
      rw [dif_pos hq, if_pos (by nlinarith)]
      simp [Nat.div_eq_of_lt hq, Nat.mod_eq_of_lt hq]
    · rw [List.getElem?_append_right (by simp [oneHot]; omega), flat_get b hb ds]
      simp only [oneHot, List.length_ofFn, List.length_cons]
      have e1 : q / b = (q - b) / b + 1 := by
        rw [show q = (q - b) + b * 1 by omega, Nat.add_mul_div_left _ _ hb]; simp
      have e2 : q % b = (q - b) % b := by
        conv_lhs => rw [show q = (q - b) + b * 1 by omega]
        rw [Nat.add_mul_mod_self_left]
      by_cases hr : q - b < ds.length * b
      · rw [if_pos hr, if_pos (by rw [Nat.add_mul, one_mul]; omega), e1, e2]
        simp
      · rw [if_neg hr, if_neg (by rw [Nat.add_mul, one_mul]; omega)]

theorem getD_ofFn_nat {h : ℕ} (d : ℕ → ℕ) (i : ℕ) (hi : i < h) : (List.ofFn fun j : Fin h => d j).getD i 0 = d i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

theorem decWord_get (b h tail : ℕ) (hb : 0 < b) (right : Bool) (d : ℕ → ℕ) (p : ℕ) :
    (decWord b h tail right (List.ofFn fun j : Fin h => d j))[p]? =
      if p < h * b + h * b + tail then some (decide (decAt b h right d p)) else none := by
  have hl := length_flatMap_oneHot b (List.ofFn fun j : Fin h => d j)
  simp only [List.length_ofFn] at hl
  cases right
  · simp only [decWord, Bool.false_eq_true, if_false]
    unfold decAt
    simp only [Bool.false_eq_true, if_false]
    by_cases hpl : p < h * b
    · rw [List.getElem?_append_left (by rw [hl]; exact hpl), flat_get b hb, List.length_ofFn, if_pos hpl,
        if_pos (by omega), getD_ofFn_nat d _ ((Nat.div_lt_iff_lt_mul hb).mpr hpl)]
      simp [hpl]
    · rw [List.getElem?_append_right (by rw [hl]; omega), List.getElem?_replicate, hl]
      by_cases hp2 : p < h * b + h * b + tail
      · rw [if_pos (by omega), if_pos hp2]; simp [hpl]
      · rw [if_neg (by omega), if_neg hp2]
  · simp only [decWord, if_true]
    unfold decAt
    simp only [if_true]
    by_cases hp1 : p < h * b
    · rw [List.append_assoc, List.getElem?_append_left (by simp; omega), List.getElem?_replicate, if_pos hp1,
        if_pos (by omega)]
      simp; omega
    · by_cases hp2 : p < h * b + h * b
      · rw [List.append_assoc, List.getElem?_append_right (by simp; omega), List.length_replicate,
          List.getElem?_append_left (by rw [hl]; omega), flat_get b hb, List.length_ofFn, if_pos (by omega),
          if_pos (by omega), getD_ofFn_nat d _ ((Nat.div_lt_iff_lt_mul hb).mpr (by omega))]
        simp only [Option.some.injEq]
        apply decide_eq_decide.mpr
        constructor
        · intro h1; exact ⟨by omega, hp2, h1⟩
        · intro h1; exact h1.2.2
      · rw [List.getElem?_append_right (by rw [List.length_append, hl]; simp; omega), List.getElem?_replicate,
          List.length_append, List.length_replicate, hl]
        by_cases hp3 : p < h * b + h * b + tail
        · rw [if_pos (by omega), if_pos hp3]; simp; omega
        · rw [if_neg (by omega), if_neg hp3]

/-- The block decomposition of a coordinate: `p = j·b + i` with `i < b` exactly at `j = p / b`, `i = p % b`. -/
theorem block_iff (b h : ℕ) (d : ℕ → ℕ) (p off : ℕ) :
    (∃ j < h, ∃ i < b, d j = i + 1 ∧ (off + j) * b + i = p) ↔
      (off * b ≤ p ∧ p < off * b + h * b ∧ d ((p - off * b) / b) = (p - off * b) % b + 1) := by
  constructor
  · rintro ⟨j, hj, i, hi, hd, hc⟩
    have hb : 0 < b := by omega
    have hq : p - off * b = j * b + i := by rw [← hc, add_mul]; omega
    have e1 : (p - off * b) / b = j := by
      rw [hq, Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hi]; simp
    have e2 : (p - off * b) % b = i := by rw [hq, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
    refine ⟨by rw [← hc, add_mul]; omega, ?_, by rw [e1, e2]; exact hd⟩
    have h3 : (j + 1) * b ≤ h * b := Nat.mul_le_mul_right _ (by omega)
    rw [← hc, add_mul]; rw [add_mul, one_mul] at h3; omega
  · rintro ⟨h1, h2, hd⟩
    have hb : 0 < b := by rcases Nat.eq_zero_or_pos b with h0 | h0 <;> [simp [h0] at h2; exact h0]
    refine ⟨(p - off * b) / b, ?_, (p - off * b) % b, Nat.mod_lt _ hb, hd, ?_⟩
    · exact (Nat.div_lt_iff_lt_mul hb).mpr (by omega)
    · have := Nat.div_add_mod' (p - off * b) b
      rw [add_mul]; omega

theorem optionFin_symm_some (b : ℕ) (dj : Fin (b + 1)) (i : Fin b) :
    (optionFinEquiv b).symm dj = some i ↔ dj.val = i.val + 1 := by
  unfold optionFinEquiv
  simp only [Equiv.coe_fn_symm_mk]
  by_cases h0 : dj.val = 0
  · simp [h0]
  · rw [dif_neg h0]
    simp only [Option.some.injEq]
    constructor
    · intro hs; rw [← hs]; simp only []; omega
    · intro hs; ext; simp only []; omega

/-- **The error vector of the half with index `a`** is `decWord` of the digits of `binary (s·r/2) a`. -/
theorem errorVector_decode (P : StarParams) (right : Bool) (k : Fin ((P.b + 1) ^ (P.r / 2))) :
    List.ofFn (P.errorVector (if right then P.rightBlock else P.leftBlock) ((errorsEquiv P).symm k)) =
      decWord P.b (P.r / 2) (P.n - P.r * P.b) right (digitsOf P.s (P.r / 2) (binary (P.s * (P.r / 2)) k)) := by
  have hbs : P.b + 1 = 2 ^ P.s := P.b_succ
  have hb0 : 0 < P.b := P.b_pos
  have hrb := P.r_mul_b_le
  have hre : P.r / 2 * 2 = P.r := Nat.div_mul_cancel (even_iff_two_dvd.mp P.r_even)
  have hhb : P.r / 2 * P.b + P.r / 2 * P.b = P.r * P.b := by rw [← two_mul, ← mul_assoc, mul_comm 2, hre]
  have htot : P.r / 2 * P.b + P.r / 2 * P.b + (P.n - P.r * P.b) = P.n := by omega
  rw [digitsOf_binary P.s (P.r / 2) k]
  -- the digit of block `j`
  have hdj : ∀ (j : Fin (P.r / 2)) (i : Fin P.b),
      ((errorsEquiv P).symm k j = some i ↔ (k : ℕ) / 2 ^ (P.s * j) % 2 ^ P.s = i.val + 1) := by
    intro j i
    have he : (errorsEquiv P).symm k j = (optionFinEquiv P.b).symm (finFunctionFinEquiv.symm k j) := rfl
    have hd : ((finFunctionFinEquiv.symm k j : Fin (P.b + 1)) : ℕ) = (k : ℕ) / 2 ^ (P.s * j) % 2 ^ P.s := by
      simp only [finFunctionFinEquiv_symm_apply_val]
      obtain ⟨kv, hkv⟩ : ∃ kv : ℕ, kv = (k : ℕ) := ⟨_, rfl⟩
      rw [← hkv, hbs, ← pow_mul]
    rw [he, optionFin_symm_some, hd]
  apply List.ext_getElem?
  intro p
  rw [decWord_get _ _ _ hb0 _ (fun j => (k : ℕ) / 2 ^ (P.s * j) % 2 ^ P.s) p, List.getElem?_ofFn]
  by_cases hp : p < P.n
  · rw [dif_pos hp, if_pos (show p < P.r / 2 * P.b + P.r / 2 * P.b + (P.n - P.r * P.b) by rw [htot]; exact hp)]
    congr 1
    unfold StarParams.errorVector
    apply decide_eq_decide.mpr
    have hlhs : (∃ j : Fin (P.r / 2), ∃ i : Fin P.b, (errorsEquiv P).symm k j = some i ∧
        P.blockCoord ((if right then P.rightBlock else P.leftBlock) j) i = ⟨p, hp⟩) ↔
        (∃ j < P.r / 2, ∃ i < P.b, (k : ℕ) / 2 ^ (P.s * j) % 2 ^ P.s = i + 1 ∧
          ((if right then P.r / 2 else 0) + j) * P.b + i = p) := by
      constructor
      · rintro ⟨j, i, hji, hc⟩
        refine ⟨j, j.isLt, i, i.isLt, (hdj j i).mp hji, ?_⟩
        have := congrArg Fin.val hc
        cases right <;> simpa [StarParams.blockCoord, StarParams.leftBlock, StarParams.rightBlock] using this
      · rintro ⟨j, hj, i, hi, hd, hc⟩
        refine ⟨⟨j, hj⟩, ⟨i, hi⟩, (hdj ⟨j, hj⟩ ⟨i, hi⟩).mpr hd, ?_⟩
        apply Fin.ext
        cases right <;> simpa [StarParams.blockCoord, StarParams.leftBlock, StarParams.rightBlock] using hc
    rw [hlhs, block_iff]
    unfold decAt
    cases right
    · simp only [Bool.false_eq_true, if_false, Nat.zero_mul, Nat.sub_zero, zero_le, true_and, Nat.zero_add]
    · simp only [if_true]
  · rw [dif_neg hp, if_neg (show ¬ p < P.r / 2 * P.b + P.r / 2 * P.b + (P.n - P.r * P.b) by rw [htot]; exact hp)]

/-- **The sample word** read by the final pass (the sampler's output format): per sampled pair `(a, b)` of live-half
indices, the framed `kh`-bit binary words of `a` and `b` (`kh = s·r/2`, `callKh`). -/
def sampleWord (kh : ℕ) (S : List (ℕ × ℕ)) : List Bool :=
  S.flatMap fun p => NearCubicWires.RepairOrdinary.frame (binary kh p.1) ++ NearCubicWires.RepairOrdinary.frame (binary kh p.2)

end NearCubicWires.WireExponent3_5.FinalPass.Sample
