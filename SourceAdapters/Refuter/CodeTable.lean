import SourceAdapters.Refuter.CheckerSem
import NineInputs

/-!
# Where the checker finds things in `VerifierEncoding.code` (input 7, F01 machine layer, part 2)

`VerifierEncoding.code v` (`L/Statement.lean:680`) is the transition table the checking machine
reads: `1^t 0 1^s 0`, the start control in `wd = natBitLength s` bits, the halted/accepting bit pair
of every control, then for every control `q` and every display mask `mk < 2^t` the entry
`actionCode wd (rule q mk)` of `ew = 1 + wd + 4t` bits. proof of `lem:multitape-refuter` ("the universal simulation
… the code of `P`") and SFM78 Condition 1 (`adapters/sourcetext/SFM78.txt` l.323–326, "a program
code … from which the transition table can be read") are realized by these offsets.

The facts are cell reads (`readTapeBit`), exactly what the machine's code-tape reads return:
`code_halted`, `code_accepting`, `code_entry_some`, `code_entry_body` (and its two consumers
`code_nextBit`, `code_actBit`). `maskL` turns guessed display bits (least significant first, tape
`0` first, as in the table's `mask.testBit tape`) into the entry index; `maskL_ofFn_testBit` turns
the `wd` bits of a control back into its value.
-/

namespace NearCubicGates.Adapters.Refuter

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairSource
open NearCubicWires.RepairSource.VerifierEncoding

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## Cell reads on lists -/

theorem rd_append_left {l₁ l₂ : List Bool} {p : ℕ} (h : p < l₁.length) :
    readTapeBit (l₁ ++ l₂) p = readTapeBit l₁ p := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem rd_append_right (l₁ l₂ : List Bool) (p : ℕ) :
    readTapeBit (l₁ ++ l₂) (l₁.length + p) = readTapeBit l₂ p := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  congr 2
  omega

theorem rd_append_right' (l₁ l₂ : List Bool) {p : ℕ} (h : l₁.length ≤ p) :
    readTapeBit (l₁ ++ l₂) p = readTapeBit l₂ (p - l₁.length) := by
  rw [← rd_append_right l₁ l₂ (p - l₁.length)]
  congr 1
  omega

/-- Block `j` of a list of equal-length blocks starts at `j·L`. -/
theorem rd_flatten_ofFn (L : ℕ) :
    ∀ {n : ℕ} (f : Fin n → List Bool), (∀ j, (f j).length = L) → ∀ (j : Fin n) (k : ℕ), k < L →
      readTapeBit (List.ofFn f).flatten (j.val * L + k) = readTapeBit (f j) k
  | 0, _, _, j, _, _ => j.elim0
  | n + 1, f, hf, j, k, hk => by
    rw [List.ofFn_succ, List.flatten_cons]
    by_cases hj : j.val = 0
    · have e : j = 0 := Fin.ext hj
      subst e
      simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add]
      exact rd_append_left (by rw [hf 0]; exact hk)
    · obtain ⟨j', hj'⟩ : ∃ j' : Fin n, j = j'.succ := ⟨⟨j.val - 1, by omega⟩, by ext; simp; omega⟩
      subst hj'
      have e : j'.succ.val * L + k = (f 0).length + (j'.val * L + k) := by
        rw [hf 0, Fin.val_succ]; ring
      rw [e, rd_append_right]
      exact rd_flatten_ofFn L (fun i => f i.succ) (fun i => hf _) j' k hk

theorem rd_cons_succ (b : Bool) (l : List Bool) (k : ℕ) : readTapeBit (b :: l) (k + 1) = readTapeBit l k := by
  simp [readTapeBit]

theorem rd_replicate (n : ℕ) (b : Bool) {p : ℕ} (h : p < n) : readTapeBit (List.replicate n b) p = b := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  simp [h]

theorem rd_fixedBits (w v j : ℕ) (h : j < w) : readTapeBit (fixedBits w v) j = v.testBit j := by
  unfold readTapeBit fixedBits
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [h]

theorem rd_beyond (l : List Bool) {p : ℕ} (h : l.length ≤ p) : readTapeBit l p = false := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

/-! ## Bits to numbers, least significant first -/

/-- A bit list read least significant first. -/
def maskL : List Bool → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * maskL l

theorem maskL_testBit : ∀ (l : List Bool) (j : ℕ), (maskL l).testBit j = l.getD j false
  | [], j => by simp [maskL]
  | b :: l, 0 => by
    simp only [maskL, Nat.testBit_zero, List.getD_cons_zero]
    cases b <;> simp <;> omega
  | b :: l, j + 1 => by
    rw [← Nat.testBit_div_two, List.getD_cons_succ, ← maskL_testBit l j]
    congr 1
    cases b <;> simp [maskL] <;> omega

theorem maskL_lt : ∀ l : List Bool, maskL l < 2 ^ l.length
  | [] => by simp [maskL]
  | b :: l => by
    have := maskL_lt l
    simp only [maskL, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem maskL_append_single (l : List Bool) (b : Bool) :
    maskL (l ++ [b]) = maskL l + (if b then 2 ^ l.length else 0) := by
  induction l with
  | nil => cases b <;> simp [maskL]
  | cons a l ih =>
    simp only [List.cons_append, maskL, ih, List.length_cons, pow_succ]
    cases b <;> simp <;> ring

/-- The `w` low bits of a number below `2^w` give the number back. -/
theorem maskL_ofFn_testBit : ∀ (w v : ℕ), v < 2 ^ w → maskL (List.ofFn fun j : Fin w => v.testBit j.val) = v
  | 0, v, h => by simp at h; subst h; rfl
  | w + 1, v, h => by
    rw [List.ofFn_succ]
    simp only [maskL, Fin.val_zero, Fin.val_succ]
    have hd : v / 2 < 2 ^ w := by rw [pow_succ] at h; omega
    have e : (fun j : Fin w => v.testBit (j.val + 1)) = fun j : Fin w => (v / 2).testBit j.val := by
      funext j; rw [Nat.testBit_div_two]
    rw [e, maskL_ofFn_testBit w (v / 2) hd]
    by_cases hv : v % 2 = 1 <;> simp [Nat.testBit_zero, hv] <;> omega

/-- The display read from a mask. -/
def maskDisplay (t mk : ℕ) : Fin t → Bool := fun j => mk.testBit j.val

theorem maskDisplay_maskL {t : ℕ} (d : Fin t → Bool) : maskDisplay t (maskL (List.ofFn d)) = d := by
  funext j
  simp only [maskDisplay, maskL_testBit]
  unfold List.getD
  rw [List.getElem?_ofFn]
  simp

theorem maskL_ofFn_lt {t : ℕ} (d : Fin t → Bool) : maskL (List.ofFn d) < 2 ^ t := by
  simpa using maskL_lt (List.ofFn d)

/-! ## The layout of the code -/

section Layout
variable (v : RepairOrdinary.Verifier)

/-- `wd = natBitLength s`, the width of a control. -/
def cWd : ℕ := natBitLength v.stateCount
/-- Entry width `1 + wd + 4t`. -/
def cEw : ℕ := 1 + cWd v + 4 * v.tapeCount
/-- Offset of the halted/accepting pairs: `t + 1 + s + 1 + wd`. -/
def cHb : ℕ := v.tapeCount + 1 + v.stateCount + 1 + cWd v
/-- Offset of the transition table. -/
def cAt : ℕ := cHb v + 2 * v.stateCount
/-- Width of one control's block of `2^t` entries. -/
def cBs : ℕ := 2 ^ v.tapeCount * cEw v

/-- The action body of an entry: the next control in `wd` bits, then per tape the write and move
codes. -/
def actionBody (w : ℕ) {t s : ℕ} (a : Action t s) : List Bool :=
  fixedBits w a.nextControl.val ++
    (List.ofFn fun i : Fin t => writeCode (a.write i) ++ moveCode (a.move i)).flatten

theorem writeCode_length (o : Option Bool) : (writeCode o).length = 2 := by
  rcases o with _ | _ | _ <;> rfl

theorem moveCode_length (mv : HeadMove) : (moveCode mv).length = 2 := by
  cases mv <;> rfl

theorem wm_flatten_length {t s : ℕ} (a : Action t s) :
    (List.ofFn fun i : Fin t => writeCode (a.write i) ++ moveCode (a.move i)).flatten.length =
      4 * t := by
  rw [List.length_flatten]
  simp only [List.map_ofFn]
  have : (List.length ∘ fun i : Fin t => writeCode (a.write i) ++ moveCode (a.move i)) =
      fun _ => 4 := by
    funext i; simp [writeCode_length, moveCode_length]
  rw [this, List.sum_ofFn]
  simp [mul_comm]

theorem actionCode_length {t s : ℕ} (w : ℕ) (o : Option (Action t s)) :
    (actionCode w o).length = 1 + w + 4 * t := by
  cases o with
  | none => simp [actionCode]; omega
  | some a =>
    simp only [actionCode, List.length_cons, List.length_append]
    rw [wm_flatten_length]
    simp [fixedBits]; omega

theorem code_split :
    VerifierEncoding.code v =
      (List.replicate v.tapeCount true ++ [false] ++ List.replicate v.stateCount true ++ [false] ++
        fixedBits (cWd v) v.machine.start.val ++
        (List.ofFn fun i : Fin v.stateCount => [v.machine.halted i, v.accepting i]).flatten) ++
      (List.ofFn fun i : Fin v.stateCount =>
        (List.ofFn fun mask : Fin (2 ^ v.tapeCount) =>
          actionCode (cWd v) (v.machine.rule i (fun tape => mask.val.testBit tape.val))).flatten).flatten := by
  rfl

theorem header_length :
    (List.replicate v.tapeCount true ++ [false] ++ List.replicate v.stateCount true ++ [false] ++
        fixedBits (cWd v) v.machine.start.val ++
        (List.ofFn fun i : Fin v.stateCount => [v.machine.halted i, v.accepting i]).flatten).length =
      cAt v := by
  simp only [List.length_append, List.length_replicate, List.length_singleton, fixedBits,
    List.length_ofFn, List.length_flatten, List.map_ofFn]
  have : (List.length ∘ fun i : Fin v.stateCount => [v.machine.halted i, v.accepting i]) =
      fun _ => 2 := by funext i; rfl
  rw [this, List.sum_ofFn]
  simp [cAt, cHb, mul_comm]

theorem pre_length :
    (List.replicate v.tapeCount true ++ [false] ++ List.replicate v.stateCount true ++ [false] ++
        fixedBits (cWd v) v.machine.start.val).length = cHb v := by
  simp [fixedBits, cHb]; omega

/-- The start control's bits (`t + 1 + s + 1 + j`, `j < wd`). -/
theorem code_start (j : ℕ) (hj : j < cWd v) :
    readTapeBit (VerifierEncoding.code v) (v.tapeCount + 1 + v.stateCount + 1 + j) =
      v.machine.start.val.testBit j := by
  rw [code_split, rd_append_left (by rw [header_length]; simp [cAt, cHb]; omega)]
  rw [rd_append_left (by simp [fixedBits]; omega)]
  have e : v.tapeCount + 1 + v.stateCount + 1 + j =
      (List.replicate v.tapeCount true ++ [false] ++ List.replicate v.stateCount true ++ [false]).length + j := by
    simp; omega
  rw [e, rd_append_right, rd_fixedBits _ _ _ hj]

theorem code_pair (q : Fin v.stateCount) (k : ℕ) (hk : k < 2) :
    readTapeBit (VerifierEncoding.code v) (cHb v + 2 * q.val + k) =
      [v.machine.halted q, v.accepting q].getD k false := by
  rw [code_split, rd_append_left (by rw [header_length]; simp [cAt]; omega)]
  have e : cHb v + 2 * q.val + k =
      (List.replicate v.tapeCount true ++ [false] ++ List.replicate v.stateCount true ++ [false] ++
        fixedBits (cWd v) v.machine.start.val).length + (q.val * 2 + k) := by
    rw [pre_length]; ring
  rw [e, rd_append_right, rd_flatten_ofFn 2 _ (fun _ => rfl) q k hk]
  unfold readTapeBit
  rfl

/-- The halted bit of control `q` is at `hb + 2q`. -/
theorem code_halted (q : Fin v.stateCount) :
    readTapeBit (VerifierEncoding.code v) (cHb v + 2 * q.val) = v.machine.halted q := by
  simpa using code_pair v q 0 (by norm_num)

/-- The accepting bit of control `q` is at `hb + 2q + 1`. -/
theorem code_accepting (q : Fin v.stateCount) :
    readTapeBit (VerifierEncoding.code v) (cHb v + 2 * q.val + 1) = v.accepting q := by
  simpa using code_pair v q 1 (by norm_num)

theorem code_entry (q : Fin v.stateCount) (mk : ℕ) (hmk : mk < 2 ^ v.tapeCount) (k : ℕ)
    (hk : k < cEw v) :
    readTapeBit (VerifierEncoding.code v) (cAt v + q.val * cBs v + mk * cEw v + k) =
      readTapeBit (actionCode (cWd v) (v.machine.rule q (maskDisplay v.tapeCount mk))) k := by
  rw [code_split, rd_append_right' _ _ (by rw [header_length]; omega), header_length]
  rw [show cAt v + q.val * cBs v + mk * cEw v + k - cAt v = q.val * cBs v + (mk * cEw v + k) by omega]
  have hin : mk * cEw v + k < cBs v := by
    unfold cBs
    have : (mk + 1) * cEw v ≤ 2 ^ v.tapeCount * cEw v := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  rw [rd_flatten_ofFn (cBs v) _ ?_ q _ hin]
  · rw [rd_flatten_ofFn (cEw v) _ (fun _ => by rw [actionCode_length]; rfl) ⟨mk, hmk⟩ k hk]
    rfl
  · intro j
    rw [List.length_flatten, List.map_ofFn]
    have : (List.length ∘ fun mask : Fin (2 ^ v.tapeCount) =>
        actionCode (cWd v) (v.machine.rule j (fun tape => mask.val.testBit tape.val))) =
        fun _ => cEw v := by funext i; simp [actionCode_length, cEw]
    rw [this, List.sum_ofFn]
    simp [cBs]

/-- The first bit of an entry says whether it is an action. -/
theorem code_entry_some (q : Fin v.stateCount) (mk : ℕ) (hmk : mk < 2 ^ v.tapeCount) :
    readTapeBit (VerifierEncoding.code v) (cAt v + q.val * cBs v + mk * cEw v) =
      (v.machine.rule q (maskDisplay v.tapeCount mk)).isSome := by
  have := code_entry v q mk hmk 0 (by simp [cEw])
  rw [Nat.add_zero] at this
  rw [this]
  cases v.machine.rule q (maskDisplay v.tapeCount mk) <;> rfl

/-- The rest of an entry is the body of the decoded action (all zero for `none`). -/
theorem code_entry_body (q : Fin v.stateCount) (mk : ℕ) (hmk : mk < 2 ^ v.tapeCount) (k : ℕ)
    (hk : k < cWd v + 4 * v.tapeCount) :
    readTapeBit (VerifierEncoding.code v) (cAt v + q.val * cBs v + mk * cEw v + 1 + k) =
      readTapeBit (actionBody (cWd v) (decodedAction v.machine q (maskDisplay v.tapeCount mk))) k := by
  rw [show cAt v + q.val * cBs v + mk * cEw v + 1 + k = cAt v + q.val * cBs v + mk * cEw v + (k + 1) by
    ring, code_entry v q mk hmk (k + 1) (by unfold cEw; omega)]
  unfold decodedAction
  cases hr : v.machine.rule q (maskDisplay v.tapeCount mk) with
  | some a =>
    simp only [actionCode, Option.getD_some, actionBody]
    rw [rd_cons_succ]
  | none =>
    simp only [actionCode, Option.getD_none]
    rw [rd_cons_succ, rd_replicate _ _ hk]
    unfold actionBody noAction zeroCtl
    simp only
    by_cases hkw : k < cWd v
    · rw [rd_append_left (by simp [fixedBits]; omega), rd_fixedBits _ _ _ hkw]
      simp
    · rw [rd_append_right' _ _ (by simp [fixedBits]; omega)]
      simp only [fixedBits, List.length_ofFn]
      have hk' : k - cWd v < 4 * v.tapeCount := by omega
      have e : k - cWd v = ((k - cWd v) / 4) * 4 + (k - cWd v) % 4 := by omega
      rw [e, rd_flatten_ofFn 4 _ (fun _ => rfl) ⟨(k - cWd v) / 4, by omega⟩ _ (by omega)]
      have h4 : (k - cWd v) % 4 < 4 := by omega
      generalize (k - cWd v) % 4 = k4 at h4 ⊢
      interval_cases k4 <;> rfl

/-- Bit `j < wd` of the decoded next control. -/
theorem code_nextBit (q : Fin v.stateCount) (mk : ℕ) (hmk : mk < 2 ^ v.tapeCount) (j : ℕ)
    (hj : j < cWd v) :
    readTapeBit (VerifierEncoding.code v) (cAt v + q.val * cBs v + mk * cEw v + 1 + j) =
      (decodedAction v.machine q (maskDisplay v.tapeCount mk)).nextControl.val.testBit j := by
  rw [code_entry_body v q mk hmk j (by omega), actionBody,
    rd_append_left (by simp [fixedBits]; omega), rd_fixedBits _ _ _ hj]

/-- Bit `k < 4` of tape `i`'s write and move codes of the decoded action. -/
theorem code_actBit (q : Fin v.stateCount) (mk : ℕ) (hmk : mk < 2 ^ v.tapeCount)
    (i : Fin v.tapeCount) (k : ℕ) (hk : k < 4) :
    readTapeBit (VerifierEncoding.code v)
        (cAt v + q.val * cBs v + mk * cEw v + 1 + cWd v + 4 * i.val + k) =
      readTapeBit (writeCode ((decodedAction v.machine q (maskDisplay v.tapeCount mk)).write i) ++
        moveCode ((decodedAction v.machine q (maskDisplay v.tapeCount mk)).move i)) k := by
  have hi := i.isLt
  rw [show cAt v + q.val * cBs v + mk * cEw v + 1 + cWd v + 4 * i.val + k =
      cAt v + q.val * cBs v + mk * cEw v + 1 + (cWd v + (i.val * 4 + k)) by ring,
    code_entry_body v q mk hmk _ (by omega), actionBody, rd_append_right' _ _ (by simp [fixedBits])]
  simp only [fixedBits, List.length_ofFn, Nat.add_sub_cancel_left]
  rw [rd_flatten_ofFn 4 _ (fun j => by
    simp [writeCode_length, moveCode_length]) i k hk]

end Layout

end NearCubicGates.Adapters.Refuter
