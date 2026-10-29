import SourceAdapters.Compile.CNFTokens

/-!
# The finite control read off the verifier code bits

proof of `lem:multitape-refuter` (the finite control is part of the request, its code length is paid) and the native code
`VerifierEncoding.code` (L `Statement.lean:687`: unary tape count, unary state count, the start state in
`natBitLength s` bits, one (halted, accepting) pair per state, then one action record of `1 + w + 4t` bits per
(state, scan mask)). The printing program keeps the code bits in a store and reads the table at computed positions;
`TD.ofBits` is that reading, and `ofBits_rep` proves it represents the machine (`TD.Rep`), so `CNFTokens.requestToks_eq`
applies to it.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
  NearCubicWires.FinitePredicateCircuit NearCubicWires.RepairSource NearCubicWires.RepairSource.VerifierEncoding
set_option autoImplicit false

/-- A stored bit (`1` is true). -/
def bitAt (cb : List ℕ) (p : ℕ) : Bool := decide (cb.getD p 0 = 1)

/-- The number whose `w` low bits are stored at `p, p+1, …` (least significant first). -/
def numAt (f : ℕ → Bool) (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | w + 1 => numAt f p w + (f (p + w)).toNat * 2 ^ w

/-- The table, read from stored code bits with geometry `t w o2 o3 R`. -/
def TD.ofBits (cb : List ℕ) (t w o2 o3 R : ℕ) : TD where
  hl q := bitAt cb (o2 + 2 * q)
  ac q := bitAt cb (o2 + 2 * q + 1)
  pr q m := bitAt cb (o3 + (q * 2 ^ t + m) * R)
  nc q m := numAt (bitAt cb) (o3 + (q * 2 ^ t + m) * R + 1) w
  wr q m tape := if bitAt cb (o3 + (q * 2 ^ t + m) * R + 1 + w + 4 * tape)
    then some (bitAt cb (o3 + (q * 2 ^ t + m) * R + 1 + w + 4 * tape + 1)) else none
  mv q m tape pos := if bitAt cb (o3 + (q * 2 ^ t + m) * R + 1 + w + 4 * tape + 3) then pos + 1
    else if bitAt cb (o3 + (q * 2 ^ t + m) * R + 1 + w + 4 * tape + 2) then pos else pos - 1

/-! ## Geometry of the code -/

def codeW (v : Verifier) : ℕ := natBitLength v.stateCount
def codeO1 (v : Verifier) : ℕ := v.tapeCount + 1 + v.stateCount + 1
def codeO2 (v : Verifier) : ℕ := codeO1 v + codeW v
def codeO3 (v : Verifier) : ℕ := codeO2 v + 2 * v.stateCount
def codeR (v : Verifier) : ℕ := 1 + codeW v + 4 * v.tapeCount

/-- The stored code bits. -/
def codeBits (v : Verifier) : List ℕ := (code v).map Bool.toNat

theorem bitAt_map (l : List Bool) (p : ℕ) : bitAt (l.map Bool.toNat) p = l.getD p false := by
  unfold bitAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : l[p]? with
  | none => simp
  | some b => cases b <;> simp

theorem getD_flatten_blocks {α : Type} (d : α) (L : ℕ) :
    ∀ (k : ℕ) (f : Fin k → List α), (∀ i, (f i).length = L) → ∀ (i j : ℕ) (hi : i < k), j < L →
      (List.ofFn f).flatten.getD (i * L + j) d = (f ⟨i, hi⟩).getD j d := by
  intro k
  induction k with
  | zero => intro f _ i j hi; omega
  | succ k ih =>
      intro f hf i j hi hj
      rw [List.ofFn_succ, List.flatten_cons]
      rcases i with _ | i
      · rw [Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by rw [hf 0]; exact hj)]
        rfl
      · rw [List.getD_append_right _ _ _ _ (by rw [hf 0]; nlinarith), hf 0,
          show (i + 1) * L + j - L = i * L + j by rw [Nat.add_mul, Nat.one_mul]; omega]
        exact ih (fun i => f i.succ) (fun i => hf i.succ) i j (by omega) hj

theorem fixedBits_length (w x : ℕ) : (fixedBits w x).length = w := by simp [fixedBits]

theorem fixedBits_getD (w x i : ℕ) (hi : i < w) : (fixedBits w x).getD i false = x.testBit i := by
  simp [fixedBits, List.getD_eq_getElem?_getD, hi]

theorem numAt_testBit (f : ℕ → Bool) (p x : ℕ) :
    ∀ w, (∀ i < w, f (p + i) = x.testBit i) → numAt f p w = x % 2 ^ w := by
  intro w
  induction w with
  | zero => intro _; simp [numAt, Nat.mod_one]
  | succ w ih =>
      intro h
      rw [numAt, ih (fun i hi => h i (by omega)), h w (by omega), Nat.pow_succ, Nat.mod_mul,
        Nat.testBit_eq_decide_div_mod_eq]
      have h2 : x / 2 ^ w % 2 < 2 := Nat.mod_lt _ (by norm_num)
      rcases (by omega : x / 2 ^ w % 2 = 0 ∨ x / 2 ^ w % 2 = 1) with h0 | h0 <;> simp [h0]

theorem lt_two_pow_natBitLength (v : ℕ) : v < 2 ^ natBitLength v :=
  Nat.lt_pow_succ_log_self (by norm_num) v

theorem length_flatten_ofFn {α : Type} (L : ℕ) :
    ∀ (k : ℕ) (f : Fin k → List α), (∀ i, (f i).length = L) → (List.ofFn f).flatten.length = k * L := by
  intro k
  induction k with
  | zero => intro f _; simp
  | succ k ih =>
      intro f hf
      rw [List.ofFn_succ, List.flatten_cons, List.length_append, hf 0, ih _ (fun i => hf i.succ)]
      ring

theorem actionCode_length {t s : ℕ} (w : ℕ) (a : Option (Action t s)) : (actionCode w a).length = 1 + w + 4 * t := by
  cases a with
  | none => simp [actionCode]; omega
  | some a =>
      have h : ∀ i : Fin t, (writeCode (a.write i) ++ moveCode (a.move i)).length = 4 := by
        intro i
        cases hw : a.write i with
        | none => cases a.move i <;> rfl
        | some b => cases b <;> cases a.move i <;> rfl
      simp only [actionCode, List.length_cons, List.length_append, fixedBits_length]
      rw [length_flatten_ofFn 4 t _ h]
      ring

/-- The code as header ++ pairs ++ table. -/
theorem code_split (v : Verifier) : code v =
    (List.replicate v.tapeCount true ++ [false] ++ List.replicate v.stateCount true ++ [false] ++
      fixedBits (codeW v) v.machine.start.val) ++
    (List.ofFn fun i : Fin v.stateCount => [v.machine.halted i, v.accepting i]).flatten ++
    (List.ofFn fun i : Fin v.stateCount =>
      (List.ofFn fun mask : Fin (2 ^ v.tapeCount) =>
        actionCode (codeW v) (v.machine.rule i (fun tape => mask.val.testBit tape.val))).flatten).flatten := rfl

theorem code_head_length (v : Verifier) :
    (List.replicate v.tapeCount true ++ [false] ++ List.replicate v.stateCount true ++ [false] ++
      fixedBits (codeW v) v.machine.start.val).length = codeO2 v := by
  simp [codeO2, codeO1]
  omega

theorem pairs_length (v : Verifier) :
    (List.ofFn fun i : Fin v.stateCount => [v.machine.halted i, v.accepting i]).flatten.length =
      2 * v.stateCount := by
  simp [List.length_flatten, List.sum_ofFn]
  ring

/-- Halted and accepting bits. -/
theorem codeBit_pair (v : Verifier) (q : Fin v.stateCount) (k : ℕ) (hk : k < 2) :
    (code v).getD (codeO2 v + 2 * q.val + k) false = [v.machine.halted q, v.accepting q].getD k false := by
  rw [code_split, List.append_assoc, show codeO2 v + 2 * q.val + k = (List.replicate v.tapeCount true ++ [false] ++
    List.replicate v.stateCount true ++ [false] ++ fixedBits (codeW v) v.machine.start.val).length +
      (q.val * 2 + k) by rw [code_head_length]; ring]
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by rw [pairs_length]; omega)]
  exact getD_flatten_blocks false 2 v.stateCount _ (fun i => rfl) q.val k q.isLt hk

/-- Bit `j` of the action record of `(q, m)`. -/
theorem codeBit_action (v : Verifier) (q : Fin v.stateCount) (m : Fin (2 ^ v.tapeCount)) (j : ℕ)
    (hj : j < codeR v) :
    (code v).getD (codeO3 v + (q.val * 2 ^ v.tapeCount + m.val) * codeR v + j) false =
      (actionCode (codeW v) (v.machine.rule q (scanMask m))).getD j false := by
  rw [code_split, show codeO3 v + (q.val * 2 ^ v.tapeCount + m.val) * codeR v + j =
    ((List.replicate v.tapeCount true ++ [false] ++ List.replicate v.stateCount true ++ [false] ++
      fixedBits (codeW v) v.machine.start.val) ++
    (List.ofFn fun i : Fin v.stateCount => [v.machine.halted i, v.accepting i]).flatten).length +
      (q.val * (2 ^ v.tapeCount * codeR v) + (m.val * codeR v + j)) by
        rw [List.length_append, code_head_length, pairs_length, codeO3]; ring]
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  have hblk : ∀ i : Fin v.stateCount, ((List.ofFn fun mask : Fin (2 ^ v.tapeCount) =>
      actionCode (codeW v) (v.machine.rule i (fun tape => mask.val.testBit tape.val))).flatten).length =
        2 ^ v.tapeCount * codeR v := by
    intro i
    rw [length_flatten_ofFn (codeR v) _ _ (fun mask => actionCode_length _ _), codeR]
  have hm : m.val * codeR v + j < 2 ^ v.tapeCount * codeR v := by
    have := m.isLt
    nlinarith
  rw [getD_flatten_blocks false _ v.stateCount _ hblk q.val _ q.isLt hm]
  exact getD_flatten_blocks false (codeR v) _ _ (fun i => actionCode_length _ _) m.val j m.isLt hj

theorem codeBits_start (v : Verifier) :
    numAt (bitAt (codeBits v)) (codeO1 v) (codeW v) = v.machine.start.val := by
  rw [numAt_testBit _ _ v.machine.start.val (codeW v) (fun i hi => ?_)]
  · apply Nat.mod_eq_of_lt
    have h1 := v.machine.start.isLt
    have h2 : v.stateCount < 2 ^ codeW v := lt_two_pow_natBitLength _
    omega
  · rw [codeBits, bitAt_map, code_split, List.append_assoc, List.append_assoc,
      show codeO1 v + i = (List.replicate v.tapeCount true ++ [false] ++ List.replicate v.stateCount true ++
        [false]).length + i by simp [codeO1]; omega]
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
      List.getD_append _ _ _ _ (by rw [fixedBits_length]; exact hi), fixedBits_getD _ _ _ hi]

theorem writeCode_getD (o : Option Bool) :
    (writeCode o).getD 0 false = o.isSome ∧ (writeCode o).getD 1 false = (o.getD false) := by
  cases o with
  | none => exact ⟨rfl, rfl⟩
  | some b => cases b <;> exact ⟨rfl, rfl⟩

/-- **The stored code represents the machine.** -/
theorem ofBits_rep (v : Verifier) :
    (TD.ofBits (codeBits v) v.tapeCount (codeW v) (codeO2 v) (codeO3 v) (codeR v)).Rep v.machine v.accepting := by
  have hc : ∀ p, bitAt (codeBits v) p = (code v).getD p false := fun p => bitAt_map _ p
  have act : ∀ (q : Fin v.stateCount) (m : Fin (2 ^ v.tapeCount)) (j : ℕ), j < codeR v →
      bitAt (codeBits v) (codeO3 v + (q.val * 2 ^ v.tapeCount + m.val) * codeR v + j) =
        (actionCode (codeW v) (v.machine.rule q (scanMask m))).getD j false := by
    intro q m j hj
    rw [hc, codeBit_action v q m j hj]
  have rec4 : ∀ (q : Fin v.stateCount) (m : Fin (2 ^ v.tapeCount)) (a : Action v.tapeCount v.stateCount)
      (tape : Fin v.tapeCount) (k : ℕ), k < 4 → v.machine.rule q (scanMask m) = some a →
      bitAt (codeBits v) (codeO3 v + (q.val * 2 ^ v.tapeCount + m.val) * codeR v + 1 + codeW v + 4 * tape.val + k) =
        (writeCode (a.write tape) ++ moveCode (a.move tape)).getD k false := by
    intro q m a tape k hk ha
    have ht := tape.isLt
    rw [show codeO3 v + (q.val * 2 ^ v.tapeCount + m.val) * codeR v + 1 + codeW v + 4 * tape.val + k =
      codeO3 v + (q.val * 2 ^ v.tapeCount + m.val) * codeR v + (1 + codeW v + (tape.val * 4 + k)) by ring,
      act q m _ (by unfold codeR; omega), ha, actionCode]
    rw [show 1 + codeW v + (tape.val * 4 + k) = (codeW v + (tape.val * 4 + k)) + 1 by ring, List.getD_cons_succ,
      show codeW v + (tape.val * 4 + k) = (fixedBits (codeW v) a.nextControl.val).length +
      (tape.val * 4 + k) by rw [fixedBits_length]]
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
    refine getD_flatten_blocks false 4 v.tapeCount _ (fun i => ?_) tape.val k tape.isLt hk
    cases hw : a.write i with
    | none => cases a.move i <;> rfl
    | some b => cases b <;> cases a.move i <;> rfl
  refine ⟨fun q => ?_, fun q => ?_, fun q m => ?_, fun q m a ha => ?_, fun q m a tape ha => ?_,
    fun q m a tape pos ha => ?_⟩
  · simp only [TD.ofBits]
    rw [hc, show codeO2 v + 2 * q.val = codeO2 v + 2 * q.val + 0 by rfl, codeBit_pair v q 0 (by norm_num)]
    rfl
  · simp only [TD.ofBits]
    rw [hc, codeBit_pair v q 1 (by norm_num)]
    rfl
  · simp only [TD.ofBits]
    rw [show codeO3 v + (q.val * 2 ^ v.tapeCount + m.val) * codeR v =
      codeO3 v + (q.val * 2 ^ v.tapeCount + m.val) * codeR v + 0 by rfl, act q m 0 (by unfold codeR; omega)]
    cases v.machine.rule q (scanMask m) <;> rfl
  · simp only [TD.ofBits]
    rw [numAt_testBit _ _ a.nextControl.val (codeW v) (fun i hi => ?_)]
    · apply Nat.mod_eq_of_lt
      have h1 := a.nextControl.isLt
      have h2 : v.stateCount < 2 ^ codeW v := lt_two_pow_natBitLength _
      omega
    · rw [show codeO3 v + (q.val * 2 ^ v.tapeCount + m.val) * codeR v + 1 + i =
        codeO3 v + (q.val * 2 ^ v.tapeCount + m.val) * codeR v + (i + 1) by ring,
        act q m _ (by unfold codeR; omega), ha, actionCode, List.getD_cons_succ,
        List.getD_append _ _ _ _ (by rw [fixedBits_length]; exact hi), fixedBits_getD _ _ _ hi]
  · simp only [TD.ofBits]
    have h0 := rec4 q m a tape 0 (by norm_num) ha
    have h1 := rec4 q m a tape 1 (by norm_num) ha
    rw [Nat.add_zero] at h0
    have hw := writeCode_getD (a.write tape)
    rw [List.getD_append _ _ _ _ (by cases a.write tape with
      | none => simp [writeCode] | some b => cases b <;> simp [writeCode])] at h0 h1
    rw [h0, h1, hw.1, hw.2]
    cases a.write tape <;> rfl
  · simp only [TD.ofBits]
    have h2 := rec4 q m a tape 2 (by norm_num) ha
    have h3 := rec4 q m a tape 3 (by norm_num) ha
    have hl : (writeCode (a.write tape)).length = 2 := by
      cases a.write tape with
      | none => rfl
      | some b => cases b <;> rfl
    rw [List.getD_append_right _ _ _ _ (by omega), hl] at h2 h3
    rw [h2, h3]
    cases a.move tape <;> simp [moveCode, HeadMove.apply]

end NearCubicGates.Adapters.Compile
