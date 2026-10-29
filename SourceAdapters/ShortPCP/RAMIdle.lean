import SourceAdapters.ACSP.Model

/-!
# The counted idle loop and the verdict of `lem:tm-ram`

Paper anchor: proof of `lem:tm-ram`, "Idling" and "The verdict":
"an idle block of exactly `8` instructions. In order, they are: `add` `8` to the counter; `cmp` the counter with the
constant `T_n − 8`; five `nop`s; `jne` back to the start of the idle block if the comparison found the counter
different from `T_n − 8` … So if the counter is at most `T_n − 16` on entry, the loop ends after the pass at whose
end exactly `T_n − 8` steps have been made. … Then `M_n` executes six `nop`s and one `je` on the verdict register.
The `je` jumps to an instruction `(out, reject)` if the verdict is rejection, and otherwise falls through to an
instruction `(out, accept)`. … After these seven steps exactly `T_n − 1` steps have been made, and the `out`
instruction with the verdict is executed at step `T_n − 1`."

This module proves that statement in the RAM model of `ACSP/Model.lean` (`def:ram`):
entering the block at step `c` (a multiple of `8`, `c ≤ T − 16`) with the counter equal to `c`, the deterministic
read-free run reaches the `out` instruction at step exactly `T − 1`, every intermediate step is a legal step of
`Ram.Step` that leaves memory unchanged, and the final configuration is accepting iff the verdict register is
nonzero.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP

open NearCubicGates.Adapters.ACSP

variable {M : Ram}

/-! ## Deterministic successor of read-free instructions -/

/-- The successor configuration for `nop`, an arithmetic-unit operation, `je`, `jne`, `jmp` (identity elsewhere). -/
def pureSucc (S : M.Config) : M.Config :=
  match M.instrAt S.pc with
  | some .nop => S.next
  | some (.arith op i x y) => S.setNext i (some (M.alu op (S.val x) (S.val y)))
  | some (.je i c) => if S.val (.reg i) = 0 then S.jump c else S.next
  | some (.jne i c) => if S.val (.reg i) ≠ 0 then S.jump c else S.next
  | some (.jmp c) => S.jump c
  | _ => S

/-- `I_pc` is one of the read-free, memory-free instructions. -/
def IsPureAt (S : M.Config) : Prop :=
  match M.instrAt S.pc with
  | some .nop => True
  | some (.arith _ _ _ _) => True
  | some (.je _ _) => True
  | some (.jne _ _) => True
  | some (.jmp _) => True
  | _ => False

/-- A read-free instruction makes a legal step (Def. 6.11) to `pureSucc S`, leaving memory unchanged. -/
theorem step_pureSucc (S : M.Config) (mem : M.Memory) (h : IsPureAt S) : M.Step S mem (pureSucc S) mem := by
  unfold IsPureAt at h
  unfold Ram.Step pureSucc
  rcases hI : M.instrAt S.pc with _ | I
  · simp [hI] at h
  · rw [hI] at h
    cases I <;> simp_all

/-- A read-free instruction is not `out`: the configuration is not final. -/
theorem not_final_of_pure (S : M.Config) (h : IsPureAt S) : ¬ M.Final S := by
  rintro ⟨b, hb⟩
  unfold IsPureAt at h
  rw [hb] at h
  exact h

/-! ## The idle block -/

/-- The comparison operation of `def:ram` returns `1` for `x < y`, `0` for
`x = y`, and `2^w - 1` for `x > y`. -/
def cmpFn {w : ℕ} (x y : BitVec w) : BitVec w :=
  if x.toNat < y.toNat then 1 else if x = y then 0 else -1

/-- `M_n`'s arithmetic unit: `0 = add`, `1 = sub`, `2 = and`, `3 = cmp`. -/
def mnAlu (w : ℕ) : Fin 4 → BitVec w → BitVec w → BitVec w :=
  ![(· + ·), (· - ·), (· &&& ·), cmpFn]

/-- The 17 instructions at positions `b, …, b + 16`: the idle block (8), six `nop`s and `je` on the verdict
register (7), `(out, accept)`, `(out, reject)`. -/
def idleCode {w k ops : ℕ} (addOp cmpOp : Fin ops) (cnt tmp vd : Fin k) (b T : ℕ) : List (Instr w k ops) :=
  [ .arith addOp cnt (.reg cnt) (.const (BitVec.ofNat w 8)),
    .arith cmpOp tmp (.reg cnt) (.const (BitVec.ofNat w (T - 8))),
    .nop, .nop, .nop, .nop, .nop,
    .jne tmp b,
    .nop, .nop, .nop, .nop, .nop, .nop,
    .je vd (b + 16),
    .out true,
    .out false ]

/-- The hypotheses on the machine: the block sits at `b`, the arithmetic unit has `add` and `cmp`, and the three
registers are distinct. -/
structure IdleSetup (M : Ram) where
  addOp : Fin M.ops
  cmpOp : Fin M.ops
  cnt : Fin M.k
  tmp : Fin M.k
  vd : Fin M.k
  b : ℕ
  T : ℕ
  add_eq : M.alu addOp = fun x y => x + y
  cmp_eq : M.alu cmpOp = cmpFn
  cnt_tmp : cnt ≠ tmp
  vd_cnt : vd ≠ cnt
  vd_tmp : vd ≠ tmp
  code_eq : ∀ i, i < 17 → M.code[b + i]? = (idleCode (w := M.w) addOp cmpOp cnt tmp vd b T)[i]?
  fits : b + 17 ≤ 2 ^ M.w
  T_lt : T < 2 ^ M.w
  T_ge : 16 ≤ T
  T_dvd : 8 ∣ T

variable (I : IdleSetup M)

theorem instrAt_of_pc (S : M.Config) (a : ℕ) (hpc : S.pc = BitVec.ofNat M.w a) (ha : a < 2 ^ M.w) :
    M.instrAt S.pc = M.code[a]? := by
  simp [Ram.instrAt, hpc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem ofNat_inj {w a b : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    BitVec.ofNat w a = BitVec.ofNat w b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
  · rintro rfl
    rfl

theorem pc_step {w a c : ℕ} (h : a + 1 = c) : BitVec.ofNat w a + 1#w = BitVec.ofNat w c := by
  subst h; exact BitVec.ofNat_add_ofNat a 1

theorem one_ne_zero_of {w : ℕ} (hw : 1 < 2 ^ w) : (1 : BitVec w) ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [show (1 : BitVec w) = BitVec.ofNat w 1 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw] at this
  simp at this

theorem neg_one_ne_zero_of {w : ℕ} (hw : 1 < 2 ^ w) : (-1 : BitVec w) ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_neg, show (1 : BitVec w) = BitVec.ofNat w 1 from rfl, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt (by omega)] at this
  simp at this
  omega

/-- A configuration in the block: `pc = a`, counter `= v`, verdict register `= rv`. -/
def At (a v : ℕ) (rv : Option (BitVec M.w)) (S : M.Config) : Prop :=
  S.pc = BitVec.ofNat M.w a ∧ S.regs I.cnt = some (BitVec.ofNat M.w v) ∧ S.regs I.vd = rv

/-- One `nop` inside the block. -/
theorem nop_step (S : M.Config) (a v : ℕ) (rv : Option (BitVec M.w)) (hS : At I a v rv S)
    (ha : a + 1 < 2 ^ M.w) (hI : M.code[a]? = some .nop) :
    IsPureAt S ∧ At I (a + 1) v rv (pureSucc S) := by
  have hi : M.instrAt S.pc = some .nop := by rw [instrAt_of_pc S a hS.1 (by omega), hI]
  refine ⟨by simp [IsPureAt, hi], ?_⟩
  simp only [pureSucc, hi]
  exact ⟨by simp only [Ram.Config.next, hS.1]; exact pc_step rfl, hS.2.1, hS.2.2⟩

theorem iterate_succ' {α : Type} (f : α → α) (n : ℕ) (x : α) : f^[n + 1] x = f^[n] (f x) :=
  Function.iterate_succ_apply f n x

/-- Several `nop`s in a row. -/
theorem nops (S : M.Config) (a v j : ℕ) (rv : Option (BitVec M.w)) (hS : At I a v rv S)
    (ha : a + j < 2 ^ M.w) (hI : ∀ i < j, M.code[a + i]? = some .nop) :
    (∀ i < j, IsPureAt (pureSucc^[i] S)) ∧ At I (a + j) v rv (pureSucc^[j] S) := by
  induction j generalizing S a with
  | zero => exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), by simpa using hS⟩
  | succ j ih =>
    obtain ⟨hp, hS'⟩ := nop_step I S a v rv hS (by omega) (by simpa using hI 0 (by omega))
    obtain ⟨hps, hfin⟩ := ih (pureSucc S) (a + 1) hS' (by omega)
      (fun i hi => by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hI (i + 1) (by omega))
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases i with _ | i
      · simpa using hp
      · rw [iterate_succ']
        exact hps i (by omega)
    · rw [iterate_succ']
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using hfin

/-- **One pass of the idle block.** Entering at `b` with counter `v`, `v + 8 ≤ T − 8`, the pass makes exactly `8`
read-free steps, adds `8` to the counter, and returns to `b` unless the counter has reached `T − 8`, in which case
it falls through to `b + 8`. -/
theorem idle_pass (S : M.Config) (v : ℕ) (rv : Option (BitVec M.w)) (hS : At I I.b v rv S)
    (hv : v + 16 ≤ I.T) :
    (∀ i < 8, IsPureAt (pureSucc^[i] S)) ∧
      At I (if v + 8 = I.T - 8 then I.b + 8 else I.b) (v + 8) rv (pureSucc^[8] S) := by
  have hT := I.T_lt
  have hfits := I.fits
  have code : ∀ i, i < 17 → M.code[I.b + i]? = _ := I.code_eq
  -- step 1: `add` 8 to the counter
  have h0 : M.instrAt S.pc = some (.arith I.addOp I.cnt (.reg I.cnt) (.const (BitVec.ofNat M.w 8))) := by
    rw [instrAt_of_pc S I.b hS.1 (by omega)]; simpa [idleCode] using code 0 (by norm_num)
  set S1 := pureSucc S with hS1
  have hS1v : At I (I.b + 1) (v + 8) rv S1 := by
    simp only [hS1, pureSucc, h0, I.add_eq]
    refine ⟨by simp only [Ram.Config.setNext, hS.1]; exact pc_step rfl, ?_, ?_⟩
    · simp [Ram.Config.setNext, Ram.Config.val, hS.2.1, BitVec.ofNat_add_ofNat]
    · simp [Ram.Config.setNext, Function.update_of_ne I.vd_cnt, hS.2.2]
  have hp0 : IsPureAt S := by simp [IsPureAt, h0]
  -- step 2: `cmp` the counter with `T − 8`
  have h1 : M.instrAt S1.pc = some (.arith I.cmpOp I.tmp (.reg I.cnt)
      (.const (BitVec.ofNat M.w (I.T - 8)))) := by
    rw [instrAt_of_pc S1 (I.b + 1) hS1v.1 (by omega)]; simpa [idleCode] using code 1 (by norm_num)
  set S2 := pureSucc S1 with hS2
  have hcmp : S2.regs I.tmp = some (cmpFn (BitVec.ofNat M.w (v + 8)) (BitVec.ofNat M.w (I.T - 8))) := by
    simp [hS2, pureSucc, h1, I.cmp_eq, Ram.Config.setNext, Ram.Config.val, hS1v.2.1]
  have hS2v : At I (I.b + 2) (v + 8) rv S2 := by
    simp only [hS2, pureSucc, h1]
    refine ⟨by simp only [Ram.Config.setNext, hS1v.1]; exact pc_step rfl, ?_, ?_⟩
    · simp [Ram.Config.setNext, Function.update_of_ne I.cnt_tmp, hS1v.2.1]
    · simp [Ram.Config.setNext, Function.update_of_ne I.vd_tmp, hS1v.2.2]
  have hp1 : IsPureAt S1 := by simp [IsPureAt, h1]
  -- steps 3–7: five `nop`s
  obtain ⟨hpn, hS7v⟩ := nops I S2 (I.b + 2) (v + 8) 5 rv hS2v (by omega) (fun i hi => by
    have := code (2 + i) (by omega)
    interval_cases i <;> simpa [idleCode, Nat.add_assoc] using this)
  set S7 := pureSucc^[5] S2 with hS7
  have htmp7 : S7.regs I.tmp = S2.regs I.tmp := by
    have key : ∀ j ≤ 5, (pureSucc^[j] S2).regs I.tmp = S2.regs I.tmp := by
      intro j hj
      induction j with
      | zero => rfl
      | succ j ih =>
        have hpj := nops I S2 (I.b + 2) (v + 8) j rv hS2v (by omega) (fun i hi => by
          have := code (2 + i) (by omega)
          have hi5 : i < 5 := by omega
          interval_cases i <;> simpa [idleCode, Nat.add_assoc] using this)
        rw [Function.iterate_succ_apply']
        have hc : M.code[I.b + 2 + j]? = some .nop := by
          have := code (2 + j) (by omega)
          have hj5 : j < 5 := by omega
          interval_cases j <;> simpa [idleCode, Nat.add_assoc] using this
        have hi : M.instrAt (pureSucc^[j] S2).pc = some .nop := by
          rw [instrAt_of_pc _ (I.b + 2 + j) hpj.2.1 (by omega), hc]
        simp only [pureSucc, hi, Ram.Config.next]
        exact ih (by omega)
    exact key 5 le_rfl
  -- step 8: `jne` back to `b` unless the counter equals `T − 8`
  have h7 : M.instrAt S7.pc = some (.jne I.tmp I.b) := by
    rw [instrAt_of_pc S7 (I.b + 2 + 5) hS7v.1 (by omega)]; simpa [idleCode] using code 7 (by norm_num)
  have hp7 : IsPureAt S7 := by simp [IsPureAt, h7]
  have hv8 : v + 8 < 2 ^ M.w := by omega
  have hT8 : I.T - 8 < 2 ^ M.w := by omega
  have hcmpval : cmpFn (BitVec.ofNat M.w (v + 8)) (BitVec.ofNat M.w (I.T - 8)) = 0 ↔ v + 8 = I.T - 8 := by
    unfold cmpFn
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv8, Nat.mod_eq_of_lt hT8]
    by_cases hlt : v + 8 < I.T - 8
    · simp only [hlt, if_true]
      constructor
      · intro h
        exact absurd h (one_ne_zero_of (by omega))
      · intro h; omega
    · simp only [hlt, if_false]
      by_cases heq : v + 8 = I.T - 8
      · simp [heq]
      · rw [if_neg (by rw [ofNat_inj hv8 hT8]; exact heq)]
        constructor
        · intro h
          exact absurd h (neg_one_ne_zero_of (by omega))
        · intro h; exact absurd h heq
  have hS8 : pureSucc^[8] S = pureSucc S7 := by
    rw [hS7, hS2, hS1, ← Function.iterate_succ_apply' (f := pureSucc), ← Function.iterate_succ_apply,
      ← Function.iterate_succ_apply]
  refine ⟨fun i hi => ?_, ?_⟩
  · interval_cases i
    · simpa using hp0
    · simpa using hp1
    · simpa using hpn 0 (by norm_num)
    · simpa [Function.iterate_succ_apply] using hpn 1 (by norm_num)
    · simpa [Function.iterate_succ_apply] using hpn 2 (by norm_num)
    · simpa [Function.iterate_succ_apply] using hpn 3 (by norm_num)
    · simpa [Function.iterate_succ_apply] using hpn 4 (by norm_num)
    · simpa [Function.iterate_succ_apply, hS7] using hp7
  · rw [hS8]
    have hjne : pureSucc S7 =
        if cmpFn (BitVec.ofNat M.w (v + 8)) (BitVec.ofNat M.w (I.T - 8)) ≠ 0 then S7.jump I.b else S7.next := by
      simp only [pureSucc, h7, Ram.Config.val, htmp7, hcmp, Option.getD_some]
    rw [hjne]
    by_cases heq : v + 8 = I.T - 8
    · rw [if_neg (not_not.mpr (hcmpval.mpr heq)), if_pos heq]
      exact ⟨by simp only [Ram.Config.next, hS7v.1]; exact pc_step rfl, hS7v.2.1, hS7v.2.2⟩
    · rw [if_pos (fun h => heq (hcmpval.mp h)), if_neg heq]
      exact ⟨rfl, hS7v.2.1, hS7v.2.2⟩

/-- **The counted loop.** Entering at `b` with counter `v` such that `v + 8(q+1) = T − 8`, the loop makes exactly
`8(q+1)` read-free steps and leaves at `b + 8` with counter `T − 8`. -/
theorem idle_loop (rv : Option (BitVec M.w)) : ∀ (q : ℕ) (S : M.Config) (v : ℕ), At I I.b v rv S →
    v + 8 * (q + 1) = I.T - 8 →
    (∀ i < 8 * (q + 1), IsPureAt (pureSucc^[i] S)) ∧
      At I (I.b + 8) (I.T - 8) rv (pureSucc^[8 * (q + 1)] S) := by
  have hT := I.T_ge
  intro q
  induction q with
  | zero =>
    intro S v hS hv
    obtain ⟨hp, hA⟩ := idle_pass I S v rv hS (by omega)
    rw [if_pos (by omega)] at hA
    exact ⟨fun i hi => hp i (by omega), by simpa [show v + 8 = I.T - 8 by omega] using hA⟩
  | succ q ih =>
    intro S v hS hv
    obtain ⟨hp, hA⟩ := idle_pass I S v rv hS (by omega)
    rw [if_neg (by omega)] at hA
    obtain ⟨hp', hA'⟩ := ih (pureSucc^[8] S) (v + 8) hA (by omega)
    have hsplit : ∀ j, pureSucc^[j + 8] S = pureSucc^[j] (pureSucc^[8] S) :=
      fun j => Function.iterate_add_apply pureSucc j 8 S
    refine ⟨fun i hi => ?_, ?_⟩
    · by_cases h8 : i < 8
      · exact hp i h8
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 8 := ⟨i - 8, by omega⟩
        rw [hsplit]
        exact hp' j (by omega)
    · rw [show 8 * (q + 1 + 1) = 8 * (q + 1) + 8 by ring, hsplit]
      exact hA'

/-- **The verdict.** From `b + 8`: six `nop`s and `je` on the verdict register, `7` read-free steps, ending at
`(out, accept)` (position `b + 15`) if the verdict register is nonzero and at `(out, reject)` (`b + 16`) if it is
zero. -/
theorem verdict_tail (S : M.Config) (v : ℕ) (rv : Option (BitVec M.w)) (hS : At I (I.b + 8) v rv S) :
    (∀ i < 7, IsPureAt (pureSucc^[i] S)) ∧
      (pureSucc^[7] S).pc = BitVec.ofNat M.w (if rv.getD 0 = 0 then I.b + 16 else I.b + 15) := by
  have hfits := I.fits
  have code : ∀ i, i < 17 → M.code[I.b + i]? = _ := I.code_eq
  obtain ⟨hpn, hS6⟩ := nops I S (I.b + 8) v 6 rv hS (by omega) (fun i hi => by
    have := code (8 + i) (by omega)
    interval_cases i <;> simpa [idleCode, Nat.add_assoc] using this)
  set S6 := pureSucc^[6] S with hS6def
  have h6 : M.instrAt S6.pc = some (.je I.vd (I.b + 16)) := by
    rw [instrAt_of_pc S6 (I.b + 8 + 6) hS6.1 (by omega)]; simpa [idleCode] using code 14 (by norm_num)
  have hp6 : IsPureAt S6 := by simp [IsPureAt, h6]
  refine ⟨fun i hi => ?_, ?_⟩
  · by_cases h : i < 6
    · exact hpn i h
    · rw [show i = 6 by omega]; exact hp6
  · rw [show 7 = 6 + 1 from rfl, Function.iterate_succ_apply', ← hS6def]
    simp only [pureSucc, h6, Ram.Config.val, hS6.2.2]
    by_cases hz : rv.getD 0 = 0
    · rw [if_pos hz, if_pos hz]; rfl
    · rw [if_neg hz, if_neg hz]
      simp only [Ram.Config.next, hS6.1]
      exact pc_step (by omega)

/-- **`lem:tm-ram`, "Idling" + "The verdict", exact count.** If the block is entered at step `c`
with the counter equal to `c`, where `8 ∣ c` and `c ≤ T − 16`, then the next `T − 1 − c` steps are legal read-free
steps of Def. 6.11 that leave memory unchanged and pass no final configuration, and the configuration reached —
the one at step `T − 1` — is final, and accepting exactly when the verdict register is nonzero. -/
theorem idle_exact (S : M.Config) (c : ℕ) (rv : Option (BitVec M.w)) (hS : At I I.b c rv S)
    (hc8 : 8 ∣ c) (hc : c + 16 ≤ I.T) (mem : M.Memory) :
    (∀ i < I.T - 1 - c, M.Step (pureSucc^[i] S) mem (pureSucc^[i + 1] S) mem ∧ ¬ M.Final (pureSucc^[i] S)) ∧
      M.Final (pureSucc^[I.T - 1 - c] S) ∧
      (M.AcceptingConfig (pureSucc^[I.T - 1 - c] S) ↔ rv.getD 0 ≠ 0) := by
  have hT8 := I.T_dvd
  have hfits := I.fits
  obtain ⟨q, hq⟩ : ∃ q, c + 8 * (q + 1) = I.T - 8 := by
    obtain ⟨a, ha⟩ := hc8
    obtain ⟨b, hb⟩ := hT8
    exact ⟨b - a - 2, by omega⟩
  obtain ⟨hpl, hAl⟩ := idle_loop I rv q S c hS hq
  obtain ⟨hpt, hpc⟩ := verdict_tail I _ _ rv hAl
  have hm : I.T - 1 - c = 7 + 8 * (q + 1) := by omega
  have hsplit : ∀ j, pureSucc^[j + 8 * (q + 1)] S = pureSucc^[j] (pureSucc^[8 * (q + 1)] S) :=
    fun j => Function.iterate_add_apply pureSucc j _ S
  have hpure : ∀ i < I.T - 1 - c, IsPureAt (pureSucc^[i] S) := by
    intro i hi
    by_cases h : i < 8 * (q + 1)
    · exact hpl i h
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 8 * (q + 1) := ⟨i - 8 * (q + 1), by omega⟩
      rw [hsplit]
      exact hpt j (by omega)
  have hlast : (pureSucc^[I.T - 1 - c] S).pc =
      BitVec.ofNat M.w (if rv.getD 0 = 0 then I.b + 16 else I.b + 15) := by
    rw [hm, hsplit]; exact hpc
  have code : ∀ i, i < 17 → M.code[I.b + i]? = _ := I.code_eq
  have hout : M.instrAt (pureSucc^[I.T - 1 - c] S).pc = some (.out (rv.getD 0 ≠ 0)) := by
    by_cases hz : rv.getD 0 = 0
    · rw [if_pos hz] at hlast
      have hb : (decide (rv.getD 0 ≠ 0) : Bool) = false := by rw [decide_eq_false_iff_not, not_not]; exact hz
      rw [hb, instrAt_of_pc _ (I.b + 16) hlast (by omega)]
      simpa [idleCode] using code 16 (by norm_num)
    · rw [if_neg hz] at hlast
      have hb : (decide (rv.getD 0 ≠ 0) : Bool) = true := by rw [decide_eq_true_iff]; exact hz
      rw [hb, instrAt_of_pc _ (I.b + 15) hlast (by omega)]
      simpa [idleCode] using code 15 (by norm_num)
  refine ⟨fun i hi => ⟨?_, not_final_of_pure _ (hpure i hi)⟩, ⟨_, hout⟩, ?_⟩
  · rw [Function.iterate_succ_apply']
    exact step_pureSucc _ mem (hpure i hi)
  · unfold Ram.AcceptingConfig
    rw [hout]
    simp

/-- `idle_exact`, in the form used with the run of `M_n`: every step from entry to step `T − 1` is read-free, and the
instruction reached is `(out, [verdict ≠ 0])`. -/
theorem idle_exact_pure (S : M.Config) (c : ℕ) (rv : Option (BitVec M.w)) (hS : At I I.b c rv S)
    (hc8 : 8 ∣ c) (hc : c + 16 ≤ I.T) :
    (∀ i < I.T - 1 - c, IsPureAt (pureSucc^[i] S)) ∧
      M.instrAt (pureSucc^[I.T - 1 - c] S).pc = some (.out (rv.getD 0 ≠ 0)) := by
  have hT8 := I.T_dvd
  have hfits := I.fits
  obtain ⟨q, hq⟩ : ∃ q, c + 8 * (q + 1) = I.T - 8 := by
    obtain ⟨a, ha⟩ := hc8
    obtain ⟨b, hb⟩ := hT8
    exact ⟨b - a - 2, by omega⟩
  obtain ⟨hpl, hAl⟩ := idle_loop I rv q S c hS hq
  obtain ⟨hpt, hpc⟩ := verdict_tail I _ _ rv hAl
  have hm : I.T - 1 - c = 7 + 8 * (q + 1) := by omega
  have hsplit : ∀ j, pureSucc^[j + 8 * (q + 1)] S = pureSucc^[j] (pureSucc^[8 * (q + 1)] S) :=
    fun j => Function.iterate_add_apply pureSucc j _ S
  refine ⟨fun i hi => ?_, ?_⟩
  · by_cases h : i < 8 * (q + 1)
    · exact hpl i h
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 8 * (q + 1) := ⟨i - 8 * (q + 1), by omega⟩
      rw [hsplit]
      exact hpt j (by omega)
  · have hlast : (pureSucc^[I.T - 1 - c] S).pc =
        BitVec.ofNat M.w (if rv.getD 0 = 0 then I.b + 16 else I.b + 15) := by
      rw [hm, hsplit]; exact hpc
    have code : ∀ i, i < 17 → M.code[I.b + i]? = _ := I.code_eq
    by_cases hz : rv.getD 0 = 0
    · rw [if_pos hz] at hlast
      have hb : (decide (rv.getD 0 ≠ 0) : Bool) = false := by rw [decide_eq_false_iff_not, not_not]; exact hz
      rw [hb, instrAt_of_pc _ (I.b + 16) hlast (by omega)]
      simpa [idleCode] using code 16 (by norm_num)
    · rw [if_neg hz] at hlast
      have hb : (decide (rv.getD 0 ≠ 0) : Bool) = true := by rw [decide_eq_true_iff]; exact hz
      rw [hb, instrAt_of_pc _ (I.b + 15) hlast (by omega)]
      simpa [idleCode] using code 15 (by norm_num)

end NearCubicGates.Adapters.ShortPCP
