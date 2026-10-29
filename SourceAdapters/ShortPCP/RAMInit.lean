import SourceAdapters.ShortPCP.RAMSteps

/-!
# The framed initialization inside the RAM run (P02b)

Paper context: proof of `lem:tm-ram`, “Loading the tapes” and “Counting”, and “The exact Lean
interface” in `app:short-pcp-proof`. The machine reads the words containing the prescribed input and witness
bits and writes their framed encodings to the simulated tapes. A read of `#` enters a loop that never
reaches `out`. Loading takes `O(n + t + w_n)` steps; each completed block adds its actual step count,
a multiple of eight, to the counter.

`unpack_loop`: the loop of `unpackBlock` at `u`, entered with `p = 0`, either reads only proper words and leaves
after exactly `24N + 8` steps with `fr(b_0⋯b_{N−1})` on its tape (`b_p` = bit `p mod w` of word `p / w` read) and the
counter advanced by `24N + 8`, or reads `#` and jumps to `dead`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP

open NearCubicGates.Adapters.ACSP
open NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape

/-! ## One step -/

section Step

variable {M : Ram} (ga gb : ℕ → Option (BitVec M.w))

theorem xrun_step {X : XState M} {a : ℕ} {I : Instr M.w M.k M.ops} (hc : M.code[a]? = some I)
    (hpc : X.S.pc = BitVec.ofNat M.w a) (ha : a < 2 ^ M.w) (hI : ∀ b, I ≠ .out b) (m : ℕ) :
    xrun ga gb X (m + 1) = xrun ga gb (xexec ga gb X I) m ∧ Steppable X := by
  have hi : M.instrAt X.S.pc = some I := by rw [instrAt_ofNat X.S a hpc ha, hc]
  refine ⟨?_, I, hi, hI⟩
  rw [xrun_succ]; unfold xstep; rw [hi]

@[simp] theorem setNext_pc {M : Ram} (S : M.Config) (r : Fin M.k) (v : Option (BitVec M.w)) :
    (S.setNext r v).pc = S.pc + 1 := rfl
@[simp] theorem setNext_regs {M : Ram} (S : M.Config) (r : Fin M.k) (v : Option (BitVec M.w)) :
    (S.setNext r v).regs = Function.update S.regs r v := rfl
@[simp] theorem next_pc {M : Ram} (S : M.Config) : S.next.pc = S.pc + 1 := rfl
@[simp] theorem next_regs {M : Ram} (S : M.Config) : S.next.regs = S.regs := rfl
@[simp] theorem jump_pc {M : Ram} (S : M.Config) (c : ℕ) : (S.jump c).pc = BitVec.ofNat M.w c := rfl
@[simp] theorem jump_regs {M : Ram} (S : M.Config) (c : ℕ) : (S.jump c).regs = S.regs := rfl
@[simp] theorem val_reg {M : Ram} (S : M.Config) (r : Fin M.k) : S.val (.reg r) = (S.regs r).getD 0 := rfl
@[simp] theorem val_const {M : Ram} (S : M.Config) (c : BitVec M.w) : S.val (.const c) = c := rfl

/-- `X` makes `m` steps, each from a configuration that can step, and arrives at `Y`. -/
def Runs (X : XState M) (m : ℕ) (Y : XState M) : Prop :=
  (∀ i < m, Steppable (xrun ga gb X i)) ∧ xrun ga gb X m = Y

theorem Runs.zero (X : XState M) : Runs ga gb X 0 X := ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl⟩

theorem Runs.single {X : XState M} {a : ℕ} {I : Instr M.w M.k M.ops} (hc : M.code[a]? = some I)
    (hpc : X.S.pc = BitVec.ofNat M.w a) (ha : a < 2 ^ M.w) (hI : ∀ b, I ≠ .out b) :
    Runs ga gb X 1 (xexec ga gb X I) := by
  obtain ⟨h1, h2⟩ := xrun_step ga gb hc hpc ha hI 0
  exact ⟨fun i hi => by rw [show i = 0 by omega]; exact h2, h1⟩

theorem Runs.trans {X Y Z : XState M} {m k : ℕ} (h1 : Runs ga gb X m Y) (h2 : Runs ga gb Y k Z) :
    Runs ga gb X (m + k) Z := by
  refine ⟨fun i hi => ?_, by rw [xrun_add, h1.2, h2.2]⟩
  rcases Nat.lt_or_ge i m with h | h
  · exact h1.1 i h
  · obtain ⟨j, rfl⟩ : ∃ j, i = m + j := ⟨i - m, by omega⟩
    rw [xrun_add, h1.2]; exact h2.1 j (by omega)

end Step

theorem ofNat_add {w : ℕ} (a b : ℕ) : BitVec.ofNat w a + BitVec.ofNat w b = BitVec.ofNat w (a + b) :=
  BitVec.ofNat_add_ofNat a b

/-! ## The read instruction of a loop -/

/-- The read instruction of the loop on tape A (`isA`) or B. -/
def rdI (V : Verifier) (w : ℕ) (isA : Bool) : Fin (regCount V) → MI V w :=
  if isA then fun r => .readA r else fun r => .readB r

/-- The read counter of tape A or B. -/
def qsel {M : Ram} (isA : Bool) (X : XState M) : ℕ := if isA then X.qa else X.qb

/-- The word stream of tape A or B. -/
def gsel {w : ℕ} (isA : Bool) (ga gb : ℕ → Option (BitVec w)) : ℕ → Option (BitVec w) :=
  if isA then ga else gb

/-- Bit `p` of the stream read from position `q0`: bit `p mod w` of word `q0 + p / w` (C3). -/
def streamBit {w : ℕ} (g : ℕ → Option (BitVec w)) (q0 p : ℕ) : Bool :=
  ((g (q0 + p / w)).getD 0).getLsbD (p % w)

@[simp] theorem mnRam_w (V : Verifier) (w n t T : ℕ) (hfit : codeLen V ≤ 2 ^ w) :
    (mnRam V w n t T hfit).w = w := rfl

@[simp] theorem mnRam_alu (V : Verifier) (w n t T : ℕ) (hfit : codeLen V ≤ 2 ^ w) :
    (mnRam V w n t T hfit).alu = mnAlu w := rfl

/-! ## Division by the word width -/

theorem ceil_div_eq {p w : ℕ} (hw : 0 < w) : (p + w - 1) / w = p / w + (if p % w = 0 then 0 else 1) := by
  have h := Nat.div_add_mod p w
  have hr := Nat.mod_lt p hw
  generalize p / w = d at *
  generalize p % w = r at *
  subst h
  split_ifs with h0
  · apply Nat.div_eq_of_lt_le <;> (try simp only [Nat.add_mul, Nat.one_mul, Nat.add_zero]) <;> rw [Nat.mul_comm d w] <;>
      omega
  · apply Nat.div_eq_of_lt_le <;> (try simp only [Nat.add_mul, Nat.one_mul]) <;> rw [Nat.mul_comm d w] <;> omega

theorem succ_div_mod {p w : ℕ} (hw : 0 < w) :
    (p + 1) / w = (if p % w + 1 = w then p / w + 1 else p / w) ∧
    (p + 1) % w = (if p % w + 1 = w then 0 else p % w + 1) := by
  have h := Nat.div_add_mod p w
  have hr := Nat.mod_lt p hw
  have h' := Nat.div_add_mod (p + 1) w
  generalize p / w = d at *
  generalize p % w = r at *
  have hd : (p + 1) / w = if r + 1 = w then d + 1 else d := by
    split_ifs with he
    · apply Nat.div_eq_of_lt_le <;> (try simp only [Nat.add_mul, Nat.one_mul]) <;> rw [Nat.mul_comm d w] <;> omega
    · apply Nat.div_eq_of_lt_le <;> (try simp only [Nat.add_mul, Nat.one_mul]) <;> rw [Nat.mul_comm d w] <;> omega
  refine ⟨hd, ?_⟩
  rw [hd] at h'
  split_ifs at h' ⊢ with he
  · rw [Nat.mul_add, Nat.mul_one] at h'; omega
  · omega

/-! ## The read instruction -/

theorem xexec_rdI (V : Verifier) {w n t T : ℕ} {hfit : codeLen V ≤ 2 ^ w} (ga gb : ℕ → Option (BitVec w))
    (isA : Bool) (X : XState (mnRam V w n t T hfit)) (r : Fin (regCount V)) :
    (xexec ga gb X (rdI V w isA r)).S = X.S.setNext r (gsel isA ga gb (qsel isA X)) ∧
    (xexec ga gb X (rdI V w isA r)).mem = X.mem ∧
    qsel isA (xexec ga gb X (rdI V w isA r)) = qsel isA X + 1 ∧
    qsel (!isA) (xexec ga gb X (rdI V w isA r)) = qsel (!isA) X := by
  cases isA <;> exact ⟨rfl, rfl, rfl, rfl⟩

section Loop

variable (V : Verifier) {w n t T : ℕ} (hfit : codeLen V ≤ 2 ^ w)
variable (ga gb : ℕ → Option (BitVec w))

local notation "MM" => mnRam V w n t T hfit

/-- The loop invariant at the loop head `u` after `p` bits. -/
structure LoopInv (isA : Bool) (i0 : Fin V.tapeCount) (u N c0 q0 qo : ℕ) (τ : Fin V.tapeCount → ℕ → Bool)
    (X : XState MM) (p : ℕ) : Prop where
  pc : X.S.pc = BitVec.ofNat w u
  p_le : p ≤ N
  regP : X.S.regs rP = some (BitVec.ofNat w p)
  regMask : X.S.regs rMask = some (BitVec.ofNat w (if p % w = 0 then 0 else 2 ^ (p % w)))
  regWord : p % w ≠ 0 → X.S.regs rWord = gsel isA ga gb (q0 + p / w)
  regA : X.S.regs rA = some (BitVec.ofNat w (stride V * (2 * p) + i0.val))
  regCnt : X.S.regs rCnt = some (BitVec.ofNat w (c0 + 24 * p))
  q : qsel isA X = q0 + (p + w - 1) / w
  qo : qsel (!isA) X = qo
  ok : ∀ q < (p + w - 1) / w, gsel isA ga gb (q0 + q) ≠ none
  mem : X.mem = memRep V w (Function.update τ i0 (frameFn p (streamBit (gsel isA ga gb) q0)))

end Loop

theorem CodeAt.sub {M : Ram} {a i : ℕ} {l l' : List (Instr M.w M.k M.ops)} (h : CodeAt M a l)
    (hl : l' = (l.drop i).take l'.length) : CodeAt M (a + i) l' := by
  intro j hj
  have hj' : j < ((l.drop i).take l'.length).length := by rw [← hl]; exact hj
  simp only [List.length_take, List.length_drop] at hj'
  rw [show a + i + j = a + (i + j) by omega, h (i + j) (by omega)]
  conv_rhs => rw [hl]
  rw [List.getElem?_take_of_lt hj, List.getElem?_drop]

theorem bit_of_and {w : ℕ} (W : BitVec w) (j : ℕ) (hj : j < w) :
    cmpFn (BitVec.ofNat w 0) (W &&& BitVec.ofNat w (2 ^ j)) = if W.getLsbD j then 1 else 0 := by
  rw [show BitVec.ofNat w 0 = 0 from rfl, cmpFn_zero_left]
  by_cases h : W.getLsbD j = true
  · rw [if_neg ((and_two_pow_ne_zero W j hj).mpr h), if_pos h]
  · rw [if_pos (by by_contra h'; exact h ((and_two_pow_ne_zero W j hj).mp h')), if_neg h]

theorem memRep_frame_step (V : Verifier) (w : ℕ) (τ : Fin V.tapeCount → ℕ → Bool) (i0 : Fin V.tapeCount)
    (f : ℕ → Bool) (p : ℕ) (b : Bool) (hb : stride V * (2 * p + 1) + i0.val < 2 ^ w) :
    Function.update (Function.update (memRep V w (Function.update τ i0 f))
        (BitVec.ofNat w (stride V * (2 * p) + i0.val)) (BitVec.ofNat w 1))
      (BitVec.ofNat w (stride V * (2 * p) + i0.val + stride V)) (if b then 1 else 0) =
    memRep V w (Function.update τ i0 (Function.update (Function.update f (2 * p) true) (2 * p + 1) b)) := by
  have h0 : stride V * (2 * p) + i0.val < 2 ^ w := by
    have : stride V * (2 * p) ≤ stride V * (2 * p + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have e1 : Function.update (memRep V w (Function.update τ i0 f)) (BitVec.ofNat w (stride V * (2 * p) + i0.val))
      (BitVec.ofNat w 1) = memRep V w (Function.update τ i0 (Function.update f (2 * p) true)) := by
    have := memRep_write V w (Function.update τ i0 f) i0 (2 * p) true h0
    simp only [Function.update_self, Function.update_idem, if_true] at this
    exact this
  rw [e1]
  have e2 := memRep_write V w (Function.update τ i0 (Function.update f (2 * p) true)) i0 (2 * p + 1) b hb
  simp only [Function.update_self, Function.update_idem] at e2
  rw [show stride V * (2 * p) + i0.val + stride V = stride V * (2 * p + 1) + i0.val by ring, e2]

section Loop2

variable (V : Verifier) {w n t T : ℕ} (hfit : codeLen V ≤ 2 ^ w)
variable (ga gb : ℕ → Option (BitVec w))

local notation "MM" => mnRam V w n t T hfit

/-- The straight part of a pass (positions `7–22` of `unpackBlock`). -/
def unpackTail (V : Verifier) (w : ℕ) : List (MI V w) :=
  [ .arith 2 rTmp (.reg rWord) (.reg rMask),
    .arith 3 rTmp (cst 0) (.reg rTmp),
    .store rA (cst 1),
    .arith 0 rA (.reg rA) (cst (stride V)),
    .store rA (.reg rTmp),
    .arith 0 rA (.reg rA) (cst (stride V)),
    .arith 0 rMask (.reg rMask) (.reg rMask),
    .arith 0 rP (.reg rP) (cst 1),
    .nop, .nop, .nop, .nop, .nop, .nop, .nop,
    .arith 0 rCnt (.reg rCnt) (cst 24) ]

theorem unpackTail_codeAt (isA : Bool) (u N dead : ℕ)
    (hc : CodeAt MM u (unpackBlock V w (rdI V w isA) u N dead)) : CodeAt MM (u + 7) (unpackTail V w) :=
  CodeAt.sub hc rfl

/-- **The tail of a pass** (17 steps from `u + 7` back to `u`): writes `1` and the bit `W_j` into cells `2p`,
`2p + 1` of the tape at `a`, and advances `a`, `mask`, `p` and the counter. -/
theorem unpack_tail (isA : Bool) (i0 : Fin V.tapeCount) (u N dead c0 p j : ℕ) (W : BitVec w)
    (τ : Fin V.tapeCount → ℕ → Bool) (f : ℕ → Bool)
    (hc : CodeAt MM u (unpackBlock V w (rdI V w isA) u N dead)) (X : XState MM)
    (hpc : X.S.pc = BitVec.ofNat w (u + 7)) (hu : u + 34 < 2 ^ w) (hj : j < w)
    (hP : X.S.regs rP = some (BitVec.ofNat w p)) (hM : X.S.regs rMask = some (BitVec.ofNat w (2 ^ j)))
    (hW : X.S.regs rWord = some W) (hA : X.S.regs rA = some (BitVec.ofNat w (stride V * (2 * p) + i0.val)))
    (hC : X.S.regs rCnt = some (BitVec.ofNat w (c0 + 24 * p)))
    (hmem : X.mem = memRep V w (Function.update τ i0 f)) (haddr : stride V * (2 * p + 1) + i0.val < 2 ^ w) :
    (∀ i < 17, Steppable (xrun ga gb X i)) ∧
      (xrun ga gb X 17).S.pc = BitVec.ofNat w u ∧
      (xrun ga gb X 17).S.regs rP = some (BitVec.ofNat w (p + 1)) ∧
      (xrun ga gb X 17).S.regs rMask = some (BitVec.ofNat w (2 ^ (j + 1))) ∧
      (xrun ga gb X 17).S.regs rWord = some W ∧
      (xrun ga gb X 17).S.regs rA = some (BitVec.ofNat w (stride V * (2 * (p + 1)) + i0.val)) ∧
      (xrun ga gb X 17).S.regs rCnt = some (BitVec.ofNat w (c0 + 24 * (p + 1))) ∧
      (xrun ga gb X 17).qa = X.qa ∧ (xrun ga gb X 17).qb = X.qb ∧
      (xrun ga gb X 17).mem =
        memRep V w (Function.update τ i0 (Function.update (Function.update f (2 * p) true) (2 * p + 1)
          (W.getLsbD j))) := by
  have hcT := unpackTail_codeAt V hfit isA u N dead hc
  obtain ⟨h1, h2, h3⟩ := xrun_straight (M := MM) ga gb (unpackTail V w) (u + 7) X hcT
    (by change u + 7 + 16 < 2 ^ w; omega) hpc
    (by
      intro I hI
      change I ∈ unpackTail V w at hI
      simp only [unpackTail, List.mem_cons, List.not_mem_nil, or_false] at hI
      rcases hI with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> rw [h] <;> exact trivial)
  have hlen : (unpackTail V w).length = 16 := rfl
  rw [hlen] at h1 h2 h3
  set Y := (unpackTail V w).foldl (xexec ga gb) X with hY
  -- the jump back
  have hjmp : (mnRam V w n t T hfit).code[u + 23]? = some (Instr.jmp u) := by
    have := hc 23 (by simp [unpackBlock])
    simpa [unpackBlock] using this
  have hYP : Y.S.regs rP = some (BitVec.ofNat w (p + 1)) := by
    simp [hY, unpackTail, xexec, reg_eq_iff, hP, cst, ofNat_add]
  have hYC : Y.S.regs rCnt = some (BitVec.ofNat w (c0 + 24 * (p + 1))) := by
    simp [hY, unpackTail, xexec, reg_eq_iff, hC, cst, ofNat_add]
    ring_nf
  have hYM : Y.S.regs rMask = some (BitVec.ofNat w (2 ^ (j + 1))) := by
    simp [hY, unpackTail, xexec, reg_eq_iff, hM, cst, ofNat_add]
    ring_nf
  have hYW : Y.S.regs rWord = some W := by
    simp [hY, unpackTail, xexec, reg_eq_iff, hW]
  have hYA : Y.S.regs rA = some (BitVec.ofNat w (stride V * (2 * (p + 1)) + i0.val)) := by
    simp [hY, unpackTail, xexec, reg_eq_iff, hA, cst, ofNat_add]
    ring_nf
  have hYq : Y.qa = X.qa ∧ Y.qb = X.qb := by
    simp [hY, unpackTail, xexec]
  have hYmem : Y.mem = memRep V w (Function.update τ i0 (Function.update (Function.update f (2 * p) true)
      (2 * p + 1) (W.getLsbD j))) := by
    simp [hY, unpackTail, xexec, reg_eq_iff, hA, hW, hM, cst, ofNat_add, hmem]
    rw [bit_of_and W j hj]
    exact memRep_frame_step V w τ i0 f p _ haddr
  -- the jump back
  clear_value Y
  obtain ⟨hs, hst⟩ := xrun_step (M := MM) ga gb hjmp (by rw [h3]) (by show u + 23 < 2 ^ w; omega) (by intro b h; cases h) 0
  have h17 : xrun ga gb X 17 = xexec ga gb Y (.jmp u) := by
    rw [show 17 = 16 + 1 from rfl, xrun_add, h1, hs]; rfl
  refine ⟨fun i hi => ?_, ?_⟩
  · rcases Nat.lt_or_ge i 16 with h | h
    · exact h2 i h
    · rw [show i = 16 by omega, h1]; exact hst
  · rw [h17]
    simp only [xexec, jump_pc, jump_regs]
    exact ⟨trivial, hYP, hYM, hYW, hYA, hYC, hYq.1, hYq.2, hYmem⟩

/-- **The head of a pass** (7 steps from `u` to `u + 7`), when `p < N` and the word holding bit `p` is proper:
it is read if `p mod w = 0` (and `mask ← 1`), else the loop waits 4 steps. -/
theorem unpack_prefix (isA : Bool) (i0 : Fin V.tapeCount) (u N dead c0 q0 qo : ℕ)
    (τ : Fin V.tapeCount → ℕ → Bool)
    (hc : CodeAt MM u (unpackBlock V w (rdI V w isA) u N dead)) (X : XState MM) (p : ℕ)
    (hI : LoopInv V hfit ga gb isA i0 u N c0 q0 qo τ X p) (hp : p < N)
    (hok : p % w = 0 → gsel isA ga gb (q0 + p / w) ≠ none)
    (hu : u + 34 < 2 ^ w) (hN : N < 2 ^ w) (hw : 0 < w) :
    ∃ Z W, Runs ga gb X 7 Z ∧ Z.S.pc = BitVec.ofNat w (u + 7) ∧ Z.S.regs rP = some (BitVec.ofNat w p) ∧
      Z.S.regs rMask = some (BitVec.ofNat w (2 ^ (p % w))) ∧ Z.S.regs rWord = some W ∧
      gsel isA ga gb (q0 + p / w) = some W ∧ Z.S.regs rA = X.S.regs rA ∧ Z.S.regs rCnt = X.S.regs rCnt ∧
      qsel isA Z = q0 + p / w + 1 ∧ qsel (!isA) Z = qo ∧ Z.mem = X.mem := by
  have code : ∀ k, k < 34 → (mnRam V w n t T hfit).code[u + k]? =
      (unpackBlock V w (rdI V w isA) u N dead)[k]? := hc
  have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hpw : p < 2 ^ w := by omega
  have hone : (1 : BitVec w) ≠ 0 := one_ne_zero_of hw1
  -- step 0: `tmp ← cmp(p, N)` = 1
  have c0' : (mnRam V w n t T hfit).code[u]? = some (.arith 3 rTmp (.reg rP) (cst N)) := by
    simpa [unpackBlock] using code 0 (by norm_num)
  have r0 := Runs.single (M := MM) ga gb c0' hI.pc (by show u < 2 ^ w; omega) (by intro b h; cases h)
  set X1 := xexec ga gb X (.arith 3 rTmp (.reg rP) (cst N)) with hX1
  have X1pc : X1.S.pc = BitVec.ofNat w (u + 1) := by simp [hX1, xexec, hI.pc, ofNat_add]
  have X1tmp : X1.S.regs rTmp = some 1 := by
    simp [hX1, xexec, hI.regP, cst, cmpFn_lt (w := w) hpw hN hp]
  -- step 1: `je tmp (u+28)` falls through
  have c1 : (mnRam V w n t T hfit).code[u + 1]? = some (.je rTmp (u + 28)) := by
    simpa [unpackBlock] using code 1 (by norm_num)
  have r1 := Runs.single (M := MM) ga gb c1 X1pc (by show u + 1 < 2 ^ w; omega) (by intro b h; cases h)
  set X2 := xexec ga gb X1 (.je rTmp (u + 28)) with hX2
  have hw0 : w ≠ 0 := by omega
  have X2S : X2.S = X1.S.next := by simp [hX2, xexec, X1tmp, hw0]
  have X2pc : X2.S.pc = BitVec.ofNat w (u + 2) := by rw [X2S, next_pc, X1pc, ofNat_succ]
  have c2 : (mnRam V w n t T hfit).code[u + 2]? = some (.jne rMask (u + 24)) := by
    simpa [unpackBlock] using code 2 (by norm_num)
  have r2 := Runs.single (M := MM) ga gb c2 X2pc (by show u + 2 < 2 ^ w; omega) (by intro b h; cases h)
  set X3 := xexec ga gb X2 (.jne rMask (u + 24)) with hX3
  have X2mask : X2.S.regs rMask = X.S.regs rMask := by
    rw [X2S, next_regs]; simp [hX1, xexec, reg_eq_iff]
  by_cases hpm : p % w = 0
  · -- read path: mask = 0, read the word, test `#`, `mask ← 1`
    have hmask : X2.S.regs rMask = some (BitVec.ofNat w 0) := by
      rw [X2mask, hI.regMask, if_pos hpm]
    have X3S : X3.S = X2.S.next := by simp [hX3, xexec, hmask]
    have hq := hI.q
    rw [ceil_div_eq hw, if_pos hpm, Nat.add_zero] at hq
    obtain ⟨W, hW⟩ : ∃ W, gsel isA ga gb (q0 + p / w) = some W :=
      Option.ne_none_iff_exists'.mp (hok hpm)
    have c3 : (mnRam V w n t T hfit).code[u + 3]? = some (rdI V w isA rWord) := by
      simpa [unpackBlock] using code 3 (by norm_num)
    have c4 : (mnRam V w n t T hfit).code[u + 4]? = some (.iseof rTmp rWord) := by
      simpa [unpackBlock] using code 4 (by norm_num)
    have c5 : (mnRam V w n t T hfit).code[u + 5]? = some (.jne rTmp dead) := by
      simpa [unpackBlock] using code 5 (by norm_num)
    have c6 : (mnRam V w n t T hfit).code[u + 6]? = some (.arith 0 rMask (cst 1) (cst 0)) := by
      simpa [unpackBlock] using code 6 (by norm_num)
    have r3 := Runs.single (M := MM) ga gb c3 (by rw [X3S, next_pc, X2pc, ofNat_succ])
      (by show u + 3 < 2 ^ w; omega) (by intro b h; cases isA <;> simp [rdI] at h)
    obtain ⟨X4S, X4mem, X4q, X4qo⟩ := xexec_rdI V ga gb isA X3 rWord
    set X4 := xexec ga gb X3 (rdI V w isA rWord) with hX4
    have X3q : qsel isA X3 = qsel isA X ∧ qsel (!isA) X3 = qsel (!isA) X := by
      cases isA <;> simp [qsel, hX3, hX2, hX1, xexec]
    have X4word : X4.S.regs rWord = some W := by
      rw [X4S, setNext_regs, Function.update_self, X3q.1, hq, hW]
    have X4pc : X4.S.pc = BitVec.ofNat w (u + 4) := by
      rw [X4S, setNext_pc, X3S, next_pc, X2pc, ofNat_succ, ofNat_succ]
    have r4 := Runs.single (M := MM) ga gb c4 X4pc (by show u + 4 < 2 ^ w; omega) (by intro b h; cases h)
    set X5 := xexec ga gb X4 (.iseof rTmp rWord) with hX5
    have X5tmp : X5.S.regs rTmp = some (BitVec.ofNat w 0) := by simp [hX5, xexec, X4word]
    have X5pc : X5.S.pc = BitVec.ofNat w (u + 5) := by simp [hX5, xexec, X4pc, ofNat_add]
    have r5 := Runs.single (M := MM) ga gb c5 X5pc (by show u + 5 < 2 ^ w; omega) (by intro b h; cases h)
    set X6 := xexec ga gb X5 (.jne rTmp dead) with hX6
    have X6S : X6.S = X5.S.next := by simp [hX6, xexec, X5tmp]
    have X6pc : X6.S.pc = BitVec.ofNat w (u + 6) := by rw [X6S, next_pc, X5pc, ofNat_succ]
    have r6 := Runs.single (M := MM) ga gb c6 X6pc (by show u + 6 < 2 ^ w; omega) (by intro b h; cases h)
    refine ⟨_, W, r0.trans _ _ (r1.trans _ _ (r2.trans _ _ (r3.trans _ _ (r4.trans _ _ (r5.trans _ _ r6))))),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [xexec, X6pc, ofNat_add]
    · simp [xexec, X6S, hX5, X4S, X3S, X2S, hX1, reg_eq_iff, hI.regP]
    · simp [xexec, hpm, cst]
    · simp [xexec, X6S, hX5, reg_eq_iff, X4word]
    · exact hW
    · simp [xexec, X6S, hX5, X4S, X3S, X2S, hX1, reg_eq_iff]
    · simp [xexec, X6S, hX5, X4S, X3S, X2S, hX1, reg_eq_iff]
    · have h1 : qsel isA X4 = q0 + p / w + 1 := by rw [X4q, X3q.1, hq]
      cases isA <;> simpa [qsel, xexec, hX6, hX5] using h1
    · have h1 : qsel (!isA) X4 = qo := by rw [X4qo, X3q.2, hI.qo]
      cases isA <;> simpa [qsel, xexec, hX6, hX5] using h1
    · simp [xexec, hX6, hX5, hX3, hX2, hX1, X4mem]
  · -- no-read path: mask ≠ 0, wait at `u + 24 … u + 27`
    have hmask : X2.S.regs rMask = some (BitVec.ofNat w (2 ^ (p % w))) := by
      rw [X2mask, hI.regMask, if_neg hpm]
    have hmne : BitVec.ofNat w (2 ^ (p % w)) ≠ BitVec.ofNat w 0 :=
      ofNat_ne_zero (Nat.pow_lt_pow_right (by norm_num) (Nat.mod_lt _ hw)) (by positivity)
    have X3S : X3.S = X2.S.jump (u + 24) := by simp [hX3, xexec, hmask, hmne]
    have c24 : (mnRam V w n t T hfit).code[u + 24]? = some .nop := by
      simpa [unpackBlock] using code 24 (by norm_num)
    have c25 : (mnRam V w n t T hfit).code[u + 25]? = some .nop := by
      simpa [unpackBlock] using code 25 (by norm_num)
    have c26 : (mnRam V w n t T hfit).code[u + 26]? = some .nop := by
      simpa [unpackBlock] using code 26 (by norm_num)
    have c27 : (mnRam V w n t T hfit).code[u + 27]? = some (.jmp (u + 7)) := by
      simpa [unpackBlock] using code 27 (by norm_num)
    have r3 := Runs.single (M := MM) ga gb c24 (by rw [X3S]; rfl) (by show u + 24 < 2 ^ w; omega)
      (by intro b h; cases h)
    have r4 := Runs.single (M := MM) ga gb (X := xexec ga gb X3 .nop) c25 (by simp [xexec, X3S, ofNat_add])
      (by show u + 25 < 2 ^ w; omega) (by intro b h; cases h)
    have r5 := Runs.single (M := MM) ga gb (X := xexec ga gb (xexec ga gb X3 .nop) .nop) c26
      (by simp [xexec, X3S, ofNat_add]) (by show u + 26 < 2 ^ w; omega) (by intro b h; cases h)
    have r6 := Runs.single (M := MM) ga gb (X := xexec ga gb (xexec ga gb (xexec ga gb X3 .nop) .nop) .nop) c27
      (by simp [xexec, X3S, ofNat_add]) (by show u + 27 < 2 ^ w; omega) (by intro b h; cases h)
    have hq := hI.q
    rw [ceil_div_eq hw, if_neg hpm] at hq
    obtain ⟨W, hW⟩ : ∃ W, gsel isA ga gb (q0 + p / w) = some W := by
      have := hI.ok (p / w) (by rw [ceil_div_eq hw, if_neg hpm]; omega)
      exact Option.ne_none_iff_exists'.mp this
    refine ⟨_, W, r0.trans _ _ (r1.trans _ _ (r2.trans _ _ (r3.trans _ _ (r4.trans _ _ (r5.trans _ _ r6))))),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [xexec]
    · simp [xexec, X3S, X2S, hX1, reg_eq_iff, hI.regP]
    · simp [xexec, X3S, X2S, hX1, reg_eq_iff, hI.regMask, hpm]
    · simp [xexec, X3S, X2S, hX1, reg_eq_iff, hI.regWord hpm, hW]
    · exact hW
    · simp [xexec, X3S, X2S, hX1, reg_eq_iff]
    · simp [xexec, X3S, X2S, hX1, reg_eq_iff]
    · have h1 : qsel isA X = q0 + p / w + 1 := by rw [hq]; ring
      cases isA <;> simpa [qsel, xexec, hX3, hX2, hX1] using h1
    · have h1 := hI.qo
      cases isA <;> simpa [qsel, xexec, hX3, hX2, hX1] using h1
    · simp [xexec, hX3, hX2, hX1]

/-- **One pass** (24 steps): from the invariant at `p < N` (with a proper word for bit `p`) to the invariant at
`p + 1`. -/
theorem unpack_pass (isA : Bool) (i0 : Fin V.tapeCount) (u N dead c0 q0 qo : ℕ)
    (τ : Fin V.tapeCount → ℕ → Bool)
    (hc : CodeAt MM u (unpackBlock V w (rdI V w isA) u N dead)) (X : XState MM) (p : ℕ)
    (hI : LoopInv V hfit ga gb isA i0 u N c0 q0 qo τ X p) (hp : p < N)
    (hok : p % w = 0 → gsel isA ga gb (q0 + p / w) ≠ none)
    (hu : u + 34 < 2 ^ w) (hN : N < 2 ^ w) (hw : 0 < w)
    (haddr : stride V * (2 * N) + i0.val < 2 ^ w) :
    ∃ Y, Runs ga gb X 24 Y ∧ LoopInv V hfit ga gb isA i0 u N c0 q0 qo τ Y (p + 1) := by
  obtain ⟨Z, W, rZ, Zpc, ZP, ZM, ZW, hW, ZA, ZC, Zq, Zqo, Zmem⟩ :=
    unpack_prefix V hfit ga gb isA i0 u N dead c0 q0 qo τ hc X p hI hp hok hu hN hw
  have hj : p % w < w := Nat.mod_lt _ hw
  have haddr' : stride V * (2 * p + 1) + i0.val < 2 ^ w := by
    have : stride V * (2 * p + 1) ≤ stride V * (2 * N) := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := unpack_tail V hfit ga gb isA i0 u N dead c0 p (p % w) W τ
    (frameFn p (streamBit (gsel isA ga gb) q0)) hc Z Zpc hu hj ZP ZM ZW (ZA.trans hI.regA)
    (ZC.trans hI.regCnt) (Zmem.trans hI.mem) haddr'
  refine ⟨_, rZ.trans _ _ ⟨t1, rfl⟩, ?_⟩
  obtain ⟨hd, hm⟩ := succ_div_mod (p := p) hw
  have hYq : qsel isA (xrun ga gb Z 17) = qsel isA Z ∧ qsel (!isA) (xrun ga gb Z 17) = qsel (!isA) Z := by
    cases isA <;> simp [qsel, t8, t9]
  have hceil : (p + 1 + w - 1) / w = p / w + 1 := by
    rw [show p + 1 + w - 1 = p + w by omega, Nat.add_div_right _ hw]
  refine ⟨t2, by omega, t3, ?_, ?_, t6, t7, ?_, ?_, ?_, ?_⟩
  · rw [t4, hm]
    by_cases h1 : p % w + 1 = w
    · rw [if_pos h1, if_pos rfl, h1]; exact congrArg some (ofNat_two_pow_self w)
    · rw [if_neg h1, if_neg (by omega : p % w + 1 ≠ 0)]
  · intro hne
    rw [hm] at hne
    split_ifs at hne with h1
    · exact absurd rfl hne
    · rw [t5, hd, if_neg h1, hW]
  · rw [hYq.1, Zq, hceil]; ring
  · rw [hYq.2, Zqo]
  · intro q hq
    rw [hceil] at hq
    rcases Nat.lt_or_ge q (p / w) with h | h
    · exact hI.ok q (by rw [ceil_div_eq hw]; split_ifs <;> omega)
    · rw [show q = p / w by omega, hW]; simp
  · have hb : streamBit (gsel isA ga gb) q0 p = W.getLsbD (p % w) := by simp [streamBit, hW]
    rw [t10, frameFn_succ, hb]

/-- **A `#` word** (6 steps): at `p < N` with `p mod w = 0` and a `#` read, the loop jumps to `dead`. -/
theorem unpack_dead (isA : Bool) (i0 : Fin V.tapeCount) (u N dead c0 q0 qo : ℕ)
    (τ : Fin V.tapeCount → ℕ → Bool)
    (hc : CodeAt MM u (unpackBlock V w (rdI V w isA) u N dead)) (X : XState MM) (p : ℕ)
    (hI : LoopInv V hfit ga gb isA i0 u N c0 q0 qo τ X p) (hp : p < N)
    (hpm : p % w = 0) (hnone : gsel isA ga gb (q0 + p / w) = none)
    (hu : u + 34 < 2 ^ w) (hN : N < 2 ^ w) (hw : 0 < w) :
    ∃ Y, Runs ga gb X 6 Y ∧ Y.S.pc = BitVec.ofNat w dead := by
  have code : ∀ k, k < 34 → (mnRam V w n t T hfit).code[u + k]? =
      (unpackBlock V w (rdI V w isA) u N dead)[k]? := hc
  have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hpw : p < 2 ^ w := by omega
  have hw0 : w ≠ 0 := by omega
  have c0' : (mnRam V w n t T hfit).code[u]? = some (.arith 3 rTmp (.reg rP) (cst N)) := by
    simpa [unpackBlock] using code 0 (by norm_num)
  have c1 : (mnRam V w n t T hfit).code[u + 1]? = some (.je rTmp (u + 28)) := by
    simpa [unpackBlock] using code 1 (by norm_num)
  have c2 : (mnRam V w n t T hfit).code[u + 2]? = some (.jne rMask (u + 24)) := by
    simpa [unpackBlock] using code 2 (by norm_num)
  have c3 : (mnRam V w n t T hfit).code[u + 3]? = some (rdI V w isA rWord) := by
    simpa [unpackBlock] using code 3 (by norm_num)
  have c4 : (mnRam V w n t T hfit).code[u + 4]? = some (.iseof rTmp rWord) := by
    simpa [unpackBlock] using code 4 (by norm_num)
  have c5 : (mnRam V w n t T hfit).code[u + 5]? = some (.jne rTmp dead) := by
    simpa [unpackBlock] using code 5 (by norm_num)
  have r0 := Runs.single (M := MM) ga gb c0' hI.pc (by show u < 2 ^ w; omega) (by intro b h; cases h)
  set X1 := xexec ga gb X (.arith 3 rTmp (.reg rP) (cst N)) with hX1
  have X1pc : X1.S.pc = BitVec.ofNat w (u + 1) := by simp [hX1, xexec, hI.pc, ofNat_add]
  have X1tmp : X1.S.regs rTmp = some 1 := by
    simp [hX1, xexec, hI.regP, cst, cmpFn_lt (w := w) hpw hN hp]
  have r1 := Runs.single (M := MM) ga gb c1 X1pc (by show u + 1 < 2 ^ w; omega) (by intro b h; cases h)
  set X2 := xexec ga gb X1 (.je rTmp (u + 28)) with hX2
  have X2S : X2.S = X1.S.next := by simp [hX2, xexec, X1tmp, hw0]
  have X2pc : X2.S.pc = BitVec.ofNat w (u + 2) := by rw [X2S, next_pc, X1pc, ofNat_succ]
  have r2 := Runs.single (M := MM) ga gb c2 X2pc (by show u + 2 < 2 ^ w; omega) (by intro b h; cases h)
  set X3 := xexec ga gb X2 (.jne rMask (u + 24)) with hX3
  have hmask : X2.S.regs rMask = some (BitVec.ofNat w 0) := by
    rw [X2S, next_regs]; simp [hX1, xexec, reg_eq_iff, hI.regMask, hpm]
  have X3S : X3.S = X2.S.next := by simp [hX3, xexec, hmask]
  have hq := hI.q
  rw [ceil_div_eq hw, if_pos hpm, Nat.add_zero] at hq
  have r3 := Runs.single (M := MM) ga gb c3 (by rw [X3S, next_pc, X2pc, ofNat_succ])
    (by show u + 3 < 2 ^ w; omega) (by intro b h; cases isA <;> simp [rdI] at h)
  obtain ⟨X4S, -, -, -⟩ := xexec_rdI V ga gb isA X3 rWord
  set X4 := xexec ga gb X3 (rdI V w isA rWord) with hX4
  have X3q : qsel isA X3 = qsel isA X := by cases isA <;> simp [qsel, hX3, hX2, hX1, xexec]
  have X4word : X4.S.regs rWord = none := by
    rw [X4S, setNext_regs, Function.update_self, X3q, hq, hnone]
  have X4pc : X4.S.pc = BitVec.ofNat w (u + 4) := by
    rw [X4S, setNext_pc, X3S, next_pc, X2pc, ofNat_succ, ofNat_succ]
  have r4 := Runs.single (M := MM) ga gb c4 X4pc (by show u + 4 < 2 ^ w; omega) (by intro b h; cases h)
  set X5 := xexec ga gb X4 (.iseof rTmp rWord) with hX5
  have X5tmp : X5.S.regs rTmp = some 1 := by simp [hX5, xexec, X4word]
  have X5pc : X5.S.pc = BitVec.ofNat w (u + 5) := by simp [hX5, xexec, X4pc, ofNat_add]
  have r5 := Runs.single (M := MM) ga gb c5 X5pc (by show u + 5 < 2 ^ w; omega) (by intro b h; cases h)
  refine ⟨_, r0.trans _ _ (r1.trans _ _ (r2.trans _ _ (r3.trans _ _ (r4.trans _ _ r5)))), ?_⟩
  simp [xexec, X5tmp, hw0]

/-- The exit path's straight part (positions `28–33`). -/
def unpackExit (V : Verifier) (w : ℕ) : List (MI V w) :=
  [.nop, .nop, .nop, .nop, .nop, .arith 0 rCnt (.reg rCnt) (cst 8)]

/-- **The exit** (8 steps): at `p = N` the loop leaves to `u + 34` with the counter advanced by `8`. -/
theorem unpack_exit (isA : Bool) (i0 : Fin V.tapeCount) (u N dead c0 q0 qo : ℕ)
    (τ : Fin V.tapeCount → ℕ → Bool)
    (hc : CodeAt MM u (unpackBlock V w (rdI V w isA) u N dead)) (X : XState MM)
    (hI : LoopInv V hfit ga gb isA i0 u N c0 q0 qo τ X N) (hu : u + 34 < 2 ^ w) :
    ∃ Y, Runs ga gb X 8 Y ∧ Y.S.pc = BitVec.ofNat w (u + 34) ∧
      Y.S.regs rCnt = some (BitVec.ofNat w (c0 + 24 * N + 8)) ∧ Y.qa = X.qa ∧ Y.qb = X.qb ∧ Y.mem = X.mem := by
  have code : ∀ k, k < 34 → (mnRam V w n t T hfit).code[u + k]? =
      (unpackBlock V w (rdI V w isA) u N dead)[k]? := hc
  have c0' : (mnRam V w n t T hfit).code[u]? = some (.arith 3 rTmp (.reg rP) (cst N)) := by
    simpa [unpackBlock] using code 0 (by norm_num)
  have c1 : (mnRam V w n t T hfit).code[u + 1]? = some (.je rTmp (u + 28)) := by
    simpa [unpackBlock] using code 1 (by norm_num)
  have r0 := Runs.single (M := MM) ga gb c0' hI.pc (by show u < 2 ^ w; omega) (by intro b h; cases h)
  set X1 := xexec ga gb X (.arith 3 rTmp (.reg rP) (cst N)) with hX1
  have X1pc : X1.S.pc = BitVec.ofNat w (u + 1) := by simp [hX1, xexec, hI.pc, ofNat_add]
  have X1tmp : X1.S.regs rTmp = some (BitVec.ofNat w 0) := by
    simp [hX1, xexec, hI.regP, cst, cmpFn_eq]
  have r1 := Runs.single (M := MM) ga gb c1 X1pc (by show u + 1 < 2 ^ w; omega) (by intro b h; cases h)
  set X2 := xexec ga gb X1 (.je rTmp (u + 28)) with hX2
  have X2S : X2.S = X1.S.jump (u + 28) := by simp [hX2, xexec, X1tmp]
  have hcE : CodeAt MM (u + 28) (unpackExit V w) := CodeAt.sub hc rfl
  obtain ⟨h1, h2, h3⟩ := xrun_straight (M := MM) ga gb (unpackExit V w) (u + 28) X2 hcE
    (by change u + 28 + 6 < 2 ^ w; omega) (by rw [X2S]; rfl)
    (by
      intro I hI
      change I ∈ unpackExit V w at hI
      simp only [unpackExit, List.mem_cons, List.not_mem_nil, or_false] at hI
      rcases hI with h|h|h|h|h|h <;> rw [h] <;> exact trivial)
  refine ⟨_, r0.trans _ _ (r1.trans _ _ ⟨h2, h1⟩), ?_, ?_, ?_, ?_, ?_⟩
  · rw [h3]; rfl
  · simp [unpackExit, xexec, X2S, hX1, reg_eq_iff, hI.regCnt, cst, ofNat_add]
  · simp [unpackExit, xexec, hX2, hX1]
  · simp [unpackExit, xexec, hX2, hX1]
  · simp [unpackExit, xexec, hX2, hX1]

/-- What the loop leaves behind on a successful exit. -/
structure LoopDone (isA : Bool) (i0 : Fin V.tapeCount) (u N c0 q0 qo : ℕ) (τ : Fin V.tapeCount → ℕ → Bool)
    (Y : XState MM) : Prop where
  pc : Y.S.pc = BitVec.ofNat w (u + 34)
  regCnt : Y.S.regs rCnt = some (BitVec.ofNat w (c0 + 24 * N + 8))
  q : qsel isA Y = q0 + (N + w - 1) / w
  qo : qsel (!isA) Y = qo
  mem : Y.mem = memRep V w (Function.update τ i0 (frameFn N (streamBit (gsel isA ga gb) q0)))

theorem div_lt_ceil {p N w : ℕ} (hw : 0 < w) (hp : p < N) : p / w < (N + w - 1) / w := by
  have h1 : (p + 1 + w - 1) / w ≤ (N + w - 1) / w := Nat.div_le_div_right (by omega)
  rw [show p + 1 + w - 1 = p + w by omega, Nat.add_div_right _ hw] at h1
  omega

/-- **The loop, all words proper**: from the invariant at `p`, exactly `24(N − p) + 8` steps to the exit. -/
theorem unpack_loop_ok (isA : Bool) (i0 : Fin V.tapeCount) (u N dead c0 q0 qo : ℕ)
    (τ : Fin V.tapeCount → ℕ → Bool)
    (hc : CodeAt MM u (unpackBlock V w (rdI V w isA) u N dead))
    (hu : u + 34 < 2 ^ w) (hN : N < 2 ^ w) (hw : 0 < w) (haddr : stride V * (2 * N) + i0.val < 2 ^ w)
    (hall : ∀ q < (N + w - 1) / w, gsel isA ga gb (q0 + q) ≠ none) :
    ∀ d p (X : XState MM), d = N - p → LoopInv V hfit ga gb isA i0 u N c0 q0 qo τ X p →
      ∃ Y, Runs ga gb X (24 * d + 8) Y ∧ LoopDone V hfit ga gb isA i0 u N c0 q0 qo τ Y := by
  intro d
  induction d with
  | zero =>
    intro p X hd hI
    have hpN : p = N := by have := hI.p_le; omega
    subst hpN
    obtain ⟨Y, rY, Ypc, YC, Yqa, Yqb, Ymem⟩ := unpack_exit V hfit ga gb isA i0 u p dead c0 q0 qo τ hc X hI hu
    have hYq : qsel isA Y = qsel isA X ∧ qsel (!isA) Y = qsel (!isA) X := by
      cases isA <;> simp [qsel, Yqa, Yqb]
    exact ⟨Y, rY, ⟨Ypc, YC, by rw [hYq.1, hI.q], by rw [hYq.2, hI.qo], by rw [Ymem, hI.mem]⟩⟩
  | succ d ih =>
    intro p X hd hI
    have hp : p < N := by omega
    obtain ⟨Y, rY, hY⟩ := unpack_pass V hfit ga gb isA i0 u N dead c0 q0 qo τ hc X p hI hp
      (fun _ => hall (p / w) (div_lt_ceil hw hp)) hu hN hw haddr
    obtain ⟨Z, rZ, hZ⟩ := ih (p + 1) Y (by omega) hY
    exact ⟨Z, by rw [show 24 * (d + 1) + 8 = 24 + (24 * d + 8) by ring]; exact rY.trans _ _ rZ, hZ⟩

/-- **The loop, some word `#`**: from the invariant at `p`, the run reaches `dead`. -/
theorem unpack_loop_bad (isA : Bool) (i0 : Fin V.tapeCount) (u N dead c0 q0 qo : ℕ)
    (τ : Fin V.tapeCount → ℕ → Bool)
    (hc : CodeAt MM u (unpackBlock V w (rdI V w isA) u N dead))
    (hu : u + 34 < 2 ^ w) (hN : N < 2 ^ w) (hw : 0 < w) (haddr : stride V * (2 * N) + i0.val < 2 ^ w)
    (hbad : ¬ ∀ q < (N + w - 1) / w, gsel isA ga gb (q0 + q) ≠ none) :
    ∀ d p (X : XState MM), d = N - p → LoopInv V hfit ga gb isA i0 u N c0 q0 qo τ X p →
      ∃ m Y, Runs ga gb X m Y ∧ Y.S.pc = BitVec.ofNat w dead := by
  intro d
  induction d with
  | zero =>
    intro p X hd hI
    have hpN : p = N := by have := hI.p_le; omega
    subst hpN
    exact absurd hI.ok hbad
  | succ d ih =>
    intro p X hd hI
    have hp : p < N := by omega
    by_cases hz : p % w = 0 ∧ gsel isA ga gb (q0 + p / w) = none
    · obtain ⟨Y, rY, hY⟩ := unpack_dead V hfit ga gb isA i0 u N dead c0 q0 qo τ hc X p hI hp hz.1 hz.2 hu hN hw
      exact ⟨6, Y, rY, hY⟩
    · obtain ⟨Y, rY, hY⟩ := unpack_pass V hfit ga gb isA i0 u N dead c0 q0 qo τ hc X p hI hp
        (fun h => fun h' => hz ⟨h, h'⟩) hu hN hw haddr
      obtain ⟨m, Z, rZ, hZ⟩ := ih (p + 1) Y (by omega) hY
      exact ⟨24 + m, Z, rY.trans _ _ rZ, hZ⟩

end Loop2

end NearCubicGates.Adapters.ShortPCP
