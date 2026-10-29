import SourceAdapters.ShortPCP.RAMInit

/-!
# The initialization of `M_n`, composed (P02b)

Paper context: “The exact Lean interface” in `app:short-pcp-proof` and the proof of `lem:tm-ram`,
“Loading the tapes” and “Counting”. The simulated tapes receive `fr(x)` and the frame of the first `t`
witness bits, with terminators at their prescribed positions and blank zeros beyond them. The block
counter records the exact elapsed number of steps, in multiples of eight.

`init_ok`: from the initial configuration with zero memory (`def:ram`), if the first `⌈n/w⌉` words read
from tape A and the first `⌈t/w⌉` words read from tape B are proper, the run reaches the interpreter after exactly
`initLen = 24n + 24t + 8k_V + 40` steps, with the counter `= initLen`, the heads at cell `0`, `sr = start`, and the
memory holding `fr(x')` on tape 0 and `fr(y')` on tape 1 (all other cells blank), where `x'_p`, `y'_p` are bit
`p mod w` of word `p / w` read. `init_bad`: otherwise the run reaches `jmp dead`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP

open NearCubicGates.Adapters.ACSP
open NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape

section Start

variable (V : Verifier) {w n t T : ℕ} (hfit : codeLen V ≤ 2 ^ w)
variable (ga gb : ℕ → Option (BitVec w))

local notation "MM" => mnRam V w n t T hfit

/-! ## Block addresses -/

theorem code_all : CodeAt MM 0 (mnCode V w n t T) := fun j _ => by rw [Nat.zero_add]

theorem interpAddr_eq : interpAddr V = 84 + 8 * (V.tapeCount + 1) := by
  unfold interpAddr; try ring

theorem code_start : CodeAt MM 0 (startBlock V w) :=
  (code_all V hfit : CodeAt MM 0 (mnCode V w n t T)).append_left.append_left.append_left.append_left.append_left.append_left.append_left
    |>.append_left.append_left

theorem code_unpackA : CodeAt MM 8 (unpackBlock V w (rdI V w true) 8 n (deadAddr V)) := by
  have := (code_all V hfit : CodeAt MM 0 (mnCode V w n t T)).append_left.append_left.append_left.append_left.append_left.append_left
    |>.append_left.append_left.append_right
  exact (by simpa [startBlock_length] using this :
    CodeAt MM 8 (unpackBlock V w (fun r => .readA r) 8 n (deadAddr V)))

theorem code_setup : CodeAt MM 42 (setupBlock V w) := by
  have := (code_all V hfit : CodeAt MM 0 (mnCode V w n t T)).append_left.append_left.append_left.append_left.append_left.append_left
    |>.append_left.append_right
  simpa [startBlock_length, unpackBlock_length] using this

theorem code_unpackB : CodeAt MM 50 (unpackBlock V w (rdI V w false) 50 t (deadAddr V)) := by
  have := (code_all V hfit : CodeAt MM 0 (mnCode V w n t T)).append_left.append_left.append_left.append_left.append_left.append_left
    |>.append_right
  exact (by simpa [startBlock_length, unpackBlock_length, setupBlock_length] using this :
    CodeAt MM 50 (unpackBlock V w (fun r => .readB r) 50 t (deadAddr V)))

theorem code_simSetup : CodeAt MM 84 (simSetupBlock V w) := by
  have := (code_all V hfit : CodeAt MM 0 (mnCode V w n t T)).append_left.append_left.append_left.append_left.append_left.append_right
  simpa [startBlock_length, unpackBlock_length, setupBlock_length] using this

theorem code_header : CodeAt MM (interpAddr V) (headerBlock V w) := by
  have := (code_all V hfit : CodeAt MM 0 (mnCode V w n t T)).append_left.append_left.append_left.append_left.append_right
  have e : 0 + (startBlock V w ++ unpackBlock V w (fun r => .readA r) 8 n (deadAddr V) ++ setupBlock V w ++
      unpackBlock V w (fun r => .readB r) 50 t (deadAddr V) ++ simSetupBlock V w).length = interpAddr V := by
    simp only [List.length_append, startBlock_length, unpackBlock_length, setupBlock_length,
      simSetupBlock_length, interpAddr]
    ring
  rw [← e]; exact this

theorem code_chain : CodeAt MM (chainAddr V) (chainBlock V w) := by
  have := (code_all V hfit : CodeAt MM 0 (mnCode V w n t T)).append_left.append_left.append_left.append_right
  have e : 0 + (startBlock V w ++ unpackBlock V w (fun r => .readA r) 8 n (deadAddr V) ++ setupBlock V w ++
      unpackBlock V w (fun r => .readB r) 50 t (deadAddr V) ++ simSetupBlock V w ++ headerBlock V w).length =
      chainAddr V := by
    simp only [List.length_append, startBlock_length, unpackBlock_length, setupBlock_length,
      simSetupBlock_length, headerBlock_length, chainAddr, interpAddr]
    ring
  rw [← e]; exact this

theorem code_leaves : CodeAt MM (leafAddr V) (List.ofFn (leafCode V w)).flatten := by
  have := (code_all V hfit : CodeAt MM 0 (mnCode V w n t T)).append_left.append_left.append_right
  have e : 0 + (startBlock V w ++ unpackBlock V w (fun r => .readA r) 8 n (deadAddr V) ++ setupBlock V w ++
      unpackBlock V w (fun r => .readB r) 50 t (deadAddr V) ++ simSetupBlock V w ++ headerBlock V w ++
      chainBlock V w).length = leafAddr V := by
    simp only [List.length_append, startBlock_length, unpackBlock_length, setupBlock_length,
      simSetupBlock_length, headerBlock_length, chainBlock_length, leafAddr, chainAddr, interpAddr]
    ring
  rw [← e]; exact this

theorem code_dead : (mnRam V w n t T hfit).code[deadAddr V]? = some (Instr.jmp (deadAddr V)) := by
  have := (code_all V hfit : CodeAt MM 0 (mnCode V w n t T)).append_left.append_right
  have e : 0 + (startBlock V w ++ unpackBlock V w (fun r => .readA r) 8 n (deadAddr V) ++ setupBlock V w ++
      unpackBlock V w (fun r => .readB r) 50 t (deadAddr V) ++ simSetupBlock V w ++ headerBlock V w ++
      chainBlock V w ++ (List.ofFn (leafCode V w)).flatten).length = deadAddr V := by
    simp only [List.length_append, startBlock_length, unpackBlock_length, setupBlock_length,
      simSetupBlock_length, headerBlock_length, chainBlock_length, List.length_flatten, List.map_ofFn,
      deadAddr, leafAddr, chainAddr, interpAddr]
    rw [sum_ofFn_length _ (leafCode_length V w)]
    ring
  rw [e] at this
  simpa using this 0 (by simp)

theorem code_idle : CodeAt MM (idleAddr V) (idleCode 0 3 rCnt rTmp rVd (idleAddr V) T) := by
  have := (code_all V hfit : CodeAt MM 0 (mnCode V w n t T)).append_right
  have e : 0 + (startBlock V w ++ unpackBlock V w (fun r => .readA r) 8 n (deadAddr V) ++ setupBlock V w ++
      unpackBlock V w (fun r => .readB r) 50 t (deadAddr V) ++ simSetupBlock V w ++ headerBlock V w ++
      chainBlock V w ++ (List.ofFn (leafCode V w)).flatten ++ [Instr.jmp (deadAddr V)]).length = idleAddr V := by
    simp only [List.length_append, startBlock_length, unpackBlock_length, setupBlock_length,
      simSetupBlock_length, headerBlock_length, chainBlock_length, List.length_flatten, List.map_ofFn,
      idleAddr, deadAddr, leafAddr, chainAddr, interpAddr, List.length_cons, List.length_nil]
    rw [sum_ofFn_length _ (leafCode_length V w)]
    ring
  rw [e] at this
  exact this

/-! ## The `dead` loop -/

/-- At `jmp dead` the run stays there forever, every configuration able to step and none final. -/
theorem dead_forever (hd : deadAddr V < 2 ^ w) (Y : XState MM) (hY : Y.S.pc = BitVec.ofNat w (deadAddr V)) :
    ∀ m, (xrun ga gb Y m).S.pc = BitVec.ofNat w (deadAddr V) ∧ Steppable (xrun ga gb Y m) := by
  intro m
  induction m with
  | zero =>
    refine ⟨hY, .jmp (deadAddr V), ?_, by intro b h; cases h⟩
    show Ram.instrAt (mnRam V w n t T hfit) Y.S.pc = _
    rw [instrAt_ofNat Y.S (deadAddr V) hY hd]; exact code_dead V hfit
  | succ m ih =>
    have hi : Ram.instrAt (mnRam V w n t T hfit) (xrun ga gb Y m).S.pc = some (Instr.jmp (deadAddr V)) := by
      rw [instrAt_ofNat _ _ ih.1 hd]; exact code_dead V hfit
    have hpc : (xrun ga gb Y (m + 1)).S.pc = BitVec.ofNat w (deadAddr V) := by
      rw [xrun_succ']; unfold xstep; rw [hi]; rfl
    refine ⟨hpc, .jmp (deadAddr V), ?_, by intro b h; cases h⟩
    rw [instrAt_ofNat _ (deadAddr V) hpc hd]; exact code_dead V hfit

/-! ## The initialization -/

/-- The initial state: Def. 6.8's initial configuration, the zero memory (Def. 6.13), no reads. -/
def initState (M : Ram) : XState M := ⟨⟨0, fun _ => some 0⟩, 0, 0, 0⟩

/-- Steps of the initialization. -/
def initLen (V : Verifier) (n t : ℕ) : ℕ := 24 * n + 24 * t + 8 * V.tapeCount + 40

/-- The tapes after the initialization: `fr(x')` on tape 0, `fr(y')` on tape 1, blank elsewhere. -/
def initTapes (V : Verifier) {w : ℕ} (ga gb : ℕ → Option (BitVec w)) (n t : ℕ) :
    Fin V.tapeCount → ℕ → Bool :=
  fun i => if i.val = 0 then frameFn n (streamBit ga 0) else if i.val = 1 then frameFn t (streamBit gb 0)
    else fun _ => false

/-- The state at the interpreter after a successful initialization. -/
structure InitDone (Y : XState MM) : Prop where
  pc : Y.S.pc = BitVec.ofNat w (interpAddr V)
  regCnt : Y.S.regs rCnt = some (BitVec.ofNat w (initLen V n t))
  regSr : Y.S.regs rSr = some (BitVec.ofNat w V.machine.start.val)
  regH : ∀ i, Y.S.regs (rH i) = some (BitVec.ofNat w (stride V * 0 + i.val))
  mem : Y.mem = memRep V w (initTapes V ga gb n t)

/-- Sizes the initialization needs (all follow from `lem:tm-ram`'s "Constants", `lem:tm-ram` and its proof). -/
structure InitFits (V : Verifier) (w n t : ℕ) : Prop where
  w_pos : 0 < w
  code : codeLen V < 2 ^ w
  n_lt : n < 2 ^ w
  t_lt : t < 2 ^ w
  addrA : stride V * (2 * n) + 0 < 2 ^ w
  addrB : stride V * (2 * t) + 1 < 2 ^ w

theorem tape0_lt : 0 < V.tapeCount := by have := V.twoTapes; omega
theorem tape1_lt : 1 < V.tapeCount := by have := V.twoTapes; omega

/-- The start block (8 steps), and the loop invariant of the input loop at `p = 0`. -/
theorem start_block (hF : InitFits V w n t) :
    ∃ Y, Runs ga gb (initState MM) 8 Y ∧
      LoopInv V hfit ga gb true ⟨0, tape0_lt V⟩ 8 n 8 0 0 (fun _ _ => false) Y 0 := by
  have hc := code_start V hfit (n := n) (t := t) (T := T)
  have hF1 := hF.code
  have h8 : 8 < codeLen V := by unfold codeLen idleAddr deadAddr leafAddr chainAddr interpAddr; omega
  obtain ⟨h1, h2, h3⟩ := xrun_straight (M := MM) ga gb (startBlock V w) 0 (initState MM) hc
    (by change 0 + 8 < 2 ^ w; omega) rfl
    (by
      intro I hI
      change I ∈ startBlock V w at hI
      simp only [startBlock, List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil,
        or_false] at hI
      rcases hI with (h|⟨-, h⟩)|h <;> rw [h] <;> exact trivial)
  have hw := hF.w_pos
  refine ⟨_, ⟨h2, h1⟩, ⟨?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [h3]; rfl
  · simp [startBlock, xexec, initState, reg_eq_iff]
  · simp [startBlock, xexec, initState, reg_eq_iff]
  · intro h; simp at h
  · simp [startBlock, xexec, initState, reg_eq_iff]
  · simp [startBlock, xexec, initState, cst, ofNat_add]
  · simp [qsel, startBlock, xexec, initState]
    exact (Nat.div_eq_of_lt (by omega)).symm
  · simp [qsel, startBlock, xexec, initState]
  · intro q hq
    rw [Nat.zero_add, Nat.div_eq_of_lt (by omega)] at hq
    omega
  · simp [startBlock, xexec, initState, frameFn_zero, memRep_blank, cst]

/-- Between the loops (8 steps): from the input loop's exit to the witness loop's invariant at `p = 0`. -/
theorem setup_block (hF : InitFits V w n t) (Y : XState MM)
    (hY : LoopDone V hfit ga gb true ⟨0, tape0_lt V⟩ 8 n 8 0 0 (fun _ _ => false) Y) :
    ∃ Z, Runs ga gb Y 8 Z ∧
      LoopInv V hfit ga gb false ⟨1, tape1_lt V⟩ 50 t (24 * n + 24) 0 (0 + (n + w - 1) / w)
        (Function.update (fun _ _ => false) ⟨0, tape0_lt V⟩ (frameFn n (streamBit (gsel true ga gb) 0))) Z 0 := by
  have hc := code_setup V hfit (n := n) (t := t) (T := T)
  have hF1 := hF.code
  have hw := hF.w_pos
  obtain ⟨h1, h2, h3⟩ := xrun_straight (M := MM) ga gb (setupBlock V w) 42 Y hc
    (by change 42 + 8 < 2 ^ w; unfold codeLen idleAddr deadAddr leafAddr chainAddr interpAddr at hF1; omega)
    (by rw [hY.pc])
    (by
      intro I hI
      change I ∈ setupBlock V w at hI
      simp only [setupBlock, List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil,
        or_false] at hI
      rcases hI with ((h|h|h)|⟨-, h⟩)|h <;> rw [h] <;> exact trivial)
  have hq := hY.q
  have hqo := hY.qo
  simp only [qsel, if_true, Bool.not_true, Bool.false_eq_true, if_false] at hq hqo
  refine ⟨_, ⟨h2, h1⟩, ⟨?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [h3]; rfl
  · simp [setupBlock, xexec, reg_eq_iff, cst]
  · simp [setupBlock, xexec, reg_eq_iff, cst]
  · intro h; simp at h
  · simp [setupBlock, xexec, reg_eq_iff, cst]
  · simp [setupBlock, xexec, reg_eq_iff, cst, ofNat_add, hY.regCnt]; ring_nf
  · have : ((setupBlock V w).foldl (xexec ga gb) Y).qb = Y.qb := by simp [setupBlock, xexec]
    simp only [qsel, Bool.false_eq_true, if_false]
    rw [this, hqo, Nat.zero_add, Nat.div_eq_of_lt (by omega)]
  · simp [qsel, setupBlock, xexec, hq]
  · intro q hq'
    rw [Nat.zero_add, Nat.div_eq_of_lt (by omega)] at hq'
    omega
  · have hm : ((setupBlock V w).foldl (xexec ga gb) Y).mem = Y.mem := by simp [setupBlock, xexec]
    rw [hm, hY.mem, frameFn_zero]
    symm
    apply congrArg (memRep V w)
    rw [Function.update_eq_self_iff]
    have hne : (⟨1, tape1_lt V⟩ : Fin V.tapeCount) ≠ ⟨0, tape0_lt V⟩ := by simp [Fin.ext_iff]
    exact (Function.update_of_ne hne (frameFn n (streamBit (gsel true ga gb) 0))
      (fun (_ : Fin V.tapeCount) (_ : ℕ) => false)).symm

/-- Setting the head registers: register `rH i` gets the word `i` (cell `0` of tape `i`). -/
theorem fold_heads (l : List (Fin V.tapeCount)) (X : XState MM) :
    (∀ r, (l.foldl (fun X i => xexec ga gb X (.arith 0 (rH i) (cst i.val) (cst 0))) X).S.regs r =
      if ∃ i ∈ l, r = rH i then some (BitVec.ofNat w (r.val - 9)) else X.S.regs r) ∧
    (l.foldl (fun X i => xexec ga gb X (.arith 0 (rH i) (cst i.val) (cst 0))) X).mem = X.mem := by
  induction l generalizing X with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ih1, ih2⟩ := ih (xexec ga gb X (.arith 0 (rH a) (cst a.val) (cst 0)))
    refine ⟨fun r => ?_, by rw [List.foldl_cons, ih2]; rfl⟩
    rw [List.foldl_cons, ih1 r]
    by_cases h1 : ∃ i ∈ l, r = rH i
    · rw [if_pos h1, if_pos (by obtain ⟨i, hi, hr⟩ := h1; exact ⟨i, by simp [hi], hr⟩)]
    · rw [if_neg h1]
      by_cases h2 : r = rH a
      · rw [if_pos ⟨a, by simp, h2⟩]
        subst h2
        simp [xexec, cst]
      · rw [if_neg (by rintro ⟨i, hi, hr⟩; simp at hi; rcases hi with rfl | hi; exact h2 hr; exact h1 ⟨i, hi, hr⟩)]
        simp [xexec, Function.update_of_ne h2]

/-- The simulation setup (`8(k_V + 1)` steps): heads at cell `0`, `sr ← start`, counter. -/
theorem simSetup_block (hF : InitFits V w n t) (Y : XState MM)
    (hY : LoopDone V hfit ga gb false ⟨1, tape1_lt V⟩ 50 t (24 * n + 24) 0 (0 + (n + w - 1) / w)
        (Function.update (fun _ _ => false) ⟨0, tape0_lt V⟩ (frameFn n (streamBit (gsel true ga gb) 0))) Y) :
    ∃ Z, Runs ga gb Y (8 * (V.tapeCount + 1)) Z ∧ InitDone V hfit ga gb Z := by
  have hc := code_simSetup V hfit (n := n) (t := t) (T := T)
  have hF1 := hF.code
  have hlen : (simSetupBlock V w).length = 8 * (V.tapeCount + 1) := simSetupBlock_length V w
  obtain ⟨h1, h2, h3⟩ := xrun_straight (M := MM) ga gb (simSetupBlock V w) 84 Y hc
    (by
      change 84 + (simSetupBlock V w).length < 2 ^ w
      rw [hlen]; unfold codeLen idleAddr deadAddr leafAddr chainAddr interpAddr at hF1; omega)
    (by rw [hY.pc])
    (by
      intro I hI
      change I ∈ simSetupBlock V w at hI
      simp only [simSetupBlock, List.mem_append, List.mem_ofFn, List.mem_cons, List.mem_replicate,
        List.not_mem_nil, or_false] at hI
      rcases hI with ((⟨i, h⟩|h)|⟨-, h⟩)|h <;> first | (rw [h]; exact trivial) | (rw [← h]; exact trivial))
  change xrun ga gb Y (simSetupBlock V w).length = _ at h1
  rw [hlen] at h1 h2
  rw [hlen] at h3
  set Z := (simSetupBlock V w).foldl (xexec ga gb) Y with hZ
  obtain ⟨fh1, fh2⟩ := fold_heads V hfit ga gb (List.finRange V.tapeCount) Y
  set Y1 := (List.finRange V.tapeCount).foldl
    (fun X i => xexec ga gb X (.arith 0 (rH i) (cst i.val) (cst 0))) Y with hY1
  set Y2 := xexec ga gb Y1 (.arith 0 rSr (cst V.machine.start.val) (cst 0)) with hY2
  set Y3 := (List.replicate (7 * V.tapeCount + 6) Instr.nop).foldl (xexec ga gb) Y2 with hY3
  have hsplit : Z = xexec ga gb Y3 (.arith 0 rCnt (.reg rCnt) (cst (8 * (V.tapeCount + 1)))) := by
    rw [hZ, simSetupBlock, List.foldl_append, List.foldl_append, List.foldl_append, List.ofFn_eq_map,
      List.foldl_map]
    rfl
  have hnop : ∀ (k : ℕ) (X : XState MM), ((List.replicate k Instr.nop).foldl (xexec ga gb) X).S.regs = X.S.regs ∧
      ((List.replicate k Instr.nop).foldl (xexec ga gb) X).mem = X.mem := by
    intro k
    induction k with
    | zero => intro X; simp
    | succ k ih => intro X; rw [List.replicate_succ, List.foldl_cons]; rw [(ih _).1, (ih _).2]; simp [xexec]
  have Y3r : Y3.S.regs = Y2.S.regs := (hnop _ _).1
  have Y3m : Y3.mem = Y2.mem := (hnop _ _).2
  have Zr : ∀ r, r ≠ rCnt → Z.S.regs r = Y2.S.regs r := by
    intro r hr; rw [hsplit]; simp only [xexec, setNext_regs]; rw [Function.update_of_ne hr, Y3r]
  have Y2r : ∀ r, r ≠ rSr → Y2.S.regs r = Y1.S.regs r := by
    intro r hr; rw [hY2]; simp only [xexec, setNext_regs]; rw [Function.update_of_ne hr]
  refine ⟨Z, ⟨h2, h1⟩, ⟨by rw [h3, interpAddr_eq], ?_, ?_, ?_, ?_⟩⟩
  · rw [hsplit]
    simp only [xexec, setNext_regs, Function.update_self, val_reg, Y3r]
    rw [Y2r _ (by simp [reg_eq_iff]), fh1, if_neg (by simp [reg_eq_iff]; intro x; omega), hY.regCnt]
    simp [ofNat_add, initLen, cst]; ring_nf
  · rw [Zr _ (by simp [reg_eq_iff]), hY2]
    simp [xexec, cst]
  · intro i
    rw [Zr _ (by simp [reg_eq_iff]), Y2r _ (by simp [reg_eq_iff]; omega), fh1,
      if_pos ⟨i, List.mem_finRange i, rfl⟩]
    simp
  · rw [hsplit]
    simp only [xexec]
    rw [Y3m, hY2]
    simp only [xexec]
    rw [fh2, hY.mem]
    apply congrArg (memRep V w)
    funext i j
    simp only [initTapes, Function.update_apply, Fin.ext_iff, gsel]
    split_ifs <;> simp_all

theorem fits_small (hF : InitFits V w n t) : 50 + 34 < 2 ^ w := by
  have := hF.code; unfold codeLen idleAddr deadAddr leafAddr chainAddr interpAddr at this; omega

/-- **The initialization, all words proper** (`initLen` steps). -/
theorem init_ok (hF : InitFits V w n t) (hA : ∀ q < (n + w - 1) / w, ga q ≠ none)
    (hB : ∀ q < (t + w - 1) / w, gb q ≠ none) :
    ∃ Y, Runs ga gb (initState MM) (initLen V n t) Y ∧ InitDone V hfit ga gb Y := by
  have hs := fits_small V hF
  obtain ⟨Y1, r1, hY1⟩ := start_block V hfit ga gb hF
  obtain ⟨Y2, r2, hY2⟩ := unpack_loop_ok V hfit ga gb true ⟨0, tape0_lt V⟩ 8 n (deadAddr V) 8 0 0
    (fun _ _ => false) (code_unpackA V hfit) (by omega) hF.n_lt hF.w_pos hF.addrA
    (fun q hq => by simpa [gsel] using hA q hq) n 0 Y1 (by omega) hY1
  obtain ⟨Y3, r3, hY3⟩ := setup_block V hfit ga gb hF Y2 hY2
  obtain ⟨Y4, r4, hY4⟩ := unpack_loop_ok V hfit ga gb false ⟨1, tape1_lt V⟩ 50 t (deadAddr V) (24 * n + 24) 0
    (0 + (n + w - 1) / w) _ (code_unpackB V hfit) hs hF.t_lt hF.w_pos hF.addrB
    (fun q hq => by simpa [gsel] using hB q hq) t 0 Y3 (by omega) hY3
  obtain ⟨Y5, r5, hY5⟩ := simSetup_block V hfit ga gb hF Y4 hY4
  refine ⟨Y5, ?_, hY5⟩
  have := r1.trans _ _ (r2.trans _ _ (r3.trans _ _ (r4.trans _ _ r5)))
  rw [show initLen V n t = 8 + (24 * (n - 0) + 8 + (8 + (24 * (t - 0) + 8 + 8 * (V.tapeCount + 1)))) by
    unfold initLen; omega]
  exact this

/-- **The initialization, some word `#`**: the run reaches `jmp dead`. -/
theorem init_bad (hF : InitFits V w n t)
    (hbad : ¬ ((∀ q < (n + w - 1) / w, ga q ≠ none) ∧ (∀ q < (t + w - 1) / w, gb q ≠ none))) :
    ∃ m Y, Runs ga gb (initState MM) m Y ∧ Y.S.pc = BitVec.ofNat w (deadAddr V) := by
  have hs := fits_small V hF
  obtain ⟨Y1, r1, hY1⟩ := start_block V hfit ga gb hF
  by_cases hA : ∀ q < (n + w - 1) / w, ga q ≠ none
  · have hB : ¬ ∀ q < (t + w - 1) / w, gb q ≠ none := fun hB => hbad ⟨hA, hB⟩
    obtain ⟨Y2, r2, hY2⟩ := unpack_loop_ok V hfit ga gb true ⟨0, tape0_lt V⟩ 8 n (deadAddr V) 8 0 0
      (fun _ _ => false) (code_unpackA V hfit) (by omega) hF.n_lt hF.w_pos hF.addrA
      (fun q hq => by simpa [gsel] using hA q hq) n 0 Y1 (by omega) hY1
    obtain ⟨Y3, r3, hY3⟩ := setup_block V hfit ga gb hF Y2 hY2
    obtain ⟨m, Y4, r4, hY4⟩ := unpack_loop_bad V hfit ga gb false ⟨1, tape1_lt V⟩ 50 t (deadAddr V) (24 * n + 24) 0
      (0 + (n + w - 1) / w) _ (code_unpackB V hfit) hs hF.t_lt hF.w_pos hF.addrB
      (fun h => hB fun q hq => by simpa [gsel] using h q hq) t 0 Y3 (by omega) hY3
    exact ⟨_, Y4, r1.trans _ _ (r2.trans _ _ (r3.trans _ _ r4)), hY4⟩
  · obtain ⟨m, Y2, r2, hY2⟩ := unpack_loop_bad V hfit ga gb true ⟨0, tape0_lt V⟩ 8 n (deadAddr V) 8 0 0
      (fun _ _ => false) (code_unpackA V hfit) (by omega) hF.n_lt hF.w_pos hF.addrA
      (fun h => hA fun q hq => by simpa [gsel] using h q hq) n 0 Y1 (by omega) hY1
    exact ⟨_, Y2, r1.trans _ _ r2, hY2⟩

end Start

end NearCubicGates.Adapters.ShortPCP
