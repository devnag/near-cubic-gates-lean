import SourceAdapters.ACSP.Model

/-!
# Runs of a RAM with read counters

The run and tape-prefix conditions of `def:ram`, used in `lem:tm-ram`, are
expressed here with explicit counters for the words read from each tape.

- `xstep ga gb` advances a configuration and memory using `ga q` or `gb q`
  for the next word of the corresponding tape.
- `valid_eq_xrun` identifies any legal configuration sequence with this run,
  taking `ga,gb` from the words that it reads.
- `readsA_xrun` and `readString_xrun` identify the read string with the
  concatenation of its non-`#` words in order.
- `xrun_straight` evaluates jump-free, halt-free code by a left fold.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP

open NearCubicGates.Adapters.ACSP

variable {M : Ram}

/-- A configuration, a memory, and the numbers of words read so far from tapes A and B. -/
structure XState (M : Ram) where
  S : M.Config
  mem : M.Memory
  qa : ℕ
  qb : ℕ

/-- One instruction, with reads answered by `ga` / `gb` at the current read count (Def. 6.11, with the memory update of the model). -/
def xexec (ga gb : ℕ → Option (BitVec M.w)) (X : XState M) : Instr M.w M.k M.ops → XState M
  | .nop => { X with S := X.S.next }
  | .readA i => { X with S := X.S.setNext i (ga X.qa), qa := X.qa + 1 }
  | .readB i => { X with S := X.S.setNext i (gb X.qb), qb := X.qb + 1 }
  | .load i j => { X with S := X.S.setNext j (some (X.mem (X.S.val (.reg i)))) }
  | .pload _ _ => { X with S := X.S.next }
  | .store j x => { X with S := X.S.next, mem := Function.update X.mem (X.S.val (.reg j)) (X.S.val x) }
  | .iseof i j => { X with S := X.S.setNext i (some (if X.S.regs j = none then 1 else 0)) }
  | .out _ => X
  | .arith op i x y => { X with S := X.S.setNext i (some (M.alu op (X.S.val x) (X.S.val y))) }
  | .je i c => { X with S := if X.S.val (.reg i) = 0 then X.S.jump c else X.S.next }
  | .jne i c => { X with S := if X.S.val (.reg i) ≠ 0 then X.S.jump c else X.S.next }
  | .jmp c => { X with S := X.S.jump c }

/-- The successor (unchanged when `pc` is outside the code). -/
def xstep (ga gb : ℕ → Option (BitVec M.w)) (X : XState M) : XState M :=
  match M.instrAt X.S.pc with
  | none => X
  | some I => xexec ga gb X I

/-- `n` steps. -/
def xrun (ga gb : ℕ → Option (BitVec M.w)) (X : XState M) (n : ℕ) : XState M := (xstep ga gb)^[n] X

theorem xrun_zero (ga gb : ℕ → Option (BitVec M.w)) (X : XState M) : xrun ga gb X 0 = X := rfl

theorem xrun_succ (ga gb : ℕ → Option (BitVec M.w)) (X : XState M) (n : ℕ) :
    xrun ga gb X (n + 1) = xrun ga gb (xstep ga gb X) n := Function.iterate_succ_apply _ _ _

theorem xrun_succ' (ga gb : ℕ → Option (BitVec M.w)) (X : XState M) (n : ℕ) :
    xrun ga gb X (n + 1) = xstep ga gb (xrun ga gb X n) := Function.iterate_succ_apply' _ _ _

theorem xrun_add (ga gb : ℕ → Option (BitVec M.w)) (X : XState M) (m n : ℕ) :
    xrun ga gb X (m + n) = xrun ga gb (xrun ga gb X m) n := by
  unfold xrun; rw [Nat.add_comm, Function.iterate_add_apply]

/-- `I_pc` exists and is not `out`: a Def. 6.11 step is possible and the configuration is not final. -/
def Steppable (X : XState M) : Prop := ∃ I, M.instrAt X.S.pc = some I ∧ ∀ b, I ≠ .out b

theorem step_xstep (ga gb : ℕ → Option (BitVec M.w)) (X : XState M) (h : Steppable X) :
    M.Step X.S X.mem (xstep ga gb X).S (xstep ga gb X).mem := by
  obtain ⟨I, hI, hno⟩ := h
  unfold Ram.Step xstep
  rw [hI]
  cases I with
  | out b => exact absurd rfl (hno b)
  | readA i => exact ⟨⟨_, rfl⟩, rfl⟩
  | readB i => exact ⟨⟨_, rfl⟩, rfl⟩
  | _ => exact ⟨rfl, rfl⟩

theorem not_final_of_steppable (X : XState M) (h : Steppable X) : ¬ M.Final X.S := by
  obtain ⟨I, hI, hno⟩ := h
  rintro ⟨b, hb⟩
  rw [hI] at hb
  exact hno b (Option.some.inj hb)

/-! ## The `⇐` direction: a valid sequence is a run -/

/-- The values read from tape A (`tapeA = true`) or B at the steps `0, …, m − 1` of a sequence. -/
def readsUpTo (tapeA : Bool) (S : ℕ → M.Config) (m : ℕ) : List (Option (BitVec M.w)) :=
  (List.range m).filterMap (M.readAt tapeA S)

theorem readsUpTo_succ (tapeA : Bool) (S : ℕ → M.Config) (m : ℕ) :
    readsUpTo tapeA S (m + 1) = readsUpTo tapeA S m ++ (M.readAt tapeA S m).toList := by
  unfold readsUpTo
  rw [List.range_succ, List.filterMap_append]
  congr 1

/-- The `q`-th value read (`#` = `none` beyond the end). -/
def readOracle (tapeA : Bool) (S : ℕ → M.Config) (T : ℕ) (q : ℕ) : Option (BitVec M.w) :=
  (readsUpTo tapeA S (T - 1)).getD q none

theorem readsUpTo_prefix (tapeA : Bool) (S : ℕ → M.Config) {m n : ℕ} (h : m ≤ n) :
    readsUpTo tapeA S m <+: readsUpTo tapeA S n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => rw [readsUpTo_succ]; exact ih.trans (List.prefix_append _ _)

theorem readOracle_at (tapeA : Bool) (S : ℕ → M.Config) (T i : ℕ) (hi : i + 1 ≤ T - 1)
    (v : Option (BitVec M.w)) (hv : M.readAt tapeA S i = some v) :
    readOracle tapeA S T (readsUpTo tapeA S i).length = v := by
  unfold readOracle
  have hp := readsUpTo_prefix tapeA S hi
  rw [readsUpTo_succ, hv] at hp
  obtain ⟨rest, hrest⟩ := hp
  rw [← hrest]
  simp

/-- **A valid sequence is a run.** If consecutive configurations are Def. 6.11 steps for `i + 1 < T`, then for every
`i ≤ T − 1` the sequence agrees with `xrun` driven by the words it reads. -/
theorem valid_eq_xrun (T : ℕ) (S : ℕ → M.Config) (mem : ℕ → M.Memory)
    (hstep : ∀ i, i + 1 < T → M.Step (S i) (mem i) (S (i + 1)) (mem (i + 1))) :
    ∀ i, i ≤ T - 1 →
      xrun (readOracle true S T) (readOracle false S T) ⟨S 0, mem 0, 0, 0⟩ i =
        ⟨S i, mem i, (readsUpTo true S i).length, (readsUpTo false S i).length⟩ := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [xrun_succ', ih (by omega)]
    have hs := hstep i (by omega)
    unfold Ram.Step at hs
    unfold xstep
    simp only
    rw [readsUpTo_succ, readsUpTo_succ]
    rcases hI : M.instrAt (S i).pc with _ | I
    · rw [hI] at hs; exact hs.elim
    · rw [hI] at hs
      have hrA : ∀ r, I = .readA r → M.readAt true S i = some ((S (i + 1)).regs r) := by
        intro r hr; subst hr; simp [Ram.readAt, hI]
      have hrB : ∀ r, I = .readB r → M.readAt false S i = some ((S (i + 1)).regs r) := by
        intro r hr; subst hr; simp [Ram.readAt, hI]
      have hnA : (∀ r, I ≠ .readA r) → M.readAt true S i = none := by
        intro h; unfold Ram.readAt; rw [hI]; cases I <;> simp_all
      have hnB : (∀ r, I ≠ .readB r) → M.readAt false S i = none := by
        intro h; unfold Ram.readAt; rw [hI]; cases I <;> simp_all
      cases I with
      | readA r =>
        obtain ⟨⟨v, hv⟩, hm⟩ := hs
        have hA := hrA r rfl
        have hB := hnB (by intro r' h; cases h)
        rw [hA, hB]
        have hval : (S (i + 1)).regs r = v := by rw [hv]; simp [Ram.Config.setNext]
        have ho := readOracle_at true S T i (by omega) _ hA
        simp only [xexec, ho, Option.toList, List.length_append, List.length_cons, List.length_nil,
          List.length_nil, hm]
        rw [hval, ← hv]; simp
      | readB r =>
        obtain ⟨⟨v, hv⟩, hm⟩ := hs
        have hB := hrB r rfl
        have hA := hnA (by intro r' h; cases h)
        rw [hA, hB]
        have hval : (S (i + 1)).regs r = v := by rw [hv]; simp [Ram.Config.setNext]
        have ho := readOracle_at false S T i (by omega) _ hB
        simp only [xexec, ho, Option.toList, List.length_append, List.length_cons, List.length_nil, hm]
        rw [hval, ← hv]; simp
      | out b => exact hs.elim
      | _ =>
        rw [hnA (by intro r h; cases h), hnB (by intro r h; cases h)]
        obtain ⟨h1, h2⟩ := hs
        simp only [xexec, Option.toList, List.append_nil, h1, h2]

/-! ## The `⇒` direction: the words read by a run -/

/-- `I` is a read of tape A. -/
def isReadA {w k ops : ℕ} : Option (Instr w k ops) → Bool
  | some (.readA _) => true
  | _ => false

/-- `I` is a read of tape B. -/
def isReadB {w k ops : ℕ} : Option (Instr w k ops) → Bool
  | some (.readB _) => true
  | _ => false

theorem readAt_xrun_A (ga gb : ℕ → Option (BitVec M.w)) (X : XState M) (i : ℕ) :
    M.readAt true (fun j => (xrun ga gb X j).S) i =
      (if isReadA (M.instrAt (xrun ga gb X i).S.pc) then some (ga (xrun ga gb X i).qa) else none) ∧
    (xrun ga gb X (i + 1)).qa =
      (xrun ga gb X i).qa + (if isReadA (M.instrAt (xrun ga gb X i).S.pc) then 1 else 0) := by
  simp only [Ram.readAt]
  rw [xrun_succ']
  unfold xstep
  rcases hI : M.instrAt (xrun ga gb X i).S.pc with _ | I
  · simp [isReadA]
  · cases I <;> simp [xexec, Ram.Config.setNext, isReadA]

theorem readAt_xrun_B (ga gb : ℕ → Option (BitVec M.w)) (X : XState M) (i : ℕ) :
    M.readAt false (fun j => (xrun ga gb X j).S) i =
      (if isReadB (M.instrAt (xrun ga gb X i).S.pc) then some (gb (xrun ga gb X i).qb) else none) ∧
    (xrun ga gb X (i + 1)).qb =
      (xrun ga gb X i).qb + (if isReadB (M.instrAt (xrun ga gb X i).S.pc) then 1 else 0) := by
  simp only [Ram.readAt]
  rw [xrun_succ']
  unfold xstep
  rcases hI : M.instrAt (xrun ga gb X i).S.pc with _ | I
  · simp [isReadB]
  · cases I <;> simp [xexec, Ram.Config.setNext, isReadB]

/-- The words a run reads from tape A in its first `m` steps are `ga X.qa, …, ga (qa_m − 1)`. -/
theorem readsA_xrun (ga gb : ℕ → Option (BitVec M.w)) (X : XState M) (m : ℕ) :
    readsUpTo true (fun j => (xrun ga gb X j).S) m =
      (List.range ((xrun ga gb X m).qa - X.qa)).map (fun q => ga (X.qa + q)) ∧ X.qa ≤ (xrun ga gb X m).qa := by
  induction m with
  | zero => simp [readsUpTo, xrun_zero]
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨h1, h2⟩ := readAt_xrun_A ga gb X m
    rw [readsUpTo_succ, ih1, h1, h2]
    split_ifs
    · refine ⟨?_, by omega⟩
      rw [show (xrun ga gb X m).qa + 1 - X.qa = ((xrun ga gb X m).qa - X.qa) + 1 by omega, List.range_succ,
        List.map_append]
      simp only [List.map_cons, List.map_nil, Option.toList_some]
      congr 3
      omega
    · simp [ih2]

theorem readsB_xrun (ga gb : ℕ → Option (BitVec M.w)) (X : XState M) (m : ℕ) :
    readsUpTo false (fun j => (xrun ga gb X j).S) m =
      (List.range ((xrun ga gb X m).qb - X.qb)).map (fun q => gb (X.qb + q)) ∧ X.qb ≤ (xrun ga gb X m).qb := by
  induction m with
  | zero => simp [readsUpTo, xrun_zero]
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨h1, h2⟩ := readAt_xrun_B ga gb X m
    rw [readsUpTo_succ, ih1, h1, h2]
    split_ifs
    · refine ⟨?_, by omega⟩
      rw [show (xrun ga gb X m).qb + 1 - X.qb = ((xrun ga gb X m).qb - X.qb) + 1 by omega, List.range_succ,
        List.map_append]
      simp only [List.map_cons, List.map_nil, Option.toList_some]
      congr 3
      omega
    · simp [ih2]

/-- Def. 6.10's read string is the concatenation of the non-`#` values read. -/
theorem readString_eq (tapeA : Bool) (T : ℕ) (S : ℕ → M.Config) :
    M.readString tapeA T S = ((readsUpTo tapeA S (T - 1)).filterMap fun v => v.map Ram.wordBits).flatten := by
  unfold Ram.readString readsUpTo
  rw [List.filterMap_filterMap]

/-! ## Words of a bit string -/

/-- The `q`-th `w`-bit word of `x` (bits `q·w, …, q·w + w − 1`, least significant first; blank `0` beyond). -/
def wordOf (w : ℕ) (x : List Bool) (q : ℕ) : BitVec w :=
  (BitVec.ofBoolListLE (List.ofFn fun j : Fin w => x.getD (q * w + j.val) false)).cast (by simp)

theorem getLsbD_wordOf (w : ℕ) (x : List Bool) (q j : ℕ) (hj : j < w) :
    (wordOf w x q).getLsbD j = x.getD (q * w + j) false := by
  unfold wordOf
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD, hj]

theorem wordBits_wordOf (w : ℕ) (x : List Bool) (q : ℕ) (hq : (q + 1) * w ≤ x.length) :
    Ram.wordBits (wordOf w x q) = (x.drop (q * w)).take w := by
  apply List.ext_getElem
  · simp [Ram.wordBits]; rw [Nat.add_mul] at hq; omega
  · intro j h1 h2
    simp only [Ram.wordBits, List.getElem_ofFn, List.getElem_take, List.getElem_drop]
    have hj : j < w := by simpa [Ram.wordBits] using h1
    rw [getLsbD_wordOf w x q j hj]
    rw [Nat.add_mul] at hq
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show q * w + j < x.length by omega)]

/-- The first `m` words of `x`, concatenated, are a prefix of `x` (when they fit). -/
theorem words_prefix (w : ℕ) (x : List Bool) (m : ℕ) (hm : m * w ≤ x.length) :
    ((List.range m).map fun q => Ram.wordBits (wordOf w x q)).flatten = x.take (m * w) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih (by rw [Nat.add_mul] at hm; omega)]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [wordBits_wordOf w x m hm, Nat.add_mul, one_mul, List.take_add]

/-- The word stream of `x`: word `q` while it fits, `#` after. -/
def wordStream (w : ℕ) (x : List Bool) (q : ℕ) : Option (BitVec w) :=
  if (q + 1) * w ≤ x.length then some (wordOf w x q) else none

/-- Reading any number of words of the stream of `x` gives a prefix of `x` (Def. 6.10). -/
theorem wordStream_prefix (w : ℕ) (x : List Bool) (m : ℕ) :
    (((List.range m).map (wordStream w x)).filterMap fun v => v.map Ram.wordBits).flatten <+: x := by
  have key : ∀ m, (((List.range m).map (wordStream w x)).filterMap fun v => v.map Ram.wordBits).flatten =
      x.take (min m (if w = 0 then m else x.length / w) * w) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.filterMap_append, List.flatten_append, ih]
      simp only [List.map_cons, List.map_nil]
      unfold wordStream
      by_cases hw : w = 0
      · subst hw; simp [Ram.wordBits]
      · simp only [hw, if_false]
        by_cases hfit : (m + 1) * w ≤ x.length
        · have hm : m + 1 ≤ x.length / w := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hw)).mpr hfit
          rw [if_pos hfit]
          simp only [List.filterMap_cons, Option.map_some, List.filterMap_nil, List.flatten_cons,
            List.flatten_nil, List.append_nil]
          rw [min_eq_left (by omega), min_eq_left (by omega), wordBits_wordOf w x m hfit, Nat.add_mul, one_mul,
            List.take_add]
        · have hm : x.length / w < m + 1 := by
            by_contra h
            exact hfit ((Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hw)).mp (by omega))
          rw [if_neg hfit]
          simp only [List.filterMap_cons, Option.map_none, List.filterMap_nil, List.flatten_nil,
            List.append_nil]
          rw [min_eq_right (by omega), min_eq_right (by omega)]
  rw [key]
  exact List.take_prefix _ _

/-! ## Straight-line code -/

/-- An instruction that is not a jump and not `out`: it advances `pc` by one. -/
def IsStraight {w k ops : ℕ} : Instr w k ops → Prop
  | .out _ => False
  | .je _ _ => False
  | .jne _ _ => False
  | .jmp _ => False
  | _ => True

theorem xexec_pc_straight (ga gb : ℕ → Option (BitVec M.w)) (X : XState M) (I : Instr M.w M.k M.ops)
    (h : IsStraight I) : (xexec ga gb X I).S.pc = X.S.pc + 1 := by
  cases I <;> simp_all [IsStraight, xexec, Ram.Config.next, Ram.Config.setNext]

theorem instrAt_ofNat (S : M.Config) (a : ℕ) (hpc : S.pc = BitVec.ofNat M.w a) (ha : a < 2 ^ M.w) :
    M.instrAt S.pc = M.code[a]? := by
  simp [Ram.instrAt, hpc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem ofNat_succ {w : ℕ} (a : ℕ) : BitVec.ofNat w a + 1 = BitVec.ofNat w (a + 1) := by
  rw [show (1 : BitVec w) = BitVec.ofNat w 1 from rfl, BitVec.ofNat_add_ofNat]

/-- The code `prog` sits at `a`, `…`, `a + |prog| − 1`. -/
def CodeAt (M : Ram) (a : ℕ) (prog : List (Instr M.w M.k M.ops)) : Prop :=
  ∀ j, j < prog.length → M.code[a + j]? = prog[j]?

theorem CodeAt.tail {a : ℕ} {I : Instr M.w M.k M.ops} {prog : List (Instr M.w M.k M.ops)}
    (h : CodeAt M a (I :: prog)) : CodeAt M (a + 1) prog := by
  intro j hj
  have := h (j + 1) (by simp; omega)
  rw [show a + 1 + j = a + (j + 1) by omega, this]
  simp

theorem CodeAt.head {a : ℕ} {I : Instr M.w M.k M.ops} {prog : List (Instr M.w M.k M.ops)}
    (h : CodeAt M a (I :: prog)) : M.code[a]? = some I := by
  simpa using h 0 (by simp)

theorem CodeAt.append_left {a : ℕ} {p q : List (Instr M.w M.k M.ops)} (h : CodeAt M a (p ++ q)) :
    CodeAt M a p := by
  intro j hj
  rw [h j (by simp; omega), List.getElem?_append_left hj]

theorem CodeAt.append_right {a : ℕ} {p q : List (Instr M.w M.k M.ops)} (h : CodeAt M a (p ++ q)) :
    CodeAt M (a + p.length) q := by
  intro j hj
  rw [show a + p.length + j = a + (p.length + j) by omega, h _ (by simp; omega),
    List.getElem?_append_right (by omega)]
  simp

/-- **Straight-line execution.** Running through straight-line code `prog` at `a` (with `a + |prog| ≤ 2^w`) is the
left fold of `xexec` over `prog`; every intermediate state can step, and `pc` ends at `a + |prog|`. -/
theorem xrun_straight (ga gb : ℕ → Option (BitVec M.w)) :
    ∀ (prog : List (Instr M.w M.k M.ops)) (a : ℕ) (X : XState M), CodeAt M a prog →
      a + prog.length < 2 ^ M.w → X.S.pc = BitVec.ofNat M.w a → (∀ I ∈ prog, IsStraight I) →
      xrun ga gb X prog.length = prog.foldl (xexec ga gb) X ∧
      (∀ i < prog.length, Steppable (xrun ga gb X i)) ∧
      (prog.foldl (xexec ga gb) X).S.pc = BitVec.ofNat M.w (a + prog.length)
  | [], a, X, _, _, hpc, _ => ⟨rfl, fun i hi => absurd hi (by simp), by simpa using hpc⟩
  | I :: prog, a, X, hc, hfit, hpc, hs => by
    have hI : M.instrAt X.S.pc = some I := by
      rw [instrAt_ofNat X.S a hpc (by simp at hfit; omega)]; exact hc.head
    have hsI : IsStraight I := hs I (by simp)
    have hx : xstep ga gb X = xexec ga gb X I := by unfold xstep; rw [hI]
    have hpc' : (xexec ga gb X I).S.pc = BitVec.ofNat M.w (a + 1) := by
      rw [xexec_pc_straight ga gb X I hsI, hpc, ofNat_succ]
    obtain ⟨h1, h2, h3⟩ := xrun_straight ga gb prog (a + 1) (xexec ga gb X I) hc.tail
      (by simp at hfit; omega) hpc' (fun J hJ => hs J (by simp [hJ]))
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_cons, xrun_succ, hx, h1]; rfl
    · intro i hi
      rcases i with _ | i
      · refine ⟨I, hI, fun b hb => ?_⟩
        subst hb; exact hsI
      · rw [xrun_succ, hx]; exact h2 i (by simp at hi; omega)
    · rw [List.foldl_cons, h3, List.length_cons]; congr 1; omega

end NearCubicGates.Adapters.ShortPCP
