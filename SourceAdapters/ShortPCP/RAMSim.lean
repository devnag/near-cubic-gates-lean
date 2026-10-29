import SourceAdapters.ShortPCP.RAMStart

/-!
# One step of `V` inside `M_n` (P02c)

Paper context: proof of `lem:tm-ram`, “Simulating `V`” and “Counting”. The interpreter loads the
scanned symbols, forms the index of the state-symbol pair, and branches to its transition leaf. That leaf
writes the symbols, moves the heads and sets the state. For fixed `V` this costs a constant number of
instructions. Each completed block adds its padded, multiple-of-eight length to the counter.

`SimAt C c Y`: `M_n` is at the interpreter with the counter `c`, `sr` = the state of `C`, head registers at the
heads of `C`, and memory = the tapes of `C` (layout of `RAMSteps.memRep`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP

open NearCubicGates.Adapters.ACSP
open NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape

/-! ## Horner's rule for the leaf index -/

theorem symCode_succ {k : ℕ} (σ : Fin (k + 1) → Bool) :
    (symCode σ).val = (if σ 0 then 1 else 0) * 2 ^ k + (symCode (σ ∘ Fin.succ)).val := by
  simp only [symCode, finFunctionFinEquiv_apply]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.rev_last, Fin.val_last, Function.comp_apply, Fin.val_castSucc]
  rw [Nat.add_comm]
  congr 1
  · split_ifs <;> simp
  · apply Finset.sum_congr rfl
    intro i _
    rw [Fin.rev_castSucc]
    rfl

theorem horner_eq : ∀ (k : ℕ) (σ : Fin k → Bool) (q : ℕ),
    (List.finRange k).foldl (fun acc i => 2 * acc + (if σ i then 1 else 0)) q = q * 2 ^ k + (symCode σ).val
  | 0, σ, q => by simp [symCode]
  | k + 1, σ, q => by
    rw [List.finRange_succ, List.foldl_cons, List.foldl_map]
    have h := horner_eq k (σ ∘ Fin.succ) (2 * q + (if σ 0 then 1 else 0))
    refine Eq.trans h ?_
    rw [symCode_succ]
    rw [pow_succ]; ring

theorem CodeAt.flatten_ofFn {M : Ram} {L : ℕ} : ∀ {k a : ℕ} (f : Fin k → List (Instr M.w M.k M.ops)),
    (∀ m, (f m).length = L) → CodeAt M a (List.ofFn f).flatten → ∀ m : Fin k, CodeAt M (a + m.val * L) (f m)
  | 0, _, _, _, _, m => m.elim0
  | k + 1, a, f, hL, h, m => by
    rw [List.ofFn_succ, List.flatten_cons] at h
    refine Fin.cases ?_ (fun m' => ?_) m
    · simpa using h.append_left
    · have h2 := CodeAt.flatten_ofFn (fun i => f i.succ) (fun i => hL _) (h.append_right) m'
      rw [hL 0] at h2
      simp only [Fin.val_succ]
      rw [show a + (m'.val + 1) * L = a + L + m'.val * L by ring]
      exact h2

theorem ofNat_sub_eq_zero {w a b : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    BitVec.ofNat w a - BitVec.ofNat w b = 0#w ↔ a = b := by
  rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add, ofNat_inj ha hb]

theorem ofNat_sub_ofNat_le {w a b : ℕ} (ha : a < 2 ^ w) (hba : b ≤ a) :
    BitVec.ofNat w a - BitVec.ofNat w b = BitVec.ofNat w (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat_lt ha, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
  rw [show 2 ^ w - b + a = (a - b) + 2 ^ w by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- The left move: `h ← h − ((0 − cmp(0, cmp(h, K) − 1)) & K)` is `h − K·[h ≥ K]`. -/
theorem left_value {w K p i : ℕ} (hw : 2 ≤ w) (hi : i < K) (hK : K < 2 ^ w) (hh : K * p + i < 2 ^ w) :
    BitVec.ofNat w (K * p + i) -
      ((BitVec.ofNat w 0 - cmpFn (BitVec.ofNat w 0) (cmpFn (BitVec.ofNat w (K * p + i)) (BitVec.ofNat w K) -
        BitVec.ofNat w 1)) &&& BitVec.ofNat w K) = BitVec.ofNat w (K * (p - 1) + i) := by
  have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp only [Nat.mul_zero, Nat.zero_add, Nat.zero_sub]
    rw [cmpFn_lt (by omega) hK hi, show (1 : BitVec w) - BitVec.ofNat w 1 = 0 from BitVec.sub_self _,
      show BitVec.ofNat w 0 = (0 : BitVec w) from rfl, cmpFn_zero_left, if_pos rfl]
    simp
  · have hge : K ≤ K * p + i := by nlinarith
    have ht1 : cmpFn (BitVec.ofNat w (K * p + i)) (BitVec.ofNat w K) = 0 ∨
        cmpFn (BitVec.ofNat w (K * p + i)) (BitVec.ofNat w K) = -1 := by
      rcases Nat.eq_or_lt_of_le hge with h | h
      · left; rw [← h]; exact cmpFn_eq
      · right; exact cmpFn_gt hh hK h
    have ht2 : cmpFn (BitVec.ofNat w (K * p + i)) (BitVec.ofNat w K) - BitVec.ofNat w 1 ≠ 0 := by
      intro h0
      rw [BitVec.sub_eq_iff_eq_add] at h0
      have h : cmpFn (BitVec.ofNat w (K * p + i)) (BitVec.ofNat w K) = BitVec.ofNat w 1 := by
        rw [h0]; exact BitVec.zero_add _
      rcases ht1 with h1 | h1 <;> rw [h1] at h
      · exact one_ne_zero_of hw1 h.symm
      · have := congrArg BitVec.toNat h
        rw [BitVec.toNat_neg, toNat_ofNat_lt hw1, show (1 : BitVec w) = BitVec.ofNat w 1 from rfl,
          toNat_ofNat_lt hw1, Nat.mod_eq_of_lt (by omega)] at this
        have : 4 ≤ 2 ^ w := by
          calc 4 = 2 ^ 2 := rfl
            _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
        omega
    rw [show BitVec.ofNat w 0 = (0 : BitVec w) from rfl, cmpFn_zero_left, if_neg ht2,
      show (0 : BitVec w) - 1 = BitVec.allOnes w from (BitVec.zero_sub _).trans BitVec.neg_one_eq_allOnes,
      BitVec.allOnes_and, ofNat_sub_ofNat_le hh hge]
    congr 1
    have : K ≤ K * p := Nat.le_mul_of_pos_right K hp
    rw [Nat.mul_sub_one]; omega

/-- The straight part of an action leaf (all but the final jump). -/
def actStraight (V : Verifier) (w m : ℕ) (a : Action V.tapeCount V.stateCount) : List (MI V w) :=
  List.replicate (2 * (leafCount V - 1 - m)) .nop ++ (List.ofFn (tapeSeg V w a)).flatten ++
    [.arith 0 rSr (cst a.nextControl.val) (cst 0)] ++ List.replicate (simPad V) .nop ++
    [.arith 0 rCnt (.reg rCnt) (cst (simLen V))]

theorem actLeaf_eq (V : Verifier) (w m : ℕ) (a : Action V.tapeCount V.stateCount) :
    actLeaf V w m a = actStraight V w m a ++ [.jmp (interpAddr V)] := by
  simp [actLeaf, actStraight]

theorem actStraight_length (V : Verifier) (w m : ℕ) (a : Action V.tapeCount V.stateCount) :
    (actStraight V w m a).length = 2 * (leafCount V - 1 - m) + 7 * V.tapeCount + 2 + simPad V := by
  simp only [actStraight, List.length_append, List.length_replicate, List.length_flatten, List.map_ofFn,
    List.length_cons, List.length_nil]
  rw [sum_ofFn_length _ (tapeSeg_length V w a)]; ring

theorem tapeSeg_straight (V : Verifier) (w : ℕ) (a : Action V.tapeCount V.stateCount) (i : Fin V.tapeCount) :
    ∀ I ∈ tapeSeg V w a i, IsStraight I := by
  intro I hI
  simp only [tapeSeg, List.mem_cons] at hI
  rcases hI with rfl | hI
  · generalize a.write i = o
    cases o <;> exact trivial
  · generalize a.move i = mv at hI
    cases mv <;> simp only [moveInstrs, List.mem_cons, List.not_mem_nil, or_false] at hI <;>
      rcases hI with h|h|h|h|h|h <;> rw [h] <;> exact trivial

theorem actStraight_straight (V : Verifier) (w m : ℕ) (a : Action V.tapeCount V.stateCount) :
    ∀ I ∈ actStraight V w m a, IsStraight I := by
  intro I hI
  simp only [actStraight, List.mem_append, List.mem_replicate, List.mem_flatten, List.mem_ofFn,
    List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with (((⟨-, h⟩ | ⟨l, ⟨i, hl⟩, h⟩) | h) | ⟨-, h⟩) | h
  · rw [h]; exact trivial
  · subst hl; exact tapeSeg_straight V w a i I h
  · rw [h]; exact trivial
  · rw [h]; exact trivial
  · rw [h]; exact trivial

/-- The straight part of the accepting leaf. -/
def accStraight (V : Verifier) (w m : ℕ) : List (MI V w) :=
  List.replicate (2 * (leafCount V - 1 - m)) .nop ++ [.arith 0 rVd (cst 1) (cst 0)] ++
    List.replicate (accPad V) .nop ++ [.arith 0 rCnt (.reg rCnt) (cst (accLen V))]

theorem accLeaf_eq (V : Verifier) (w m : ℕ) : accLeaf V w m = accStraight V w m ++ [.jmp (idleAddr V)] := by
  simp [accLeaf, accStraight]

theorem accStraight_length (V : Verifier) (w m : ℕ) :
    (accStraight V w m).length = 2 * (leafCount V - 1 - m) + 2 + accPad V := by
  simp [accStraight]; ring

section Sim

variable (V : Verifier) {w n t T : ℕ} (hfit : codeLen V ≤ 2 ^ w)
variable (ga gb : ℕ → Option (BitVec w))

local notation "MM" => mnRam V w n t T hfit

/-- The tapes of a configuration as functions of the cell. -/
def tapeFn (C : Configuration V.tapeCount V.stateCount) : Fin V.tapeCount → ℕ → Bool :=
  fun i j => (C.tapes i).getD j false

/-- `M_n` at the interpreter, simulating `C`, with counter `c`. -/
structure SimAt (C : Configuration V.tapeCount V.stateCount) (c : ℕ) (Y : XState MM) : Prop where
  pc : Y.S.pc = BitVec.ofNat w (interpAddr V)
  regCnt : Y.S.regs rCnt = some (BitVec.ofNat w c)
  regSr : Y.S.regs rSr = some (BitVec.ofNat w C.control.val)
  regH : ∀ i, Y.S.regs (rH i) = some (BitVec.ofNat w (stride V * C.heads i + i.val))
  mem : Y.mem = memRep V w (tapeFn V C)

/-! ## The header: loads and the index -/

theorem fold_loads (l : List (Fin V.tapeCount)) (X : XState MM) :
    let Y := l.foldl (fun X i => (([.load (rH i) (rS i), .pload (rH i) (rS i)] : List (MI V w))).foldl
      (xexec ga gb) X) X
    (∀ i ∈ l, Y.S.regs (rS i) = some (X.mem ((X.S.regs (rH i)).getD 0))) ∧
    (∀ r, (∀ i ∈ l, r ≠ rS i) → Y.S.regs r = X.S.regs r) ∧ Y.mem = X.mem := by
  simp only [List.foldl_cons, List.foldl_nil]
  induction l generalizing X with
  | nil => simp
  | cons a l ih =>
    set X' := xexec ga gb (xexec ga gb X (.load (rH a) (rS a))) (.pload (rH a) (rS a)) with hX'
    obtain ⟨ih1, ih2, ih3⟩ := ih X'
    have e1 : X'.S.regs = Function.update X.S.regs (rS a) (some (X.mem ((X.S.regs (rH a)).getD 0))) := by
      simp [hX', xexec]
    have e2 : X'.mem = X.mem := by simp [hX', xexec]
    have hHS : ∀ i j : Fin V.tapeCount, rH i ≠ rS j := by intro i j h; simp [reg_eq_iff] at h; omega
    simp only [List.foldl_cons]
    refine ⟨fun i hi => ?_, fun r hr => ?_, by rw [ih3, e2]⟩
    · by_cases hil : i ∈ l
      · rw [ih1 i hil, e2, e1, Function.update_of_ne (hHS i a)]
      · have hia : i = a := by simp at hi; tauto
        subst hia
        rw [ih2 _ (fun j hj h => hil (by rw [rS_inj.mp h]; exact hj)), e1, Function.update_self]
    · rw [ih2 r (fun i hi => hr i (by simp [hi])), e1, Function.update_of_ne (hr a (by simp))]

theorem fold_idx (l : List (Fin V.tapeCount)) (X : XState MM) (v : ℕ) (b : Fin V.tapeCount → Bool)
    (hv : X.S.regs rIdx = some (BitVec.ofNat w v))
    (hs : ∀ i, X.S.regs (rS i) = some (BitVec.ofNat w (if b i then 1 else 0))) :
    let Y := l.foldl (fun X i => (([.arith 0 rIdx (.reg rIdx) (.reg rIdx), .arith 0 rIdx (.reg rIdx) (.reg (rS i))] :
      List (MI V w))).foldl (xexec ga gb) X) X
    Y.S.regs rIdx = some (BitVec.ofNat w (l.foldl (fun acc i => 2 * acc + (if b i then 1 else 0)) v)) ∧
    (∀ r, r ≠ rIdx → Y.S.regs r = X.S.regs r) ∧ Y.mem = X.mem := by
  simp only [List.foldl_cons, List.foldl_nil]
  induction l generalizing X v with
  | nil => simp [hv]
  | cons a l ih =>
    have hSI : ∀ i : Fin V.tapeCount, rS i ≠ rIdx := by intro i h; simp [reg_eq_iff] at h; omega
    set X' := xexec ga gb (xexec ga gb X (.arith 0 rIdx (.reg rIdx) (.reg rIdx))) (.arith 0 rIdx (.reg rIdx)
      (.reg (rS a))) with hX'
    have e1 : X'.S.regs rIdx = some (BitVec.ofNat w (2 * v + (if b a then 1 else 0))) := by
      simp [hX', xexec, hv, Function.update_of_ne (hSI a), hs a, ofNat_add]; ring_nf
    have e2 : ∀ r, r ≠ rIdx → X'.S.regs r = X.S.regs r := by
      intro r hr; simp [hX', xexec, Function.update_of_ne hr]
    have e3 : X'.mem = X.mem := by simp [hX', xexec]
    obtain ⟨ih1, ih2, ih3⟩ := ih X' _ e1 (fun i => by rw [e2 _ (hSI i), hs i])
    simp only [List.foldl_cons]
    exact ⟨ih1, fun r hr => by rw [ih2 r hr, e2 r hr], by rw [ih3, e3]⟩

/-- Head bounds: every head and the cell to its right are addressable. -/
def HeadsFit (C : Configuration V.tapeCount V.stateCount) : Prop :=
  ∀ i, stride V * (C.heads i + 1) + i.val < 2 ^ w

theorem ite_ofNat {w : ℕ} (b : Bool) : (if b then (1 : BitVec w) else 0) = BitVec.ofNat w (if b then 1 else 0) := by
  cases b <;> rfl

/-- **The header** (`4k_V + 1` steps): loads the scanned symbols and forms the leaf index of (state, scanned). -/
theorem header_run (C : Configuration V.tapeCount V.stateCount) (c : ℕ) (Y : XState MM)
    (hY : SimAt V hfit C c Y) (hfitH : HeadsFit V (w := w) C) (hcode : codeLen V < 2 ^ w) :
    ∃ Z, Runs ga gb Y (4 * V.tapeCount + 1) Z ∧ Z.S.pc = BitVec.ofNat w (chainAddr V) ∧
      Z.S.regs rIdx = some (BitVec.ofNat w (leafIndex V C.control C.scanned)) ∧
      Z.S.regs rCnt = some (BitVec.ofNat w c) ∧
      (∀ i, Z.S.regs (rH i) = some (BitVec.ofNat w (stride V * C.heads i + i.val))) ∧
      Z.mem = Y.mem := by
  have hc := code_header V hfit (n := n) (t := t) (T := T)
  have hlen := headerBlock_length V w
  obtain ⟨h1, h2, h3⟩ := xrun_straight (M := MM) ga gb (headerBlock V w) (interpAddr V) Y hc
    (by
      change interpAddr V + (headerBlock V w).length < 2 ^ w
      rw [hlen]; unfold codeLen idleAddr deadAddr leafAddr chainAddr at hcode; omega)
    hY.pc
    (by
      intro I hI
      change I ∈ headerBlock V w at hI
      simp only [headerBlock, List.mem_append, List.mem_flatten, List.mem_ofFn, List.mem_cons,
        List.not_mem_nil, or_false] at hI
      obtain (⟨l, ⟨i, hl⟩, h⟩ | h) | ⟨l, ⟨i, hl⟩, h⟩ := hI
      · subst hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> rw [h] <;> exact trivial
      · rw [h]; exact trivial
      · subst hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> rw [h] <;> exact trivial)
  change xrun ga gb Y (headerBlock V w).length = _ at h1
  rw [hlen] at h1 h2
  set Z := (headerBlock V w).foldl (xexec ga gb) Y with hZ
  obtain ⟨l1, l2, l3⟩ := fold_loads V hfit ga gb (List.finRange V.tapeCount) Y
  set Y1 := (List.finRange V.tapeCount).foldl (fun X i => (([.load (rH i) (rS i), .pload (rH i) (rS i)] :
    List (MI V w))).foldl (xexec ga gb) X) Y with hY1
  set Y2 := xexec ga gb Y1 (.arith 0 rIdx (.reg rSr) (cst 0)) with hY2
  have hHS : ∀ i j : Fin V.tapeCount, rH i ≠ rS j := by intro i j h; simp [reg_eq_iff] at h; omega
  have hSI : ∀ i : Fin V.tapeCount, rS i ≠ rIdx := by intro i h; simp [reg_eq_iff] at h; omega
  have Y2idx : Y2.S.regs rIdx = some (BitVec.ofNat w C.control.val) := by
    rw [hY2]; simp only [xexec, setNext_regs, Function.update_self, val_reg]
    rw [l2 _ (by intro i _ h; simp [reg_eq_iff] at h; omega), hY.regSr]; simp [cst]
  have Y2r : ∀ r, r ≠ rIdx → Y2.S.regs r = Y1.S.regs r := by
    intro r hr; rw [hY2]; simp only [xexec, setNext_regs]; rw [Function.update_of_ne hr]
  have Y2s : ∀ i, Y2.S.regs (rS i) = some (BitVec.ofNat w (if C.scanned i then 1 else 0)) := by
    intro i
    rw [Y2r _ (hSI i), l1 i (List.mem_finRange i), hY.regH i, hY.mem]
    simp only [Option.getD_some]
    rw [memRep_read V w _ i _ (by have := hfitH i; rw [Nat.mul_add] at this; omega), ite_ofNat]
    rfl
  obtain ⟨d1, d2, d3⟩ := fold_idx V hfit ga gb (List.finRange V.tapeCount) Y2 C.control.val C.scanned Y2idx Y2s
  have hsplit : Z = (List.finRange V.tapeCount).foldl (fun X i => (([.arith 0 rIdx (.reg rIdx) (.reg rIdx),
      .arith 0 rIdx (.reg rIdx) (.reg (rS i))] : List (MI V w))).foldl (xexec ga gb) X) Y2 := by
    rw [hZ, headerBlock, List.foldl_append, List.foldl_append, List.foldl_flatten, List.foldl_flatten,
      List.ofFn_eq_map, List.ofFn_eq_map, List.foldl_map, List.foldl_map]
    rfl
  refine ⟨Z, ⟨h2, h1⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h3, hlen, chainAddr, Nat.add_assoc]
  · rw [hsplit, d1, horner_eq]; rfl
  · rw [hsplit, d2 _ (by simp [reg_eq_iff]), Y2r _ (by simp [reg_eq_iff]),
      l2 _ (by intro i _ h; simp [reg_eq_iff] at h; omega), hY.regCnt]
  · intro i
    rw [hsplit, d2 _ (by simp [reg_eq_iff]; omega), Y2r _ (by simp [reg_eq_iff]; omega),
      l2 _ (fun j _ => hHS i j), hY.regH]
  · rw [hsplit, d3, hY2]; simp only [xexec]; rw [l3]

/-- **The chain**: from entry `j` with index `m` (`j ≤ m < N`), `2(m − j + 1)` steps to leaf `m`, changing only the
scratch register. -/
theorem chain_run (hcode : codeLen V < 2 ^ w) (hidx : leafCount V < 2 ^ w) (m : ℕ) (hm : m < leafCount V) :
    ∀ d j (Z : XState MM), d = m - j → j ≤ m → Z.S.pc = BitVec.ofNat w (chainAddr V + 2 * j) →
      Z.S.regs rIdx = some (BitVec.ofNat w m) →
      ∃ Z', Runs ga gb Z (2 * (d + 1)) Z' ∧ Z'.S.pc = BitVec.ofNat w (leafAddr V + m * leafLen V) ∧
        (∀ r, r ≠ rTmp → Z'.S.regs r = Z.S.regs r) ∧ Z'.mem = Z.mem := by
  have hc := code_chain V hfit (n := n) (t := t) (T := T)
  have hent := CodeAt.flatten_ofFn (M := MM) (L := 2) _ (fun _ => rfl) hc.append_left
  have hchain : chainAddr V + 2 * leafCount V < 2 ^ w := by
    unfold codeLen idleAddr deadAddr leafAddr at hcode; omega
  intro d
  induction d with
  | zero =>
    intro j Z hd hj hpc hi
    have hjm : j = m := by omega
    subst hjm
    have e := hent ⟨j, hm⟩
    have c0 : (mnRam V w n t T hfit).code[chainAddr V + 2 * j]? = some (.arith 1 rTmp (.reg rIdx) (cst j)) := by
      have := e 0 (by simp); simpa [Nat.mul_comm] using this
    have c1 : (mnRam V w n t T hfit).code[chainAddr V + 2 * j + 1]? =
        some (.je rTmp (leafAddr V + j * leafLen V)) := by
      have := e 1 (by simp); simpa [Nat.mul_comm] using this
    have r0 := Runs.single (M := MM) ga gb c0 hpc (by show _ < 2 ^ w; omega) (by intro b h; cases h)
    have r1 := Runs.single (M := MM) ga gb (X := xexec ga gb Z (.arith 1 rTmp (.reg rIdx) (cst j))) c1
      (by simp [xexec, hpc, ofNat_add]) (by show _ < 2 ^ w; omega) (by intro b h; cases h)
    refine ⟨_, r0.trans _ _ r1, ?_, ?_, ?_⟩
    · simp [xexec, hi, cst]
    · intro r hr; simp only [xexec]; split_ifs <;> simp [Function.update_of_ne hr]
    · simp [xexec]
  | succ d ih =>
    intro j Z hd hj hpc hi
    have hjm : j < m := by omega
    have e := hent ⟨j, by omega⟩
    have c0 : (mnRam V w n t T hfit).code[chainAddr V + 2 * j]? = some (.arith 1 rTmp (.reg rIdx) (cst j)) := by
      have := e 0 (by simp); simpa [Nat.mul_comm] using this
    have c1 : (mnRam V w n t T hfit).code[chainAddr V + 2 * j + 1]? =
        some (.je rTmp (leafAddr V + j * leafLen V)) := by
      have := e 1 (by simp); simpa [Nat.mul_comm] using this
    have r0 := Runs.single (M := MM) ga gb c0 hpc (by show _ < 2 ^ w; omega) (by intro b h; cases h)
    have r1 := Runs.single (M := MM) ga gb (X := xexec ga gb Z (.arith 1 rTmp (.reg rIdx) (cst j))) c1
      (by simp [xexec, hpc, ofNat_add]) (by show _ < 2 ^ w; omega) (by intro b h; cases h)
    have hne : BitVec.ofNat w m - BitVec.ofNat w j ≠ 0#w := by
      rw [Ne, ofNat_sub_eq_zero (by omega) (by omega)]; omega
    set Z2 := xexec ga gb (xexec ga gb Z (.arith 1 rTmp (.reg rIdx) (cst j))) (.je rTmp (leafAddr V + j * leafLen V))
      with hZ2
    have Z2pc : Z2.S.pc = BitVec.ofNat w (chainAddr V + 2 * (j + 1)) := by
      simp [hZ2, xexec, hi, cst, hne, hpc, ofNat_add]; ring_nf
    have Z2r : ∀ r, r ≠ rTmp → Z2.S.regs r = Z.S.regs r := by
      intro r hr; simp only [hZ2, xexec]; split_ifs <;> simp [Function.update_of_ne hr]
    have Z2m : Z2.mem = Z.mem := by simp [hZ2, xexec]
    obtain ⟨Z', r', h1, h2, h3⟩ := ih (j + 1) Z2 (by omega) (by omega) Z2pc
      (by rw [Z2r _ (by simp [reg_eq_iff]), hi])
    refine ⟨Z', ?_, h1, fun r hr => by rw [h2 r hr, Z2r r hr], by rw [h3, Z2m]⟩
    rw [show 2 * (d + 1 + 1) = 1 + 1 + 2 * (d + 1) by ring]
    exact (r0.trans _ _ r1).trans _ _ r'

/-- The tape after an optional write at `h`. -/
def wrTape (o : Option Bool) (f : ℕ → Bool) (h : ℕ) : ℕ → Bool :=
  match o with
  | none => f
  | some b => Function.update f h b

/-- Head registers and memory represent heads `hd` and tapes `tp`. -/
structure RelH (hd : Fin V.tapeCount → ℕ) (tp : Fin V.tapeCount → ℕ → Bool) (X : XState MM) : Prop where
  regH : ∀ i, X.S.regs (rH i) = some (BitVec.ofNat w (stride V * hd i + i.val))
  mem : X.mem = memRep V w tp

/-- **One tape of an action** (7 straight instructions): write at the head, then move it. -/
theorem seg_run (a : Action V.tapeCount V.stateCount) (i : Fin V.tapeCount) (hd : Fin V.tapeCount → ℕ)
    (tp : Fin V.tapeCount → ℕ → Bool) (X : XState MM) (hX : RelH V hfit hd tp X)
    (hfi : stride V * (hd i + 1) + i.val < 2 ^ w) (hw : 2 ≤ w) :
    RelH V hfit (Function.update hd i ((a.move i).apply (hd i)))
        (Function.update tp i (wrTape (a.write i) (tp i) (hd i))) ((tapeSeg V w a i).foldl (xexec ga gb) X) ∧
      (∀ r, r ≠ rTmp → (∀ j, r ≠ rH j) →
        ((tapeSeg V w a i).foldl (xexec ga gb) X).S.regs r = X.S.regs r) := by
  have hK : stride V < 2 ^ w := by rw [Nat.mul_add, Nat.mul_one] at hfi; omega
  have hh : stride V * hd i + i.val < 2 ^ w := by rw [Nat.mul_add, Nat.mul_one] at hfi; omega
  have hiK : i.val < stride V := by unfold stride; omega
  set X1 := xexec ga gb X (writeInstr V w i (a.write i)) with hX1
  have X1r : X1.S.regs = X.S.regs := by
    rw [hX1]; cases a.write i <;> simp [writeInstr, xexec]
  have X1m : X1.mem = memRep V w (Function.update tp i (wrTape (a.write i) (tp i) (hd i))) := by
    rw [hX1]
    cases hwr : a.write i with
    | none => simp [writeInstr, xexec, wrTape, hX.mem]
    | some b =>
      simp only [writeInstr, xexec, wrTape, val_reg, hX.regH, Option.getD_some, cst, val_const, hX.mem]
      rw [← ite_ofNat, memRep_write V w tp i (hd i) b hh]
  have hHT : ∀ j : Fin V.tapeCount, rH j ≠ rTmp := by intro j h; simp [reg_eq_iff] at h; omega
  have hHH : ∀ j : Fin V.tapeCount, j ≠ i → rH j ≠ rH i := fun j hj h => hj (rH_inj.mp h)
  have hgoal : (tapeSeg V w a i).foldl (xexec ga gb) X = (moveInstrs V w i (a.move i)).foldl (xexec ga gb) X1 := by
    rw [tapeSeg, List.foldl_cons]
  rw [hgoal]
  have key : ((moveInstrs V w i (a.move i)).foldl (xexec ga gb) X1).S.regs (rH i) =
        some (BitVec.ofNat w (stride V * (a.move i).apply (hd i) + i.val)) ∧
      (∀ r, r ≠ rTmp → r ≠ rH i → ((moveInstrs V w i (a.move i)).foldl (xexec ga gb) X1).S.regs r =
        X1.S.regs r) ∧ ((moveInstrs V w i (a.move i)).foldl (xexec ga gb) X1).mem = X1.mem := by
    have hXi : X1.S.regs (rH i) = some (BitVec.ofNat w (stride V * hd i + i.val)) := by rw [X1r, hX.regH]
    cases a.move i with
    | right =>
      refine ⟨?_, fun r h1 h2 => ?_, ?_⟩
      · simp [moveInstrs, xexec, hXi, cst, ofNat_add, HeadMove.apply]; ring_nf
      · simp [moveInstrs, xexec, Function.update_of_ne h2]
      · simp [moveInstrs, xexec]
    | stay =>
      refine ⟨?_, fun r h1 h2 => ?_, ?_⟩
      · simp [moveInstrs, xexec, hXi, HeadMove.apply]
      · simp [moveInstrs, xexec]
      · simp [moveInstrs, xexec]
    | left =>
      refine ⟨?_, fun r h1 h2 => ?_, ?_⟩
      · simp only [moveInstrs, List.foldl_cons, List.foldl_nil, xexec, setNext_regs, Function.update_self,
          val_reg, val_const, cst, Option.getD_some, mnAlu_cmp, mnAlu_sub, mnAlu_and,
          Function.update_of_ne (hHT i), hXi, HeadMove.apply]
        rw [left_value hw hiK hK hh]
      · simp [moveInstrs, xexec, Function.update_of_ne h1, Function.update_of_ne h2]
      · simp [moveInstrs, xexec]
  obtain ⟨k1, k2, k3⟩ := key
  refine ⟨⟨fun j => ?_, by rw [k3, X1m]⟩, fun r h1 h2 => by rw [k2 r h1 (h2 i), X1r]⟩
  by_cases hj : j = i
  · subst hj; rw [k1, Function.update_self]
  · rw [k2 _ (hHT j) (hHH j hj), X1r, hX.regH, Function.update_of_ne hj]

theorem fold_nops (k : ℕ) (X : XState MM) :
    ((List.replicate k (Instr.nop : MI V w)).foldl (xexec ga gb) X).S.regs = X.S.regs ∧
      ((List.replicate k (Instr.nop : MI V w)).foldl (xexec ga gb) X).mem = X.mem := by
  induction k generalizing X with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.foldl_cons, (ih _).1, (ih _).2]; simp [xexec]

/-- **All tapes of an action**, in order. -/
theorem fold_segs (a : Action V.tapeCount V.stateCount) (hw : 2 ≤ w) :
    ∀ (l : List (Fin V.tapeCount)), l.Nodup → ∀ (hd : Fin V.tapeCount → ℕ) (tp : Fin V.tapeCount → ℕ → Bool)
      (X : XState MM), RelH V hfit hd tp X → (∀ j ∈ l, stride V * (hd j + 1) + j.val < 2 ^ w) →
      RelH V hfit (fun j => if j ∈ l then (a.move j).apply (hd j) else hd j)
          (fun j => if j ∈ l then wrTape (a.write j) (tp j) (hd j) else tp j)
          (l.foldl (fun X j => (tapeSeg V w a j).foldl (xexec ga gb) X) X) ∧
        (∀ r, r ≠ rTmp → (∀ j, r ≠ rH j) →
          (l.foldl (fun X j => (tapeSeg V w a j).foldl (xexec ga gb) X) X).S.regs r = X.S.regs r)
  | [], _, hd, tp, X, hX, _ => by simpa using hX
  | b :: l, hnd, hd, tp, X, hX, hfi => by
    have hb : b ∉ l := (List.nodup_cons.mp hnd).1
    obtain ⟨s1, s2⟩ := seg_run V hfit ga gb a b hd tp X hX (hfi b (by simp)) hw
    obtain ⟨i1, i2⟩ := fold_segs a hw l (List.nodup_cons.mp hnd).2 _ _ _ s1 (fun j hj => by
      have hjb : j ≠ b := fun h => hb (by rw [← h]; exact hj)
      rw [Function.update_of_ne hjb]; exact hfi j (by simp [hj]))
    rw [List.foldl_cons]
    refine ⟨?_, fun r h1 h2 => by rw [i2 r h1 h2, s2 r h1 h2]⟩
    have e1 : (fun j => if j ∈ l then (a.move j).apply (Function.update hd b ((a.move b).apply (hd b)) j)
        else Function.update hd b ((a.move b).apply (hd b)) j) =
        (fun j => if j ∈ b :: l then (a.move j).apply (hd j) else hd j) := by
      funext j
      by_cases hj : j = b
      · subst hj; simp [hb]
      · by_cases hjl : j ∈ l <;> simp [hj, hjl]
    have e2 : (fun j => if j ∈ l then wrTape (a.write j) (Function.update tp b (wrTape (a.write b) (tp b) (hd b)) j)
        (Function.update hd b ((a.move b).apply (hd b)) j)
        else Function.update tp b (wrTape (a.write b) (tp b) (hd b)) j) =
        (fun j => if j ∈ b :: l then wrTape (a.write j) (tp j) (hd j) else tp j) := by
      funext j
      by_cases hj : j = b
      · subst hj; simp [hb]
      · by_cases hjl : j ∈ l <;> simp [hj, hjl]
    rw [← e1, ← e2]
    exact i1

/-- **An action leaf**: from leaf `m`'s start, with the head registers and memory representing `C`, the leaf
applies `a` to every tape, sets `sr ← a.nextControl`, adds `simLen` to the counter and jumps to the interpreter. -/
theorem act_leaf_run (C : Configuration V.tapeCount V.stateCount) (c m : ℕ) (a : Action V.tapeCount V.stateCount)
    (Z : XState MM) (hcode : CodeAt MM (leafAddr V + m * leafLen V) (actLeaf V w m a))
    (hpc : Z.S.pc = BitVec.ofNat w (leafAddr V + m * leafLen V)) (hcnt : Z.S.regs rCnt = some (BitVec.ofNat w c))
    (hrel : RelH V hfit C.heads (tapeFn V C) Z) (hfitH : HeadsFit V (w := w) C) (hw : 2 ≤ w)
    (hcl : codeLen V < 2 ^ w) (hm : m < leafCount V) :
    ∃ Z', Runs ga gb Z (actStraight V w m a).length.succ Z' ∧
      SimAt V hfit (applyAction C a) (c + simLen V) Z' := by
  rw [actLeaf_eq] at hcode
  have hlenS := actStraight_length V w m a
  have hpad : simPad V < 8 := by unfold simPad; omega
  have hend : leafAddr V + m * leafLen V + (actStraight V w m a).length < 2 ^ w := by
    have h1 : m * leafLen V + leafLen V ≤ leafCount V * leafLen V := by
      have := Nat.mul_le_mul_right (leafLen V) (show m + 1 ≤ leafCount V from hm)
      rwa [Nat.succ_mul] at this
    have hLL : leafLen V = 2 * leafCount V + 7 * V.tapeCount + 12 := rfl
    unfold codeLen idleAddr deadAddr at hcl
    rw [hlenS]; omega
  obtain ⟨h1, h2, h3⟩ := xrun_straight (M := MM) ga gb (actStraight V w m a) _ Z hcode.append_left hend hpc
    (actStraight_straight V w m a)
  set Y := (actStraight V w m a).foldl (xexec ga gb) Z with hY
  have cj : (mnRam V w n t T hfit).code[leafAddr V + m * leafLen V + (actStraight V w m a).length]? =
      some (.jmp (interpAddr V)) := by simpa using hcode.append_right 0 (by simp)
  -- decompose the fold
  obtain ⟨n1, n2⟩ := fold_nops V hfit ga gb (2 * (leafCount V - 1 - m)) Z
  set YA := (List.replicate (2 * (leafCount V - 1 - m)) (Instr.nop : MI V w)).foldl (xexec ga gb) Z with hYA
  have relA : RelH V hfit C.heads (tapeFn V C) YA := ⟨fun i => by rw [n1, hrel.regH], by rw [n2, hrel.mem]⟩
  obtain ⟨g1, g2⟩ := fold_segs V hfit ga gb a hw (List.finRange V.tapeCount) (List.nodup_finRange _) _ _ YA relA
    (fun j _ => hfitH j)
  set YB := (List.finRange V.tapeCount).foldl (fun X j => (tapeSeg V w a j).foldl (xexec ga gb) X) YA with hYB
  set YS := xexec ga gb YB (.arith 0 rSr (cst a.nextControl.val) (cst 0)) with hYS
  obtain ⟨p1, p2⟩ := fold_nops V hfit ga gb (simPad V) YS
  set YP := (List.replicate (simPad V) (Instr.nop : MI V w)).foldl (xexec ga gb) YS with hYP
  have hsplit : Y = xexec ga gb YP (.arith 0 rCnt (.reg rCnt) (cst (simLen V))) := by
    rw [hY, actStraight, List.foldl_append, List.foldl_append, List.foldl_append, List.foldl_append,
      List.foldl_flatten, List.ofFn_eq_map, List.foldl_map]
    rfl
  have hHS : ∀ j : Fin V.tapeCount, rSr ≠ rH j := by intro j h; simp [reg_eq_iff] at h; omega
  have hHC : ∀ j : Fin V.tapeCount, rCnt ≠ rH j := by intro j h; simp [reg_eq_iff] at h; omega
  have hHS' : ∀ j : Fin V.tapeCount, rH j ≠ rSr := fun j h => hHS j h.symm
  have hHC' : ∀ j : Fin V.tapeCount, rH j ≠ rCnt := fun j h => hHC j h.symm
  have rZ := Runs.single (M := MM) ga gb (X := Y) cj h3 hend (by intro b h; cases h)
  refine ⟨_, (show Runs ga gb Z _ Y from ⟨h2, h1⟩).trans _ _ rZ, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [xexec]
  · rw [show (xexec ga gb Y (.jmp (interpAddr V))).S.regs = Y.S.regs from rfl, hsplit]
    simp only [xexec, setNext_regs, Function.update_self, val_reg, val_const, cst]
    rw [p1]
    simp only [hYS, xexec, setNext_regs]
    rw [Function.update_of_ne (by simp [reg_eq_iff]), g2 _ (by simp [reg_eq_iff]) hHC, n1, hcnt]
    simp [ofNat_add]
  · rw [show (xexec ga gb Y (.jmp (interpAddr V))).S.regs = Y.S.regs from rfl, hsplit]
    simp only [xexec, setNext_regs]
    rw [Function.update_of_ne (by simp [reg_eq_iff]), p1]
    simp [hYS, xexec, cst, applyAction]
  · intro j
    rw [show (xexec ga gb Y (.jmp (interpAddr V))).S.regs = Y.S.regs from rfl, hsplit]
    simp only [xexec, setNext_regs]
    rw [Function.update_of_ne (hHC' j), p1]
    simp only [hYS, xexec, setNext_regs]
    rw [Function.update_of_ne (hHS' j), g1.regH j]
    simp [applyAction]
  · rw [show (xexec ga gb Y (.jmp (interpAddr V))).mem = Y.mem from rfl, hsplit]
    simp only [xexec]
    rw [p2]
    simp only [hYS, xexec]
    rw [g1.mem]
    apply congrArg (memRep V w)
    funext j k
    simp only [List.mem_finRange, if_true, tapeFn, applyAction]
    cases hwj : a.write j with
    | none => simp only [wrTape, tapeFn]
    | some b =>
      simp only [wrTape, Function.update_apply, tapeFn]
      rw [writeTapeBit_getD]

/-- Interpreter header and chain: `4k_V + 1 + 2(m + 1)` steps to leaf `m = leafIndex(state, scanned)`. -/
theorem to_leaf (C : Configuration V.tapeCount V.stateCount) (c : ℕ) (Y : XState MM)
    (hY : SimAt V hfit C c Y) (hfitH : HeadsFit V (w := w) C) (hcl : codeLen V < 2 ^ w) :
    ∃ Z, Runs ga gb Y (4 * V.tapeCount + 1 + 2 * (leafIndex V C.control C.scanned + 1)) Z ∧
      Z.S.pc = BitVec.ofNat w (leafAddr V + leafIndex V C.control C.scanned * leafLen V) ∧
      Z.S.regs rCnt = some (BitVec.ofNat w c) ∧ RelH V hfit C.heads (tapeFn V C) Z := by
  have hN : leafCount V < 2 ^ w := by
    have : leafCount V ≤ codeLen V := by
      unfold codeLen idleAddr deadAddr leafAddr chainAddr; omega
    omega
  obtain ⟨Z1, r1, z1pc, z1idx, z1cnt, z1h, z1m⟩ := header_run V hfit ga gb C c Y hY hfitH hcl
  have hm := leafIndex_lt V C.control C.scanned
  obtain ⟨Z2, r2, z2pc, z2r, z2m⟩ := chain_run V hfit ga gb hcl hN _ hm (leafIndex V C.control C.scanned) 0 Z1
    (Nat.sub_zero _).symm (Nat.zero_le _) (by rw [z1pc]; simp) z1idx
  refine ⟨Z2, r1.trans _ _ r2, z2pc, ?_, ⟨fun i => ?_, by rw [z2m, z1m, hY.mem]⟩⟩
  · rw [z2r _ (by simp [reg_eq_iff]), z1cnt]
  · rw [z2r _ (by simp [reg_eq_iff]; omega), z1h]

theorem code_leaf (q : Fin V.stateCount) (σ : Fin V.tapeCount → Bool) :
    CodeAt MM (leafAddr V + leafIndex V q σ * leafLen V) (leafCode V w ⟨leafIndex V q σ, leafIndex_lt V q σ⟩) :=
  CodeAt.flatten_ofFn (M := MM) _ (leafCode_length V w) (code_leaves V hfit) ⟨_, leafIndex_lt V q σ⟩

/-- **A simulated step of `V`** (`simLen` steps): `C` not halted, `δ(C) = a`. -/
theorem sim_step_act (C : Configuration V.tapeCount V.stateCount) (c : ℕ) (Y : XState MM)
    (hY : SimAt V hfit C c Y) (hfitH : HeadsFit V (w := w) C) (hcl : codeLen V < 2 ^ w) (hw : 2 ≤ w)
    (hnh : V.machine.halted C.control = false) (a : Action V.tapeCount V.stateCount)
    (hrule : V.machine.rule C.control C.scanned = some a) :
    ∃ Y', Runs ga gb Y (simLen V) Y' ∧ SimAt V hfit (applyAction C a) (c + simLen V) Y' := by
  obtain ⟨Z, r1, zpc, zcnt, zrel⟩ := to_leaf V hfit ga gb C c Y hY hfitH hcl
  have hc := code_leaf V hfit (n := n) (t := t) (T := T) C.control C.scanned
  have hdec := leaf_decode V C.control C.scanned
  have hm := leafIndex_lt V C.control C.scanned
  have hlc : leafCode V w ⟨leafIndex V C.control C.scanned, hm⟩ =
      padLeaf V w (actLeaf V w (leafIndex V C.control C.scanned) a) := by
    simp only [leafCode, hdec.1, hdec.2, hnh, hrule, Bool.false_eq_true, if_false]
  rw [hlc] at hc
  obtain ⟨Z', r2, hZ'⟩ := act_leaf_run V hfit ga gb C c _ a Z hc.append_left zpc zcnt zrel hfitH hw hcl hm
  refine ⟨Z', ?_, hZ'⟩
  have e : simLen V = 4 * V.tapeCount + 1 + 2 * (leafIndex V C.control C.scanned + 1) +
      (actStraight V w (leafIndex V C.control C.scanned) a).length.succ := by
    rw [actStraight_length]; unfold simLen; omega
  rw [e]; exact r1.trans _ _ r2

/-- The accepting leaf at `m`: verdict `1`, counter `+= accLen`, jump to the idle block. -/
theorem acc_leaf_run (c m : ℕ) (Z : XState MM)
    (hc : CodeAt MM (leafAddr V + m * leafLen V) (accLeaf V w m))
    (zpc : Z.S.pc = BitVec.ofNat w (leafAddr V + m * leafLen V)) (zcnt : Z.S.regs rCnt = some (BitVec.ofNat w c))
    (hcl : codeLen V < 2 ^ w) (hm : m < leafCount V) :
    ∃ Z', Runs ga gb Z (accStraight V w m).length.succ Z' ∧ Z'.S.pc = BitVec.ofNat w (idleAddr V) ∧
      Z'.S.regs rCnt = some (BitVec.ofNat w (c + accLen V)) ∧ Z'.S.regs rVd = some (BitVec.ofNat w 1) := by
  rw [accLeaf_eq] at hc
  have hlenS := accStraight_length V w m
  have hpad : accPad V < 8 := by unfold accPad; omega
  have hend : leafAddr V + m * leafLen V + (accStraight V w m).length < 2 ^ w := by
    have h1 : m * leafLen V + leafLen V ≤ leafCount V * leafLen V := by
      have := Nat.mul_le_mul_right (leafLen V) (show m + 1 ≤ leafCount V from hm)
      rwa [Nat.succ_mul] at this
    have hLL : leafLen V = 2 * leafCount V + 7 * V.tapeCount + 12 := rfl
    unfold codeLen idleAddr deadAddr at hcl
    rw [hlenS]; omega
  obtain ⟨h1, h2, h3⟩ := xrun_straight (M := MM) ga gb (accStraight V w m) _ Z hc.append_left hend zpc
    (by
      intro I hI
      simp only [accStraight, List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
        or_false] at hI
      rcases hI with ((⟨-, h⟩ | h) | ⟨-, h⟩) | h <;> rw [h] <;> exact trivial)
  set Y1 := (accStraight V w m).foldl (xexec ga gb) Z with hY1
  have cj : (mnRam V w n t T hfit).code[leafAddr V + m * leafLen V + (accStraight V w m).length]? =
      some (.jmp (idleAddr V)) := by simpa using hc.append_right 0 (by simp)
  have rZ := Runs.single (M := MM) ga gb (X := Y1) cj h3 hend (by intro b h; cases h)
  obtain ⟨n1, -⟩ := fold_nops V hfit ga gb (2 * (leafCount V - 1 - m)) Z
  set YA := (List.replicate (2 * (leafCount V - 1 - m)) (Instr.nop : MI V w)).foldl (xexec ga gb) Z with hYA
  set YV := xexec ga gb YA (.arith 0 rVd (cst 1) (cst 0)) with hYV
  obtain ⟨p1, -⟩ := fold_nops V hfit ga gb (accPad V) YV
  set YP := (List.replicate (accPad V) (Instr.nop : MI V w)).foldl (xexec ga gb) YV with hYP
  have hsplit : Y1 = xexec ga gb YP (.arith 0 rCnt (.reg rCnt) (cst (accLen V))) := by
    rw [hY1, accStraight, List.foldl_append, List.foldl_append, List.foldl_append]; rfl
  refine ⟨_, (show Runs ga gb Z _ Y1 from ⟨h2, h1⟩).trans _ _ rZ, ?_, ?_, ?_⟩
  · simp [xexec]
  · rw [show (xexec ga gb Y1 (.jmp (idleAddr V))).S.regs = Y1.S.regs from rfl, hsplit]
    simp only [xexec, setNext_regs, Function.update_self, val_reg, val_const, cst]
    rw [p1, hYV]
    simp only [xexec, setNext_regs]
    rw [Function.update_of_ne (by simp [reg_eq_iff]), n1, zcnt]
    simp [ofNat_add]
  · rw [show (xexec ga gb Y1 (.jmp (idleAddr V))).S.regs = Y1.S.regs from rfl, hsplit]
    simp only [xexec, setNext_regs]
    rw [Function.update_of_ne (by simp [reg_eq_iff]), p1, hYV]
    simp [xexec, cst]

/-- **A halted accepting state** (`accLen` steps): verdict `1`, counter, jump to the idle block. -/
theorem sim_step_acc (C : Configuration V.tapeCount V.stateCount) (c : ℕ) (Y : XState MM)
    (hY : SimAt V hfit C c Y) (hfitH : HeadsFit V (w := w) C) (hcl : codeLen V < 2 ^ w)
    (hh : V.machine.halted C.control = true) (hacc : V.accepting C.control = true) :
    ∃ Y', Runs ga gb Y (accLen V) Y' ∧ Y'.S.pc = BitVec.ofNat w (idleAddr V) ∧
      Y'.S.regs rCnt = some (BitVec.ofNat w (c + accLen V)) ∧ Y'.S.regs rVd = some (BitVec.ofNat w 1) := by
  obtain ⟨Z, r1, zpc, zcnt, -⟩ := to_leaf V hfit ga gb C c Y hY hfitH hcl
  have hc := code_leaf V hfit (n := n) (t := t) (T := T) C.control C.scanned
  have hdec := leaf_decode V C.control C.scanned
  have hm := leafIndex_lt V C.control C.scanned
  have hlc : leafCode V w ⟨leafIndex V C.control C.scanned, hm⟩ =
      padLeaf V w (accLeaf V w (leafIndex V C.control C.scanned)) := by
    simp only [leafCode, hdec.1, hh, hacc, if_true]
  rw [hlc] at hc
  obtain ⟨Z', r2, h1, h2, h3⟩ := acc_leaf_run V hfit ga gb c _ Z hc.append_left zpc zcnt hcl hm
  refine ⟨Z', ?_, h1, h2, h3⟩
  have e : accLen V = 4 * V.tapeCount + 1 + 2 * (leafIndex V C.control C.scanned + 1) +
      (accStraight V w (leafIndex V C.control C.scanned)).length.succ := by
    rw [accStraight_length]; unfold accLen; omega
  rw [e]; exact r1.trans _ _ r2

/-- **A halted rejecting state or a stuck configuration**: `M_n` reaches `jmp dead`. -/
theorem sim_step_dead (C : Configuration V.tapeCount V.stateCount) (c : ℕ) (Y : XState MM)
    (hY : SimAt V hfit C c Y) (hfitH : HeadsFit V (w := w) C) (hcl : codeLen V < 2 ^ w)
    (hd : (V.machine.halted C.control = true ∧ V.accepting C.control = false) ∨
      (V.machine.halted C.control = false ∧ V.machine.rule C.control C.scanned = none)) :
    ∃ k Y', Runs ga gb Y k Y' ∧ Y'.S.pc = BitVec.ofNat w (deadAddr V) := by
  obtain ⟨Z, r1, zpc, -, -⟩ := to_leaf V hfit ga gb C c Y hY hfitH hcl
  have hc := code_leaf V hfit (n := n) (t := t) (T := T) C.control C.scanned
  have hdec := leaf_decode V C.control C.scanned
  have hm := leafIndex_lt V C.control C.scanned
  have hlc : leafCode V w ⟨leafIndex V C.control C.scanned, hm⟩ = padLeaf V w (deadLeaf V w) := by
    rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [leafCode, hdec.1, h1, h2, if_true, Bool.false_eq_true, if_false]
    · simp only [leafCode, hdec.1, hdec.2, h1, h2, Bool.false_eq_true, if_false]
  rw [hlc] at hc
  set m := leafIndex V C.control C.scanned with hmdef
  have hend : leafAddr V + m * leafLen V < 2 ^ w := by
    have h1 : m * leafLen V + leafLen V ≤ leafCount V * leafLen V := by
      have := Nat.mul_le_mul_right (leafLen V) (show m + 1 ≤ leafCount V from hm)
      rwa [Nat.succ_mul] at this
    have hLL : leafLen V = 2 * leafCount V + 7 * V.tapeCount + 12 := rfl
    unfold codeLen idleAddr deadAddr at hcl
    omega
  have cj : (mnRam V w n t T hfit).code[leafAddr V + m * leafLen V]? = some (.jmp (deadAddr V)) := by
    simpa [padLeaf, deadLeaf] using hc 0 (by simp [padLeaf, deadLeaf])
  have rZ := Runs.single (M := MM) ga gb (X := Z) cj zpc hend (by intro b h; cases h)
  exact ⟨_, _, r1.trans _ _ rZ, by simp [xexec]⟩

end Sim

end NearCubicGates.Adapters.ShortPCP
