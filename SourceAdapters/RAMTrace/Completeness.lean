import SourceAdapters.RAMTrace.Soundness
import Mathlib.Data.Fin.Tuple.Sort

/-!
# `thm:trace` (⇐): a bounded accepting run gives a satisfying event trace

`app:event-trace`, proof of `thm:trace` (⇐). From the data of the bounded-run definition `def:ram` — configurations `S^i`, memories `mem_i` with
`mem_0 = 0` and `Ram.Step` links, the witness `y` — fill row `ρ_i` canonically from `(S^i, S^{i+1}, access_i)`
(`lem:trace-step` existence) with time stamp `i` and honest counters (`lem:trace-counters`); add the input records `ι_c` and zero
dummies; sort the active records by key (`Tuple.sort`), fill `PREV` by (B4) and the sorted auxiliaries canonically;
`lem:trace-sorted` (converse) gives (S1)–(S5).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMTrace

open NearCubicGates.Adapters.ACSP Expr BitVec

variable (M : Ram) (kind : Fin M.ops → AluOp) (τ : ℕ) (xbar : List Bool) (S : ℕ → M.Config)
  (mem : ℕ → M.Memory)

/-! ## The rows of a run -/

/-- The instruction at step `i`. -/
def insS (i : ℕ) : Instr M.w M.k M.ops := (M.instrAt (S i).pc).getD .nop

/-- The memory channel of step `i`: the loaded word, the stored word, `0` otherwise. -/
def mvS (i : ℕ) : BitVec M.w :=
  match insS M S i with
  | .load a _ => mem i ((S i).val (.reg a))
  | .store _ x => (S i).val x
  | _ => 0

/-- The tape channel of step `i`: the value a read put into its register, `0` otherwise. -/
def rdS (i : ℕ) : Option (BitVec M.w) :=
  match insS M S i with
  | .readA r => (S (i + 1)).regs r
  | .readB r => (S (i + 1)).regs r
  | _ => some 0

/-- Step `i` reads a word from tape A. -/
def aAS (i : ℕ) : Bool := isRdA (insS M S i) && !(rdS M S i).isNone

/-- Step `i` reads a word from tape B. -/
def aBS (i : ℕ) : Bool := isRdB (insS M S i) && !(rdS M S i).isNone

/-- Words read from tape A before step `m`. -/
def cntAS (m : ℕ) : ℕ := ((List.range m).filter (aAS M S)).length

/-- Words read from tape B before step `m`. -/
def cntBS (m : ℕ) : ℕ := ((List.range m).filter (aBS M S)).length

theorem cntAS_succ (m : ℕ) : cntAS M S (m + 1) = cntAS M S m + (aAS M S m).toNat := by
  unfold cntAS; rw [List.range_succ, List.filter_append, List.length_append]
  cases h : aAS M S m <;> simp [h]

theorem cntBS_succ (m : ℕ) : cntBS M S (m + 1) = cntBS M S m + (aBS M S m).toNat := by
  unfold cntBS; rw [List.range_succ, List.filter_append, List.length_append]
  cases h : aBS M S m <;> simp [h]

theorem cntAS_le (m : ℕ) : cntAS M S m ≤ m := by
  unfold cntAS; exact (List.length_filter_le _ _).trans (by simp)

theorem cntAS_mono {m n : ℕ} (h : m ≤ n) : cntAS M S m ≤ cntAS M S n := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => rw [cntAS_succ]; omega

theorem cntBS_mono {m n : ℕ} (h : m ≤ n) : cntBS M S m ≤ cntBS M S n := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => rw [cntBS_succ]; omega

/-- The canonical row `ρ_i` of the run (`lem:trace-step` existence): time stamp `i`, honest counters. -/
def rowS (i : ℕ) : TVar → Bool :=
  canon kind τ (S i) (insS M S i) (mvS M S mem i) (rdS M S i) (BitVec.ofNat τ i) (BitVec.ofNat τ (cntAS M S i))
    (BitVec.ofNat ((dims M τ).β + 1) (cntBS M S i))

/-- The input record `ι_c` (B5). -/
def inputRec (c : ℕ) : RecField → ℕ → Bool
  | .act, _ => true
  | .rgn, _ => true
  | .ad, k => c.testBit k
  | .va, k => xbar.getD (c * M.w + k) false
  | _, _ => false

/-- The source list: time records, input records, zero dummies. -/
def srcS (x : ℕ) (f : RecField) (k : ℕ) : Bool :=
  if x < 2 ^ τ then rowS M kind τ S mem x (.inr (f, k))
  else if x < 2 ^ τ + xbar.length / M.w then inputRec M xbar (x - 2 ^ τ) f k else false

/-! ## Facts of the run -/

section Run

variable (hacc : M.AcceptingSeq (2 ^ τ) S) (hmem0 : mem 0 = 0)
  (hstep : ∀ i, i + 1 < 2 ^ τ → M.Step (S i) (mem i) (S (i + 1)) (mem (i + 1)))

omit hacc hmem0 in
include hstep in
/-- A step of the run is the row's successor (`lem:trace-step` (iii) read backwards). -/
theorem run_step (i : ℕ) (hi : i + 1 < 2 ^ τ) :
    M.instrAt (S i).pc = some (insS M S i) ∧ isOut (insS M S i) = false ∧
      S (i + 1) = rowSucc (S i) (mvS M S mem i) (rdS M S i) (insS M S i) ∧
      mem (i + 1) = memNext (S i) (insS M S i) (mem i) := by
  have h := hstep i hi
  unfold Ram.Step at h
  rcases hI : M.instrAt (S i).pc with _ | I
  · rw [hI] at h; exact h.elim
  · rw [hI] at h
    have hins : insS M S i = I := by simp [insS, hI]
    rw [hins]
    refine ⟨rfl, ?_, ?_⟩
    · cases I <;> simp_all [isOut]
    · cases I with
      | readA r =>
        obtain ⟨⟨v, hv⟩, hm⟩ := h
        refine ⟨?_, by rw [hm]; rfl⟩
        have : rdS M S i = v := by
          simp only [rdS, hins, hv, Ram.Config.setNext, Function.update_self]
        simp only [rowSucc, this, hv]
      | readB r =>
        obtain ⟨⟨v, hv⟩, hm⟩ := h
        refine ⟨?_, by rw [hm]; rfl⟩
        have : rdS M S i = v := by
          simp only [rdS, hins, hv, Ram.Config.setNext, Function.update_self]
        simp only [rowSucc, this, hv]
      | load a j =>
        obtain ⟨h1, h2⟩ := h
        refine ⟨?_, by rw [h2]; rfl⟩
        simp only [rowSucc, mvS, hins, h1]
      | store j x =>
        obtain ⟨h1, h2⟩ := h
        exact ⟨h1, by rw [h2]; rfl⟩
      | out b => exact h.elim
      | _ => obtain ⟨h1, h2⟩ := h; exact ⟨h1, by rw [h2]; rfl⟩

omit hmem0 hstep in
include hacc in
theorem run_last : M.instrAt (S (2 ^ τ - 1)).pc = some (insS M S (2 ^ τ - 1)) ∧
    insS M S (2 ^ τ - 1) = .out true := by
  have h := hacc.2
  unfold Ram.AcceptingConfig at h
  simp [insS, h]

omit hacc hmem0 hstep in
theorem mvS_store (i : ℕ) (h : isSt (insS M S i) = true) : mvS M S mem i = yWord (S i) (insS M S i) := by
  unfold mvS; cases hI : insS M S i <;> simp_all [isSt, yWord]

omit hacc hmem0 hstep in
theorem mvS_load (i : ℕ) (h : isLd (insS M S i) = true) :
    mvS M S mem i = mem i (xWord (S i) (insS M S i)) := by
  unfold mvS; cases hI : insS M S i <;> simp_all [isLd, xWord]

include hmem0 hstep in
omit hmem0 in
/-- The memory only changes at stores. -/
theorem run_mem_stable (A : BitVec M.w) (i' : ℕ) :
    ∀ i, i' ≤ i → i < 2 ^ τ → (∀ i'', i' ≤ i'' → i'' < i →
      ¬ (isSt (insS M S i'') = true ∧ xWord (S i'') (insS M S i'') = A)) → mem i A = mem i' A := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => intro _ _; rfl
  | succ m hm ih =>
    intro hmT h
    rw [(run_step M τ S mem hstep m hmT).2.2.2,
      memNext_ne _ _ _ _ (fun hs hx => h m hm (by omega) ⟨hs, hx⟩),
      ih (by omega) (fun i'' h1 h2 => h i'' h1 (by omega))]

end Run

/-! ## The read strings of the run -/

section Reads

variable (hstep : ∀ i, i + 1 < 2 ^ τ → M.Step (S i) (mem i) (S (i + 1)) (mem (i + 1)))
include hstep

theorem run_readAt (tA : Bool) (i : ℕ) (hi : i + 1 < 2 ^ τ) :
    M.readAt tA S i = if (if tA then isRdA (insS M S i) else isRdB (insS M S i)) then some (rdS M S i) else none := by
  have hI := (run_step M τ S mem hstep i hi).1
  unfold Ram.readAt
  rw [hI]
  cases h : insS M S i <;> cases tA <;> simp [isRdA, isRdB, rdS, h]

/-- The words read from one tape at steps `< m`, flattened. -/
def readPart (tA : Bool) (m : ℕ) : List Bool :=
  ((List.range m).filterMap fun i => (M.readAt tA S i).bind fun v => v.map Ram.wordBits).flatten

omit hstep in
theorem readPart_succ (tA : Bool) (m : ℕ) :
    readPart M S tA (m + 1) = readPart M S tA m ++ (((M.readAt tA S m).bind fun v => v.map Ram.wordBits).toList.flatten) := by
  unfold readPart
  rw [List.range_succ, List.filterMap_append, List.flatten_append]
  congr 1

omit hstep in
theorem readPart_prefix (tA : Bool) {m n : ℕ} (h : m ≤ n) : readPart M S tA m <+: readPart M S tA n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => rw [readPart_succ]; exact ih.trans (List.prefix_append _ _)

theorem readPart_A (m : ℕ) (hm : m ≤ 2 ^ τ - 1) :
    (readPart M S true m).length = cntAS M S m * M.w := by
  induction m with
  | zero => simp [readPart, cntAS]
  | succ m ih =>
    rw [readPart_succ, List.length_append, ih (by omega), cntAS_succ,
      run_readAt M τ S mem hstep true m (by have := Nat.one_le_two_pow (n := τ); omega)]
    simp only [if_true]
    cases ha : aAS M S m
    · have : (isRdA (insS M S m) && !(rdS M S m).isNone) = false := ha
      cases hr : isRdA (insS M S m) <;> cases hd : rdS M S m <;> simp_all
    · have : (isRdA (insS M S m) && !(rdS M S m).isNone) = true := ha
      have hr : isRdA (insS M S m) = true := by simp_all
      obtain ⟨v, hv⟩ : ∃ v, rdS M S m = some v := by
        cases hd : rdS M S m <;> simp_all
      simp [hr, hv, Ram.wordBits]; ring

theorem readPart_B (m : ℕ) (hm : m ≤ 2 ^ τ - 1) :
    (readPart M S false m).length = cntBS M S m * M.w := by
  induction m with
  | zero => simp [readPart, cntBS]
  | succ m ih =>
    rw [readPart_succ, List.length_append, ih (by omega), cntBS_succ,
      run_readAt M τ S mem hstep false m (by have := Nat.one_le_two_pow (n := τ); omega)]
    simp only [Bool.false_eq_true, if_false]
    cases ha : aBS M S m
    · have : (isRdB (insS M S m) && !(rdS M S m).isNone) = false := ha
      cases hr : isRdB (insS M S m) <;> cases hd : rdS M S m <;> simp_all
    · have : (isRdB (insS M S m) && !(rdS M S m).isNone) = true := ha
      have hr : isRdB (insS M S m) = true := by simp_all
      obtain ⟨v, hv⟩ : ∃ v, rdS M S m = some v := by
        cases hd : rdS M S m <;> simp_all
      simp [hr, hv, Ram.wordBits]; ring

omit hstep in
theorem wordBits_inj {w : ℕ} (u v : BitVec w) (h : Ram.wordBits u = Ram.wordBits v) : u = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have := congrArg (fun l => l.getD j false) h
  simpa [Ram.wordBits, List.getD_eq_getElem?_getD, hj] using this

/-- **`lem:trace-sorted` converse (tape A).** The `c`-th word read from tape A (`c = cA_i`) is word `c` of `x̄`, and
`c < N_A`. -/
theorem run_readA (hw1 : 1 ≤ M.w) (hconsA : M.readString true (2 ^ τ) S <+: xbar) (i : ℕ) (hi : i + 1 < 2 ^ τ)
    (ha : aAS M S i = true) :
    cntAS M S i < xbar.length / M.w ∧ rdS M S i = some (ShortPCP.wordOf M.w xbar (cntAS M S i)) := by
  have hr : isRdA (insS M S i) = true := by unfold aAS at ha; simp_all
  obtain ⟨v, hv⟩ : ∃ v, rdS M S i = some v := by
    unfold aAS at ha; cases hd : rdS M S i <;> simp_all
  have hpre : readPart M S true (i + 1) <+: xbar :=
    (readPart_prefix M S true (show i + 1 ≤ 2 ^ τ - 1 by omega)).trans hconsA
  have hsucc : readPart M S true (i + 1) = readPart M S true i ++ Ram.wordBits v := by
    rw [readPart_succ, run_readAt M τ S mem hstep true i hi]
    simp [hr, hv]
  have hlen := readPart_A M τ S mem hstep i (by omega)
  have hw : (Ram.wordBits v).length = M.w := by simp [Ram.wordBits]
  have hfit : (cntAS M S i + 1) * M.w ≤ xbar.length := by
    have := hpre.length_le
    rw [hsucc, List.length_append, hlen, hw] at this
    rw [Nat.add_mul, one_mul]; exact this
  have hw0 : 0 < M.w := hw1
  refine ⟨?_, ?_⟩
  · rw [Nat.lt_div_iff_mul_lt hw0]; rw [Nat.add_mul, one_mul] at hfit; omega
  · rw [hv]
    congr 1
    apply wordBits_inj
    rw [ShortPCP.wordBits_wordOf _ _ _ hfit]
    obtain ⟨rest, hrest⟩ := hpre
    rw [hsucc] at hrest
    rw [← hrest, List.append_assoc, List.drop_left' hlen, List.take_left' hw]

end Reads

/-! ## The records of the source list -/

section Records

variable (hτw : τ < M.w) (hlen : xbar.length ≤ 2 ^ τ)
include hτw hlen

omit hlen hτw in
theorem srcS_time (i : ℕ) (hi : i < 2 ^ τ) (f : RecField) (k : ℕ) :
    srcS M kind τ xbar S mem i f k = rowS M kind τ S mem i (.inr (f, k)) := by
  simp [srcS, hi]

omit hτw hlen in
theorem srcS_input (c : ℕ) (hc : c < xbar.length / M.w) (f : RecField) (k : ℕ) :
    srcS M kind τ xbar S mem (2 ^ τ + c) f k = inputRec M xbar c f k := by
  simp [srcS, hc]

omit hτw hlen in
theorem srcS_dummy (x : ℕ) (hx : 2 ^ τ + xbar.length / M.w ≤ x) (f : RecField) (k : ℕ) :
    srcS M kind τ xbar S mem x f k = false := by
  unfold srcS
  generalize xbar.length / M.w = NA at hx ⊢
  rw [if_neg (by omega), if_neg (by omega)]

omit hlen hτw in
theorem srcS_ph (i : ℕ) (hi : i < 2 ^ τ) : srcS M kind τ xbar S mem i .ph 0 = true := by
  rw [srcS_time M kind τ xbar S mem i hi]; rfl

omit hlen hτw in
theorem srcS_low (i : ℕ) (hi : i < 2 ^ τ) : lowN (dims M τ) (srcS M kind τ xbar S mem i) = i + 2 ^ τ := by
  unfold lowN
  rw [srcS_ph M kind τ xbar S mem i hi]
  have : natOf (srcS M kind τ xbar S mem i .ts) (dims M τ).τ = i := by
    rw [natOf_congr _ (BitVec.ofNat τ i).getLsbD _ (fun k _ => by
      rw [srcS_time M kind τ xbar S mem i hi]; rfl)]
    rw [show (dims M τ).τ = τ from rfl, natOf_getLsbD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
  rw [this]; simp [dims]

omit hlen hτw in
theorem srcS_mem (i : ℕ) (hi : i < 2 ^ τ) (hls : (isLd (insS M S i) || isSt (insS M S i)) = true) :
    srcS M kind τ xbar S mem i .act 0 = true ∧ srcS M kind τ xbar S mem i .rgn 0 = false ∧
      srcS M kind τ xbar S mem i .st 0 = isSt (insS M S i) ∧
      cellN (dims M τ) (srcS M kind τ xbar S mem i) = (xWord (S i) (insS M S i)).toNat ∧
      ∀ k < M.w, srcS M kind τ xbar S mem i .va k = (mvS M S mem i).getLsbD k := by
  have hx := ld_st_rdA (insS M S i)
  have hA : isRdA (insS M S i) = false := by
    cases h1 : isLd (insS M S i) <;> cases h2 : isSt (insS M S i) <;> simp_all
  have hxo : Bool.xor (isLd (insS M S i)) (isSt (insS M S i)) = true := by
    cases h1 : isLd (insS M S i) <;> cases h2 : isSt (insS M S i) <;> simp_all
  have hsrc := srcS_time M kind τ xbar S mem i hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hsrc]; simp [rowS, canon, hA, hxo]
  · rw [hsrc]; simp [rowS, canon, hA]
  · rw [hsrc]; rfl
  · unfold cellN
    rw [hsrc .rgn 0]
    simp only [rowS, canon, hA, Bool.false_and, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
    rw [natOf_congr _ (xWord (S i) (insS M S i)).getLsbD _ (fun k _ => by
      rw [hsrc .ad k]; simp [rowS, canon, hA, hxo])]
    exact natOf_getLsbD _
  · intro k hk
    rw [hsrc]; simp [rowS, canon, hA, hxo]

omit hlen in
theorem srcS_rdA (i : ℕ) (hi : i < 2 ^ τ) (ha : aAS M S i = true) :
    srcS M kind τ xbar S mem i .act 0 = true ∧ srcS M kind τ xbar S mem i .rgn 0 = true ∧
      cellN (dims M τ) (srcS M kind τ xbar S mem i) = cntAS M S i + 2 ^ M.w ∧
      ∀ k < M.w, srcS M kind τ xbar S mem i .va k = ((rdS M S i).getD 0).getLsbD k := by
  have hx := ld_st_rdA (insS M S i)
  have hA : isRdA (insS M S i) = true := by unfold aAS at ha; simp_all
  have hL : isLd (insS M S i) = false := by cases h : isLd (insS M S i) <;> simp_all
  have hSt : isSt (insS M S i) = false := by cases h : isSt (insS M S i) <;> simp_all
  have ha' : (isRdA (insS M S i) && !(rdS M S i).isNone) = true := ha
  have hsrc := srcS_time M kind τ xbar S mem i hi
  have hcnt : cntAS M S i < 2 ^ τ := lt_of_le_of_lt (cntAS_le M S i) hi
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsrc]; simp only [rowS, canon, hL, hSt, ha']; rfl
  · rw [hsrc]; simp only [rowS, canon, ha']
  · unfold cellN
    rw [hsrc .rgn 0]
    simp only [rowS, canon, ha', Bool.toNat_true, Nat.mul_one]
    congr 1
    rw [natOf_low (show τ ≤ (dims M τ).w from hτw.le) _ (BitVec.ofNat τ (cntAS M S i)) (fun k _ => by
      rw [hsrc .ad k]
      simp only [rowS, canon, hL, hSt, ha']
      split_ifs with h <;> simp [h]), BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcnt]
  · intro k hk
    rw [hsrc]; simp only [rowS, canon, hL, hSt, ha']; simp

omit hlen hτw in
theorem srcS_act_time (i : ℕ) (hi : i < 2 ^ τ) (h : srcS M kind τ xbar S mem i .act 0 = true) :
    (isLd (insS M S i) || isSt (insS M S i)) = true ∨ aAS M S i = true := by
  have hx := ld_st_rdA (insS M S i)
  rw [srcS_time M kind τ xbar S mem i hi] at h
  simp only [rowS, canon] at h
  unfold aAS
  cases h1 : isLd (insS M S i) <;> cases h2 : isSt (insS M S i) <;>
    cases h3 : (isRdA (insS M S i) && !(rdS M S i).isNone) <;> simp_all

theorem srcS_input_facts (c : ℕ) (hc : c < xbar.length / M.w) :
    srcS M kind τ xbar S mem (2 ^ τ + c) .act 0 = true ∧ srcS M kind τ xbar S mem (2 ^ τ + c) .rgn 0 = true ∧
      srcS M kind τ xbar S mem (2 ^ τ + c) .ph 0 = false ∧
      lowN (dims M τ) (srcS M kind τ xbar S mem (2 ^ τ + c)) = 0 ∧
      cellN (dims M τ) (srcS M kind τ xbar S mem (2 ^ τ + c)) = c + 2 ^ M.w ∧
      ∀ k < M.w, srcS M kind τ xbar S mem (2 ^ τ + c) .va k = xbar.getD (c * M.w + k) false := by
  have hcw : c < 2 ^ M.w := by
    have h1 : xbar.length / M.w ≤ xbar.length := Nat.div_le_self _ _
    have h2 : 2 ^ τ < 2 ^ M.w := Nat.pow_lt_pow_right (by norm_num) hτw
    omega
  have hs := srcS_input M kind τ xbar S mem c hc
  refine ⟨by rw [hs]; rfl, by rw [hs]; rfl, by rw [hs]; rfl, ?_, ?_, fun k _ => by rw [hs]; rfl⟩
  · unfold lowN
    rw [natOf_congr _ (fun _ => false) _ (fun k _ => by rw [hs]; rfl), natOf_false, hs]
    rfl
  · unfold cellN
    rw [natOf_congr _ c.testBit _ (fun k _ => by rw [hs]; rfl), hs]
    rw [show (dims M τ).w = M.w from rfl, natOf_testBit c _ hcw]
    simp [inputRec]

end Records

/-! ## Sorting the records by key -/

theorem key_lt_pow (d : Dims) (r : RecField → ℕ → Bool) : keyOf d r < 2 ^ d.κ := natOf_lt _ _

theorem key_eq_parts (d : Dims) (r r' : RecField → ℕ → Bool) (h : keyOf d r = keyOf d r') :
    lowN d r = lowN d r' ∧ cellN d r = cellN d r' := by
  have h1 := (key_lt_iff d r r').not.mp (by omega)
  have h2 := (key_lt_iff d r' r).not.mp (by omega)
  push Not at h1 h2
  have hc : cellN d r = cellN d r' := by
    rcases Nat.lt_trichotomy (cellN d r) (cellN d r') with h | h | h
    · have := h1.1; omega
    · exact h
    · have := h2.1; omega
  exact ⟨by have := h1.2 hc; have := h2.2 hc.symm; omega, hc⟩

section Sorting

variable (hτw : τ < M.w) (hlen : xbar.length ≤ 2 ^ τ)
include hτw hlen

omit hτw hlen in
/-- Active lanes are time lanes or input lanes. -/
theorem lane_class (x : ℕ) (ha : srcS M kind τ xbar S mem x .act 0 = true) :
    x < 2 ^ τ ∨ ∃ c < xbar.length / M.w, x = 2 ^ τ + c := by
  rcases Nat.lt_or_ge x (2 ^ τ) with h | h
  · exact Or.inl h
  · rcases Nat.lt_or_ge x (2 ^ τ + xbar.length / M.w) with h' | h'
    · exact Or.inr ⟨x - 2 ^ τ, by omega, by omega⟩
    · rw [srcS_dummy M kind τ xbar S mem x h'] at ha; exact absurd ha (by simp)

/-- Distinct active lanes have distinct keys. -/
theorem key_inj (x y : ℕ) (hx : x < 2 ^ (τ + 1)) (hy : y < 2 ^ (τ + 1))
    (hax : srcS M kind τ xbar S mem x .act 0 = true) (hay : srcS M kind τ xbar S mem y .act 0 = true)
    (h : keyOf (dims M τ) (srcS M kind τ xbar S mem x) = keyOf (dims M τ) (srcS M kind τ xbar S mem y)) :
    x = y := by
  obtain ⟨hlow, hcell⟩ := key_eq_parts _ _ _ h
  rcases lane_class M kind τ xbar S mem x hax with hxT | ⟨c, hc, rfl⟩ <;>
    rcases lane_class M kind τ xbar S mem y hay with hyT | ⟨c', hc', rfl⟩
  · rw [srcS_low M kind τ xbar S mem x hxT, srcS_low M kind τ xbar S mem y hyT] at hlow; omega
  · rw [srcS_low M kind τ xbar S mem x hxT, (srcS_input_facts M kind τ xbar S mem hτw hlen c' hc').2.2.2.1] at hlow
    omega
  · rw [srcS_low M kind τ xbar S mem y hyT, (srcS_input_facts M kind τ xbar S mem hτw hlen c hc).2.2.2.1] at hlow
    omega
  · rw [(srcS_input_facts M kind τ xbar S mem hτw hlen c hc).2.2.2.2.1,
      (srcS_input_facts M kind τ xbar S mem hτw hlen c' hc').2.2.2.2.1] at hcell
    omega

/-- Active records have positive keys. -/
theorem key_pos_of_act (x : ℕ) (hx : x < 2 ^ (τ + 1)) (ha : srcS M kind τ xbar S mem x .act 0 = true) :
    0 < keyOf (dims M τ) (srcS M kind τ xbar S mem x) := by
  rw [key_eq]
  rcases lane_class M kind τ xbar S mem x ha with hxT | ⟨c, hc, rfl⟩
  · rw [srcS_low M kind τ xbar S mem x hxT]; have := Nat.one_le_two_pow (n := τ); omega
  · rw [(srcS_input_facts M kind τ xbar S mem hτw hlen c hc).2.2.2.2.1]
    have := Nat.one_le_two_pow (n := M.w)
    have : 1 ≤ 2 ^ ((dims M τ).τ + 1) * (c + 2 ^ M.w) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega

omit hτw hlen in
/-- The sort key: the record key for active records, after all of them the lane index. -/
def skS (x : Fin (2 ^ (τ + 1))) : ℕ :=
  if srcS M kind τ xbar S mem x .act 0 then keyOf (dims M τ) (srcS M kind τ xbar S mem x)
  else 2 ^ (dims M τ).κ + x.val

theorem skS_inj : Function.Injective (skS M kind τ xbar S mem) := by
  intro x y h
  unfold skS at h
  have kx := key_lt_pow (dims M τ) (srcS M kind τ xbar S mem x)
  have ky := key_lt_pow (dims M τ) (srcS M kind τ xbar S mem y)
  split_ifs at h with hx hy hy
  · exact Fin.ext (key_inj M kind τ xbar S mem hτw hlen x y x.isLt y.isLt hx hy h)
  · omega
  · omega
  · exact Fin.ext (by omega)

omit hτw hlen in
/-- The sorting permutation. -/
def sortPerm : Equiv.Perm (Fin (2 ^ (τ + 1))) := Tuple.sort (skS M kind τ xbar S mem)

theorem skS_strictMono : StrictMono (skS M kind τ xbar S mem ∘ sortPerm M kind τ xbar S mem) :=
  (Tuple.monotone_sort _).strictMono_of_injective
    ((skS_inj M kind τ xbar S mem hτw hlen).comp (sortPerm M kind τ xbar S mem).injective)

end Sorting

omit S mem in
/-- The sorted records `σ_j.REC`. -/
def dstS (j : ℕ) : RecField → ℕ → Bool :=
  if h : j < 2 ^ (τ + 1) then srcS M kind τ xbar S mem (sortPerm M kind τ xbar S mem ⟨j, h⟩) else fun _ _ => false

/-! ## The sorted list satisfies (S1)–(S5) (`lem:trace-sorted`, converse) -/

theorem keyOf_sentinel (d : Dims) : keyOf d sentinelR = 0 := by
  unfold keyOf
  rw [natOf_congr _ (fun _ => false) _ (fun l _ => by
    simp only [keySlot]; split_ifs <;> simp [sentinelR])]
  exact natOf_false _


section SortedOK

variable (hτw : τ < M.w) (hlen : xbar.length ≤ 2 ^ τ) (hw1 : 1 ≤ M.w)
  (hacc : M.AcceptingSeq (2 ^ τ) S) (hmem0 : mem 0 = 0)
  (hstep : ∀ i, i + 1 < 2 ^ τ → M.Step (S i) (mem i) (S (i + 1)) (mem (i + 1)))
  (hconsA : M.readString true (2 ^ τ) S <+: xbar)
include hτw hlen hw1 hacc hmem0 hstep hconsA

omit hτw hlen hw1 hacc hmem0 hstep hconsA in
theorem dstS_at (j : ℕ) (hj : j < 2 ^ (τ + 1)) :
    dstS M kind τ xbar S mem j = srcS M kind τ xbar S mem (sortPerm M kind τ xbar S mem ⟨j, hj⟩) := by
  simp [dstS, hj]

omit hτw hlen hw1 hacc hmem0 hstep hconsA in
theorem dstS_lane (x : Fin (2 ^ (τ + 1))) :
    dstS M kind τ xbar S mem ((sortPerm M kind τ xbar S mem).symm x).val = srcS M kind τ xbar S mem x := by
  rw [dstS_at M kind τ xbar S mem _ ((sortPerm M kind τ xbar S mem).symm x).isLt]
  simp

omit hw1 hacc hmem0 hstep hconsA in
theorem ord_dstS (j : ℕ) (hj : j < 2 ^ (τ + 1)) :
    OrdOK (dims M τ) (dstS M kind τ xbar S mem j) (predR (dstS M kind τ xbar S mem) j) := by
  have hmono := skS_strictMono M kind τ xbar S mem hτw hlen
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    have hp : predR (dstS M kind τ xbar S mem) 0 = sentinelR := by simp [predR]
    rw [hp]
    refine ⟨fun _ => by simp [sentinelR], fun ha _ => ?_⟩
    rw [keyOf_sentinel, dstS_at M kind τ xbar S mem 0 hj]
    rw [dstS_at M kind τ xbar S mem 0 hj] at ha
    exact key_pos_of_act M kind τ xbar S mem hτw hlen _ (Fin.isLt _) ha
  · have hp : predR (dstS M kind τ xbar S mem) j = dstS M kind τ xbar S mem (j - 1) := by
      simp [predR, show j ≠ 0 by omega]
    rw [hp, dstS_at M kind τ xbar S mem j hj,
      dstS_at M kind τ xbar S mem (j - 1) (by omega)]
    set a := sortPerm M kind τ xbar S mem ⟨j - 1, by omega⟩
    set c := sortPerm M kind τ xbar S mem ⟨j, hj⟩
    have hlt : skS M kind τ xbar S mem a < skS M kind τ xbar S mem c :=
      hmono (show (⟨j - 1, by omega⟩ : Fin (2 ^ (τ + 1))) < ⟨j, hj⟩ from Fin.mk_lt_mk.mpr (by omega))
    have kc := key_lt_pow (dims M τ) (srcS M kind τ xbar S mem c)
    have hpa : srcS M kind τ xbar S mem c .act 0 = true → srcS M kind τ xbar S mem a .act 0 = true := by
      intro hc
      by_contra ha
      simp only [skS, hc, if_true] at hlt
      rw [if_neg (by simp [ha])] at hlt
      omega
    refine ⟨hpa, fun hc ha => ?_⟩
    simp only [skS, hc, ha, if_true] at hlt
    exact hlt

omit hw1 hacc hmem0 hstep hconsA in
theorem pos_lt_of_key (x x' : Fin (2 ^ (τ + 1))) (ha : srcS M kind τ xbar S mem x .act 0 = true)
    (ha' : srcS M kind τ xbar S mem x' .act 0 = true)
    (hk : keyOf (dims M τ) (srcS M kind τ xbar S mem x') < keyOf (dims M τ) (srcS M kind τ xbar S mem x)) :
    ((sortPerm M kind τ xbar S mem).symm x').val < ((sortPerm M kind τ xbar S mem).symm x).val := by
  have hl := dstS_lane M kind τ xbar S mem
  apply key_pos (dims M τ) _ (dstS M kind τ xbar S mem)
    (fun j hj => ord_dstS M kind τ xbar S mem hτw hlen j hj) _ _ (Fin.isLt _) (Fin.isLt _)
  · rw [hl]; exact ha
  · rw [hl]; exact ha'
  · rw [hl, hl]; exact hk

omit hw1 hacc hmem0 hstep hconsA in
theorem key_le_pred_lane (x x' : Fin (2 ^ (τ + 1))) (ha : srcS M kind τ xbar S mem x .act 0 = true)
    (ha' : srcS M kind τ xbar S mem x' .act 0 = true) (hpos : 1 ≤ ((sortPerm M kind τ xbar S mem).symm x).val)
    (hk : keyOf (dims M τ) (srcS M kind τ xbar S mem x') < keyOf (dims M τ) (srcS M kind τ xbar S mem x)) :
    keyOf (dims M τ) (srcS M kind τ xbar S mem x') ≤
      keyOf (dims M τ) (dstS M kind τ xbar S mem (((sortPerm M kind τ xbar S mem).symm x).val - 1)) := by
  have hl := dstS_lane M kind τ xbar S mem
  have := key_gap (dims M τ) _ (dstS M kind τ xbar S mem)
    (fun j hj => ord_dstS M kind τ xbar S mem hτw hlen j hj) _ _ (Fin.isLt _) hpos
    (Fin.isLt _) (by rw [hl]; exact ha) (by rw [hl]; exact ha') (by rw [hl, hl]; exact hk)
  rw [hl] at this; exact this

omit hw1 hacc hmem0 hstep hconsA in
theorem lane_memS (y : ℕ) (hy : y < 2 ^ (τ + 1)) (ha : srcS M kind τ xbar S mem y .act 0 = true)
    (hr : srcS M kind τ xbar S mem y .rgn 0 = false) :
    y < 2 ^ τ ∧ (isLd (insS M S y) || isSt (insS M S y)) = true := by
  rcases lane_class M kind τ xbar S mem y ha with hyT | ⟨c, hc, rfl⟩
  · refine ⟨hyT, ?_⟩
    rcases srcS_act_time M kind τ xbar S mem y hyT ha with h | h
    · exact h
    · rw [(srcS_rdA M kind τ xbar S mem hτw y hyT h).2.1] at hr; exact absurd hr (by simp)
  · rw [(srcS_input_facts M kind τ xbar S mem hτw hlen c hc).2.1] at hr; exact absurd hr (by simp)

omit hlen hw1 hacc hmem0 hstep hconsA hτw in
theorem mem_keyS (i i' : ℕ) (hi : i < 2 ^ τ) (hi' : i' < i)
    (hls : (isLd (insS M S i) || isSt (insS M S i)) = true)
    (hls' : (isLd (insS M S i') || isSt (insS M S i')) = true)
    (hA : xWord (S i') (insS M S i') = xWord (S i) (insS M S i)) :
    keyOf (dims M τ) (srcS M kind τ xbar S mem i') < keyOf (dims M τ) (srcS M kind τ xbar S mem i) := by
  rw [key_lt_iff]
  right
  refine ⟨?_, ?_⟩
  · rw [(srcS_mem M kind τ xbar S mem i hi hls).2.2.2.1, (srcS_mem M kind τ xbar S mem i' (by omega) hls').2.2.2.1,
      hA]
  · rw [srcS_low M kind τ xbar S mem i hi, srcS_low M kind τ xbar S mem i' (by omega)]; omega

/-- **`lem:trace-sorted` converse.** Every sorted vertex satisfies `SortOK` with its predecessor. -/
theorem sortOK_dstS (j : ℕ) (hj : j < 2 ^ (τ + 1)) :
    SortOK (dims M τ) (dstS M kind τ xbar S mem j) (predR (dstS M kind τ xbar S mem) j) := by
  obtain ⟨o1, o2⟩ := ord_dstS M kind τ xbar S mem hτw hlen j hj
  refine ⟨o1, o2, ?_, ?_⟩
  all_goals rw [dstS_at M kind τ xbar S mem j hj]
  all_goals set x := sortPerm M kind τ xbar S mem ⟨j, hj⟩ with hxdef
  all_goals have hxj : (sortPerm M kind τ xbar S mem).symm x = ⟨j, hj⟩ := by simp [hxdef]
  all_goals have hN : ∀ i, i < 2 ^ τ → i < 2 ^ (τ + 1) := fun i hi => by rw [pow_succ]; omega
  · -- (S4): memory loads
    intro ha hrgn hst k hk
    obtain ⟨hxT, hls⟩ := lane_memS M kind τ xbar S mem hτw hlen x x.isLt ha hrgn
    obtain ⟨-, -, hstx, hcell, hva⟩ := srcS_mem M kind τ xbar S mem x hxT hls
    have hld : isLd (insS M S x) = true := by
      rw [hstx] at hst; simpa [hst] using hls
    set A := xWord (S x) (insS M S x) with hAdef
    have hmvA : mvS M S mem x = mem x A := mvS_load M S mem x hld
    have hearly : ∀ i'' (hi'' : i'' < x.val), isSt (insS M S i'') = true → xWord (S i'') (insS M S i'') = A →
        ((sortPerm M kind τ xbar S mem).symm ⟨i'', hN i'' (by omega)⟩).val < j := by
      intro i'' hi'' hs hA''
      have hls'' : (isLd (insS M S i'') || isSt (insS M S i'')) = true := by simp [hs]
      have := pos_lt_of_key M kind τ xbar S mem hτw hlen x ⟨i'', hN i'' (by omega)⟩ ha
        (srcS_mem M kind τ xbar S mem i'' (by omega) hls'').1
        (mem_keyS M kind τ xbar S mem x i'' hxT hi'' hls hls'' hA'')
      rw [hxj] at this; exact this
    have hzero : (∀ i'' < x.val, ¬ (isSt (insS M S i'') = true ∧ xWord (S i'') (insS M S i'') = A)) →
        srcS M kind τ xbar S mem x .va k = false := by
      intro h
      rw [hva k hk, hmvA, run_mem_stable M τ S mem hstep A 0 x.val (Nat.zero_le _) hxT
        (fun i'' _ h2 => h i'' h2), hmem0]
      simp
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      have hp : predR (dstS M kind τ xbar S mem) 0 = sentinelR := by simp [predR]
      rw [hp, hzero (fun i'' hi'' ⟨hs, hA''⟩ => by have := hearly i'' hi'' hs hA''; omega)]
      simp [sentinelR]
    · have hp : predR (dstS M kind τ xbar S mem) j = dstS M kind τ xbar S mem (j - 1) := by
        simp [predR, show j ≠ 0 by omega]
      rw [hp, dstS_at M kind τ xbar S mem (j - 1) (by omega)]
      set y := sortPerm M kind τ xbar S mem ⟨j - 1, by omega⟩ with hydef
      have hyj : (sortPerm M kind τ xbar S mem).symm y = ⟨j - 1, by omega⟩ := by simp [hydef]
      have hya : srcS M kind τ xbar S mem y .act 0 = true := by
        have := o1 (by rw [dstS_at M kind τ xbar S mem j hj]; exact ha)
        rw [hp, dstS_at M kind τ xbar S mem (j - 1) (by omega)] at this
        exact this
      have hkey : keyOf (dims M τ) (srcS M kind τ xbar S mem y) < keyOf (dims M τ) (srcS M kind τ xbar S mem x) := by
        have := o2 (by rw [dstS_at M kind τ xbar S mem j hj]; exact ha)
          (by rw [hp, dstS_at M kind τ xbar S mem (j - 1) (by omega)]; exact hya)
        rw [hp, dstS_at M kind τ xbar S mem (j - 1) (by omega),
          dstS_at M kind τ xbar S mem j hj] at this
        exact this
      by_cases hsame : sameCell (dims M τ) (srcS M kind τ xbar S mem x) (srcS M kind τ xbar S mem y) = true
      · rw [hsame, Bool.true_and]
        have hcy : cellN (dims M τ) (srcS M kind τ xbar S mem y) = A.toNat := by
          rw [← (sameCell_iff _ _ _).mp hsame, hcell]
        have hyrgn : srcS M kind τ xbar S mem y .rgn 0 = false := by
          have hlt : natOf (srcS M kind τ xbar S mem y .ad) (dims M τ).w < 2 ^ M.w := natOf_lt _ _
          have hA : A.toNat < 2 ^ M.w := A.isLt
          unfold cellN at hcy
          cases h : srcS M kind τ xbar S mem y .rgn 0
          · rfl
          · rw [h] at hcy; simp [dims] at hcy; omega
        obtain ⟨hyT, hyls⟩ := lane_memS M kind τ xbar S mem hτw hlen y y.isLt hya hyrgn
        obtain ⟨-, -, -, hycell, hyva⟩ := srcS_mem M kind τ xbar S mem y hyT hyls
        have hyA : xWord (S y) (insS M S y) = A := by
          apply BitVec.eq_of_toNat_eq; rw [← hycell]; exact hcy
        have hyx : y.val < x.val := by
          have hl := (key_lt_iff _ _ _).mp hkey
          rcases hl with hl | ⟨-, hl⟩
          · rw [hcy, hcell] at hl; omega
          · rw [srcS_low M kind τ xbar S mem y hyT, srcS_low M kind τ xbar S mem x hxT] at hl; omega
        have hbetween : ∀ i'', y.val + 1 ≤ i'' → i'' < x.val →
            ¬ (isSt (insS M S i'') = true ∧ xWord (S i'') (insS M S i'') = A) := by
          rintro i'' h1'' h2'' ⟨hs, hA''⟩
          have hls'' : (isLd (insS M S i'') || isSt (insS M S i'')) = true := by simp [hs]
          have hpx := hearly i'' h2'' hs hA''
          have hpy := pos_lt_of_key M kind τ xbar S mem hτw hlen ⟨i'', hN i'' (by omega)⟩ y
            (srcS_mem M kind τ xbar S mem i'' (by omega) hls'').1 hya
            (mem_keyS M kind τ xbar S mem i'' y (by omega) (by omega) hls'' hyls
              (by rw [hyA, hA'']))
          rw [hyj] at hpy
          simp only at hpy
          omega
        rw [hva k hk, hmvA, run_mem_stable M τ S mem hstep A (y.val + 1) x.val (by omega) hxT hbetween,
          hyva k hk]
        congr 1
        rw [(run_step M τ S mem hstep y.val (by omega)).2.2.2]
        cases hys : isSt (insS M S y)
        · have hyld : isLd (insS M S y) = true := by simpa [hys] using hyls
          rw [memNext_ne _ _ _ _ (fun hs => absurd hs (by rw [hys]; simp)), ← hyA, mvS_load M S mem y hyld]
        · rw [← hyA, memNext_store _ _ _ hys, mvS_store M S mem y hys]
      · have hsameF : sameCell (dims M τ) (srcS M kind τ xbar S mem x) (srcS M kind τ xbar S mem y) = false := by
          simpa using hsame
        rw [hsameF, Bool.false_and]
        apply hzero
        rintro i'' hi'' ⟨hs, hA''⟩
        have hls'' : (isLd (insS M S i'') || isSt (insS M S i'')) = true := by simp [hs]
        have hk'' := mem_keyS M kind τ xbar S mem x i'' hxT hi'' hls hls'' hA''
        have hle := key_le_pred_lane M kind τ xbar S mem hτw hlen x ⟨i'', hN i'' (by omega)⟩ ha
          (srcS_mem M kind τ xbar S mem i'' (by omega) hls'').1 (by rw [hxj]; simp; omega) hk''
        rw [hxj] at hle
        simp only at hle
        rw [dstS_at M kind τ xbar S mem (j - 1) (by omega)] at hle
        have hc := cell_sandwich (dims M τ) (srcS M kind τ xbar S mem i'') (srcS M kind τ xbar S mem y)
          (srcS M kind τ xbar S mem x) hle hkey
          (by rw [(srcS_mem M kind τ xbar S mem i'' (by omega) hls'').2.2.2.1, hcell, hA''])
        apply absurd hsameF
        rw [Bool.not_eq_false, sameCell_iff, hc, (srcS_mem M kind τ xbar S mem i'' (by omega) hls'').2.2.2.1,
          hcell, hA'']
  · -- (S5): tape-A reads
    intro ha hrgn hph
    have hxT : x.val < 2 ^ τ := by
      rcases lane_class M kind τ xbar S mem x ha with h | ⟨c, hc, hxc⟩
      · exact h
      · rw [hxc, (srcS_input_facts M kind τ xbar S mem hτw hlen c hc).2.2.1] at hph; exact absurd hph (by simp)
    have haA : aAS M S x = true := by
      rcases srcS_act_time M kind τ xbar S mem x hxT ha with h | h
      · rw [(srcS_mem M kind τ xbar S mem x hxT h).2.1] at hrgn; exact absurd hrgn (by simp)
      · exact h
    have hxT1 : x.val + 1 < 2 ^ τ := by
      by_contra hc
      have hx1 : x.val = 2 ^ τ - 1 := by omega
      have := (run_last M τ S hacc).2
      unfold aAS at haA
      rw [hx1, this] at haA
      simp [isRdA] at haA
    obtain ⟨hcNA, hrd⟩ := run_readA M τ xbar S mem hstep hw1 hconsA x.val hxT1 haA
    set c := cntAS M S x with hcdef
    obtain ⟨-, -, hxcell, hxva⟩ := srcS_rdA M kind τ xbar S mem hτw x hxT haA
    have hzN : 2 ^ τ + c < 2 ^ (τ + 1) := by
      have : xbar.length / M.w ≤ xbar.length := Nat.div_le_self _ _
      rw [pow_succ]; omega
    set z : Fin (2 ^ (τ + 1)) := ⟨2 ^ τ + c, hzN⟩ with hzdef
    obtain ⟨hza, hzr, hzph, hzlow, hzcell, hzva⟩ := srcS_input_facts M kind τ xbar S mem hτw hlen c hcNA
    have hkz : keyOf (dims M τ) (srcS M kind τ xbar S mem z) < keyOf (dims M τ) (srcS M kind τ xbar S mem x) := by
      rw [key_lt_iff]; right
      exact ⟨by rw [hzcell, hxcell], by rw [hzlow, srcS_low M kind τ xbar S mem x hxT]; omega⟩
    have hpz := pos_lt_of_key M kind τ xbar S mem hτw hlen x z ha hza hkz
    rw [hxj] at hpz
    simp only at hpz
    -- the input record is the immediate predecessor
    have hpzj : ((sortPerm M kind τ xbar S mem).symm z).val = j - 1 := by
      by_contra hne
      have hlt : ((sortPerm M kind τ xbar S mem).symm z).val < j - 1 := by omega
      have hord := fun j' hj' => ord_dstS M kind τ xbar S mem hτw hlen j' hj'
      have hya := active_prefix (dims M τ) _ (dstS M kind τ xbar S mem) hord j hj
        (by rw [dstS_at M kind τ xbar S mem j hj]; exact ha) (j - 1) (by omega)
      have hk1 := key_mono (dims M τ) _ (dstS M kind τ xbar S mem) hord (j - 1) (by omega) hya _ hlt
      have hk2 := key_mono (dims M τ) _ (dstS M kind τ xbar S mem) hord j hj
        (by rw [dstS_at M kind τ xbar S mem j hj]; exact ha) (j - 1) (by omega)
      rw [dstS_lane M kind τ xbar S mem z,
        dstS_at M kind τ xbar S mem (j - 1) (by omega)] at hk1
      rw [dstS_at M kind τ xbar S mem (j - 1) (by omega),
        dstS_at M kind τ xbar S mem j hj] at hk2
      rw [dstS_at M kind τ xbar S mem (j - 1) (by omega)] at hya
      set y := sortPerm M kind τ xbar S mem ⟨j - 1, by omega⟩ with hydef
      have hcy := cell_sandwich (dims M τ) _ _ _ hk1.le hk2 (by rw [hzcell, hxcell])
      rw [hzcell] at hcy
      have hyr : srcS M kind τ xbar S mem y .rgn 0 = true := by
        have hlt' : natOf (srcS M kind τ xbar S mem y .ad) (dims M τ).w < 2 ^ M.w := natOf_lt _ _
        unfold cellN at hcy
        cases h : srcS M kind τ xbar S mem y .rgn 0
        · rw [h] at hcy; simp [dims] at hcy hlt'; omega
        · rfl
      rcases lane_class M kind τ xbar S mem y hya with hyT | ⟨c', hc', hyc'⟩
      · rcases srcS_act_time M kind τ xbar S mem y hyT hya with h | h
        · rw [(srcS_mem M kind τ xbar S mem y hyT h).2.1] at hyr; exact absurd hyr (by simp)
        · have hyc := (srcS_rdA M kind τ xbar S mem hτw y hyT h).2.2.1
          rw [hcy] at hyc
          have hcc : cntAS M S y = c := by omega
          have hyx : y.val < x.val := by
            have hl := (key_lt_iff _ _ _).mp hk2
            rcases hl with hl | ⟨-, hl⟩
            · rw [(srcS_rdA M kind τ xbar S mem hτw y hyT h).2.2.1, hxcell, hcc] at hl; omega
            · rw [srcS_low M kind τ xbar S mem y hyT, srcS_low M kind τ xbar S mem x hxT] at hl; omega
          have hmono := cntAS_mono M S (show y.val + 1 ≤ x.val by omega)
          rw [cntAS_succ, h, hcc] at hmono
          simp at hmono; omega
      · have := (srcS_input_facts M kind τ xbar S mem hτw hlen c' hc').2.2.2.2.1
        rw [← hyc'] at this
        rw [this] at hcy
        have hcc : c' = c := by omega
        have hyz : y = z := Fin.ext (by rw [hyc', hcc])
        apply hne
        rw [← hyz, hydef]; simp
    have hp : predR (dstS M kind τ xbar S mem) j = srcS M kind τ xbar S mem z := by
      have hj1 : 1 ≤ j := by omega
      simp only [predR, show j ≠ 0 by omega, if_false]
      rw [← hpzj, dstS_lane M kind τ xbar S mem z]
    rw [hp]
    refine ⟨by rw [sameCell_iff, hxcell, hzcell], hzph, fun k hk => ?_⟩
    rw [hxva k hk, hrd, hzva k hk]
    simp only [Option.getD_some]
    rw [ShortPCP.getLsbD_wordOf _ _ _ _ (show k < M.w from hk)]

end SortedOK

/-! ## The trace of a run and `ET(M, τ, x̄)` -/

theorem canon_eSet (S0 : M.Config) (I : Instr M.w M.k M.ops) (mv : BitVec M.w) (rd : Option (BitVec M.w))
    (ts cA : BitVec τ) (cB : BitVec ((dims M τ).β + 1)) (hI : M.instrAt S0.pc = some I)
    (Q : Instr M.w M.k M.ops → Bool) : (eSet M Q).evalB (canon kind τ S0 I mv rd ts cA cB) = Q I := by
  have hpc : S0.pc.toNat < M.code.length := by
    unfold Ram.instrAt at hI
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hI
    exact absurd hI (by simp)
  have hIc : M.code[S0.pc.toNat]'hpc = I := by
    unfold Ram.instrAt at hI
    rw [List.getElem?_eq_getElem hpc] at hI
    exact Option.some.inj hI
  rw [evalB_eSet _ _ hpc (fun p _ => rfl), hIc]

theorem ofNat_incr (n a : ℕ) (b : Bool) :
    BitVec.ofNat n a + 0#n + setWidth n (ofBool b) = BitVec.ofNat n (a + b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    BitVec.toNat_ofBool]
  rw [Nat.add_mod]
  cases b <;> simp [Nat.add_mod]

/-- **The trace of a run** (proof of `thm:trace` (⇐)). -/
def traceS : Trace Bool where
  src := srcS M kind τ xbar S mem
  dst := dstS M kind τ xbar S mem
  time i s := rowS M kind τ S mem i (.inl s)
  sort j s := sortCanon (dims M τ) (dstS M kind τ xbar S mem j) (predR (dstS M kind τ xbar S mem) j) (.inl s)

section Holds

variable (halu : ∀ op, M.alu op = (kind op).fn) (hτw : τ < M.w) (hlen : xbar.length ≤ 2 ^ τ) (hw1 : 1 ≤ M.w)
  (hacc : M.AcceptingSeq (2 ^ τ) S) (hmem0 : mem 0 = 0)
  (hstep : ∀ i, i + 1 < 2 ^ τ → M.Step (S i) (mem i) (S (i + 1)) (mem (i + 1)))
  (hconsA : M.readString true (2 ^ τ) S <+: xbar)
  (hwit : (M.readString false (2 ^ τ) S).length ≤ 2 ^ τ) (hω : 2 ^ (dims M τ).β * M.w = 2 ^ τ)
include halu hτw hlen hw1 hacc hmem0 hstep hconsA hwit hω

omit halu hτw hlen hw1 hacc hmem0 hstep hconsA hwit hω in
theorem timeRead_traceS (i : ℕ) (hi : i < 2 ^ τ) :
    (traceS M kind τ xbar S mem).timeRead i = rowS M kind τ S mem i := by
  funext v
  rcases v with s | ⟨f, k⟩
  · rfl
  · simp [Trace.timeRead, traceS, srcS, hi]

omit halu hτw hlen hw1 hmem0 hconsA hwit hω in
theorem instr_run (i : ℕ) (hi : i < 2 ^ τ) : M.instrAt (S i).pc = some (insS M S i) := by
  rcases Nat.lt_or_ge (i + 1) (2 ^ τ) with h | h
  · exact (run_step M τ S mem hstep i h).1
  · have : i = 2 ^ τ - 1 := by omega
    subst this; exact (run_last M τ S hacc).1

omit halu hτw hlen hmem0 hconsA in
theorem cntBS_bound (i : ℕ) (hi : i < 2 ^ τ) (ha : aBS M S i = true) : cntBS M S i < 2 ^ (dims M τ).β := by
  have hT1 : i + 1 < 2 ^ τ := by
    by_contra hc
    have hx1 : i = 2 ^ τ - 1 := by omega
    have := (run_last M τ S hacc).2
    unfold aBS at ha
    rw [hx1, this] at ha
    simp [isRdB] at ha
  have hB := readPart_B M τ S mem hstep (2 ^ τ - 1) le_rfl
  have hle : cntBS M S (2 ^ τ - 1) * M.w ≤ 2 ^ (dims M τ).β * M.w := by
    rw [hω, ← hB]; exact hwit
  have hle' := Nat.le_of_mul_le_mul_right hle (by omega)
  have hm := cntBS_mono M S (show i + 1 ≤ 2 ^ τ - 1 by omega)
  rw [cntBS_succ, ha] at hm
  simp at hm; omega

theorem traceS_holds : HoldsB M kind τ xbar (traceS M kind τ xbar S mem) := by
  have hT1 : 1 ≤ 2 ^ τ := Nat.one_le_two_pow
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (T1)–(T10)
    intro i hi q hq
    rw [timeRead_traceS M kind τ xbar S mem i hi]
    apply row_complete kind τ halu hw1 _ _ _ _ _ _ _ (instr_run M τ S mem hacc hstep i hi)
      (mvS_store M S mem i) _ q hq
    cases ha : (isRdB (insS M S i) && !(rdS M S i).isNone)
    · simp
    · have hlt := cntBS_bound M τ S mem hw1 hacc hstep hwit hω i hi ha
      simp only [Bool.true_and, BitVec.getLsbD_ofNat]
      simp [Nat.testBit_lt_two_pow hlt]
  · -- (B1)
    intro c hc
    rw [timeRead_traceS M kind τ xbar S mem 0 (by omega)]
    obtain ⟨hpc0, hreg0⟩ := hacc.1
    cases c with
    | pc j => simp [TCopy.dst, rowS, canon, hpc0]
    | fl r => simp [TCopy.dst, rowS, canon, regFlag, hreg0]
    | rg r j => simp [TCopy.dst, rowS, canon, regBit, hreg0]
    | ts j => simp [TCopy.dst, rowS, canon]
    | cA j => simp [TCopy.dst, rowS, canon, cntAS]
    | cB j => simp [TCopy.dst, rowS, canon, cntBS]
  · -- (B2) copies
    intro i hi c hc
    rw [timeRead_traceS M kind τ xbar S mem (i + 1) hi]
    have hsucc := (run_step M τ S mem hstep i hi).2.2.1
    cases c with
    | pc j => simp only [TCopy.dst, TCopy.src, traceS, rowS, canon]; rw [hsucc]
    | fl r => simp only [TCopy.dst, TCopy.src, traceS, rowS, canon]; rw [hsucc]
    | rg r j => simp only [TCopy.dst, TCopy.src, traceS, rowS, canon]; rw [hsucc]
    | ts j => simp only [TCopy.dst, TCopy.src, traceS, rowS, canon]; rw [ofNat_incr]; rfl
    | cA j =>
      simp only [TCopy.dst, TCopy.src, traceS, rowS, canon]; rw [ofNat_incr, cntAS_succ]; rfl
    | cB j =>
      simp only [TCopy.dst, TCopy.src, traceS, rowS, canon]; rw [ofNat_incr, cntBS_succ]; rfl
  · -- (B2) no `out` before the last row
    intro i hi
    rw [timeRead_traceS M kind τ xbar S mem i (by omega), outE,
      rowS, canon_eSet M kind τ _ _ _ _ _ _ _ (instr_run M τ S mem hacc hstep i (by omega))]
    exact (run_step M τ S mem hstep i hi).2.1
  · -- (B3) the last row accepts
    rw [timeRead_traceS M kind τ xbar S mem _ (by omega), accE]
    simp only [evalB_add, evalB_one]
    rw [rowS, canon_eSet M kind τ _ _ _ _ _ _ _ (instr_run M τ S mem hacc hstep _ (by omega)),
      (run_last M τ S hacc).2]
    rfl
  · -- (S1)–(S5)
    intro j hj q hq
    have hv : (traceS M kind τ xbar S mem).sortRead j =
        sortCanon (dims M τ) (dstS M kind τ xbar S mem j) (predR (dstS M kind τ xbar S mem) j) := by
      funext v; rcases v with s | ⟨f, k⟩ <;> rfl
    rw [hv]
    exact sorted_complete (dims M τ) hw1 _ _
      (sortOK_dstS M kind τ xbar S mem hτw hlen hw1 hacc hmem0 hstep hconsA j hj) q hq
  · -- (B4) the sentinel
    intro f k _
    simp [traceS, sortCanon, predR, sentinelR]
  · -- (B4) copies
    intro j _ f k _
    simp [traceS, sortCanon, predR]
  · -- (B5) input records
    intro c hc
    have hs := srcS_input M kind τ xbar S mem c hc
    simp [traceS, hs, inputRec]
  · -- (B5) dummies
    intro x hx _ s _
    exact srcS_dummy M kind τ xbar S mem x hx s.1 s.2
  · -- (P)
    refine ⟨(sortPerm M kind τ xbar S mem).symm, fun x s _ => ?_⟩
    show dstS M kind τ xbar S mem ((sortPerm M kind τ xbar S mem).symm x).val s.1 s.2 = srcS M kind τ xbar S mem x s.1 s.2
    rw [dstS_lane M kind τ xbar S mem x]

end Holds

/-- **`thm:trace` (⇐).** A bounded accepting run gives a Boolean assignment satisfying `ET(M, τ, x̄)`. -/
theorem bhram_complete (halu : ∀ op, M.alu op = (kind op).fn) (hw2 : M.w = 2 ^ Nat.log 2 M.w)
    (hωτ : Nat.log 2 M.w ≤ τ) (hτw : τ < M.w) (hlen : xbar.length ≤ 2 ^ τ) (h : M.BHRAM xbar τ τ) :
    ∃ b : Trace Bool, HoldsB M kind τ xbar b := by
  obtain ⟨-, -, -, wit, hwitlen, S, hacc, ⟨-, mem, hmem0, hstep⟩, ⟨hconsA, hconsB⟩, -⟩ := h
  have hw1 : 1 ≤ M.w := by rw [hw2]; exact Nat.one_le_two_pow
  have hwit : (M.readString false (2 ^ τ) S).length ≤ 2 ^ τ := hconsB.length_le.trans hwitlen
  have hω : 2 ^ (dims M τ).β * M.w = 2 ^ τ := by
    conv_lhs => rw [hw2]
    simp only [dims]; rw [← pow_add, Nat.sub_add_cancel hωτ]
  exact ⟨traceS M kind τ xbar S mem,
    traceS_holds M kind τ xbar S mem halu hτw hlen hw1 hacc hmem0 hstep hconsA hwit hω⟩

end NearCubicGates.Adapters.RAMTrace
