import SourceAdapters.RAMTrace.Records
import SourceAdapters.ShortPCP.RAMRun

/-!
# `thm:trace` (⇒): a satisfying event trace gives a bounded accepting run

`app:event-trace`, proof of `thm:trace` (⇒) with `lem:trace-step`, `lem:trace-memory`, `lem:trace-sorted` and `lem:trace-counters`. From a Boolean assignment satisfying `ET(M, τ, x̄)`:
decode the configurations `S^i = dec(ρ_i.cur)`; the copies make `S^{i+1}` the successor of `S^i` under the row's
access (`lem:trace-step`); the time stamps are `0, …, T − 1` and the counters count the reads (`lem:trace-counters`); the sorted list
makes every load read the memory (`lem:trace-memory` and `lem:trace-sorted`) and every tape-A read the next word of `x̄`; the bounded-run definition `def:ram`
concludes `(x̄, 1^τ, 1^τ) ∈ BH_RAM(M)`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMTrace

open NearCubicGates.Adapters.ACSP Expr BitVec

variable (M : Ram) (kind : Fin M.ops → AluOp) (τ : ℕ) (xbar : List Bool) (b : Trace Bool)

/-! ## The objects of a trace -/

/-- The configuration `S^i = dec(ρ_i.cur)`. -/
def cfgT (i : ℕ) : M.Config := decCur (b.timeRead i)

/-- The instruction executed by row `i`. -/
def insT (i : ℕ) : Instr M.w M.k M.ops := (M.instrAt (cfgT M b i : M.Config).pc).getD .nop

/-- The memory value of row `i`. -/
def mvT (i : ℕ) : BitVec M.w := mvOf (b.timeRead i)

/-- The tape value of row `i`. -/
def rdT (i : ℕ) : Option (BitVec M.w) := rdOf (b.timeRead i)

/-- The time stamp of row `i`. -/
def tsT (i : ℕ) : BitVec τ := tsOf τ (b.timeRead i)

/-- The tape-A counter of row `i`. -/
def cAT (i : ℕ) : BitVec τ := cAOf τ (b.timeRead i)

/-- The tape-B counter of row `i`. -/
def cBT (i : ℕ) : BitVec ((dims M τ).β + 1) := cBOf ((dims M τ).β + 1) (b.timeRead i)

/-- Row `i` reads a word (not `#`) from tape A. -/
def aAT (i : ℕ) : Bool := isRdA (insT M b i) && !(rdT M b i).isNone

/-- Row `i` reads a word from tape B. -/
def aBT (i : ℕ) : Bool := isRdB (insT M b i) && !(rdT M b i).isNone

/-- The number of tape-A words read at rows `< m`. -/
def cntA (m : ℕ) : ℕ := ((List.range m).filter (aAT M b)).length

/-- The number of tape-B words read at rows `< m`. -/
def cntB (m : ℕ) : ℕ := ((List.range m).filter (aBT M b)).length

theorem cntA_succ (m : ℕ) : cntA M b (m + 1) = cntA M b m + (aAT M b m).toNat := by
  unfold cntA; rw [List.range_succ, List.filter_append, List.length_append]
  cases h : aAT M b m <;> simp [h]

theorem cntB_succ (m : ℕ) : cntB M b (m + 1) = cntB M b m + (aBT M b m).toNat := by
  unfold cntB; rw [List.range_succ, List.filter_append, List.length_append]
  cases h : aBT M b m <;> simp [h]

theorem cntA_le (m : ℕ) : cntA M b m ≤ m := by
  unfold cntA; exact (List.length_filter_le _ _).trans (by simp)

/-- The memory before row `i` (`lem:trace-memory` (a)): `mem_0 = 0`, then each row's `store`. -/
def memSeq : ℕ → M.Memory
  | 0 => 0
  | i + 1 => memNext (cfgT M b i) (insT M b i) (memSeq i)

/-- The record of lane `x` (stage `0`). -/
def srcR (x : ℕ) : RecField → ℕ → Bool := fun f k => b.src x f k

/-- The record of sorted vertex `j`. -/
def dstR (j : ℕ) : RecField → ℕ → Bool := fun f k => b.dst j f k

/-- Exclusivity of the record kinds. -/
theorem ld_st_rdA {w k ops : ℕ} (I : Instr w k ops) :
    (isLd I && isSt I) = false ∧ (isLd I && isRdA I) = false ∧ (isSt I && isRdA I) = false := by
  cases I <;> simp [isLd, isSt, isRdA]

theorem natOf_false (n : ℕ) : natOf (fun _ => false) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natOf, ih]

theorem natOf_getLsbD {n : ℕ} (v : BitVec n) : natOf v.getLsbD n = v.toNat := by
  rw [← toNat_bvOf, bvOf_getLsbD]

theorem natOf_testBit (c n : ℕ) (hc : c < 2 ^ n) : natOf c.testBit n = c := by
  rw [← toNat_bvOf]
  have : bvOf n c.testBit = BitVec.ofNat n c := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj; rw [getLsbD_bvOf, BitVec.getLsbD_ofNat]
  rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

theorem natOf_low {n m : ℕ} (hm : m ≤ n) (f : ℕ → Bool) (v : BitVec m) (hf : ∀ j < n, f j = (decide (j < m) && v.getLsbD j)) :
    natOf f n = v.toNat := by
  rw [show n = m + (n - m) by omega, natOf_add, natOf_congr _ v.getLsbD m (fun j hj => by rw [hf j (by omega)]; simp [hj]),
    natOf_getLsbD, natOf_congr _ (fun _ => false) _ (fun j hj => by rw [hf _ (by omega)]; simp), natOf_false]
  simp

/-- The memory only changes at stores (`lem:trace-memory` (a)). -/
theorem memSeq_stable (A : BitVec M.w) (i' : ℕ) :
    ∀ i, i' ≤ i → (∀ i'', i' ≤ i'' → i'' < i →
      ¬ (isSt (insT M b i'') = true ∧ xWord (cfgT M b i'') (insT M b i'') = A)) →
      memSeq M b i A = memSeq M b i' A := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => intro _; rfl
  | succ m hm ih =>
    intro h
    simp only [memSeq]
    rw [memNext_ne _ _ _ _ (fun hs hx => h m hm (by omega) ⟨hs, hx⟩), ih (fun i'' h1 h2 => h i'' h1 (by omega))]

theorem memSeq_load (i : ℕ) (h : isSt (insT M b i) = false) (A : BitVec M.w) :
    memSeq M b (i + 1) A = memSeq M b i A := by
  simp only [memSeq]
  exact memNext_ne _ _ _ _ (fun hs => absurd hs (by rw [h]; simp))

section Sound

variable (halu : ∀ op, M.alu op = (kind op).fn) (hw : 1 ≤ M.w) (hb : HoldsB M kind τ xbar b)
include halu hw hb

/-- Row `i` is the canonical row of its inputs (`lem:trace-step`). -/
theorem row_at (i : ℕ) (hi : i < 2 ^ τ) :
    M.instrAt (cfgT M b i : M.Config).pc = some (insT M b i) ∧
    (∀ s : TVar, s.Active (dims M τ) →
      b.timeRead i s = canon kind τ (cfgT M b i) (insT M b i) (mvT M b i) (rdT M b i) (tsT τ b i) (cAT τ b i)
        (cBT M τ b i) s) ∧
    (isSt (insT M b i) = true → (mvT M b i : BitVec M.w) = yWord (cfgT M b i) (insT M b i)) ∧
    ((isRdB (insT M b i) && !(rdT M b i : Option (BitVec M.w)).isNone) &&
      (cBT M τ b i).getLsbD (dims M τ).β) = false := by
  obtain ⟨I, hI, hag, hst, hbd⟩ := row_sound kind τ (b.timeRead i) (hb.1 i hi) halu hw
  have hIns : insT M b i = I := by simp [insT, cfgT, hI]
  rw [hIns]
  exact ⟨hI, hag, hst, hbd⟩

/-- The copies `ρ_{i+1}.cur = ρ_i.nxt` make the decoded configurations consecutive steps (`lem:trace-step`, (B2)). -/
theorem cfg_succ (i : ℕ) (hi : i + 1 < 2 ^ τ) :
    cfgT M b (i + 1) = rowSucc (cfgT M b i) (mvT M b i) (rdT M b i) (insT M b i) := by
  obtain ⟨-, hag, -, -⟩ := row_at M kind τ xbar b halu hw hb i (by omega)
  have hcp := hb.2.2.1 i hi
  have h1 : (cfgT M b (i + 1) : M.Config) = decNxt (b.timeRead i) := by
    simp only [cfgT, decCur, decNxt]
    have hp : ∀ j < M.w, b.timeRead (i + 1) (.inl (.pc j)) = b.timeRead i (.inl (.npc j)) :=
      fun j hj => hcp (.pc j) hj
    have hf : ∀ r < M.k, b.timeRead (i + 1) (.inl (.fl r)) = b.timeRead i (.inl (.nfl r)) :=
      fun r hr => hcp (.fl r) hr
    have hr : ∀ r < M.k, ∀ j < M.w, b.timeRead (i + 1) (.inl (.rg r j)) = b.timeRead i (.inl (.nrg r j)) :=
      fun r hr j hj => hcp (.rg r j) ⟨hr, hj⟩
    rw [bvOf_congr _ _ _ hp]
    congr 1
    funext r
    rw [hf r.val r.isLt, bvOf_congr _ _ _ (hr r.val r.isLt)]
  rw [h1, decNxt_congr _ (canon kind τ (cfgT M b i) (insT M b i) (mvT M b i) (rdT M b i) (tsT τ b i) (cAT τ b i)
      (cBT M τ b i)) (fun j hj => hag (.inl (.npc j)) hj) (fun r hr => hag (.inl (.nfl r)) hr)
      (fun r hr j hj => hag (.inl (.nrg r j)) ⟨hr, hj⟩), decNxt_canon]

theorem ts_succ (i : ℕ) (hi : i + 1 < 2 ^ τ) :
    tsT τ b (i + 1) = tsT τ b i + 0#τ + setWidth τ (ofBool true) := by
  obtain ⟨-, hag, -, -⟩ := row_at M kind τ xbar b halu hw hb i (by omega)
  have hcp := hb.2.2.1 i hi
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [tsT, tsOf, getLsbD_bvOf, hj, decide_true, Bool.true_and]
  have hc := hcp (.ts j) hj
  simp only [TCopy.dst, TCopy.src, Trace.timeRead] at hc
  simp only [Trace.timeRead] at hag ⊢
  rw [hc]
  exact hag (.inl (.TSN j)) hj

omit halu hw in
theorem ts_zero : tsT τ b 0 = 0#τ := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [tsT, tsOf, getLsbD_bvOf, hj, decide_true, Bool.true_and, getLsbD_zero]
  exact hb.2.1 (.ts j) hj

theorem ts_val (i : ℕ) (hi : i < 2 ^ τ) : (tsT τ b i).toNat = i := by
  induction i with
  | zero => rw [ts_zero M kind τ xbar b hb]; simp
  | succ i ih =>
    rw [ts_succ M kind τ xbar b halu hw hb i hi]
    have ht := ih (by omega)
    have hpos : 1 < 2 ^ τ := by omega
    rw [BitVec.toNat_add, BitVec.toNat_add]
    simp [ht, Nat.mod_eq_of_lt hpos, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (show i < 2 ^ τ by omega)]

theorem cA_succ (i : ℕ) (hi : i + 1 < 2 ^ τ) :
    cAT τ b (i + 1) = cAT τ b i + 0#τ + setWidth τ (ofBool (isRdA (insT M b i) && !(rdT M b i).isNone)) := by
  obtain ⟨-, hag, -, -⟩ := row_at M kind τ xbar b halu hw hb i (by omega)
  have hcp := hb.2.2.1 i hi
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [cAT, cAOf, getLsbD_bvOf, hj, decide_true, Bool.true_and]
  have hc := hcp (.cA j) hj
  simp only [TCopy.dst, TCopy.src, Trace.timeRead] at hc
  simp only [Trace.timeRead] at hag ⊢
  rw [hc]
  exact hag (.inl (.ncA j)) hj

omit halu hw in
theorem cA_zero : cAT τ b 0 = 0#τ := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [cAT, cAOf, getLsbD_bvOf, hj, decide_true, Bool.true_and, getLsbD_zero]
  exact hb.2.1 (.cA j) hj

theorem cB_succ (i : ℕ) (hi : i + 1 < 2 ^ τ) :
    cBT M τ b (i + 1) = cBT M τ b i + 0#((dims M τ).β + 1) +
      setWidth ((dims M τ).β + 1) (ofBool (isRdB (insT M b i) && !(rdT M b i).isNone)) := by
  obtain ⟨-, hag, -, -⟩ := row_at M kind τ xbar b halu hw hb i (by omega)
  have hcp := hb.2.2.1 i hi
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [cBT, cBOf, getLsbD_bvOf, hj, decide_true, Bool.true_and]
  have hc := hcp (.cB j) (by show j ≤ (dims M τ).β; omega)
  simp only [TCopy.dst, TCopy.src, Trace.timeRead] at hc
  simp only [Trace.timeRead] at hag ⊢
  rw [hc]
  exact hag (.inl (.ncB j)) (by show j ≤ (dims M τ).β; omega)

omit halu hw in
theorem cB_zero : cBT M τ b 0 = 0#((dims M τ).β + 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [cBT, cBOf, getLsbD_bvOf, hj, decide_true, Bool.true_and, getLsbD_zero]
  exact hb.2.1 (.cB j) (by show j ≤ (dims M τ).β; omega)

theorem not_out (i : ℕ) (hi : i + 1 < 2 ^ τ) : isOut (insT M b i) = false := by
  obtain ⟨hI, hag, -, -⟩ := row_at M kind τ xbar b halu hw hb i (by omega)
  have := hb.2.2.2.1 i hi
  obtain ⟨hpc, hE⟩ := row_decode kind τ (b.timeRead i) (hb.1 i (by omega))
  have hIc : M.code[(decCur (b.timeRead i) : M.Config).pc.toNat]'hpc = insT M b i := by
    unfold Ram.instrAt cfgT at hI
    rw [List.getElem?_eq_getElem hpc] at hI
    exact Option.some.inj hI
  rw [outE, evalB_eSet _ _ hpc (fun p hp => (hE p hp).1), hIc] at this
  exact this

theorem accepting_last : insT M b (2 ^ τ - 1) = .out true := by
  have hT : 2 ^ τ - 1 < 2 ^ τ := by have := Nat.one_le_two_pow (n := τ); omega
  obtain ⟨hI, -, -, -⟩ := row_at M kind τ xbar b halu hw hb _ hT
  have := hb.2.2.2.2.1
  obtain ⟨hpc, hE⟩ := row_decode kind τ (b.timeRead (2 ^ τ - 1)) (hb.1 _ hT)
  have hIc : M.code[(decCur (b.timeRead (2 ^ τ - 1)) : M.Config).pc.toNat]'hpc = insT M b (2 ^ τ - 1) := by
    unfold Ram.instrAt cfgT at hI
    rw [List.getElem?_eq_getElem hpc] at hI
    exact Option.some.inj hI
  simp only [accE, evalB_add, evalB_one] at this
  rw [evalB_eSet _ _ hpc (fun p hp => (hE p hp).1), hIc] at this
  cases h : insT M b (2 ^ τ - 1) with
  | out bb => rw [h] at this; cases bb <;> simp_all [isAcc]
  | _ => rw [h] at this; simp [isAcc] at this

theorem cA_val (i : ℕ) (hi : i < 2 ^ τ) : (cAT τ b i).toNat = cntA M b i := by
  induction i with
  | zero => rw [cA_zero M kind τ xbar b hb]; simp [cntA]
  | succ i ih =>
    rw [cA_succ M kind τ xbar b halu hw hb i hi, cntA_succ, ← ih (by omega)]
    have hle := cntA_le M b (i + 1)
    rw [cntA_succ, ← ih (by omega)] at hle
    have hA : (isRdA (insT M b i) && !(rdT M b i).isNone) = aAT M b i := rfl
    rw [hA, BitVec.toNat_add, BitVec.toNat_add]
    have hlt : (cAT τ b i).toNat + (aAT M b i).toNat < 2 ^ τ := by omega
    have hb1 : (aAT M b i).toNat ≤ 1 := Bool.toNat_le _
    simp only [BitVec.toNat_zero, Nat.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
    rw [Nat.mod_eq_of_lt (BitVec.isLt _), Nat.mod_eq_of_lt (show (aAT M b i).toNat < 2 ^ τ by omega),
      Nat.mod_eq_of_lt hlt]

theorem cB_val (i : ℕ) (hi : i < 2 ^ τ) :
    (cBT M τ b i).toNat = cntB M b i ∧ cntB M b i ≤ 2 ^ (dims M τ).β := by
  induction i with
  | zero => rw [cB_zero M kind τ xbar b hb]; simp [cntB]
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    obtain ⟨-, -, -, hbd⟩ := row_at M kind τ xbar b halu hw hb i (by omega)
    have hA : (isRdB (insT M b i) && !(rdT M b i).isNone) = aBT M b i := rfl
    rw [hA] at hbd
    rw [cB_succ M kind τ xbar b halu hw hb i hi, cntB_succ, hA]
    have hlt' : (cBT M τ b i).toNat < 2 ^ ((dims M τ).β + 1) := BitVec.isLt _
    have hpow : 2 ^ (dims M τ).β < 2 ^ ((dims M τ).β + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hpos : 1 ≤ 2 ^ (dims M τ).β := Nat.one_le_two_pow
    rw [BitVec.toNat_add, BitVec.toNat_add]
    simp only [BitVec.toNat_zero, Nat.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
    rw [Nat.mod_eq_of_lt hlt']
    cases ha : aBT M b i
    · simp only [Bool.toNat_false, Nat.zero_mod, Nat.add_zero]
      rw [Nat.mod_eq_of_lt hlt']
      exact ⟨ih1, ih2⟩
    · rw [ha, Bool.true_and] at hbd
      have hsmall : (cBT M τ b i).toNat < 2 ^ (dims M τ).β := by
        apply Nat.lt_pow_two_of_testBit
        intro k hk
        rcases Nat.eq_or_lt_of_le hk with h | h
        · subst h; exact hbd
        · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt' (Nat.pow_le_pow_right (by norm_num) h))
      simp only [Bool.toNat_true]
      rw [Nat.mod_eq_of_lt (show 1 < 2 ^ ((dims M τ).β + 1) by omega), Nat.mod_eq_of_lt (by omega)]
      omega

/-- The record of a time lane (T9 at row `i`, through `lem:trace-step`). -/
theorem src_time (i : ℕ) (hi : i < 2 ^ τ) (f : RecField) (k : ℕ) (hk : k < f.width M.w τ) :
    srcR b i f k = canon kind τ (cfgT M b i) (insT M b i) (mvT M b i) (rdT M b i) (tsT τ b i) (cAT τ b i)
      (cBT M τ b i) (.inr (f, k)) :=
  (row_at M kind τ xbar b halu hw hb i hi).2.1 (.inr (f, k)) hk

/-- A time lane's record has phase `1` (T9). -/
theorem src_ph (i : ℕ) (hi : i < 2 ^ τ) : srcR b i .ph 0 = true := by
  rw [src_time M kind τ xbar b halu hw hb i hi .ph 0 (by simp [RecField.width])]; rfl

theorem src_lowN (i : ℕ) (hi : i < 2 ^ τ) : lowN (dims M τ) (srcR b i) = i + 2 ^ τ := by
  unfold lowN
  rw [src_ph M kind τ xbar b halu hw hb i hi]
  have : natOf (srcR b i .ts) (dims M τ).τ = (tsT τ b i).toNat := by
    rw [tsT, tsOf, toNat_bvOf]; rfl
  rw [this, ts_val M kind τ xbar b halu hw hb i hi]
  simp [dims]

/-- **A memory access record** (T9): active, region `0`, cell = the address, value = `MV`. -/
theorem src_mem (i : ℕ) (hi : i < 2 ^ τ) (hls : (isLd (insT M b i) || isSt (insT M b i)) = true) :
    srcR b i .act 0 = true ∧ srcR b i .rgn 0 = false ∧ srcR b i .st 0 = isSt (insT M b i) ∧
      cellN (dims M τ) (srcR b i) = (xWord (cfgT M b i) (insT M b i)).toNat ∧
      ∀ k < M.w, srcR b i .va k = (mvT M b i).getLsbD k := by
  have hx := ld_st_rdA (insT M b i)
  have hA : isRdA (insT M b i) = false := by
    cases h1 : isLd (insT M b i) <;> cases h2 : isSt (insT M b i) <;> simp_all
  have hxo : Bool.xor (isLd (insT M b i)) (isSt (insT M b i)) = true := by
    cases h1 : isLd (insT M b i) <;> cases h2 : isSt (insT M b i) <;> simp_all
  have hsrc := src_time M kind τ xbar b halu hw hb i hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hsrc .act 0 (by simp [RecField.width])]; simp [canon, hA, hxo]
  · rw [hsrc .rgn 0 (by simp [RecField.width])]; simp [canon, hA]
  · rw [hsrc .st 0 (by simp [RecField.width])]; rfl
  · unfold cellN
    rw [hsrc .rgn 0 (by simp [RecField.width])]
    simp only [canon, hA, Bool.false_and, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
    rw [natOf_congr _ (xWord (cfgT M b i) (insT M b i)).getLsbD _ (fun k hk => by
      rw [hsrc .ad k (show k < M.w from hk)]; simp [canon, hA, hxo])]
    exact natOf_getLsbD _
  · intro k hk
    rw [hsrc .va k (by simpa [RecField.width] using hk)]; simp [canon, hA, hxo]

/-- **A tape-A read record** (T9): active, region `1`, cell = `cA + 2^w`, value = the word read. -/
theorem src_rdA (i : ℕ) (hi : i < 2 ^ τ) (hτw : τ ≤ M.w) (ha : aAT M b i = true) :
    srcR b i .act 0 = true ∧ srcR b i .rgn 0 = true ∧
      cellN (dims M τ) (srcR b i) = (cAT τ b i).toNat + 2 ^ M.w ∧
      ∀ k < M.w, srcR b i .va k = ((rdT M b i).getD 0).getLsbD k := by
  have hx := ld_st_rdA (insT M b i)
  have hA : isRdA (insT M b i) = true := by unfold aAT at ha; simp_all
  have hL : isLd (insT M b i) = false := by cases h : isLd (insT M b i) <;> simp_all
  have hS : isSt (insT M b i) = false := by cases h : isSt (insT M b i) <;> simp_all
  have ha' : (isRdA (insT M b i) && !(rdT M b i).isNone) = true := ha
  have hsrc := src_time M kind τ xbar b halu hw hb i hi
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsrc .act 0 (by simp [RecField.width])]; simp only [canon, hL, hS, ha']; rfl
  · rw [hsrc .rgn 0 (by simp [RecField.width])]; simp only [canon, ha']
  · unfold cellN
    rw [hsrc .rgn 0 (by simp [RecField.width])]
    simp only [canon, ha', Bool.toNat_true, Nat.mul_one]
    congr 1
    apply natOf_low hτw
    intro k hk
    rw [hsrc .ad k (by simpa [RecField.width] using hk)]
    simp only [canon, hL, hS, ha']
    split_ifs with h <;> simp [h]
  · intro k hk
    rw [hsrc .va k (by simpa [RecField.width] using hk)]; simp only [canon, hL, hS, ha']; simp

/-- A time lane is active only for a memory access or a tape-A word read. -/
theorem src_act_time (i : ℕ) (hi : i < 2 ^ τ) (h : srcR b i .act 0 = true) :
    (isLd (insT M b i) || isSt (insT M b i)) = true ∨ aAT M b i = true := by
  have hx := ld_st_rdA (insT M b i)
  rw [src_time M kind τ xbar b halu hw hb i hi .act 0 (by simp [RecField.width])] at h
  simp only [canon] at h
  unfold aAT
  cases h1 : isLd (insT M b i) <;> cases h2 : isSt (insT M b i) <;>
    cases h3 : (isRdA (insT M b i) && !(rdT M b i).isNone) <;> simp_all

omit halu hw in
/-- **An input record** (B5). -/
theorem src_input (c : ℕ) (hc : c < xbar.length / M.w) (hcw : c < 2 ^ M.w) :
    srcR b (2 ^ τ + c) .act 0 = true ∧ srcR b (2 ^ τ + c) .rgn 0 = true ∧ srcR b (2 ^ τ + c) .ph 0 = false ∧
      cellN (dims M τ) (srcR b (2 ^ τ + c)) = c + 2 ^ M.w ∧
      ∀ k < M.w, srcR b (2 ^ τ + c) .va k = xbar.getD (c * M.w + k) false := by
  obtain ⟨h1, h2, h3, -, -, h6, h7⟩ := hb.2.2.2.2.2.2.2.2.1 c hc
  refine ⟨h1, h2, h3, ?_, h7⟩
  show natOf (fun k => b.src (2 ^ τ + c) .ad k) M.w + 2 ^ M.w * (b.src (2 ^ τ + c) .rgn 0).toNat = c + 2 ^ M.w
  rw [h2, natOf_congr _ c.testBit _ (fun k hk => h6 k hk), natOf_testBit c _ hcw]
  simp

omit halu hw in
/-- A dummy record is inactive (B5). -/
theorem src_dummy (x : ℕ) (h1 : 2 ^ τ + xbar.length / M.w ≤ x) (h2 : x < 2 ^ (τ + 1)) :
    srcR b x .act 0 = false :=
  hb.2.2.2.2.2.2.2.2.2.1 x h1 h2 (.act, 0) (by simp [RecSlot.Active, RecField.width])

omit halu in
/-- The sorted vertices satisfy `SortOK` with their predecessors (S1)–(S5), (B4). -/
theorem sortOK_dst (j : ℕ) (hj : j < 2 ^ (τ + 1)) :
    SortOK (dims M τ) (dstR b j) (predR (dstR b) j) := by
  have hw' : 1 ≤ (dims M τ).w := hw
  obtain ⟨-, h⟩ := sorted_sound (dims M τ) hw' (b.sortRead j) (hb.2.2.2.2.2.1 j hj)
  apply sortOK_congr (dims M τ) _ _ _ _ (fun f k _ => rfl) _ h
  intro f k hf hk
  have hact : (SSlot.prev f k).Active (dims M τ) := ⟨hf, hk⟩
  simp only [prevB, Trace.sortRead, predR]
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    rw [hb.2.2.2.2.2.2.1 f k hact]
    simp [sentinelR]
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [hb.2.2.2.2.2.2.2.1 j' hj f k hact]
    simp [dstR]

/-! ## Memory and tape A through the sorted list (`lem:trace-memory` and `lem:trace-sorted`) -/

section Lanes

variable (hτw : τ < M.w) (hlen : xbar.length ≤ 2 ^ τ)
  (π : Equiv.Perm (Fin (2 ^ (τ + 1))))
  (hπ : ∀ x : Fin (2 ^ (τ + 1)), ∀ s : RecSlot, s.Active (dims M τ) → b.dst (π x) s.1 s.2 = b.src x s.1 s.2)
include hτw hlen hπ

omit halu hw hb hτw hlen in
theorem agree_lane (x : Fin (2 ^ (τ + 1))) : AgreeR (dims M τ) (dstR b (π x)) (srcR b x) :=
  fun f k hk => hπ x (f, k) hk

omit halu hw hb hτw hlen in
theorem key_lane (x : Fin (2 ^ (τ + 1))) : keyOf (dims M τ) (dstR b (π x)) = keyOf (dims M τ) (srcR b x) :=
  keyOf_congr _ _ _ fun f k _ hk => agree_lane M τ b π hπ x f k hk

omit halu hw hb hτw hlen in
theorem act_lane (x : Fin (2 ^ (τ + 1))) : dstR b (π x) .act 0 = srcR b x .act 0 :=
  agree_lane M τ b π hπ x .act 0 (by simp [RecField.width])

omit halu hw hb hπ in
theorem NA_lt (c : ℕ) (hc : c < xbar.length / M.w) : c < 2 ^ M.w ∧ 2 ^ τ + c < 2 ^ (τ + 1) := by
  have h1 : xbar.length / M.w ≤ xbar.length := Nat.div_le_self _ _
  have h2 : 2 ^ τ < 2 ^ M.w := Nat.pow_lt_pow_right (by norm_num) hτw
  rw [pow_succ]; omega

omit hπ in
/-- An active record of region `0` is a memory access of a time row. -/
theorem lane_mem (x : ℕ) (hx : x < 2 ^ (τ + 1)) (ha : srcR b x .act 0 = true) (hr : srcR b x .rgn 0 = false) :
    x < 2 ^ τ ∧ (isLd (insT M b x) || isSt (insT M b x)) = true := by
  rcases Nat.lt_or_ge x (2 ^ τ) with h1 | h1
  · refine ⟨h1, ?_⟩
    rcases src_act_time M kind τ xbar b halu hw hb x h1 ha with h | h
    · exact h
    · rw [(src_rdA M kind τ xbar b halu hw hb x h1 hτw.le h).2.1] at hr; exact absurd hr (by simp)
  · rcases Nat.lt_or_ge x (2 ^ τ + xbar.length / M.w) with h2 | h2
    · obtain ⟨c, rfl⟩ : ∃ c, x = 2 ^ τ + c := ⟨x - 2 ^ τ, by omega⟩
      have hc := (NA_lt M τ xbar hτw hlen c (by omega)).1
      rw [(src_input M kind τ xbar b hb c (by omega) hc).2.1] at hr; exact absurd hr (by simp)
    · rw [src_dummy M kind τ xbar b hb x h2 hx] at ha; exact absurd ha (by simp)

omit hτw hlen hπ in
/-- An active record of region `1` and phase `0` is an input record. -/
theorem lane_input (x : ℕ) (hx : x < 2 ^ (τ + 1)) (ha : srcR b x .act 0 = true) (hph : srcR b x .ph 0 = false) :
    ∃ c < xbar.length / M.w, x = 2 ^ τ + c := by
  rcases Nat.lt_or_ge x (2 ^ τ) with h1 | h1
  · rw [src_ph M kind τ xbar b halu hw hb x h1] at hph; exact absurd hph (by simp)
  · rcases Nat.lt_or_ge x (2 ^ τ + xbar.length / M.w) with h2 | h2
    · exact ⟨x - 2 ^ τ, by omega, by omega⟩
    · rw [src_dummy M kind τ xbar b hb x h2 hx] at ha; exact absurd ha (by simp)

omit halu hτw hlen in
/-- Two active lanes: the smaller key sits earlier in the sorted list. -/
theorem lane_pos (x x' : Fin (2 ^ (τ + 1))) (ha : srcR b x .act 0 = true) (ha' : srcR b x' .act 0 = true)
    (hk : keyOf (dims M τ) (srcR b x') < keyOf (dims M τ) (srcR b x)) : (π x').val < (π x).val := by
  have hok := fun j hj => (sortOK_dst M kind τ xbar b hw hb j hj).ord
  apply key_pos (dims M τ) _ (dstR b) hok _ _ (π x).isLt (π x').isLt
  · rw [act_lane M τ b π hπ]; exact ha
  · rw [act_lane M τ b π hπ]; exact ha'
  · rw [key_lane M τ b π hπ, key_lane M τ b π hπ]; exact hk

omit halu hτw hlen in
/-- The local sorted-vertex facts at the position of an active lane. -/
theorem lane_sortOK (x : Fin (2 ^ (τ + 1))) :
    SortOK (dims M τ) (srcR b x) (predR (dstR b) (π x)) :=
  sortOK_congr _ _ _ _ _ (agree_lane M τ b π hπ x) (fun _ _ _ _ => rfl)
    (sortOK_dst M kind τ xbar b hw hb (π x) (π x).isLt)

omit halu hw hb hτw hlen in
/-- The predecessor of a non-first active lane is a lane `y`, sorted just before it. -/
theorem lane_pred (x : Fin (2 ^ (τ + 1))) (hpos : 1 ≤ (π x).val) :
    let y := π.symm ⟨(π x).val - 1, by have := (π x).isLt; omega⟩
    AgreeP (dims M τ) (predR (dstR b) (π x)) (srcR b y) ∧ (π y).val = (π x).val - 1 := by
  intro y
  have hy : π y = ⟨(π x).val - 1, by have := (π x).isLt; omega⟩ := by simp [y]
  refine ⟨fun f k _ hk => ?_, by rw [hy]⟩
  have : predR (dstR b) (π x) = dstR b ((π x).val - 1) := by simp [predR, show (π x).val ≠ 0 by omega]
  rw [this, ← agree_lane M τ b π hπ y f k hk, hy]

omit halu hτw hlen in
theorem key_le_pred (x x' : Fin (2 ^ (τ + 1))) (ha : srcR b x .act 0 = true) (ha' : srcR b x' .act 0 = true)
    (hpos : 1 ≤ (π x).val) (hk : keyOf (dims M τ) (srcR b x') < keyOf (dims M τ) (srcR b x)) :
    keyOf (dims M τ) (srcR b x') ≤ keyOf (dims M τ) (predR (dstR b) (π x)) := by
  have hok := fun j hj => (sortOK_dst M kind τ xbar b hw hb j hj).ord
  have := key_gap (dims M τ) _ (dstR b) hok (π x).val (π x').val (π x).isLt hpos (π x').isLt
    (by rw [act_lane M τ b π hπ]; exact ha) (by rw [act_lane M τ b π hπ]; exact ha')
    (by rw [key_lane M τ b π hπ, key_lane M τ b π hπ]; exact hk)
  rw [key_lane M τ b π hπ] at this
  have hp : predR (dstR b) (π x) = dstR b ((π x).val - 1) := by
    simp [predR, show (π x).val ≠ 0 by omega]
  rw [hp]; exact this

end Lanes

section Memory

variable (hτw : τ < M.w) (hlen : xbar.length ≤ 2 ^ τ)
  (π : Equiv.Perm (Fin (2 ^ (τ + 1))))
  (hπ : ∀ x : Fin (2 ^ (τ + 1)), ∀ s : RecSlot, s.Active (dims M τ) → b.dst (π x) s.1 s.2 = b.src x s.1 s.2)
include hτw hlen hπ

omit hτw hlen hπ in
theorem memSeq_store (i : ℕ) (hi : i < 2 ^ τ) (h : isSt (insT M b i) = true) :
    memSeq M b (i + 1) (xWord (cfgT M b i) (insT M b i)) = mvT M b i := by
  simp only [memSeq]
  rw [memNext_store _ _ _ h, (row_at M kind τ xbar b halu hw hb i hi).2.2.1 h]

omit hτw hlen hπ in
/-- Two memory accesses to one address: the earlier one has the smaller key. -/
theorem mem_key_lt (i i' : ℕ) (hi : i < 2 ^ τ) (hi' : i' < i)
    (hls : (isLd (insT M b i) || isSt (insT M b i)) = true)
    (hls' : (isLd (insT M b i') || isSt (insT M b i')) = true)
    (hA : xWord (cfgT M b i') (insT M b i') = xWord (cfgT M b i) (insT M b i)) :
    keyOf (dims M τ) (srcR b i') < keyOf (dims M τ) (srcR b i) := by
  rw [key_lt_iff]
  right
  refine ⟨?_, ?_⟩
  · rw [(src_mem M kind τ xbar b halu hw hb i hi hls).2.2.2.1,
      (src_mem M kind τ xbar b halu hw hb i' (by omega) hls').2.2.2.1, hA]
  · rw [src_lowN M kind τ xbar b halu hw hb i hi, src_lowN M kind τ xbar b halu hw hb i' (by omega)]; omega

/-- **Every load reads the reconstructed memory** (`lem:trace-memory`, `lem:trace-sorted`):
`MV_i = mem_i(X_i)`. -/
theorem load_reads (i : ℕ) (hi : i < 2 ^ τ) (hld : isLd (insT M b i) = true) :
    mvT M b i = memSeq M b i (xWord (cfgT M b i) (insT M b i)) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  have hN : i < 2 ^ (τ + 1) := by rw [pow_succ]; omega
  have hls : (isLd (insT M b i) || isSt (insT M b i)) = true := by simp [hld]
  have hstF : isSt (insT M b i) = false := by
    have := (ld_st_rdA (insT M b i)).1; rw [hld] at this; simpa using this
  obtain ⟨hact, hrgn, hst, hcell, hva⟩ := src_mem M kind τ xbar b halu hw hb i hi hls
  set A := xWord (cfgT M b i) (insT M b i) with hAdef
  set x : Fin (2 ^ (τ + 1)) := ⟨i, hN⟩ with hx
  obtain ⟨-, -, h3, -⟩ := lane_sortOK M kind τ xbar b hw hb π hπ x
  have hv := h3 hact hrgn (by rw [hst, hstF])
  -- every earlier access to `A` comes earlier in the sorted list
  have hearly : ∀ i'' (hi'' : i'' < i), (isLd (insT M b i'') || isSt (insT M b i'')) = true →
      xWord (cfgT M b i'') (insT M b i'') = A →
      (π ⟨i'', lt_trans hi'' hN⟩).val < (π x).val := by
    intro i'' hi'' hls'' hA''
    apply lane_pos M kind τ xbar b hw hb π hπ
    · exact hact
    · exact (src_mem M kind τ xbar b halu hw hb i'' (by omega) hls'').1
    · exact mem_key_lt M kind τ xbar b halu hw hb i i'' hi hi'' hls hls'' hA''
  have hzero : (∀ k < M.w, srcR b i .va k = false) → mvT M b i = 0 := by
    intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [← hva k hk, h k hk]; simp
  have hno : (∀ i'' < i, ¬ (isSt (insT M b i'') = true ∧ xWord (cfgT M b i'') (insT M b i'') = A)) →
      memSeq M b i A = 0 := by
    intro h
    rw [memSeq_stable M b A 0 i (Nat.zero_le _) (fun i'' _ h2 => h i'' h2)]; rfl
  by_cases hpos : (π x).val = 0
  · -- the predecessor is the sentinel: the load reads `0`, and no earlier access exists
    have hp : predR (dstR b) (π x) = sentinelR := by simp [predR, hpos]
    rw [hzero (fun k hk => by rw [hv k hk, hp]; simp [sentinelR]), hno]
    rintro i'' hi'' ⟨hs, hA''⟩
    have := hearly i'' hi'' (by simp [hs]) hA''
    omega
  · obtain ⟨hagree, hy⟩ := lane_pred M τ xbar b π hπ x (by omega)
    set y := π.symm ⟨(π x).val - 1, by have := (π x).isLt; omega⟩ with hydef
    obtain ⟨h1, h2, -, -⟩ := lane_sortOK M kind τ xbar b hw hb π hπ x
    have hpa : predR (dstR b) (π x) .act 0 = true := h1 hact
    have hya : srcR b y .act 0 = true := by
      rw [← hagree .act 0 (by decide) (by simp [RecField.width])]; exact hpa
    have hkey : keyOf (dims M τ) (srcR b y) < keyOf (dims M τ) (srcR b i) := by
      rw [← keyOf_congr _ _ _ hagree]; exact h2 hact hpa
    by_cases hsame : sameCell (dims M τ) (srcR b i) (predR (dstR b) (π x)) = true
    · -- the predecessor is the latest earlier access to `A`
      have hcy : cellN (dims M τ) (srcR b y) = A.toNat := by
        rw [← cellN_congr _ _ _ hagree, ← (sameCell_iff _ _ _).mp hsame, hcell]
      have hyrgn : srcR b y .rgn 0 = false := by
        have hlt : natOf (srcR b y .ad) (dims M τ).w < 2 ^ M.w := natOf_lt _ _
        have hA : A.toNat < 2 ^ M.w := A.isLt
        unfold cellN at hcy
        cases h : srcR b y .rgn 0
        · rfl
        · rw [h] at hcy; simp [dims] at hcy; omega
      obtain ⟨hyT, hyls⟩ := lane_mem M kind τ xbar b halu hw hb hτw hlen y.val y.isLt hya hyrgn
      obtain ⟨-, -, -, hycell, hyva⟩ := src_mem M kind τ xbar b halu hw hb y.val hyT hyls
      have hyA : xWord (cfgT M b y.val) (insT M b y.val) = A := by
        apply BitVec.eq_of_toNat_eq; rw [← hycell]; exact hcy
      have hyi : y.val < i := by
        have hl := (key_lt_iff _ _ _).mp hkey
        rcases hl with hl | ⟨-, hl⟩
        · rw [hcy, hcell] at hl; omega
        · rw [src_lowN M kind τ xbar b halu hw hb y.val hyT, src_lowN M kind τ xbar b halu hw hb i hi] at hl
          omega
      -- the values agree
      have hmv : mvT M b i = mvT M b y.val := by
        apply BitVec.eq_of_getLsbD_eq
        intro k hk
        rw [← hva k hk, hv k hk, hsame, Bool.true_and, hagree .va k (by decide) (show k < (dims M τ).w from hk),
          hyva k hk]
      -- no store to `A` strictly between `y` and `i`
      have hbetween : ∀ i'', y.val + 1 ≤ i'' → i'' < i →
          ¬ (isSt (insT M b i'') = true ∧ xWord (cfgT M b i'') (insT M b i'') = A) := by
        rintro i'' h1'' h2'' ⟨hs, hA''⟩
        have hls'' : (isLd (insT M b i'') || isSt (insT M b i'')) = true := by simp [hs]
        have hpi := hearly i'' h2'' hls'' hA''
        have hyi'' : keyOf (dims M τ) (srcR b y) < keyOf (dims M τ) (srcR b i'') := by
          have := mem_key_lt M kind τ xbar b halu hw hb i'' y.val (by omega) (by omega) hls'' hyls
            (by rw [hyA, hA''])
          exact this
        have hpos' := lane_pos M kind τ xbar b hw hb π hπ ⟨i'', lt_trans h2'' hN⟩ y
          (src_mem M kind τ xbar b halu hw hb i'' (by omega) hls'').1 hya hyi''
        rw [hy] at hpos'
        omega
      rw [hmv, memSeq_stable M b A (y.val + 1) i (by omega) hbetween]
      cases hys : isSt (insT M b y.val)
      · have hyld : isLd (insT M b y.val) = true := by simpa [hys] using hyls
        rw [memSeq_load M b y.val hys, ← hyA]
        exact ih y.val hyi (by omega) hyld
      · rw [← hyA, memSeq_store M kind τ xbar b halu hw hb y.val hyT hys]
    · -- a different cell: the load reads `0`, and no earlier access exists
      have hsameF : sameCell (dims M τ) (srcR b i) (predR (dstR b) (π x)) = false := by simpa using hsame
      rw [hzero (fun k hk => by rw [hv k hk, hsameF]; simp), hno]
      rintro i'' hi'' ⟨hs, hA''⟩
      have hls'' : (isLd (insT M b i'') || isSt (insT M b i'')) = true := by simp [hs]
      have hk'' := mem_key_lt M kind τ xbar b halu hw hb i i'' hi hi'' hls hls'' hA''
      have hle := key_le_pred M kind τ xbar b hw hb π hπ x ⟨i'', lt_trans hi'' hN⟩ hact
        (src_mem M kind τ xbar b halu hw hb i'' (by omega) hls'').1 (by omega) hk''
      have hc := cell_sandwich (dims M τ) (srcR b i'') (predR (dstR b) (π x)) (srcR b i) hle
        (by rw [keyOf_congr _ _ _ hagree]; exact hkey)
        (by rw [(src_mem M kind τ xbar b halu hw hb i'' (by omega) hls'').2.2.2.1, hcell, hA''])
      apply absurd hsameF
      rw [Bool.not_eq_false, sameCell_iff, hc, (src_mem M kind τ xbar b halu hw hb i'' (by omega) hls'').2.2.2.1,
        hcell, hA'']

end Memory

section TapeA

variable (hτw : τ < M.w) (hlen : xbar.length ≤ 2 ^ τ)
  (π : Equiv.Perm (Fin (2 ^ (τ + 1))))
  (hπ : ∀ x : Fin (2 ^ (τ + 1)), ∀ s : RecSlot, s.Active (dims M τ) → b.dst (π x) s.1 s.2 = b.src x s.1 s.2)
include hτw hlen hπ

/-- **`lem:trace-sorted` (tape A).** A tape-A word read at row `i` has index `c = cA_i < N_A` and reads word `c` of `x̄`. -/
theorem readA_word (i : ℕ) (hi : i < 2 ^ τ) (ha : aAT M b i = true) :
    (cAT τ b i).toNat < xbar.length / M.w ∧
      rdT M b i = some (ShortPCP.wordOf M.w xbar (cAT τ b i).toNat) := by
  have hN : i < 2 ^ (τ + 1) := by rw [pow_succ]; omega
  obtain ⟨hact, hrgn, hcell, hva⟩ := src_rdA M kind τ xbar b halu hw hb i hi hτw.le ha
  set x : Fin (2 ^ (τ + 1)) := ⟨i, hN⟩ with hx
  obtain ⟨h1, -, -, h4⟩ := lane_sortOK M kind τ xbar b hw hb π hπ x
  obtain ⟨hsame, hpph, hpva⟩ := h4 hact hrgn (src_ph M kind τ xbar b halu hw hb i hi)
  by_cases hpos : (π x).val = 0
  · exfalso
    have hp : predR (dstR b) (π x) = sentinelR := by simp [predR, hpos]
    rw [hp, sameCell_iff, hcell] at hsame
    unfold cellN at hsame
    have h0 : natOf (sentinelR RecField.ad) (dims M τ).w = 0 := natOf_false _
    rw [h0] at hsame
    simp [sentinelR] at hsame
  · obtain ⟨hagree, -⟩ := lane_pred M τ xbar b π hπ x (by omega)
    set y := π.symm ⟨(π x).val - 1, by have := (π x).isLt; omega⟩ with hydef
    have hya : srcR b y .act 0 = true := by
      rw [← hagree .act 0 (by decide) (by simp [RecField.width])]; exact h1 hact
    have hyph : srcR b y .ph 0 = false := by
      rw [← hagree .ph 0 (by decide) (by simp [RecField.width])]; exact hpph
    obtain ⟨c, hc, hyc⟩ := lane_input M kind τ xbar b halu hw hb y.val y.isLt hya hyph
    have hcw := (NA_lt M τ xbar hτw hlen c hc).1
    obtain ⟨-, -, -, hycell, hyva⟩ := src_input M kind τ xbar b hb c hc hcw
    rw [← hyc] at hycell hyva
    have hcc : (cAT τ b i).toNat = c := by
      have := (sameCell_iff _ _ _).mp hsame
      rw [hcell, cellN_congr _ _ _ hagree, hycell] at this
      omega
    refine ⟨by rw [hcc]; exact hc, ?_⟩
    have hsome : (rdT M b i).isSome = true := by
      have : (isRdA (insT M b i) && !(rdT M b i).isNone) = true := ha
      cases h : rdT M b i <;> simp_all
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    rw [hv]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have e1 := hva k hk
    rw [hv] at e1
    simp only [Option.getD_some] at e1
    rw [← e1, hpva k hk, hagree .va k (by decide) (show k < (dims M τ).w from hk), hyva k hk, hcc,
      ShortPCP.getLsbD_wordOf _ _ _ _ hk]

end TapeA

/-! ## The read strings (`lem:trace-counters` and the tape-read semantics of `def:ram`) -/

theorem readAt_cfg (tA : Bool) (i : ℕ) (hi : i + 1 < 2 ^ τ) :
    M.readAt tA (cfgT M b) i =
      if (if tA then isRdA (insT M b i) else isRdB (insT M b i)) then some (rdT M b i) else none := by
  unfold Ram.readAt
  rw [(row_at M kind τ xbar b halu hw hb i (by omega)).1, cfg_succ M kind τ xbar b halu hw hb i hi]
  cases insT M b i with
  | readA r => cases tA <;> simp [rowSucc, isRdA, isRdB, Ram.Config.setNext]
  | readB r => cases tA <;> simp [rowSucc, isRdA, isRdB, Ram.Config.setNext]
  | _ => cases tA <;> simp [isRdA, isRdB]

section Strings

variable (hτw : τ < M.w) (hlen : xbar.length ≤ 2 ^ τ)
  (π : Equiv.Perm (Fin (2 ^ (τ + 1))))
  (hπ : ∀ x : Fin (2 ^ (τ + 1)), ∀ s : RecSlot, s.Active (dims M τ) → b.dst (π x) s.1 s.2 = b.src x s.1 s.2)
include hτw hlen hπ

/-- The words read from tape A at rows `< m` are words `0, 1, …` of `x̄`. -/
theorem readsA_eq (m : ℕ) (hm : m ≤ 2 ^ τ - 1) :
    ((List.range m).filterMap fun i => (M.readAt true (cfgT M b) i).bind fun v => v.map Ram.wordBits).flatten =
      ((List.range (cntA M b m)).map fun q => Ram.wordBits (ShortPCP.wordOf M.w xbar q)).flatten ∧
      cntA M b m ≤ xbar.length / M.w := by
  induction m with
  | zero => simp [cntA]
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hmT : m + 1 < 2 ^ τ := by have := Nat.one_le_two_pow (n := τ); omega
    have e : ∀ (g : ℕ → Option (List Bool)), List.filterMap g [m] = (g m).toList := by
      intro g; cases h : g m <;> simp [h]
    rw [List.range_succ, List.filterMap_append, List.flatten_append, ih1, cntA_succ, e,
      readAt_cfg M kind τ xbar b halu hw hb true m hmT]
    simp only [if_true]
    cases ha : aAT M b m
    · have hnone : (if isRdA (insT M b m) = true then some (rdT M b m) else none).bind
          (fun v => v.map Ram.wordBits) = none := by
        unfold aAT at ha
        cases hr : isRdA (insT M b m) <;> simp_all
      simp [hnone, ih2]
    · obtain ⟨hlt, hrd⟩ := readA_word M kind τ xbar b halu hw hb hτw hlen π hπ m (by omega) ha
      have hA : isRdA (insT M b m) = true := by unfold aAT at ha; simp_all
      rw [cA_val M kind τ xbar b halu hw hb m (by omega)] at hlt hrd
      simp [hA, hrd, List.range_succ, hlt]

end Strings

omit halu hw hb in
theorem readsB_length (m : ℕ) (hm : ∀ i < m, M.readAt false (cfgT M b) i =
      if isRdB (insT M b i) then some (rdT M b i) else none) :
    (((List.range m).filterMap fun i => (M.readAt false (cfgT M b) i).bind fun v => v.map Ram.wordBits).flatten).length =
      cntB M b m * M.w := by
  induction m with
  | zero => simp [cntB]
  | succ m ih =>
    have e : ∀ (g : ℕ → Option (List Bool)), List.filterMap g [m] = (g m).toList := by
      intro g; cases h : g m <;> simp [h]
    rw [List.range_succ, List.filterMap_append, List.flatten_append, List.length_append,
      ih (fun i hi => hm i (by omega)), cntB_succ, e, hm m (by omega)]
    cases ha : aBT M b m
    · have hnone : (if isRdB (insT M b m) = true then some (rdT M b m) else none).bind
          (fun v => v.map Ram.wordBits) = none := by
        unfold aBT at ha
        cases hr : isRdB (insT M b m) <;> simp_all
      simp [hnone]
    · have hB : isRdB (insT M b m) = true := by unfold aBT at ha; simp_all
      have hsome : (rdT M b m).isSome = true := by unfold aBT at ha; cases h : rdT M b m <;> simp_all
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
      simp [hB, hv, Ram.wordBits]
      ring

end Sound

/-- **`thm:trace` (⇒).** A Boolean assignment satisfying `ET(M, τ, x̄)` gives `(x̄, 1^τ, 1^τ) ∈ BH_RAM(M)`. -/
theorem holdsB_sound (halu : ∀ op, M.alu op = (kind op).fn) (hw2 : M.w = 2 ^ Nat.log 2 M.w) (hτ : 1 ≤ τ)
    (hωτ : Nat.log 2 M.w ≤ τ) (hτw : τ < M.w) (hlen : xbar.length ≤ 2 ^ τ)
    (hb : HoldsB M kind τ xbar b) : M.BHRAM xbar τ τ := by
  have hw : 1 ≤ M.w := by rw [hw2]; exact Nat.one_le_two_pow
  obtain ⟨π, hπ⟩ := hb.2.2.2.2.2.2.2.2.2.2
  have hT1 : 1 ≤ 2 ^ τ := Nat.one_le_two_pow
  set T := 2 ^ τ with hT
  set S : ℕ → M.Config := cfgT M b with hS
  -- the read strings
  have hreadB : ∀ i < T - 1, M.readAt false S i = if isRdB (insT M b i) then some (rdT M b i) else none := by
    intro i hi
    have := readAt_cfg M kind τ xbar b halu hw hb false i (by omega)
    simpa using this
  have hstrB := readsB_length M b (T - 1) hreadB
  obtain ⟨hstrA, hcntA⟩ := readsA_eq M kind τ xbar b halu hw hb hτw hlen π hπ (T - 1) le_rfl
  obtain ⟨-, hcntB⟩ := cB_val M kind τ xbar b halu hw hb (T - 1) (by omega)
  have hinit : M.Initial (S 0) := by
    refine ⟨?_, fun r => ?_⟩
    · simp only [hS, cfgT, decCur]
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      rw [getLsbD_bvOf]
      simp only [hj, decide_true, Bool.true_and]
      simpa [TCopy.dst] using hb.2.1 (.pc j) hj
    · simp only [hS, cfgT, decCur]
      have hf : b.timeRead 0 (.inl (.fl r.val)) = false := hb.2.1 (.fl r.val) r.isLt
      rw [hf]
      simp only [Bool.false_eq_true, if_false, Option.some.injEq]
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      rw [getLsbD_bvOf]
      simp only [hj, decide_true, Bool.true_and]
      simpa [TCopy.dst] using hb.2.1 (.rg r.val j) ⟨r.isLt, hj⟩
  have hstep : ∀ i, i + 1 < T → M.Step (S i) (memSeq M b i) (S (i + 1)) (memSeq M b (i + 1)) := by
    intro i h
    have := step_of_row (cfgT M b i) (insT M b i) (mvT M b i) (rdT M b i) (memSeq M b i)
      (row_at M kind τ xbar b halu hw hb i (by omega)).1 (not_out M kind τ xbar b halu hw hb i h)
      (load_reads M kind τ xbar b halu hw hb hτw hlen π hπ i (by omega))
    rw [← cfg_succ M kind τ xbar b halu hw hb i h] at this
    exact this
  refine ⟨hτ, hτ, hlen, M.readString false T S, ?_, S, ⟨hinit, ?_⟩, ⟨?_, memSeq M b, rfl, hstep⟩,
    ⟨?_, List.prefix_refl _⟩, ?_⟩
  · -- `|y| ≤ 2^τ` (`lem:trace-counters`)
    show (((List.range (T - 1)).filterMap fun i => (M.readAt false S i).bind fun v => v.map Ram.wordBits).flatten).length ≤ T
    rw [hstrB]
    have h1 : cntB M b (T - 1) * M.w ≤ 2 ^ (dims M τ).β * M.w := Nat.mul_le_mul_right _ hcntB
    have h2 : 2 ^ (dims M τ).β * M.w = 2 ^ τ := by
      rw [hw2]; simp only [dims]; rw [← pow_add, Nat.sub_add_cancel hωτ]
    omega
  · -- `S^{T−1}` is accepting (B3)
    unfold Ram.AcceptingConfig
    rw [(row_at M kind τ xbar b halu hw hb (T - 1) (by omega)).1, accepting_last M kind τ xbar b halu hw hb]
  · -- the transitions (the bounded-run definition `def:ram`)
    intro i hi
    unfold Ram.transition
    rw [if_pos]
    rcases Nat.lt_or_ge (i + 1) T with h | h
    · left
      rw [Nat.mod_eq_of_lt h]
      exact ⟨memSeq M b i, memSeq M b (i + 1), hstep i h⟩
    · right
      have hiT : i = T - 1 := by omega
      rw [show (i + 1) % T = 0 by rw [show i + 1 = T by omega, Nat.mod_self]]
      refine ⟨⟨true, ?_⟩, hinit⟩
      rw [hiT, (row_at M kind τ xbar b halu hw hb (T - 1) (by omega)).1,
        accepting_last M kind τ xbar b halu hw hb]
  · -- tape A: the words read are words `0, 1, …` of `x̄`, a prefix (Lemmas 3a.6, 3a.7)
    show ((List.range (T - 1)).filterMap fun i => (M.readAt true S i).bind fun v => v.map Ram.wordBits).flatten <+: xbar
    rw [hstrA, ShortPCP.words_prefix M.w xbar _ (by
      have := Nat.div_mul_le_self xbar.length M.w
      have h2 : cntA M b (T - 1) * M.w ≤ xbar.length / M.w * M.w := Nat.mul_le_mul_right _ hcntA
      omega)]
    exact List.take_prefix _ _
  · -- at most `2^τ` addresses (the bounded-run definition `def:ram`)
    unfold Ram.addressCount
    exact (List.toFinset_card_le _).trans ((List.length_filterMap_le _ _).trans (by simp))

end NearCubicGates.Adapters.RAMTrace
