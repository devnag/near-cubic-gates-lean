import SourceAdapters.RAMTrace.RowSem

/-!
# `lem:trace-step`, soundness: a time row satisfying (T1)–(T10) is the canonical row of its inputs

`app:event-trace` `lem:trace-step` (i)–(iii) with the uniqueness part of `lem:trace-gadgets`. For a Boolean row `v` satisfying every equation of
(T1)–(T10): the decoded program counter is inside the code and `e`, `o` are its indicator and prefix-or
(`row_decode`); every slot of the slot catalog of `def:event-trace` equals the slot of `canon` at the row's inputs — the decoded
configuration, the instruction `I_pc`, the memory value `MV`, the tape value (`#` if `RF`), the time stamp and the
two counters (`row_sound`). In particular `dec(nxt) = rowSucc …` and the record is the one of (T9).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMTrace

open NearCubicGates.Adapters.ACSP Expr BitVec

variable {M : Ram}

/-! ## Boolean rearrangements -/

theorem xor2_false (a b : Bool) : Bool.xor a b = false ↔ a = b := by cases a <;> cases b <;> simp

theorem xor3_false (a b c : Bool) : Bool.xor (Bool.xor a b) c = false ↔ a = Bool.xor b c := by
  cases a <;> cases b <;> cases c <;> simp

theorem xor4_false (a b c d : Bool) :
    Bool.xor (Bool.xor (Bool.xor a b) c) d = false ↔ a = Bool.xor (Bool.xor b c) d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp

theorem atLeastTwo_false_mid (a c : Bool) : Bool.atLeastTwo a false c = (a && c) := by
  cases a <;> cases c <;> rfl

/-! ## The inputs of a row -/

/-- The memory value `MV`. -/
def mvOf (v : TVar → Bool) : BitVec M.w := bvOf M.w fun j => v (.inl (.MV j))

/-- The tape value: `#` if `RF`, the word `RV` otherwise. -/
def rdOf (v : TVar → Bool) : Option (BitVec M.w) :=
  if v (.inl .RF) then none else some (bvOf M.w fun j => v (.inl (.RV j)))

/-- The time stamp (the record's `ts`). -/
def tsOf (τ : ℕ) (v : TVar → Bool) : BitVec τ := bvOf τ fun j => v (.inr (.ts, j))

/-- The tape-A counter. -/
def cAOf (τ : ℕ) (v : TVar → Bool) : BitVec τ := bvOf τ fun j => v (.inl (.cA j))

/-- The tape-B counter (`β + 1` bits). -/
def cBOf (n : ℕ) (v : TVar → Bool) : BitVec n := bvOf n fun j => v (.inl (.cB j))

theorem evalB_caE (v : TVar → Bool) (j : ℕ) : (caE j).evalB v = cin (fun i => v (.inl (.CA i))) false j := by
  unfold caE cin; split_ifs <;> simp

theorem evalB_boE (v : TVar → Bool) (j : ℕ) : (boE j).evalB v = cin (fun i => v (.inl (.BO i))) false j := by
  unfold boE cin; split_ifs <;> simp

theorem evalB_tcE (v : TVar → Bool) (j : ℕ) : (tcE j).evalB v = cin (fun i => v (.inl (.TC i))) true j := by
  unfold tcE cin; split_ifs <;> simp

theorem evalB_acE (v : TVar → Bool) (j : ℕ) :
    (acE j).evalB v = cin (fun i => v (.inl (.AC i))) (v (.inl .aA)) j := by
  unfold acE cin; split_ifs <;> simp

theorem evalB_bcE (v : TVar → Bool) (j : ℕ) :
    (bcE j).evalB v = cin (fun i => v (.inl (.BC i))) (v (.inl .aB)) j := by
  unfold bcE cin; split_ifs <;> simp

theorem prefixOr_congr (s s' : ℕ → Bool) (j : ℕ) (hs : ∀ i ≤ j, s i = s' i) : prefixOr s j = prefixOr s' j := by
  rw [Bool.eq_iff_iff, prefixOr_iff, prefixOr_iff]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by rw [← hs i hi]; exact h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by rw [hs i hi]; exact h⟩

/-- An incrementer chain (T10): `s j = c_j + k_j`, `k_{j+1} = c_j · k_j`, `k_0 = c0`, is the ripple sum `c + c0`. -/
theorem incr_chain {ν : ℕ} (c : BitVec ν) (c0 : Bool) (s k : ℕ → Bool) (n m : ℕ) (hn : n ≤ ν) (hnm : n ≤ m + 1)
    (_hm : m ≤ ν) (hs : ∀ j < n, s j = Bool.xor (c.getLsbD j) (cin k c0 j))
    (hk : ∀ j < m, k j = (c.getLsbD j && cin k c0 j)) :
    (∀ j < n, s j = (c + 0#ν + setWidth ν (ofBool c0)).getLsbD j) ∧ ∀ j < m, k j = carry (j + 1) c 0#ν c0 := by
  apply (ripple_iff c 0#ν c0 s k n m hn hnm).mp
  constructor
  · intro j hj; rw [hs j hj]; simp
  · intro j hj; rw [hk j hj]; simp

section Sound

variable (kind : Fin M.ops → AluOp) (τ : ℕ) (v : TVar → Bool)
  (h : ∀ q : TEq, q.Active (dims M τ) → (timeEq M kind τ q).evalB v = false)
include h

/-! ## Decoding (`lem:trace-step` (i), (ii)) -/

theorem row_e_o : ∃ pcv < M.code.length, ∀ p < M.code.length,
    v (.inl (.e p)) = decide (p = pcv) ∧ v (.inl (.o p)) = decide (pcv ≤ p) := by
  have hL := M.codeNonempty
  apply (decode_iff M.code.length hL (fun p => v (.inl (.e p))) (fun p => v (.inl (.o p)))).mp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := h .decFirst trivial
    simpa [timeEq, xor2_false] using this
  · intro p hp1 hp
    have := h (.decRec p) ⟨hp1, hp⟩
    simpa [timeEq, xor3_false] using this
  · intro p hp1 hp
    have := h (.decExcl p) ⟨hp1, hp⟩
    simpa [timeEq] using this
  · have := h .decLast trivial
    simpa [timeEq] using this

theorem row_T1 : ∀ r < M.k, ∀ j < M.w, (v (.inl (.fl r)) && v (.inl (.rg r j))) = false := by
  intro r hr j hj
  have := h (.flag r j) ⟨hr, hj⟩
  simpa [timeEq] using this

/-- **Decoding.** The decoded `pc` is a position `pcv < L` of the code, `e` is its indicator and `o` its prefix-or. -/
theorem row_decode : (decCur v : M.Config).pc.toNat < M.code.length ∧
    ∀ p < M.code.length, v (.inl (.e p)) = decide (p = (decCur v : M.Config).pc.toNat) ∧
      v (.inl (.o p)) = decide ((decCur v : M.Config).pc.toNat ≤ p) := by
  obtain ⟨pcv, hpc, hE⟩ := row_e_o kind τ v h
  have hbits : ∀ j < M.w, v (.inl (.pc j)) = pcv.testBit j := by
    intro j hj
    have := h (.decPc j) hj
    simp only [timeEq, evalB_add, evalB_var] at this
    rw [evalB_decPcSum v pcv hpc (fun p hp => (hE p hp).1) j] at this
    exact (xor2_false _ _).mp this
  have hpcv : (decCur v : M.Config).pc = BitVec.ofNat M.w pcv := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [decCur, getLsbD_bvOf, hj, decide_true, Bool.true_and, BitVec.getLsbD_ofNat]
    exact hbits j hj
  have hlt : pcv < 2 ^ M.w := lt_of_lt_of_le hpc M.codeFits
  have htn : (decCur v : M.Config).pc.toNat = pcv := by
    rw [hpcv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [htn]
  exact ⟨hpc, hE⟩

/-! ## Operand buses (T3) and the arithmetic unit (T4) -/

section Buses

variable (pcv : ℕ) (hpc : pcv < M.code.length)
  (hE : ∀ p < M.code.length, v (.inl (.e p)) = decide (p = pcv))
include hpc hE

theorem row_X : ∀ j < M.w, v (.inl (.X j)) = (xWord (decCur v) (M.code[pcv]'hpc)).getLsbD j := by
  intro j hj
  have := h (.opX j) hj
  simp only [timeEq, evalB_add, evalB_var] at this
  rw [evalB_eDot v pcv hpc hE, evalB_srcX v (row_T1 kind τ v h) _ j hj] at this
  exact (xor2_false _ _).mp this

theorem row_Y : ∀ j < M.w, v (.inl (.Y j)) = (yWord (decCur v) (M.code[pcv]'hpc)).getLsbD j := by
  intro j hj
  have := h (.opY j) hj
  simp only [timeEq, evalB_add, evalB_var] at this
  rw [evalB_eDot v pcv hpc hE, evalB_srcY v (row_T1 kind τ v h) _ j hj] at this
  exact (xor2_false _ _).mp this

theorem row_XF : v (.inl .XF) = xfBit (decCur v) (M.code[pcv]'hpc) := by
  have := h .opXF trivial
  simp only [timeEq, evalB_add, evalB_var] at this
  rw [evalB_eDot v pcv hpc hE, evalB_srcXF v] at this
  exact (xor2_false _ _).mp this

end Buses

section ALU

variable (X Y : BitVec M.w) (hX : ∀ j < M.w, v (.inl (.X j)) = X.getLsbD j)
  (hY : ∀ j < M.w, v (.inl (.Y j)) = Y.getLsbD j)
include hX hY

theorem row_adder : (∀ j < M.w, v (.inl (.AD j)) = (X + Y).getLsbD j) ∧
    ∀ j, j + 1 < M.w → v (.inl (.CA j)) = carry (j + 1) X Y false := by
  apply (adder_iff X Y (fun j => v (.inl (.AD j))) (fun j => v (.inl (.CA j)))).mp
  constructor
  · intro j hj
    have := h (.sumAD j) hj
    simp only [timeEq, evalB_add, evalB_var, evalB_caE] at this
    rw [xor4_false, hX j hj, hY j hj] at this
    exact this
  · intro j hj
    have := h (.carry j) hj
    simp only [timeEq, evalB_add, evalB_var, evalB_caE, evalB_maj] at this
    rw [xor2_false, hX j (by omega), hY j (by omega), maj_eq] at this
    exact this

theorem row_subtractor : (∀ j < M.w, v (.inl (.SB j)) = (X - Y).getLsbD j) ∧
    ∀ j < M.w, v (.inl (.BO j)) = !carry (j + 1) X (~~~Y) true := by
  apply (subtractor_iff X Y (fun j => v (.inl (.SB j))) (fun j => v (.inl (.BO j)))).mp
  constructor
  · intro j hj
    have := h (.sumSB j) hj
    simp only [timeEq, evalB_add, evalB_var, evalB_boE] at this
    rw [xor4_false, hX j hj, hY j hj] at this
    exact this
  · intro j hj
    have := h (.borrow j) hj
    simp only [timeEq, evalB_add, evalB_var, evalB_boE, evalB_mul, evalB_compl] at this
    rw [xor2_false, hX j hj, hY j hj] at this
    exact this

theorem row_and : ∀ j < M.w, v (.inl (.AN j)) = (X &&& Y).getLsbD j := by
  intro j hj
  have := h (.andAN j) hj
  simp only [timeEq, evalB_add, evalB_var, evalB_mul] at this
  rw [xor2_false, hX j hj, hY j hj] at this
  rw [this, getLsbD_and]

theorem row_zero : ∀ j < M.w, v (.inl (.OZ j)) = prefixOr (X - Y).getLsbD j := by
  have hsb := (row_subtractor kind τ v h X Y hX hY).1
  have hchain := (prefixOr_chain_iff (fun j => v (.inl (.SB j))) (fun j => v (.inl (.OZ j))) M.w).mp ⟨?_, ?_⟩
  · intro j hj
    have hc : v (.inl (.OZ j)) = prefixOr (fun j => v (.inl (.SB j))) j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0; rw [hchain.1, prefixOr_zero]
      · exact hchain.2 j h0 hj
    rw [hc]
    exact prefixOr_congr _ _ j fun i hi => hsb i (by omega)
  · have := h .ozFirst trivial
    simp only [timeEq, evalB_add, evalB_var] at this
    exact (xor2_false _ _).mp this
  · intro j hj1 hj
    have := h (.ozRec j) ⟨hj1, hj⟩
    simp only [timeEq, evalB_add, evalB_var, evalB_mul] at this
    exact (xor2_false _ _).mp this

theorem row_gt (hw : 1 ≤ M.w) :
    v (.inl .GT) = (carry (M.w - 1 + 1) X (~~~Y) true && prefixOr (X - Y).getLsbD (M.w - 1)) := by
  have := h .gt trivial
  simp only [timeEq, evalB_add, evalB_var, evalB_mul, evalB_compl] at this
  rw [xor2_false, (row_subtractor kind τ v h X Y hX hY).2 (M.w - 1) (by omega),
    row_zero kind τ v h X Y hX hY (M.w - 1) (by omega), Bool.not_not] at this
  exact this

end ALU

/-! ## The whole row -/

omit h in
theorem regFlag_decCur (r : ℕ) (hr : r < M.k) : regFlag (decCur v : M.Config) r = v (.inl (.fl r)) := by
  unfold regFlag decCur
  simp only [hr, dite_true]
  cases v (.inl (.fl r)) <;> simp

theorem regBit_decCur (r : ℕ) (hr : r < M.k) (j : ℕ) (hj : j < M.w) :
    regBit (decCur v : M.Config) r j = v (.inl (.rg r j)) := by
  unfold regBit
  simp only [hr, dite_true]
  exact decCur_val_reg v (row_T1 kind τ v h) ⟨r, hr⟩ j hj

/-- The row facts at a fixed decoded position `pcv` and instruction `I = I_pcv`. -/
theorem row_facts (halu : ∀ op, M.alu op = (kind op).fn) (hw : 1 ≤ M.w) (pcv : ℕ) (hpc : pcv < M.code.length)
    (hE1 : ∀ p < M.code.length, v (.inl (.e p)) = decide (p = pcv))
    (hpcS : (decCur v : M.Config).pc.toNat = pcv) (I : Instr M.w M.k M.ops) (hI : M.code[pcv]'hpc = I) :
    (∀ j < M.w, v (.inl (.X j)) = (xWord (decCur v) I).getLsbD j) ∧
    (∀ j < M.w, v (.inl (.Y j)) = (yWord (decCur v) I).getLsbD j) ∧
    v (.inl .XF) = xfBit (decCur v) I ∧
    (∀ j < M.w, v (.inl (.Z j)) = (zWord kind (decCur v) (mvOf v) (rdOf v) I).getLsbD j) ∧
    v (.inl .ZF) = zfBit (rdOf v) I ∧
    (∀ r < M.k, ∀ j < M.w, v (.inl (.nrg r j)) = regBit (rowSucc (decCur v) (mvOf v) (rdOf v) I) r j) ∧
    (∀ r < M.k, v (.inl (.nfl r)) = regFlag (rowSucc (decCur v) (mvOf v) (rdOf v) I) r) ∧
    (∀ j < M.w, v (.inl (.npc j)) = (rowSucc (decCur v) (mvOf v) (rdOf v) I).pc.getLsbD j) ∧
    v (.inl .aA) = (isRdA I && !(rdOf v : Option (BitVec M.w)).isNone) ∧
    v (.inl .aB) = (isRdB I && !(rdOf v : Option (BitVec M.w)).isNone) ∧
    v (.inl .RF) = (rdOf v : Option (BitVec M.w)).isNone ∧
    (∀ j < M.w, v (.inl (.RV j)) = ((rdOf v : Option (BitVec M.w)).getD 0).getLsbD j) ∧
    (∀ j < M.w, v (.inl (.MV j)) = (mvOf v : BitVec M.w).getLsbD j) ∧
    (∀ Q : Instr M.w M.k M.ops → Bool, (eSet M Q).evalB v = Q I) := by
  have hESet : ∀ Q : Instr M.w M.k M.ops → Bool, (eSet M Q).evalB v = Q I := by
    intro Q; rw [evalB_eSet v pcv hpc hE1, hI]
  have hT1 := row_T1 kind τ v h
  have hX : ∀ j < M.w, v (.inl (.X j)) = (xWord (decCur v) I).getLsbD j := by
    rw [← hI]; exact row_X kind τ v h pcv hpc hE1
  have hY : ∀ j < M.w, v (.inl (.Y j)) = (yWord (decCur v) I).getLsbD j := by
    rw [← hI]; exact row_Y kind τ v h pcv hpc hE1
  have hXF : v (.inl .XF) = xfBit (decCur v) I := by
    rw [← hI]; exact row_XF kind τ v h pcv hpc hE1
  obtain ⟨hAD, -⟩ := row_adder kind τ v h _ _ hX hY
  obtain ⟨hSB, hBO⟩ := row_subtractor kind τ v h _ _ hX hY
  have hAN := row_and kind τ v h _ _ hX hY
  have hOZ := row_zero kind τ v h _ _ hX hY
  have hGT := row_gt kind τ v h _ _ hX hY hw
  have hMV : ∀ j < M.w, v (.inl (.MV j)) = (mvOf v : BitVec M.w).getLsbD j := by
    intro j hj; simp [mvOf, hj]
  have hRF : v (.inl .RF) = (rdOf v : Option (BitVec M.w)).isNone := by
    simp only [rdOf]; cases v (.inl .RF) <;> simp
  have hRV : ∀ j < M.w, v (.inl (.RV j)) = ((rdOf v : Option (BitVec M.w)).getD 0).getLsbD j := by
    intro j hj
    have := h (.rfFlag j) hj
    simp only [timeEq, evalB_mul, evalB_var] at this
    simp only [rdOf]
    by_cases hf : v (.inl .RF) = true
    · rw [hf, Bool.true_and] at this; simp [hf, this]
    · simp only [Bool.not_eq_true] at hf; simp [hf, hj]
  have hbo := canon_bo_gt hw (xWord (decCur v) I) (yWord (decCur v) I)
  -- (T6) result
  have hZ : ∀ j < M.w, v (.inl (.Z j)) = (zWord kind (decCur v) (mvOf v) (rdOf v) I).getLsbD j := by
    intro j hj
    have := h (.res j) hj
    simp only [timeEq, evalB_add, evalB_var, evalB_sum, List.foldr, evalB_mul, hESet] at this
    rw [xor2_false] at this
    rw [this, hAD j hj, hSB j hj, hAN j hj, hMV j hj, hRV j hj]
    have hcmp : (cmpE M j).evalB v = (cmpWord (xWord (decCur v) I) (yWord (decCur v) I)).getLsbD j := by
      rw [cmpWord_getLsbD hw _ _ j hj]
      unfold cmpE
      by_cases hj0 : j = 0
      · simp only [hj0, if_true, evalB_add, evalB_var]
        rw [hBO (M.w - 1) (by omega), hGT, hbo.1, hbo.2]
      · simp only [hj0, if_false, evalB_var]
        rw [hGT, hbo.2]
    rw [hcmp]
    have hxf : (if j = 0 then Expr.mul (eSet M isEof) (tv .XF) else (zero : Expr TVar)).evalB v =
        (if j = 0 then (isEof I && xfBit (decCur v) I) else false) := by
      split_ifs <;> simp [hESet, hXF]
    rw [hxf]
    cases I with
    | arith op i x y =>
      rcases hk : kind op <;> simp [isAr, hk, isLd, isRd, isRdA, isRdB, isEof, zWord, AluOp.fn, xWord, yWord]
    | iseof i j' =>
      by_cases hj0 : j = 0
      · subst hj0
        have hw0 : 0 < M.w := by omega
        cases hr : (decCur v : M.Config).regs j' <;>
          simp [isAr, isLd, isRd, isRdA, isRdB, isEof, zWord, xfBit, hr, hw0]
      · simp [isAr, isLd, isRd, isRdA, isRdB, zWord, hj0]
        split_ifs <;> simp [hj0]
    | _ => simp [isAr, isLd, isRd, isRdA, isRdB, isEof, zWord, xfBit]
  have hZF : v (.inl .ZF) = zfBit (rdOf v) I := by
    have := h .resF trivial
    simp only [timeEq, evalB_add, evalB_var, evalB_mul, hESet] at this
    rw [xor2_false, hRF] at this
    rw [this]
    cases I <;> simp [isRd, isRdA, isRdB, zfBit]
  -- (T7) registers, (T8) program counter
  have hnrg : ∀ r < M.k, ∀ j < M.w,
      v (.inl (.nrg r j)) = regBit (rowSucc (decCur v) (mvOf v) (rdOf v) I) r j := by
    intro r hr j hj
    have := h (.reg r j) ⟨hr, hj⟩
    simp only [timeEq, evalB_add, evalB_var, evalB_mul, evalB_compl, hESet] at this
    rw [xor2_false, hZ j hj, ← regBit_decCur kind τ v h r hr j hj] at this
    rw [this, regBit_rowSucc kind halu _ _ _ I r j hr]
    cases writes r I <;> simp
  have hnfl : ∀ r < M.k, v (.inl (.nfl r)) = regFlag (rowSucc (decCur v) (mvOf v) (rdOf v) I) r := by
    intro r hr
    have := h (.regF r) hr
    simp only [timeEq, evalB_add, evalB_var, evalB_mul, evalB_compl, hESet] at this
    rw [xor2_false, hZF, ← regFlag_decCur v r hr] at this
    rw [this, regFlag_rowSucc _ _ _ I r hr]
    cases writes r I <;> simp
  have hSpc : (decCur v : M.Config).pc = BitVec.ofNat M.w pcv := by
    rw [← hpcS, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hnpc : ∀ j < M.w, v (.inl (.npc j)) = (rowSucc (decCur v) (mvOf v) (rdOf v) I).pc.getLsbD j := by
    intro j hj
    have := h (.pcNext j) hj
    simp only [timeEq, evalB_add, evalB_var] at this
    rw [evalB_pcSum v pcv hpc hE1, hI, evalB_pcTerm_self v pcv I j (by simp [hE1 pcv hpc]), xor2_false,
      hOZ (M.w - 1) (by omega)] at this
    rw [this, rowSucc_pc_bit _ _ _ I pcv hSpc hw j hj]
  -- (T10) activities
  have haA : v (.inl .aA) = (isRdA I && !(rdOf v : Option (BitVec M.w)).isNone) := by
    have := h .aA trivial
    simp only [timeEq, evalB_add, evalB_var, evalB_mul, evalB_compl, hESet] at this
    rw [xor2_false, hRF] at this; exact this
  have haB : v (.inl .aB) = (isRdB I && !(rdOf v : Option (BitVec M.w)).isNone) := by
    have := h .aB trivial
    simp only [timeEq, evalB_add, evalB_var, evalB_mul, evalB_compl, hESet] at this
    rw [xor2_false, hRF] at this; exact this
  exact ⟨hX, hY, hXF, hZ, hZF, hnrg, hnfl, hnpc, haA, haB, hRF, hRV, hMV, hESet⟩


/-- **`lem:trace-step` + the uniqueness part of `lem:trace-gadgets`, soundness of one time row.** A Boolean row satisfying (T1)–(T10) decodes to an
instruction `I = I_pc` inside the code; every slot of the slot catalog of `def:event-trace` is the canonical row's slot at the row's inputs
(so `dec(nxt)` is `rowSucc` of `dec(cur)` under `I` with the row's access, and the record is the one of (T9)); a
`store` row stores `MV = Y`; and the witness bound `aB · cB[β] = 0` holds. -/
theorem row_sound (halu : ∀ op, M.alu op = (kind op).fn) (hw : 1 ≤ M.w) :
    ∃ I, M.instrAt (decCur v : M.Config).pc = some I ∧
      (∀ s : TVar, s.Active (dims M τ) →
        v s = canon kind τ (decCur v) I (mvOf v) (rdOf v) (tsOf τ v) (cAOf τ v) (cBOf ((dims M τ).β + 1) v) s) ∧
      (isSt I = true → (mvOf v : BitVec M.w) = yWord (decCur v) I) ∧
      ((isRdB I && !(rdOf v : Option (BitVec M.w)).isNone) &&
        (cBOf ((dims M τ).β + 1) v).getLsbD (dims M τ).β) = false := by
  obtain ⟨hpc, hE⟩ := row_decode kind τ v h
  have hE1 : ∀ p < M.code.length, v (.inl (.e p)) = decide (p = (decCur v : M.Config).pc.toNat) :=
    fun p hp => (hE p hp).1
  obtain ⟨hX, hY, hXF, hZ, hZF, hnrg, hnfl, hnpc, haA, haB, hRF, hRV, hMV, hESet⟩ :=
    row_facts kind τ v h halu hw _ hpc hE1 rfl _ rfl
  set I := M.code[(decCur v : M.Config).pc.toNat]'hpc with hIdef
  refine ⟨I, by simp [Ram.instrAt, hIdef], ?_, ?_, ?_⟩
  rotate_left
  · -- (T5) store
    intro hst
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have := h (.store j) hj
    simp only [timeEq, evalB_mul, evalB_add, evalB_var, hESet, hst, Bool.true_and] at this
    rw [xor2_false, hMV j hj, hY j hj] at this
    exact this
  · -- (T10) witness bound
    have := h .bound trivial
    simp only [timeEq, evalB_mul, evalB_var] at this
    rw [haB] at this
    have hcb : v (.inl (.cB (dims M τ).β)) = (cBOf ((dims M τ).β + 1) v).getLsbD (dims M τ).β := by
      simp [cBOf]
    rw [← hcb]; exact this
  obtain ⟨hAD, hCA⟩ := row_adder kind τ v h _ _ hX hY
  obtain ⟨hSB, hBO⟩ := row_subtractor kind τ v h _ _ hX hY
  have hAN := row_and kind τ v h _ _ hX hY
  have hOZ := row_zero kind τ v h _ _ hX hY
  have hGT := row_gt kind τ v h _ _ hX hY hw
  -- (T10) incrementers
  have hts : ∀ j < τ, v (.inr (.ts, j)) = (tsOf τ v).getLsbD j := by intro j hj; simp [tsOf, hj]
  have hcA : ∀ j < τ, v (.inl (.cA j)) = (cAOf τ v).getLsbD j := by intro j hj; simp [cAOf, hj]
  have hcB : ∀ j < (dims M τ).β + 1, v (.inl (.cB j)) = (cBOf ((dims M τ).β + 1) v).getLsbD j := by
    intro j hj; simp [cBOf, hj]
  obtain ⟨hTSN, hTC⟩ := incr_chain (tsOf τ v) true (fun j => v (.inl (.TSN j))) (fun j => v (.inl (.TC j)))
    τ (τ - 1) le_rfl (by omega) (by omega)
    (fun j hj => by
      have := h (.tsn j) hj
      simp only [timeEq, evalB_add, evalB_var, evalB_tcE] at this
      rw [xor3_false, hts j hj] at this; exact this)
    (fun j hj => by
      have := h (.tc j) (by simp only [TEq.Active, dims]; omega)
      simp only [timeEq, evalB_add, evalB_mul, evalB_var, evalB_tcE] at this
      rw [xor2_false, hts j (by omega)] at this; exact this)
  obtain ⟨hcAN, hAC⟩ := incr_chain (cAOf τ v) (v (.inl .aA)) (fun j => v (.inl (.ncA j)))
    (fun j => v (.inl (.AC j))) τ (τ - 1) le_rfl (by omega) (by omega)
    (fun j hj => by
      have := h (.can j) hj
      simp only [timeEq, evalB_add, evalB_var, evalB_acE] at this
      rw [xor3_false, hcA j hj] at this; exact this)
    (fun j hj => by
      have := h (.ac j) (by simp only [TEq.Active, dims]; omega)
      simp only [timeEq, evalB_add, evalB_mul, evalB_var, evalB_acE] at this
      rw [xor2_false, hcA j (by omega)] at this; exact this)
  obtain ⟨hcBN, hBC⟩ := incr_chain (cBOf ((dims M τ).β + 1) v) (v (.inl .aB)) (fun j => v (.inl (.ncB j)))
    (fun j => v (.inl (.BC j))) ((dims M τ).β + 1) (dims M τ).β le_rfl le_rfl (by omega)
    (fun j hj => by
      have := h (.cbn j) (by simp only [TEq.Active]; omega)
      simp only [timeEq, evalB_add, evalB_var, evalB_bcE] at this
      rw [xor3_false, hcB j hj] at this; exact this)
    (fun j hj => by
      have := h (.bc j) hj
      simp only [timeEq, evalB_add, evalB_mul, evalB_var, evalB_bcE] at this
      rw [xor2_false, hcB j (by omega)] at this; exact this)
  -- the slots
  intro s hs
  rcases s with s | ⟨f, j⟩
  · cases s with
    | pc j => simp [canon, decCur, show j < M.w from hs]
    | fl r => simp only [canon]; exact (regFlag_decCur v r hs).symm
    | rg r j => simp only [canon]; exact (regBit_decCur kind τ v h r hs.1 j hs.2).symm
    | e p => simp only [canon]; exact hE1 p hs
    | o p => simp only [canon]; exact (hE p hs).2
    | X j => simp only [canon]; exact hX j hs
    | XF => simp only [canon]; exact hXF
    | Y j => simp only [canon]; exact hY j hs
    | AD j => simp only [canon]; exact hAD j hs
    | CA j => simp only [canon]; exact hCA j hs
    | SB j => simp only [canon]; exact hSB j hs
    | BO j => simp only [canon]; exact hBO j hs
    | AN j => simp only [canon]; exact hAN j hs
    | OZ j => simp only [canon]; exact hOZ j hs
    | GT => simp only [canon]; exact hGT
    | Z j => simp only [canon]; exact hZ j hs
    | ZF => simp only [canon]; exact hZF
    | RV j => simp only [canon]; exact hRV j hs
    | RF => simp only [canon]; exact hRF
    | MV j => simp only [canon]; exact hMV j hs
    | TC j => simp only [canon]; exact hTC j (by have : j + 1 < τ := hs; omega)
    | cA j => simp only [canon]; exact hcA j hs
    | cB j => simp only [canon]; exact hcB j (by have : j ≤ (dims M τ).β := hs; omega)
    | AC j => simp only [canon]; rw [← haA]; exact hAC j (by have : j + 1 < τ := hs; omega)
    | BC j => simp only [canon]; rw [← haB]; exact hBC j hs
    | aA => simp only [canon]; exact haA
    | aB => simp only [canon]; exact haB
    | npc j => simp only [canon]; exact hnpc j hs
    | nfl r => simp only [canon]; exact hnfl r hs
    | nrg r j => simp only [canon]; exact hnrg r hs.1 j hs.2
    | ncA j => simp only [canon]; rw [← haA]; exact hcAN j hs
    | ncB j => simp only [canon]; rw [← haB]; exact hcBN j (by have : j ≤ (dims M τ).β := hs; omega)
    | TSN j => simp only [canon]; exact hTSN j hs
  · have h1 : ∀ f' : RecField, f' ≠ .va → f' ≠ .ad → f' ≠ .ts → j < f'.width M.w τ → j = 0 := by
      intro f' h1 h2 h3 hj
      cases f' with
      | va => exact absurd rfl h1
      | ad => exact absurd rfl h2
      | ts => exact absurd rfl h3
      | _ => simp only [RecField.width] at hj; omega
    cases f with
    | act =>
      obtain rfl := h1 .act (by decide) (by decide) (by decide) hs
      have := h .recAct trivial
      simp only [timeEq, evalB_add, evalB_var, hESet] at this
      rw [xor2_false, haA] at this
      simp only [canon]; exact this
    | rgn =>
      obtain rfl := h1 .rgn (by decide) (by decide) (by decide) hs
      have := h .recRgn trivial
      simp only [timeEq, evalB_add, evalB_var] at this
      rw [xor2_false, haA] at this
      simp only [canon]; exact this
    | ad =>
      have hj : j < M.w := hs
      have := h (.recAd j) hj
      simp only [timeEq, evalB_add, evalB_var, evalB_mul, hESet] at this
      rw [xor2_false, hX j hj] at this
      simp only [canon]
      rw [this]
      by_cases hjt : j < τ
      · simp [hjt, haA, hcA j hjt]
      · simp [hjt]
    | ph =>
      obtain rfl := h1 .ph (by decide) (by decide) (by decide) hs
      have := h .recPh trivial
      simp only [timeEq, evalB_add, evalB_var, evalB_one] at this
      simp only [canon]
      cases hv : v (.inr (.ph, 0)) <;> simp [hv] at this ⊢
    | ts => simp only [canon]; exact hts j hs
    | va =>
      have hj : j < M.w := hs
      have := h (.recVa j) hj
      simp only [timeEq, evalB_add, evalB_var, evalB_mul, hESet] at this
      rw [xor2_false, hMV j hj, haA, hRV j hj] at this
      simp only [canon]; exact this
    | st =>
      obtain rfl := h1 .st (by decide) (by decide) (by decide) hs
      have := h .recSt trivial
      simp only [timeEq, evalB_add, evalB_var, hESet] at this
      rw [xor2_false] at this
      simp only [canon]; exact this

end Sound

end NearCubicGates.Adapters.RAMTrace
