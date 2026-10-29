import SourceAdapters.RAMTrace.RowSound

/-!
# `lem:trace-step`, existence: the canonical row satisfies (T1)–(T10)

`app:event-trace` `lem:trace-step` (iii), converse (existence of an extension), with the existence part of `lem:trace-gadgets`: for a configuration `S`
whose `pc` points into the code at `I`, any access values `mv`, `rd` (a `store` must store `MV = Y`), and counters
`ts`, `cA`, `cB` (a `readB` returning a word needs `cB[β] = 0`, the witness-bound guard), the canonical row
`canon S I mv rd ts cA cB` satisfies every equation of (T1)–(T10) (`row_complete`). Its decoded `cur` block is `S`
(`decCur_canon`) and its inputs are `mv`, `rd`, `ts`, `cA`, `cB` (`inputs_canon`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMTrace

open NearCubicGates.Adapters.ACSP Expr BitVec

variable {M : Ram} (kind : Fin M.ops → AluOp) (τ : ℕ)

omit τ in
/-- A configuration is determined by its `#` flags, register bits and `pc` bits. -/
theorem config_of_bits (S : M.Config) :
    ({ pc := bvOf M.w S.pc.getLsbD,
       regs := fun r => if regFlag S r.val then none else some (bvOf M.w (regBit S r.val)) } : M.Config) = S := by
  cases S with
  | mk pc regs =>
    simp only [bvOf_getLsbD]
    congr 1
    funext r
    simp only [regFlag, r.isLt, dite_true]
    cases hr : regs r with
    | none => simp
    | some x =>
      simp only [Option.isNone_some, Bool.false_eq_true, if_false, Option.some.injEq]
      have : (fun j => regBit ({ pc := pc, regs := regs } : M.Config) r.val j) = x.getLsbD := by
        funext j; simp [regBit, hr]
      rw [show regBit ({ pc := pc, regs := regs } : M.Config) r.val = x.getLsbD from this, bvOf_getLsbD]

theorem decCur_canon (S : M.Config) (I : Instr M.w M.k M.ops) (mv : BitVec M.w) (rd : Option (BitVec M.w))
    (ts cA : BitVec τ) (cB : BitVec ((dims M τ).β + 1)) :
    (decCur (canon kind τ S I mv rd ts cA cB) : M.Config) = S := by
  simp only [decCur, canon]
  exact config_of_bits S

theorem decNxt_canon (S : M.Config) (I : Instr M.w M.k M.ops) (mv : BitVec M.w) (rd : Option (BitVec M.w))
    (ts cA : BitVec τ) (cB : BitVec ((dims M τ).β + 1)) :
    (decNxt (canon kind τ S I mv rd ts cA cB) : M.Config) = rowSucc S mv rd I := by
  simp only [decNxt, canon]
  exact config_of_bits _

theorem inputs_canon (S : M.Config) (I : Instr M.w M.k M.ops) (mv : BitVec M.w) (rd : Option (BitVec M.w))
    (ts cA : BitVec τ) (cB : BitVec ((dims M τ).β + 1)) :
    (mvOf (canon kind τ S I mv rd ts cA cB) : BitVec M.w) = mv ∧
      (rdOf (canon kind τ S I mv rd ts cA cB) : Option (BitVec M.w)) = rd ∧
      tsOf τ (canon kind τ S I mv rd ts cA cB) = ts ∧ cAOf τ (canon kind τ S I mv rd ts cA cB) = cA ∧
      cBOf ((dims M τ).β + 1) (canon kind τ S I mv rd ts cA cB) = cB := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [mvOf, canon, bvOf_getLsbD]
  · simp only [rdOf, canon]
    cases rd <;> simp [bvOf_getLsbD]
  · simp [tsOf, canon, bvOf_getLsbD]
  · simp [cAOf, canon, bvOf_getLsbD]
  · simp [cBOf, canon, bvOf_getLsbD]

/-- **`lem:trace-step` (iii) existence + the existence part of `lem:trace-gadgets`.** The canonical row satisfies (T1)–(T10). -/
theorem row_complete (halu : ∀ op, M.alu op = (kind op).fn) (hw : 1 ≤ M.w) (S : M.Config)
    (I : Instr M.w M.k M.ops) (mv : BitVec M.w) (rd : Option (BitVec M.w)) (ts cA : BitVec τ)
    (cB : BitVec ((dims M τ).β + 1)) (hI : M.instrAt S.pc = some I) (hst : isSt I = true → mv = yWord S I)
    (hbound : ((isRdB I && !rd.isNone) && cB.getLsbD (dims M τ).β) = false) :
    ∀ q : TEq, q.Active (dims M τ) → (timeEq M kind τ q).evalB (canon kind τ S I mv rd ts cA cB) = false := by
  set v := canon kind τ S I mv rd ts cA cB with hv
  have hpc : S.pc.toNat < M.code.length := by
    unfold Ram.instrAt at hI
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hI
    exact absurd hI (by simp)
  have hIc : M.code[S.pc.toNat]'hpc = I := by
    unfold Ram.instrAt at hI
    rw [List.getElem?_eq_getElem hpc] at hI
    exact Option.some.inj hI
  have hE1 : ∀ p < M.code.length, v (.inl (.e p)) = decide (p = S.pc.toNat) := fun p _ => rfl
  have hESet : ∀ Q : Instr M.w M.k M.ops → Bool, (eSet M Q).evalB v = Q I := by
    intro Q; rw [evalB_eSet v _ hpc hE1, hIc]
  have hdec : (decCur v : M.Config) = S := decCur_canon kind τ S I mv rd ts cA cB
  have hT1 : ∀ r < M.k, ∀ j < M.w, (v (.inl (.fl r)) && v (.inl (.rg r j))) = false := by
    intro r hr j hj
    simp only [hv, canon, regFlag, regBit, hr, dite_true]
    cases S.regs ⟨r, hr⟩ <;> simp
  set X := xWord S I with hX
  set Y := yWord S I with hY
  have hbo := canon_bo_gt hw X Y
  have hadd := (adder_iff X Y (fun j => (X + Y).getLsbD j) (fun j => carry (j + 1) X Y false)).mpr
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hsub := (subtractor_iff X Y (fun j => (X - Y).getLsbD j) (fun j => !carry (j + 1) X (~~~Y) true)).mpr
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hoz := (prefixOr_chain_iff (fun j => (X - Y).getLsbD j) (fun j => prefixOr (X - Y).getLsbD j) M.w).mpr
    ⟨prefixOr_zero _, fun _ _ _ => rfl⟩
  have hSpc : S.pc = BitVec.ofNat M.w S.pc.toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  intro q hq
  cases q with
  | flag r j => simpa [timeEq] using hT1 r hq.1 j hq.2
  | decFirst =>
    simp only [timeEq, evalB_add, evalB_var, hv, canon]
    by_cases h0 : S.pc.toNat = 0
    · simp [h0]
    · simp [h0]; omega
  | decRec p =>
    obtain ⟨hp1, hp⟩ := hq
    simp only [timeEq, evalB_add, evalB_var, hv, canon]
    by_cases hpp : p = S.pc.toNat
    · subst hpp; simp; omega
    · by_cases hle : S.pc.toNat ≤ p - 1
      · simp [hpp, hle, show S.pc.toNat ≤ p by omega]
      · simp [hpp, hle, show ¬ S.pc.toNat ≤ p by omega]
  | decExcl p =>
    obtain ⟨hp1, hp⟩ := hq
    simp only [timeEq, evalB_mul, evalB_var, hv, canon]
    by_cases hpp : p = S.pc.toNat
    · subst hpp; simp; omega
    · simp [hpp]
  | decLast =>
    simp only [timeEq, evalB_add, evalB_var, evalB_one, hv, canon]
    simp; omega
  | decPc j =>
    simp only [timeEq, evalB_add, evalB_var]
    rw [evalB_decPcSum v _ hpc hE1 j, xor2_false]
    rfl
  | opX j =>
    simp only [timeEq, evalB_add, evalB_var]
    rw [evalB_eDot v _ hpc hE1, hIc, evalB_srcX v hT1 I j hq, hdec, xor2_false]
    rfl
  | opY j =>
    simp only [timeEq, evalB_add, evalB_var]
    rw [evalB_eDot v _ hpc hE1, hIc, evalB_srcY v hT1 I j hq, hdec, xor2_false]
    rfl
  | opXF =>
    simp only [timeEq, evalB_add, evalB_var]
    rw [evalB_eDot v _ hpc hE1, hIc, evalB_srcXF v I, hdec, xor2_false]
    rfl
  | sumAD j =>
    simp only [timeEq, evalB_add, evalB_var, evalB_caE]
    rw [xor4_false]
    exact hadd.1 j hq
  | carry j =>
    simp only [timeEq, evalB_add, evalB_var, evalB_caE, evalB_maj]
    rw [xor2_false, maj_eq]
    exact hadd.2 j hq
  | sumSB j =>
    simp only [timeEq, evalB_add, evalB_var, evalB_boE]
    rw [xor4_false]
    exact hsub.1 j hq
  | borrow j =>
    simp only [timeEq, evalB_add, evalB_var, evalB_boE, evalB_mul, evalB_compl]
    rw [xor2_false]
    exact hsub.2 j hq
  | andAN j =>
    simp only [timeEq, evalB_add, evalB_var, evalB_mul]
    rw [xor2_false]
    simp [hv, canon]
  | ozFirst =>
    simp only [timeEq, evalB_add, evalB_var]
    rw [xor2_false]
    exact hoz.1
  | ozRec j =>
    simp only [timeEq, evalB_add, evalB_var, evalB_mul]
    rw [xor2_false]
    exact hoz.2 j hq.1 hq.2
  | gt =>
    simp only [timeEq, evalB_add, evalB_var, evalB_mul, evalB_compl]
    rw [xor2_false]
    simp only [hv, canon, Bool.not_not]
  | rfFlag j =>
    simp only [timeEq, evalB_mul, evalB_var, hv, canon]
    cases rd <;> simp
  | store j =>
    simp only [timeEq, evalB_mul, evalB_add, evalB_var, hESet]
    cases hs : isSt I
    · simp
    · simp only [Bool.true_and]
      rw [xor2_false]
      show mv.getLsbD j = (yWord S I).getLsbD j
      rw [hst hs]
  | res j =>
    simp only [timeEq, evalB_add, evalB_var, evalB_sum, List.foldr, evalB_mul, hESet]
    rw [xor2_false]
    have hcmp : (cmpE M j).evalB v = (cmpWord X Y).getLsbD j := by
      rw [cmpWord_getLsbD hw X Y j hq]
      unfold cmpE
      by_cases hj0 : j = 0
      · simp only [hj0, if_true, evalB_add, evalB_var]
        simp only [hv, canon]
        rw [hbo.1, hbo.2]
      · simp only [hj0, if_false, evalB_var]
        simp only [hv, canon]
        rw [hbo.2]
    rw [hcmp]
    have hxf : (if j = 0 then Expr.mul (eSet M isEof) (tv .XF) else (zero : Expr TVar)).evalB v =
        (if j = 0 then (isEof I && xfBit S I) else false) := by
      split_ifs
      · simp only [evalB_mul, evalB_var, hESet]; rfl
      · rfl
    rw [hxf]
    simp only [hv, canon]
    cases I with
    | arith op i x y =>
      rcases hk : kind op <;> simp [isAr, hk, isLd, isRd, isRdA, isRdB, isEof, zWord, AluOp.fn, hX, hY, xWord,
        yWord]
    | iseof i j' =>
      by_cases hj0 : j = 0
      · subst hj0
        have hw0 : 0 < M.w := by omega
        cases hr : S.regs j' <;> simp [isAr, isLd, isRd, isRdA, isRdB, isEof, zWord, xfBit, hr, hw0]
      · simp [isAr, isLd, isRd, isRdA, isRdB, zWord, hj0]
        split_ifs <;> simp [hj0]
    | _ => simp [isAr, isLd, isRd, isRdA, isRdB, isEof, zWord, xfBit]
  | resF =>
    simp only [timeEq, evalB_add, evalB_var, evalB_mul, hESet]
    rw [xor2_false]
    simp only [hv, canon]
    cases I <;> simp [isRd, isRdA, isRdB, zfBit]
  | reg r j =>
    simp only [timeEq, evalB_add, evalB_var, evalB_mul, evalB_compl, hESet]
    rw [xor2_false]
    simp only [hv, canon]
    rw [regBit_rowSucc kind halu S mv rd I r j hq.1]
    cases writes r I <;> simp
  | regF r =>
    simp only [timeEq, evalB_add, evalB_var, evalB_mul, evalB_compl, hESet]
    rw [xor2_false]
    simp only [hv, canon]
    rw [regFlag_rowSucc S mv rd I r hq]
    cases writes r I <;> simp
  | pcNext j =>
    simp only [timeEq, evalB_add, evalB_var]
    rw [evalB_pcSum v _ hpc hE1, hIc, evalB_pcTerm_self v _ I j (by simp [hv, canon]), xor2_false]
    simp only [hv, canon]
    rw [rowSucc_pc_bit S mv rd I _ hSpc hw j hq]
  | recAct =>
    simp only [timeEq, evalB_add, evalB_var, hESet]
    rw [xor2_false]; simp only [hv, canon]
  | recRgn =>
    simp only [timeEq, evalB_add, evalB_var]
    rw [xor2_false]; simp only [hv, canon]
  | recAd j =>
    simp only [timeEq, evalB_add, evalB_var, evalB_mul, hESet]
    rw [xor2_false]
    simp only [hv, canon]
    split_ifs <;> simp
  | recPh => simp [timeEq, hv, canon]
  | recVa j =>
    simp only [timeEq, evalB_add, evalB_var, evalB_mul, hESet]
    rw [xor2_false]; simp only [hv, canon]
  | recSt =>
    simp only [timeEq, evalB_add, evalB_var, hESet]
    rw [xor2_false]; simp only [hv, canon]
  | tsn j =>
    simp only [timeEq, evalB_add, evalB_var, evalB_tcE]
    rw [xor3_false, cin_carry ts 0#τ true (fun i => v (.inl (.TC i))) (τ - 1) j
      (by have : j < τ := hq; omega) (fun _ _ => rfl)]
    simp only [hv, canon]
    rw [getLsbD_add_add_bool (show j < τ from hq)]
    simp
  | tc j =>
    simp only [timeEq, evalB_add, evalB_var, evalB_mul, evalB_tcE]
    rw [xor2_false, cin_carry ts 0#τ true (fun i => v (.inl (.TC i))) j j le_rfl (fun _ _ => rfl)]
    simp only [hv, canon]
    rw [carry_succ]; simp
  | aA =>
    simp only [timeEq, evalB_add, evalB_var, evalB_mul, evalB_compl, hESet]
    rw [xor2_false]; simp only [hv, canon]
  | can j =>
    simp only [timeEq, evalB_add, evalB_var, evalB_acE]
    rw [xor3_false]
    have hc : cin (fun i => v (.inl (.AC i))) (v (.inl .aA)) j = carry j cA 0#τ (v (.inl .aA)) :=
      cin_carry cA 0#τ _ _ (τ - 1) j (by have : j < τ := hq; omega) (fun _ _ => rfl)
    rw [hc]
    simp only [hv, canon]
    rw [getLsbD_add_add_bool (show j < τ from hq)]
    simp
  | ac j =>
    simp only [timeEq, evalB_add, evalB_var, evalB_mul, evalB_acE]
    rw [xor2_false]
    have hc : cin (fun i => v (.inl (.AC i))) (v (.inl .aA)) j = carry j cA 0#τ (v (.inl .aA)) :=
      cin_carry cA 0#τ _ _ j j le_rfl (fun _ _ => rfl)
    rw [hc]
    simp only [hv, canon]
    rw [carry_succ]; simp
  | aB =>
    simp only [timeEq, evalB_add, evalB_var, evalB_mul, evalB_compl, hESet]
    rw [xor2_false]; simp only [hv, canon]
  | cbn j =>
    simp only [timeEq, evalB_add, evalB_var, evalB_bcE]
    rw [xor3_false]
    have hj : j < (dims M τ).β + 1 := by have : j ≤ (dims M τ).β := hq; omega
    have hc : cin (fun i => v (.inl (.BC i))) (v (.inl .aB)) j =
        carry j cB 0#((dims M τ).β + 1) (v (.inl .aB)) :=
      cin_carry cB _ _ _ (dims M τ).β j (by omega) (fun _ _ => rfl)
    rw [hc]
    simp only [hv, canon]
    rw [getLsbD_add_add_bool hj]
    simp
  | bc j =>
    simp only [timeEq, evalB_add, evalB_var, evalB_mul, evalB_bcE]
    rw [xor2_false]
    have hc : cin (fun i => v (.inl (.BC i))) (v (.inl .aB)) j =
        carry j cB 0#((dims M τ).β + 1) (v (.inl .aB)) :=
      cin_carry cB _ _ _ j j le_rfl (fun _ _ => rfl)
    rw [hc]
    simp only [hv, canon]
    rw [carry_succ]; simp
  | bound =>
    simp only [timeEq, evalB_mul, evalB_var, hv, canon]
    exact hbound

end NearCubicGates.Adapters.RAMTrace
