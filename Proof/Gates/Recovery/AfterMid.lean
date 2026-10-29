import Proof.Gates.Recovery.AfterMidStageTwo

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget NearCubicWires.Bindings.MW20

/-- **The middle segment's cost** (`sec:all-lengths`, `2^{O(n)}`): the five pieces' costs, each polynomial in `2^n` once
`q, ν ≤ n`, the `q^G` cap is polynomial in `q`, and stage 2 fits the clear capacity `2^{Aq n + Bq}`. -/
theorem mid_cost (n q ν Bd cap t19 t20 dl t21 cst k D cc cd uK aK ae Aq Bq : ℕ)
    (hD : 1 ≤ D) (hq : q ≤ n) (hν : ν ≤ n) (hBd : Bd + 1 ≤ (q + 1) ^ D)
    (h19 : t19 ≤ cc * (q + Bd + 1) ^ cd) (hdl : dl ≤ 39 * (q + Bd + 5) ^ 2) (h20 : t20 ≤ uK * (dl + 1))
    (h21 : t21 ≤ aK * (ν + 1) ^ ae) (hcap : cap = 2 ^ (Aq * n + Bq)) (hcst : cst ≤ cap) (hk : k ≤ cst) :
    2 * cap + 4 + 1 + (t19 + 1 + (t20 + 1 + (t21 + 1 + (cst + (k + 2) + 1)))) ≤
      (4 * 2 ^ Bq + cc * 2 ^ cd + 1405 * uK + aK + 11) * (2 ^ n + 1) ^ (D * (Aq + cd + 2 + ae)) := by
  have hX : n + 1 ≤ 2 ^ n + 1 := by have := Nat.lt_two_pow_self (n := n); omega
  have hX1 : 1 ≤ 2 ^ n + 1 := by omega
  have hY1 : 1 ≤ (2 ^ n + 1) ^ D := Nat.one_le_pow _ _ hX1
  have hXY : 2 ^ n + 1 ≤ (2 ^ n + 1) ^ D := by
    calc 2 ^ n + 1 = (2 ^ n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (2 ^ n + 1) ^ D := Nat.pow_le_pow_right hX1 hD
  generalize hYd : (2 ^ n + 1) ^ D = Y at hY1 hXY
  have hqY : q + 1 ≤ Y := by omega
  have hνY : ν + 1 ≤ Y := by omega
  have hBdY : Bd + 1 ≤ Y := by
    rw [← hYd]; exact hBd.trans (Nat.pow_le_pow_left (by omega) D)
  have e19 : t19 ≤ cc * 2 ^ cd * Y ^ cd := by
    refine h19.trans ?_
    rw [Nat.mul_assoc, ← Nat.mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hY2 : 1 ≤ Y ^ 2 := Nat.one_le_pow _ _ hY1
  have e20 : t20 ≤ uK * 1405 * Y ^ 2 := by
    have h6 : (q + Bd + 5) ^ 2 ≤ (6 * Y) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    rw [Nat.mul_pow] at h6
    refine h20.trans ?_
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by omega)
  have e21 : t21 ≤ aK * Y ^ ae := h21.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hνY _))
  have ecap : cap ≤ 2 ^ Bq * Y ^ Aq := by
    rw [hcap, Nat.pow_add, Nat.pow_mul', Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hpow : (2 ^ n + 1) ^ (D * (Aq + cd + 2 + ae)) = Y ^ (Aq + cd + 2 + ae) := by rw [Nat.pow_mul, hYd]
  rw [hpow]
  have m1 : Y ^ Aq ≤ Y ^ (Aq + cd + 2 + ae) := Nat.pow_le_pow_right hY1 (by omega)
  have m2 : Y ^ cd ≤ Y ^ (Aq + cd + 2 + ae) := Nat.pow_le_pow_right hY1 (by omega)
  have m3 : Y ^ 2 ≤ Y ^ (Aq + cd + 2 + ae) := Nat.pow_le_pow_right hY1 (by omega)
  have m4 : Y ^ ae ≤ Y ^ (Aq + cd + 2 + ae) := Nat.pow_le_pow_right hY1 (by omega)
  have m0 : 1 ≤ Y ^ (Aq + cd + 2 + ae) := Nat.one_le_pow _ _ hY1
  generalize Y ^ (Aq + cd + 2 + ae) = Z at m0 m1 m2 m3 m4
  have f1 := Nat.mul_le_mul_left (2 ^ Bq) m1
  have f2 := Nat.mul_le_mul_left (cc * 2 ^ cd) m2
  have f3 := Nat.mul_le_mul_left (uK * 1405) m3
  have f4 := Nat.mul_le_mul_left aK m4
  nlinarith

section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) (c : Cfg)

/-- Installing a bank's outputs keeps a tape below its block whose listed ports (if any) write back its own value. -/
theorem bank_keep' {t : ℕ} (b : Bank (T K) t) (A : Fin (T K) → List Bool) (out : Fin t → List Bool) (x : Fin (T K))
    (hx : x.val < b.off) (h : ∀ p ∈ b.l, p.2 = x → out p.1 = A x) : install b.slot A out x = A x := by
  rw [b.install_low A out x hx]
  by_cases hm : ∃ j, (j, x) ∈ b.l
  · obtain ⟨j, hj⟩ := hm
    rw [updates_mem b.sndNodup out A hj]
    exact h _ hj rfl
  · exact updates_not out A (fun p hp he => hm ⟨p.1, by rw [← he]; exact hp⟩)

theorem sh_lt (i : Fin 32) (k : ℕ) : (sh K i).val < off K k := by
  have := off_ge K k; have := i.isLt; simp only [sh_val]; omega

theorem midRuns : MidRuns K c := by
  intro hQ
  obtain ⟨cc, cd, -, hcc⟩ := CloseoutCaseTwo.ColdBudget.polynomial
  refine ⟨4 * 2 ^ c.Bq + cc * 2 ^ cd + 1405 * unframe.K + (aR s g).K + 11,
    2 ^ RecoveryScheduleEnvelope.oracleDepth g.degree * (c.Aq + cd + 2 + (aR s g).e), ?_⟩
  intro n ν z A h1 hL h14 h3 h15 h7 h8 h9 h16 h17 h18 hblank
  have hc : (g.firstSrc s ν z h1).size ≤ g.bound s ν :=
    (RecoveryChoice.oracleSelector (g.checkPCP s ν z) g.degree z h1).sizeBounded
  obtain ⟨hνq, hqm, hmn⟩ := hL.width_le
  have hqn : g.width s ν ≤ n := by omega
  -- piece 18: the query clear
  have tr18 := piece18 K c A (CloseoutCapacity.capacity c.Aq c.Bq n) h3 h15 (hblank _ le_rfl)
  obtain ⟨A1, hA1⟩ : ∃ A1, A1 = Function.update (Function.update A (sh K 3)
      (List.replicate (CloseoutCapacity.capacity c.Aq c.Bq n) false)) (log18 K)
      (List.replicate (CloseoutCapacity.capacity c.Aq c.Bq n + 1) false) := ⟨_, rfl⟩
  rw [← hA1] at tr18
  have h19v : off K 19 = off K 18 + 1 := rfl
  have A1_sh : ∀ i : Fin 32, i ≠ 3 → A1 (sh K i) = A (sh K i) := by
    intro i hi
    have hl : sh K i ≠ log18 K := fun e => by
      have := congrArg Fin.val e; have := sh_lt K i 18; rw [log18_val] at *; omega
    rw [hA1, Function.update_of_ne hl, Function.update_of_ne (fun e => hi ((sh_inj K i 3).mp e))]
  have A1_3 : A1 (sh K 3) = List.replicate (CloseoutCapacity.capacity c.Aq c.Bq n) false := by
    have hl : sh K 3 ≠ log18 K := fun e => by
      have := congrArg Fin.val e; have := sh_lt K 3 18; rw [log18_val] at *; omega
    rw [hA1, Function.update_of_ne hl, Function.update_self]
  have A1_hi : ∀ x : Fin (T K), off K 19 ≤ x.val → A1 x = A x := by
    intro x hx
    have hl : x ≠ log18 K := fun e => by have := congrArg Fin.val e; rw [log18_val] at this; omega
    have h3' : x ≠ sh K 3 := fun e => by have := congrArg Fin.val e; have := sh_lt K 3 19; omega
    rw [hA1, Function.update_of_ne hl, Function.update_of_ne h3']
  -- piece 19: the converter
  obtain ⟨t19, out19, ht19, tr19, o132, o1⟩ := piece19 K c A1 (g.firstSrc s ν z h1) hc
    (by rw [A1_sh 14 (by decide)]; exact h14) (by rw [A1_sh 7 (by decide)]; exact h7)
    (by rw [A1_sh 8 (by decide)]; exact h8) (by rw [A1_sh 16 (by decide)]; exact h16)
    (fun x hx => by rw [A1_hi x hx]; exact hblank x (by omega))
  obtain ⟨A2, hA2⟩ : ∃ A2, A2 = install (convBank K).slot A1 out19 := ⟨_, rfl⟩
  rw [← hA2] at tr19
  have A2_sh : ∀ i : Fin 32, i ≠ 7 → i ≠ 8 → i ≠ 16 → A2 (sh K i) = A1 (sh K i) := by
    intro i h7' h8' h16'
    rw [hA2]
    refine bank_keep' K (convBank K) A1 out19 (sh K i) (sh_lt K i 19) ?_
    intro p hp he
    simp only [convBank, mkBank, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp only [sh_inj] at he <;> subst he
    · rw [o1, A1_sh 14 (by decide), h14]
    · exact absurd rfl h7'
    · exact absurd rfl h8'
    · exact absurd rfl h16'
  have A2_16 : A2 (sh K 16) = RepairOrdinary.frame (PCPPNative.descriptor (g.firstSrc s ν z h1)) := by
    rw [hA2, (convBank K).install_port A1 out19 (j := 132) (by simp [convBank, mkBank])]
    exact o132
  have h20v : off K 20 = off K 19 + 135 := rfl
  have A2_hi : ∀ x : Fin (T K), off K 20 ≤ x.val → A2 x = A1 x := by
    intro x hx
    rw [hA2]
    exact (convBank K).install_high A1 out19 x (by show off K 19 + 135 ≤ x.val; omega)
  -- piece 20: unframe
  obtain ⟨t20, out20, ht20, tr20, o20⟩ := piece20 K c A2 (PCPPNative.descriptor (g.firstSrc s ν z h1)) A2_16
    (by rw [A2_sh 17 (by decide) (by decide) (by decide), A1_sh 17 (by decide)]; exact h17)
    (fun x hx => by rw [A2_hi x hx, A1_hi x (by omega)]; exact hblank x (by omega))
  obtain ⟨A3, hA3⟩ : ∃ A3, A3 = install (ufBank K).slot A2 out20 := ⟨_, rfl⟩
  rw [← hA3] at tr20
  have A3_sh : ∀ i : Fin 32, i ≠ 16 → i ≠ 17 → A3 (sh K i) = A2 (sh K i) := by
    intro i h16' h17'
    rw [hA3]
    refine bank_keep' K (ufBank K) A2 out20 (sh K i) (sh_lt K i 20) ?_
    intro p hp he
    simp only [ufBank, mkBank, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp only [sh_inj] at he <;> subst he
    · exact absurd rfl h16'
    · exact absurd rfl h17'
  have A3_17 : A3 (sh K 17) = PCPPNative.descriptor (g.firstSrc s ν z h1) := by
    rw [hA3, (ufBank K).install_port A2 out20 (j := unframe.dst) (by simp [ufBank, mkBank])]
    exact o20
  have h21v : off K 21 = off K 20 + unframe.t := rfl
  have A3_hi : ∀ x : Fin (T K), off K 21 ≤ x.val → A3 x = A2 x := by
    intro x hx
    rw [hA3]
    exact (ufBank K).install_high A2 out20 x (by show off K 20 + unframe.t ≤ x.val; omega)
  have A3_9 : A3 (sh K 9) = List.replicate ν true := by
    rw [A3_sh 9 (by decide) (by decide), A2_sh 9 (by decide) (by decide) (by decide), A1_sh 9 (by decide)]
    exact h9
  -- piece 21: the A-run
  obtain ⟨t21, out21, ht21, tr21, odI, onI, owO, olen⟩ := piece21 K c A3 ν (g.firstSrc s ν z h1) A3_17 A3_9
    (by rw [A3_sh 18 (by decide) (by decide), A2_sh 18 (by decide) (by decide) (by decide),
      A1_sh 18 (by decide)]; exact h18)
    (fun x hx => by
      rw [A3_hi x hx, A2_hi x (by omega), A1_hi x (by omega)]; exact hblank x (by omega))
  obtain ⟨A4, hA4⟩ : ∃ A4, A4 = install (b21 K).slot A3 out21 := ⟨_, rfl⟩
  rw [← hA4] at tr21
  have A4_sh : ∀ i : Fin 32, i ≠ 18 → A4 (sh K i) = A3 (sh K i) := by
    intro i h18'
    rw [hA4]
    refine bank_keep' K (b21 K) A3 out21 (sh K i) (sh_lt K i 21) ?_
    intro p hp he
    simp only [b21, arBank, mkBank, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [sh_inj] at he <;> subst he
    · rw [odI, A3_17]
    · rw [onI, A3_9]
    · exact absurd rfl h18'
  have A4_18 : A4 (sh K 18) = (g.outC s ν (g.firstSrc s ν z h1)).word := by
    rw [hA4, (b21 K).install_port A3 out21 (j := (aR s g).wOut) (by simp [b21, arBank, mkBank])]
    exact owO
  have h22v : off K 22 = off K 21 + (aR s g).t := rfl
  have A4_hi : ∀ x : Fin (T K), off K 22 ≤ x.val → A4 x = A3 x := by
    intro x hx
    rw [hA4]
    exact (b21 K).install_high A3 out21 x (by show off K 21 + (aR s g).t ≤ x.val; omega)
  -- piece 22: stage 2
  obtain ⟨cst, k, hcst, hk, out22, oq, otab, tr24, tr23⟩ := piece22 K c A4
    (CloseoutCapacity.capacity c.Aq c.Bq n) (g.outC s ν (g.firstSrc s ν z h1))
    (by rw [A4_sh 3 (by decide), A3_sh 3 (by decide) (by decide), A2_sh 3 (by decide) (by decide) (by decide)]
        exact A1_3)
    A4_18
    (fun x hx => by
      rw [A4_hi x hx, A3_hi x (by omega), A2_hi x (by omega), A1_hi x (by omega)]; exact hblank x (by omega))
  obtain ⟨A5, hA5⟩ : ∃ A5, A5 = install (tBank K).slot A4 out22 := ⟨_, rfl⟩
  rw [← hA5] at tr24 tr23
  have A5_sh : ∀ i : Fin 32, i ≠ 3 → i ≠ 18 → A5 (sh K i) = A4 (sh K i) := by
    intro i h3' h18'
    rw [hA5]
    refine bank_keep' K (tBank K) A4 out22 (sh K i) (sh_lt K i 22) ?_
    intro p hp he
    simp only [tBank, mkBank, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp only [sh_inj] at he <;> subst he
    · exact absurd rfl h3'
    · exact absurd rfl h18'
  have h23v : off K 23 = off K 22 + (pT K).base.tapeCount := rfl
  have A5_hi : ∀ x : Fin (T K), off K 23 ≤ x.val → A5 x = A4 x := by
    intro x hx
    rw [hA5]
    exact (tBank K).install_high A4 out22 x (by show off K 22 + (pT K).base.tapeCount ≤ x.val; omega)
  -- stage 2 fits the clear capacity (`QFits`)
  have hell : (g.outC s ν (g.firstSrc s ν z h1)).ell ≤ g.width s ν :=
    Outer.ell_le_width s.mw (g.sv s) ν (g.firstSrc s ν z h1) hL.onset hL.pos
  have hdesc := PCPPNative.descriptor_cap (g.firstSrc s ν z h1) hc
  have hword : (g.outC s ν (g.firstSrc s ν z h1)).word.length ≤
      39 * (g.width s ν + g.bound s ν + 5) ^ 2 + ν + (aR s g).K * (ν + 1) ^ (aR s g).e := by
    have h := olen
    rw [owO] at h
    change (g.outC s ν (g.firstSrc s ν z h1)).word.length ≤ _ at h
    omega
  have hcap : cst ≤ CloseoutCapacity.capacity c.Aq c.Bq n := by
    refine hcst.trans (le_trans ?_ (hQ n ν hL))
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hell
    omega
  -- assemble
  refine ⟨2 * CloseoutCapacity.capacity c.Aq c.Bq n + 4 + 1 + (t19 + 1 + (t20 + 1 + (t21 + 1 + (cst + (k + 2) + 1)))),
    ?_, A5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mid_cost n (g.width s ν) ν (g.bound s ν) (CloseoutCapacity.capacity c.Aq c.Bq n) t19 t20
      (PCPPNative.descriptor (g.firstSrc s ν z h1)).length t21 cst k
      (2 ^ RecoveryScheduleEnvelope.oracleDepth g.degree) cc cd unframe.K (aR s g).K (aR s g).e c.Aq c.Bq
      Nat.one_le_two_pow hqn (by omega) (PolynomialClock.pairIter_add_one_le_pow _ _)
      (ht19.trans (hcc _ _ _ hc)) hdesc ht20 ht21 rfl hcap hk
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    obtain ⟨i3, i7, i8, i16, i17, i18⟩ := hi
    rw [A5_sh i i3 i18, A4_sh i i18, A3_sh i i16 i17, A2_sh i i7 i8 i16, A1_sh i i3]
  · rw [A5_sh 17 (by decide) (by decide), A4_sh 17 (by decide)]
    exact A3_17
  · rw [hA5, (tBank K).install_port A4 out22 (tBank_mem_query K)]
    exact oq.trans (max_le le_rfl hcap)
  · intro x hx
    rw [A5_hi x hx, A4_hi x (by omega), A3_hi x (by omega), A2_hi x (by omega), A1_hi x (by omega)]
    exact hblank x (by omega)
  · intro h2
    refine ⟨trans tr18 (trans tr19 (trans tr20 (trans tr21 (tr24 h2)))), ?_⟩
    rw [hA5]
    unfold tbl
    rw [install_slot _ (tBank K).injective]
    exact otab _
  · intro h2
    exact trans tr18 (trans tr19 (trans tr20 (trans tr21 (tr23 h2))))

end

end NearCubicGates.Close.Recovery.After
