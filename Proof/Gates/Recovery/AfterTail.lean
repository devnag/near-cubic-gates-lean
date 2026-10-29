import Proof.Gates.Recovery.AfterTailBranches

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget NearCubicWires.ExecutableInterfaces
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.RepairSource.RecoveryChoice

section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) (c : Cfg)

theorem sh_ne_blk (i : Fin 32) (k : ℕ) (hk : k < 31) (hs : 1 ≤ sz K k) : sh K i ≠ blk K k hk hs := by
  intro h
  have := congrArg Fin.val h
  have := off_ge K k
  have := i.isLt
  simp only [sh_val, blk_val] at *
  omega

theorem blk_ne (k k' : ℕ) (hk : k < 31) (hk' : k' < 31) (hs : 1 ≤ sz K k) (hs' : 1 ≤ sz K k') (h : k < k') :
    blk K k hk hs ≠ blk K k' hk' hs' := by
  intro he
  have := congrArg Fin.val he
  simp only [blk_val] at this
  have := off_lt_succ K k hs
  have := off_mono K (show k + 1 ≤ k' by omega)
  omega

theorem pow_le_E (X a E : ℕ) (hX : 1 ≤ X) (h : a ≤ E) : X ^ a ≤ X ^ E := Nat.pow_le_pow_right hX h

/-- **The tail after stage 2** (`sec:all-lengths`, stage 3 and the two last branches). -/
theorem tailRuns : TailRuns K c := by
  intro C0 E0 hSB
  refine ⟨40 + 2 * 2 ^ c.Bq + 2 * C0 + K.c1.C + (aR s g).K + K.ht.C,
    1 + c.Aq + E0 + K.c1.E + (aR s g).e + K.ht.E, ?_⟩
  intro n point ν z A h1 h2 hL hcut hT hPT hQ h9 h10 h11 h12 h13 h15 h17 h2o h21 h22 h23 h24 h31 hB
  obtain ⟨hνq, hqm, hmn⟩ := hL.width_le
  have hqn : g.width s ν ≤ n := by omega
  have hq1 : 1 ≤ g.width s ν := by omega
  have hνn : ν ≤ n := by omega
  have hℓ : (g.outC s ν (g.firstSrc s ν z h1)).ell ≤ g.width s ν :=
    Outer.ell_le_width s.mw (g.sv s) ν (g.firstSrc s ν z h1) hL.onset hL.pos
  set t := (Classical.choice (existsFirstTable _ h2)).table with ht
  set W := CloseoutCapacity.capacity c.A c.B n with hWdef
  set N := CloseoutCapacity.capacity c.Aq c.Bq n with hNdef
  set bits := List.ofFn t with hbits
  have hbits_len : bits.length = 2 ^ (g.outC s ν (g.firstSrc s ν z h1)).ell := by simp [bits]
  -- stage 3's workspace and cost
  have hvals : (boolFunctionTable (tableOracle t)).length = 2 ^ (g.outC s ν (g.firstSrc s ν z h1)).ell := by
    rw [boolFunctionTable_tableOracle]; simp
  obtain ⟨hWs, hFs, h2s, hcs⟩ := hSB n _ (g.width s ν) (boolFunctionTable (tableOracle t)) hℓ z hqn hvals
  have hb : 0 < g.bound s ν := by
    unfold GateParams.bound oracleSizeBound
    exact NearCubicWires.PolynomialClock.pairClock_positive _ _ hq1
  have hWs' : CloseoutRecoveryWorkspace.originalWorkspace (g.width s ν) (g.bound s ν) (List.ofFn t).length
      (List.ofFn t).length ≤ W := by
    rw [boolFunctionTable_tableOracle] at hWs; exact hWs
  have hcost27 := hcs hb
  -- piece 24
  have hB24 : A (blk K 24 (by decide) le_rfl) = [] := hB _ (by rw [blk_val])
  have e24 := ready24 K c A bits hT h21 hB24
  have tr24 := step_call K c (k := 24) (l := 25) e24
    (fun q => next_plain K c 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  set A1 := Function.update (Function.update A (sh K 21) (RepairOrdinary.frame bits)) (blk K 24 (by decide) le_rfl)
    (List.replicate (2 * bits.length + 1) false) with hA1
  have hA1sh : ∀ i : Fin 32, i ≠ 21 → A1 (sh K i) = A (sh K i) := by
    intro i hi
    simp only [A1, Function.update_apply, if_neg (sh_ne_blk K i 24 (by decide) le_rfl), sh_inj, if_neg hi]
  have hA1hi : ∀ x : Fin (T K), off K 25 ≤ x.val → A1 x = A x := by
    intro x hx
    have h1' : x ≠ blk K 24 (by decide) le_rfl := by
      intro he; rw [he, blk_val] at hx; have : off K 24 < off K 25 := off_lt_succ K 24 le_rfl; omega
    have h2' : x ≠ sh K 21 := by intro he; rw [he] at hx; have := off_ge K 25; simp at hx; omega
    simp only [A1, Function.update_apply, if_neg h1', if_neg h2']
  have hA1_21 : A1 (sh K 21) = RepairOrdinary.frame bits := by
    simp only [A1, Function.update_apply, if_neg (sh_ne_blk K 21 24 (by decide) le_rfl), if_pos rfl, if_true]
  have hA1tbl : A1 (tbl K) = RepairOrdinary.frame bits := by
    have h1' : tbl K ≠ blk K 24 (by decide) le_rfl := by
      intro he; have := congrArg Fin.val he; rw [blk_val] at this; have := tbl_lt K
      have := off_mono K (show 23 ≤ 24 by omega); omega
    simp only [A1, Function.update_apply, if_neg h1', if_neg (tbl_ne K 21 (by decide) (by decide))]
    exact hT
  -- piece 25
  have e25 := ready25 K c A1 bits hA1tbl (by rw [hA1sh 22 (by decide)]; exact h22) (by
    rw [hA1hi _ (by rw [blk_val])]; exact hB _ (by rw [blk_val]; exact off_mono K (by omega)))
  have tr25 := step_call K c (k := 25) (l := 26) e25
    (fun q => next_plain K c 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  set A2 := Function.update (Function.update A1 (sh K 22) (RepairOrdinary.frame bits)) (blk K 25 (by decide) le_rfl)
    (List.replicate (2 * bits.length + 1) false) with hA2
  have hA2sh : ∀ i : Fin 32, i ≠ 22 → A2 (sh K i) = A1 (sh K i) := by
    intro i hi
    simp only [A2, Function.update_apply, if_neg (sh_ne_blk K i 25 (by decide) le_rfl), sh_inj, if_neg hi]
  have hA2hi : ∀ x : Fin (T K), off K 26 ≤ x.val → A2 x = A1 x := by
    intro x hx
    have h1' : x ≠ blk K 25 (by decide) le_rfl := by
      intro he; rw [he, blk_val] at hx; have : off K 25 < off K 26 := off_lt_succ K 25 le_rfl; omega
    have h2' : x ≠ sh K 22 := by intro he; rw [he] at hx; have := off_ge K 26; simp at hx; omega
    simp only [A2, Function.update_apply, if_neg h1', if_neg h2']
  have hA2_22 : A2 (sh K 22) = RepairOrdinary.frame bits := by
    simp only [A2, Function.update_apply, if_neg (sh_ne_blk K 22 25 (by decide) le_rfl), if_pos rfl, if_true]
  -- piece 26
  have e26 := ready26 K c A2 N (by rw [hA2sh 3 (by decide), hA1sh 3 (by decide)]; exact hQ)
    (by rw [hA2sh 15 (by decide), hA1sh 15 (by decide)]; exact h15)
    (by rw [hA2hi _ (by rw [blk_val]), hA1hi _ (by rw [blk_val]; exact off_mono K (by omega))]
        exact hB _ (by rw [blk_val]; exact off_mono K (by omega)))
  have tr26 := step_call K c (k := 26) (l := 27) e26
    (fun q => next_plain K c 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  set A3 := Function.update (Function.update A2 (sh K 3) (List.replicate N false)) (blk K 26 (by decide) le_rfl)
    (List.replicate (N + 1) false) with hA3
  have hA3sh : ∀ i : Fin 32, i ≠ 3 → A3 (sh K i) = A2 (sh K i) := by
    intro i hi
    simp only [A3, Function.update_apply, if_neg (sh_ne_blk K i 26 (by decide) le_rfl), sh_inj, if_neg hi]
  have hA3hi : ∀ x : Fin (T K), off K 27 ≤ x.val → A3 x = A x := by
    intro x hx
    have h1' : x ≠ blk K 26 (by decide) le_rfl := by
      intro he; rw [he, blk_val] at hx; have : off K 26 < off K 27 := off_lt_succ K 26 le_rfl; omega
    have h2' : x ≠ sh K 3 := by intro he; rw [he] at hx; have := off_ge K 27; simp at hx; omega
    simp only [A3, Function.update_apply, if_neg h1', if_neg h2']
    rw [hA2hi x (by have := off_mono K (show 26 ≤ 27 by omega); omega),
      hA1hi x (by have := off_mono K (show 25 ≤ 27 by omega); omega)]
  have hA3_3 : A3 (sh K 3) = List.replicate N false := by
    simp only [A3, Function.update_apply, if_neg (sh_ne_blk K 3 26 (by decide) le_rfl), if_pos rfl, if_true]

  have hA3A : ∀ i : Fin 32, i ≠ 3 → i ≠ 21 → i ≠ 22 → A3 (sh K i) = A (sh K i) := by
    intro i h3 h21' h22'
    rw [hA3sh i h3, hA2sh i h22', hA1sh i h21']
  -- piece 27
  obtain ⟨c27, hc27, A4, e27, hflag4, hdesc4, hkeep4, hhigh4⟩ := ready27 K c ν z hℓ t W N hb hWs' hFs h2s A3
    (by rw [hA3sh 21 (by decide), hA2sh 21 (by decide)]; exact hA1_21)
    (by rw [hA3A 10 (by decide) (by decide) (by decide)]; exact h10)
    (by rw [hA3A 11 (by decide) (by decide) (by decide)]; exact h11)
    (by rw [hA3A 31 (by decide) (by decide) (by decide)]; exact h31)
    (by rw [hA3A 23 (by decide) (by decide) (by decide)]; exact h23)
    hA3_3
    (fun x hx1 hx2 => by rw [hA3hi x hx1]; exact hB x (by have := off_mono K (show 24 ≤ 27 by omega); omega))
  -- the bounds
  have hX : 1 ≤ 2 ^ n + 1 := Nat.le_add_left 1 _
  set E := 1 + c.Aq + E0 + K.c1.E + (aR s g).e + K.ht.E with hE
  have hL1 : bits.length ≤ (2 ^ n + 1) ^ E := by
    rw [hbits_len]
    calc 2 ^ (g.outC s ν (g.firstSrc s ν z h1)).ell ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ (2 ^ n + 1) ^ 1 := by simp
      _ ≤ (2 ^ n + 1) ^ E := pow_le_E _ _ _ hX (by omega)
  have hN : N ≤ 2 ^ c.Bq * (2 ^ n + 1) ^ E := by
    rw [hNdef]
    unfold CloseoutCapacity.capacity
    calc 2 ^ (c.Aq * n + c.Bq) = 2 ^ c.Bq * (2 ^ n) ^ c.Aq := by rw [← pow_mul, ← pow_add]; ring_nf
      _ ≤ 2 ^ c.Bq * (2 ^ n + 1) ^ c.Aq := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ ≤ 2 ^ c.Bq * (2 ^ n + 1) ^ E := Nat.mul_le_mul_left _ (pow_le_E _ _ _ hX (by omega))
  have h27 : c27 ≤ 2 * (C0 * (2 ^ n + 1) ^ E) + 2 := by
    have := Nat.mul_le_mul_left C0 (pow_le_E _ E0 E hX (by omega))
    have h1' : ENP.UStage.cost g.degree (g.outC s ν (g.firstSrc s ν z h1)).ell (g.width s ν) W
        (boolFunctionTable (tableOracle t)) hℓ z ≤ C0 * (2 ^ n + 1) ^ E0 := hcost27
    omega
  have hRHS : (40 + 2 * 2 ^ c.Bq + 2 * C0 + K.c1.C + (aR s g).K + K.ht.C) * (2 ^ n + 1) ^ E =
      40 * (2 ^ n + 1) ^ E + 2 * (2 ^ c.Bq * (2 ^ n + 1) ^ E) + 2 * (C0 * (2 ^ n + 1) ^ E) +
        K.c1.C * (2 ^ n + 1) ^ E + (aR s g).K * (2 ^ n + 1) ^ E + K.ht.C * (2 ^ n + 1) ^ E := by ring
  have hstart : ∀ i : Fin 32, i ∉ [21, 10, 11, 31, 23, 3] → i ≠ 22 → A4 (sh K i) = A (sh K i) := by
    intro i hi h22'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [hkeep4 i (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hi)]
    exact hA3A i hi.2.2.2.2.2 hi.1 h22'
  by_cases hsm : SmallOracle (g.matchPCP s ν hℓ t) g.degree z
  · -- Case 2: the A-run on `B*_src`, then the Case 2 producer
    have hIs : g.IsCaseTwo s ν z := ⟨h1, h2, hℓ, hsm⟩
    have tr27 := step_call K c (k := 27) (l := 29) e27 (fun q => by
      rw [next_27]; simp only [hflag4.mpr hsm, if_true])
    obtain ⟨c29, hc29, A5, e29, hw5, hkeep5, hhigh5⟩ := ready29 K c ν (g.firstSrc s ν z h1) A4
      (by rw [hstart 17 (by decide) (by decide)]; exact h17) (by rw [hstart 9 (by decide) (by decide)]; exact h9)
      (by rw [hstart 24 (by decide) (by decide)]; exact h24)
      (fun x hx1 hx2 => by
        rw [hhigh4 x (by have := off_mono K (show 28 ≤ 29 by omega); omega),
          hA3hi x (by have := off_mono K (show 27 ≤ 29 by omega); omega)]
        exact hB x (by have := off_mono K (show 24 ≤ 29 by omega); omega))
    have tr29 := step_call K c (k := 29) (l := 30) e29
      (fun q => next_plain K c 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        q _)
    have hk5 : ∀ i : Fin 32, i ∉ [17, 9, 24] → i ∉ [21, 10, 11, 31, 23, 3] → i ≠ 22 → A5 (sh K i) = A (sh K i) := by
      intro i hi hi' h22'
      rw [hkeep5 i hi, hstart i hi' h22']
    obtain ⟨c30, hc30, B, e30, hB2⟩ := ready30 K c n point ν z hνn hcut hIs A5 hw5
      (by
        rw [hkeep5 23 (by decide), hdesc4 hsm]
        rfl)
      (by rw [hk5 1 (by decide) (by decide) (by decide)]; exact hPT)
      (by rw [hk5 12 (by decide) (by decide) (by decide)]; exact h12)
      (by rw [hk5 13 (by decide) (by decide) (by decide)]; exact h13)
      (by rw [hk5 2 (by decide) (by decide) (by decide)]; exact h2o)
      (fun x hx1 hx2 => by
        rw [hhigh5 x hx1, hhigh4 x (by have := off_mono K (show 28 ≤ 30 by omega); omega),
          hA3hi x (by have := off_mono K (show 27 ≤ 30 by omega); omega)]
        exact hB x (by have := off_mono K (show 24 ≤ 30 by omega); omega))
    have tr30 := step_stop K c (k := 30) e30 (fun q => next_30 K c q _)
    refine ⟨_, ?_, B, trans tr24 (trans tr25 (trans tr26 (trans tr27 (trans tr29 tr30)))), hB2⟩
    have h29 : c29 ≤ (aR s g).K * (2 ^ n + 1) ^ E := by
      refine hc29.trans (Nat.mul_le_mul_left _ ?_)
      calc (ν + 1) ^ (aR s g).e ≤ (2 ^ n + 1) ^ (aR s g).e :=
            Nat.pow_le_pow_left (by have := Nat.lt_two_pow_self (n := n); omega) _
        _ ≤ (2 ^ n + 1) ^ E := pow_le_E _ _ _ hX (by omega)
    have h30 : c30 ≤ K.ht.C * (2 ^ n + 1) ^ E :=
      hc30.trans (Nat.mul_le_mul_left _ (pow_le_E _ _ _ hX (by omega)))
    have hP1 : 1 ≤ (2 ^ n + 1) ^ E := Nat.one_le_pow _ _ (by omega)
    rw [hRHS]
    omega
  · -- Case 1 (iii): the amplified table `O*`
    have hnot : ¬ g.IsCaseTwo s ν z := fun h' => hsm h'.2.2.2
    have tr27 := step_call K c (k := 27) (l := 28) e27 (fun q => by
      rw [next_27]
      have : readTapeBit (A4 (sh K 31)) 0 = false := by
        cases hr : readTapeBit (A4 (sh K 31)) 0
        · rfl
        · exact absurd (hflag4.mp hr) hsm
      simp only [this, Bool.false_eq_true, if_false])
    have har : ((selectedAmplifier s.amplification g.degree).output (g.width s ν)
        (cycFn _ t (g.width s ν))).arity ≤ n :=
      (CaseOneSem.arity_fit s g _ hL.ampLarge ν _).trans (by omega)
    obtain ⟨c28, hc28, B, e28, hB2⟩ := ready28 K c n point t (g.width s ν) hq1 hqn har A4
      (by rw [hkeep4 22 (by decide), hA3sh 22 (by decide)]; exact hA2_22)
      (by rw [hstart 1 (by decide) (by decide)]; exact hPT)
      (by rw [hstart 12 (by decide) (by decide)]; exact h12)
      (by rw [hstart 2 (by decide) (by decide)]; exact h2o)
      (fun x hx1 hx2 => by
        rw [hhigh4 x hx1, hA3hi x (by have := off_mono K (show 27 ≤ 28 by omega); omega)]
        exact hB x (by have := off_mono K (show 24 ≤ 28 by omega); omega))
    have tr28 := step_stop K c (k := 28) e28 (fun q => next_28 K c q _)
    refine ⟨_, ?_, B, trans tr24 (trans tr25 (trans tr26 (trans tr27 tr28))), ?_⟩
    · have h28 : c28 ≤ K.c1.C * (2 ^ n + 1) ^ E :=
        hc28.trans (Nat.mul_le_mul_left _ (pow_le_E _ _ _ hX (by omega)))
      have hP1 : 1 ≤ (2 ^ n + 1) ^ E := Nat.one_le_pow _ _ (by omega)
      rw [hRHS]
      omega
    · rw [hB2, CaseOneSem.gateCore_caseOne_iii s g P _ ν z _ _ n h1 h2 hnot]

end

end NearCubicGates.Close.Recovery.After
