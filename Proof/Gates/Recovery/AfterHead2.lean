import Proof.Gates.Recovery.AfterHeadStep
import Proof.CaseAnalysis.CapacityBudget
import Proof.CaseAnalysis.RecoveryFullBoundResources

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) (c : Cfg)

theorem cap_piece (k : ℕ) (hk : k < 31) (ht : sz K k = 26) (Ac Bc : ℕ) (w : Fin 32) (hw : (1 : Fin 32) ≠ w)
    {n : ℕ} (point : BitInput n) (A : Fin (T K) → List Bool)
    (h1 : A (sh K 1) = RepairOrdinary.frame (List.ofFn point)) (hw0 : A (sh K w) = []) (hbl : BlankFrom K k A) :
    ∃ time, time ≤ CloseoutCapacity.coefficient Ac Bc * (2 ^ n + 1) ^ (Ac + 1) ∧ ∃ A' : Fin (T K) → List Bool,
      Ready RecoveryOracle.correctedSat
        ((ports K).program (ordinary (RecoveryFocus.machine (capBank K k hk ht w hw).slot
          (CloseoutCapacity.machine Ac Bc)))) time A A' ∧
      BlankFrom K (k + 1) A' ∧ (∀ i : Fin 32, i ≠ 1 → i ≠ w → A' (sh K i) = A (sh K i)) ∧
      A' (sh K 1) = RepairOrdinary.frame (List.ofFn point) ∧
      A' (sh K w) = List.replicate (CloseoutCapacity.capacity Ac Bc n) true := by
  obtain ⟨out, hrun, ho24, -, ho0⟩ := CloseoutCapacity.capacity_run Ac Bc (List.ofFn point)
  obtain ⟨time, htime, hex⟩ := exact_time hrun
  obtain ⟨R, hB, hkeep, hput⟩ := bank_piece K k hk ht [(0, 1), (24, w)]
    (by simp only [List.map_cons, List.map_nil]; decide) (by simpa using nodup2 hw) hex A
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · simpa [CloseoutCapacity.input] using h1
      · simp only [CloseoutCapacity.input]
        rw [if_neg (by decide)]
        exact hw0)
    (by
      intro j hj
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      simp only [CloseoutCapacity.input]
      rw [if_neg]
      intro h0
      exact hj.1 (Fin.ext h0))
    hbl
  refine ⟨time, ?_, _, R, hB, ?_, ?_, ?_⟩
  · refine htime.trans ?_
    have := CloseoutCapacity.budget_bound Ac Bc (List.ofFn point)
    simpa using this
  · intro i hi1 hiw
    apply hkeep
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hi1, hiw⟩
  · rw [hput (0, 1) (by simp)]
    simpa using ho0
  · rw [hput (24, w) (by simp), ho24]
    simp [CloseoutCapacity.capacity]

theorem fb_piece (k : ℕ) (hk : k < 31) (ht : sz K k = RecoveryFullBound.tapes g.degree) (q b : Fin 32) (hqb : q ≠ b)
    (R : ℕ) (A : Fin (T K) → List Bool)
    (hq : A (sh K q) = List.replicate R true) (hb0 : A (sh K b) = []) (hbl : BlankFrom K k A) :
    ∃ time, time ≤ RecoveryFullBound.coefficient g.degree * (R + 2) ^ RecoveryFullBound.degree g.degree ∧
      ∃ A' : Fin (T K) → List Bool,
      Ready RecoveryOracle.correctedSat
        ((ports K).program (ordinary (RecoveryFocus.machine (fbBank K k hk ht q b hqb).slot
          (RecoveryFullBound.machine g.degree)))) time A A' ∧
      BlankFrom K (k + 1) A' ∧ (∀ i : Fin 32, i ≠ q → i ≠ b → A' (sh K i) = A (sh K i)) ∧
      A' (sh K q) = List.replicate R true ∧
      A' (sh K b) = List.replicate (oracleSizeBound g.degree R) true := by
  obtain ⟨out, hrun, hoS, hoR, -⟩ := RecoveryFullBound.bounded_cold_run g.degree R
  obtain ⟨time, htime, hex⟩ := exact_time hrun
  have hne : RecoveryFullBound.sourceSlot g.degree ≠ RecoveryFullBound.rawSlot g.degree := by
    intro e
    have := congrArg Fin.val e
    simp [RecoveryFullBound.sourceSlot, RecoveryFullBound.rawSlot, RecoveryFullBound.old,
      RecoveryFullBound.extra] at this
    have h0 : 0 < RecoveryFullBound.base g.degree := by
      simp [RecoveryFullBound.base, ProjectionNormalization.DimensionPolynomial.tapes]
    omega
  have hsrc0 : (RecoveryFullBound.sourceSlot g.degree).val = 0 := rfl
  obtain ⟨Rd, hB, hkeep, hput⟩ := bank_piece K k hk ht
    [(RecoveryFullBound.sourceSlot g.degree, q), (RecoveryFullBound.rawSlot g.degree, b)]
    (by simp only [List.map_cons, List.map_nil]; exact nodup2 hne) (by simpa using nodup2 hqb) hex A
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · simp only [RecoveryFullBound.input]
        rw [if_pos hsrc0]
        exact hq
      · simp only [RecoveryFullBound.input]
        rw [if_neg (fun h => hne (Fin.ext (by rw [hsrc0, h])))]
        exact hb0)
    (by
      intro j hj
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      simp only [RecoveryFullBound.input]
      rw [if_neg]
      intro h0
      exact hj.1 (Fin.ext (by rw [h0, hsrc0])))
    hbl
  refine ⟨time, htime, _, Rd, hB, ?_, ?_, ?_⟩
  · intro i hiq hib
    apply hkeep
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hiq, hib⟩
  · rw [hput (RecoveryFullBound.sourceSlot g.degree, q) (by simp), hoS]
  · rw [hput (RecoveryFullBound.rawSlot g.degree, b) (by simp), hoR]

end

section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) (c : Cfg)

theorem b16_l : (b16 K).l =
    [(cslot _ (tableL g.degree), sh K 4), (cslot _ (rL g.degree), sh K 5), (cslot _ (wL g.degree), sh K 6),
      (cslot _ (ENP.UStage.flagPort g.degree), sh K 19), (cslot _ (ENP.UStage.descPort g.degree), sh K 14),
      (cslot _ (ENP.UStage.queryPort g.degree), sh K 3)] := rfl

theorem uTapes_ge (d : ℕ) : 342 ≤ ENP.USupply.uTapes d := by unfold ENP.USupply.uTapes; omega

/-- **Piece 16, stage 1** (paper §11.6): the listed-pairs stage on `z`, clocked, focused on its bank. -/
theorem s1_piece (C0 E0 : ℕ) (hSB : StageBudgetAt g.degree c.A c.B C0 E0) {n : ℕ} (ν : ℕ) (z : BitInput (2 ^ ν))
    (hL : Live s g n ν) (A : Fin (T K) → List Bool)
    (h4 : A (sh K 4) = RepairOrdinary.frame (List.ofFn z)) (h5 : A (sh K 5) = List.replicate (g.width s ν) true)
    (h6 : A (sh K 6) = List.replicate (CloseoutCapacity.capacity c.A c.B n) true)
    (h19 : A (sh K 19) = []) (h14 : A (sh K 14) = []) (h3 : A (sh K 3) = []) (hbl : BlankFrom K 16 A) :
    ∃ time, time ≤ 2 * (C0 * (2 ^ n + 1) ^ E0) + 2 ∧ ∃ A' : Fin (T K) → List Bool,
      Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c 16)) time A A' ∧
      BlankFrom K 17 A' ∧ (∀ i : Fin 32, i ∉ [4, 5, 6, 19, 14, 3] → A' (sh K i) = A (sh K i)) ∧
      (A' (sh K 3)).length ≤ C0 * (2 ^ n + 1) ^ E0 ∧
      (readTapeBit (A' (sh K 19)) 0 = true ↔ g.SrcExists s ν z) ∧
      (∀ h1 : g.SrcExists s ν z, A' (sh K 14) = RepairOrdinary.frame
        (OuterPCPRecovery.canonicalBoundedCircuitDescription (g.bound s ν) (g.firstSrc s ν z h1))) := by
  obtain ⟨hνq, hqm, hmn⟩ := hL.width_le
  have hqn : g.width s ν ≤ n := by omega
  have hb : 0 < g.bound s ν := by
    have h1 := PolynomialClock.value_le_pairIter (oracleDepth g.degree) (g.width s ν)
    unfold GateParams.bound oracleSizeBound
    exact lt_of_lt_of_le (by omega) h1
  set W := CloseoutCapacity.capacity c.A c.B n with hWdef
  obtain ⟨hW, hsrc, htwo, hcost⟩ := hSB n ν (g.width s ν) (List.ofFn z) (g.nu_lt_width s ν).le z hqn (by simp)
  obtain ⟨c1, hc1, final, tr, hal, hflag, hdesc, -, -⟩ := ENP.UInst.stage1_run s g ν z [] W hb hW hsrc htwo
  have hc1' : c1 ≤ C0 * (2 ^ n + 1) ^ E0 := hc1.trans (hcost hb)
  obtain ⟨n1, hn1, R16, hlen⟩ := clocked_ready tr hal
  set inp := ENP.UStage.input g.degree (RepairOrdinary.frame (List.ofFn z) ++ []) (g.width s ν) W with hinp
  have hu := uTapes_ge g.degree
  have hqs : (b16 K).slot (pU g).queryTape = (ports K).queryTape := by
    have := Bank.slot_port (b16 K) (j := cslot _ (ENP.UStage.queryPort g.degree)) (x := sh K 3)
      (by rw [b16_l]; simp)
    exact this
  have hin : ∀ j, A ((b16 K).slot j) = ZeroPadding.pad ((fun _ => 0) j) (clockIn _ inp j) := by
    simp only [ZeroPadding.pad_zero]
    apply Bank.input
    · intro p hp
      rw [b16_l] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [clockIn_src, hinp, uinput_eq]
      · simpa using h4
      · rw [if_neg (fun e => by have := congrArg Fin.val e; simp at this)]; simpa using h5
      · rw [if_neg (fun e => by have := congrArg Fin.val e; simp at this),
          if_neg (fun e => by have := congrArg Fin.val e; simp at this)]; simpa using h6
      · rw [if_neg (fun e => by have := congrArg Fin.val e; simp at this; omega),
          if_neg (fun e => by have := congrArg Fin.val e; simp at this; omega),
          if_neg (fun e => by have := congrArg Fin.val e; simp at this; omega)]; exact h19
      · rw [if_neg (fun e => by have := congrArg Fin.val e; simp at this; omega),
          if_neg (fun e => by have := congrArg Fin.val e; simp at this; omega),
          if_neg (fun e => by have := congrArg Fin.val e; simp at this; omega)]; exact h14
      · rw [if_neg (fun e => by have := congrArg Fin.val e; simp at this; omega),
          if_neg (fun e => by have := congrArg Fin.val e; simp at this; omega),
          if_neg (fun e => by have := congrArg Fin.val e; simp at this; omega)]; exact h3
    · intro j hj
      rw [b16_l] at hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hj
      rcases clocked_cases _ j with ⟨i, rfl⟩ | rfl | rfl
      · rw [clockIn_src, hinp, uinput_eq]
        rw [if_neg (fun e => hj.1 (by rw [e])), if_neg (fun e => hj.2.1 (by rw [e])),
          if_neg (fun e => hj.2.2.1 (by rw [e]))]
      · exact clockIn_clock _ _
      · exact clockIn_reset _ _
    · intro x hx _
      exact hbl x hx
  have R' := piece_oracle (o := RecoveryOracle.correctedSat) (ports K) R16 (fun _ => 0) (b16 K).slot
    (b16 K).injective hqs A hin
  set A' := install (b16 K).slot A (fun j => ZeroPadding.pad ((fun _ => 0) j) (clockOut _ final.tapes n1 j))
    with hA'
  have hport : ∀ (i : Fin (ENP.UStage.program g.degree).base.tapeCount) (x : Fin (T K)),
      (cslot _ i, x) ∈ (b16 K).l → A' x = final.tapes i := by
    intro i x hm
    rw [hA', Bank.install_port (b16 K) A _ hm]
    simp only [ZeroPadding.pad_zero, clockOut_src]
  refine ⟨c1 + (n1 + 2), by omega, A', R', ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hA', Bank.install_high (b16 K) A _ x (by change off K 16 + sz K 16 ≤ x.val; rw [← off_succ]; exact hx)]
    exact hbl x (le_trans (off_mono K (by norm_num)) hx)
  · intro i hi
    rw [hA', Bank.install_low (b16 K) A _ (sh K i) (sh_lt_off K i 16)]
    apply updates_not
    intro p hp he
    rw [b16_l] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    apply hi
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      · have := (sh_inj K _ _).mp he
        subst this
        simp
  · rw [hport (ENP.UStage.queryPort g.degree) (sh K 3) (by rw [b16_l]; simp)]
    have := hlen (ENP.UStage.queryPort g.degree)
    rw [hinp, uinput_eq, if_neg (fun e => by have := congrArg Fin.val e; simp at this; omega),
      if_neg (fun e => by have := congrArg Fin.val e; simp at this; omega),
      if_neg (fun e => by have := congrArg Fin.val e; simp at this; omega)] at this
    simp only [List.length_nil] at this
    omega
  · rw [hport (ENP.UStage.flagPort g.degree) (sh K 19) (by rw [b16_l]; simp)]
    exact hflag
  · intro h1
    rw [hport (ENP.UStage.descPort g.degree) (sh K 14) (by rw [b16_l]; simp)]
    exact hdesc h1

end

section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) (c : Cfg)

theorem ne_of_not_mem {i : Fin 32} {l : List (Fin 32)} (h : i ∉ l) {j : Fin 32} (hj : j ∈ l) : i ≠ j := by
  rintro rfl; exact h hj

/-- **The second half of the head** (paper §11.6, stage 1 with its workspace). -/
theorem headTwoRuns : HeadTwoRuns K c := by
  intro C0 E0 hSB
  refine ⟨2 * CloseoutCapacity.coefficient c.A c.B + CloseoutCapacity.coefficient c.Aq c.Bq +
      2 * (RecoveryFullBound.coefficient g.degree * 2 ^ RecoveryFullBound.degree g.degree) + 2 * C0 + 10,
    max (max (c.A + 1) (c.Aq + 1)) (max (RecoveryFullBound.degree g.degree) E0), ?_⟩
  intro n point ν z post A hL f0 f1 f4 f5 f7 f9 f10 f12 fz fb
  obtain ⟨hνq, hqm, hmn⟩ := hL.width_le
  have hqn : g.width s ν ≤ n := by omega
  have z2 := fz 2 (by decide)
  have z3 := fz 3 (by decide)
  have z6 := fz 6 (by decide)
  have z8 := fz 8 (by decide)
  have z11 := fz 11 (by decide)
  have z13 := fz 13 (by decide)
  have z14 := fz 14 (by decide)
  have z15 := fz 15 (by decide)
  have z19 := fz 19 (by decide)
  -- pieces 11–13: the capacities
  obtain ⟨t11, ht11, A12, R11, B12, K12, P12, W12⟩ :=
    cap_piece K 11 (by decide) rfl c.A c.B 6 (by decide) point A f1 z6 fb
  obtain ⟨t12, ht12, A13, R12, B13, K13, P13, W13⟩ :=
    cap_piece K 12 (by decide) rfl c.A c.B 11 (by decide) point A12 P12
      (by rw [K12 11 (by decide) (by decide)]; exact z11) B12
  obtain ⟨t13, ht13, A14, R13, B14, K14, P14, W14⟩ :=
    cap_piece K 13 (by decide) rfl c.Aq c.Bq 15 (by decide) point A13 P13
      (by rw [K13 15 (by decide) (by decide), K12 15 (by decide) (by decide)]; exact z15) B13
  -- pieces 14–15: the caps
  have keep14 : ∀ i : Fin 32, i ∉ [1, 6, 11, 15] → A14 (sh K i) = A (sh K i) := by
    intro i hi
    rw [K14 i (ne_of_not_mem hi (by simp)) (ne_of_not_mem hi (by simp)),
      K13 i (ne_of_not_mem hi (by simp)) (ne_of_not_mem hi (by simp)),
      K12 i (ne_of_not_mem hi (by simp)) (ne_of_not_mem hi (by simp))]
  obtain ⟨t14, ht14, A15, R14, B15, K15, Q15, Bc15⟩ :=
    fb_piece K 14 (by decide) rfl 7 8 (by decide) (g.width s ν) A14
      (by rw [keep14 7 (by decide)]; exact f7) (by rw [keep14 8 (by decide)]; exact z8) B14
  obtain ⟨t15, ht15, A16, R15, B16, K16, Q16, Bc16⟩ :=
    fb_piece K 15 (by decide) rfl 12 13 (by decide) (g.width s ν) A15
      (by rw [K15 12 (by decide) (by decide), keep14 12 (by decide)]; exact f12)
      (by rw [K15 13 (by decide) (by decide), keep14 13 (by decide)]; exact z13) B15
  have keep16 : ∀ i : Fin 32, i ∉ [1, 6, 11, 15, 7, 8, 12, 13] → A16 (sh K i) = A (sh K i) := by
    intro i hi
    rw [K16 i (ne_of_not_mem hi (by simp)) (ne_of_not_mem hi (by simp)),
      K15 i (ne_of_not_mem hi (by simp)) (ne_of_not_mem hi (by simp)), keep14 i (by
        intro hm; apply hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl <;> decide)]
  have h6 : A16 (sh K 6) = List.replicate (CloseoutCapacity.capacity c.A c.B n) true := by
    rw [K16 6 (by decide) (by decide), K15 6 (by decide) (by decide), K14 6 (by decide) (by decide),
      K13 6 (by decide) (by decide)]
    exact W12
  -- piece 16: stage 1
  obtain ⟨t16, ht16, A17, R16, B17, K17, hq17, hf17, hd17⟩ := s1_piece K c C0 E0 hSB ν z hL A16
    (by rw [keep16 4 (by decide)]; exact f4) (by rw [keep16 5 (by decide)]; exact f5) h6
    (by rw [keep16 19 (by decide)]; exact z19) (by rw [keep16 14 (by decide)]; exact z14)
    (by rw [keep16 3 (by decide)]; exact z3) B16
  have keep17 : ∀ i : Fin 32, i ∉ [1, 6, 11, 15, 7, 8, 12, 13, 4, 5, 19, 14, 3] → A17 (sh K i) = A (sh K i) := by
    intro i hi
    rw [K17 i (by
        intro hm; apply hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      keep16 i (by
        intro hm; apply hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  -- the traces
  have s11 := step_call K c (k := 11) (l := 12) R11 (fun q => next_plain K c 11 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  have s12 := step_call K c (k := 12) (l := 13) R12 (fun q => next_plain K c 12 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  have s13 := step_call K c (k := 13) (l := 14) R13 (fun q => next_plain K c 13 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  have s14 := step_call K c (k := 14) (l := 15) R14 (fun q => next_plain K c 14 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  have s15 := step_call K c (k := 15) (l := 16) R15 (fun q => next_plain K c 15 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) q _)
  have pre := trans (trans (trans (trans s11 s12) s13) s14) s15
  -- the cost
  set V := 2 ^ n + 1 with hV
  set E := max (max (c.A + 1) (c.Aq + 1)) (max (RecoveryFullBound.degree g.degree) E0) with hE
  have vA : V ^ (c.A + 1) ≤ V ^ E := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have vQ : V ^ (c.Aq + 1) ≤ V ^ E := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have vF : V ^ RecoveryFullBound.degree g.degree ≤ V ^ E := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have v0 : V ^ E0 ≤ V ^ E := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have vE : 1 ≤ V ^ E := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hq2 : g.width s ν + 2 ≤ 2 * V := by
    have : n < 2 ^ n := Nat.lt_two_pow_self
    omega
  have fbq : (g.width s ν + 2) ^ RecoveryFullBound.degree g.degree ≤
      2 ^ RecoveryFullBound.degree g.degree * V ^ RecoveryFullBound.degree g.degree := by
    rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left hq2 _
  have c11 := ht11.trans (Nat.mul_le_mul_left (CloseoutCapacity.coefficient c.A c.B) vA)
  have c12 := ht12.trans (Nat.mul_le_mul_left (CloseoutCapacity.coefficient c.A c.B) vA)
  have c13 := ht13.trans (Nat.mul_le_mul_left (CloseoutCapacity.coefficient c.Aq c.Bq) vQ)
  have fb' : RecoveryFullBound.coefficient g.degree * (g.width s ν + 2) ^ RecoveryFullBound.degree g.degree ≤
      RecoveryFullBound.coefficient g.degree * 2 ^ RecoveryFullBound.degree g.degree * V ^ E := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (fbq.trans (Nat.mul_le_mul_left _ vF))
  have c14 := ht14.trans fb'
  have c15 := ht15.trans fb'
  have c16 := ht16.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left C0 v0)) 2)
  have hsum : t11 + 1 + (t12 + 1) + (t13 + 1) + (t14 + 1) + (t15 + 1) + (t16 + 1) ≤
      (2 * CloseoutCapacity.coefficient c.A c.B + CloseoutCapacity.coefficient c.Aq c.Bq +
        2 * (RecoveryFullBound.coefficient g.degree * 2 ^ RecoveryFullBound.degree g.degree) + 2 * C0 + 10) *
        V ^ E := by
    have e : (2 * CloseoutCapacity.coefficient c.A c.B + CloseoutCapacity.coefficient c.Aq c.Bq +
        2 * (RecoveryFullBound.coefficient g.degree * 2 ^ RecoveryFullBound.degree g.degree) + 2 * C0 + 10) *
        V ^ E = 2 * (CloseoutCapacity.coefficient c.A c.B * V ^ E) + CloseoutCapacity.coefficient c.Aq c.Bq * V ^ E +
        2 * (RecoveryFullBound.coefficient g.degree * 2 ^ RecoveryFullBound.degree g.degree * V ^ E) +
        2 * (C0 * V ^ E) + 10 * V ^ E := by ring
    rw [e]; omega
  refine ⟨t11 + 1 + (t12 + 1) + (t13 + 1) + (t14 + 1) + (t15 + 1) + (t16 + 1), hsum, A17,
    by rw [keep17 0 (by decide)]; exact f0, ?_, by rw [keep17 2 (by decide)]; exact z2, hq17, ?_, ?_,
    by rw [keep17 9 (by decide)]; exact f9, by rw [keep17 10 (by decide)]; exact f10, ?_, ?_, ?_, ?_,
    by rw [keep17 16 (by decide)]; exact fz 16 (by decide), by rw [keep17 17 (by decide)]; exact fz 17 (by decide),
    by rw [keep17 18 (by decide)]; exact fz 18 (by decide), by rw [keep17 21 (by decide)]; exact fz 21 (by decide),
    by rw [keep17 22 (by decide)]; exact fz 22 (by decide), by rw [keep17 23 (by decide)]; exact fz 23 (by decide),
    by rw [keep17 24 (by decide)]; exact fz 24 (by decide), by rw [keep17 31 (by decide)]; exact fz 31 (by decide),
    B17, ?_, ?_⟩
  · rw [K17 1 (by decide), K16 1 (by decide) (by decide), K15 1 (by decide) (by decide)]; exact P14
  · rw [K17 7 (by decide), K16 7 (by decide) (by decide)]; exact Q15
  · rw [K17 8 (by decide), K16 8 (by decide) (by decide)]; exact Bc15
  · rw [K17 11 (by decide), K16 11 (by decide) (by decide), K15 11 (by decide) (by decide),
      K14 11 (by decide) (by decide)]; exact W13
  · rw [K17 12 (by decide)]; exact Q16
  · rw [K17 13 (by decide)]; exact Bc16
  · rw [K17 15 (by decide), K16 15 (by decide) (by decide), K15 15 (by decide) (by decide)]; exact W14
  · intro h1
    refine ⟨trans pre (step_call K c (k := 16) (l := 18) R16 (fun q => ?_)), hd17 h1⟩
    rw [next_16, hf17.mpr h1]
    rfl
  · intro h1
    refine trans pre (step_call K c (k := 16) (l := 17) R16 (fun q => ?_))
    have hf : readTapeBit (A17 (sh K 19)) 0 = false := by
      cases hb : readTapeBit (A17 (sh K 19)) 0
      · rfl
      · exact absurd (hf17.mp hb) h1
    rw [next_16, hf]
    rfl

end

end NearCubicGates.Close.Recovery.After
