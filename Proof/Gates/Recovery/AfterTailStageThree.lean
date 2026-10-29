import Proof.Gates.Recovery.AfterTailCopies
import Proof.Gates.ENP.ListedInst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.RecoveryChoice NearCubicWires.OuterPCPRecovery NearCubicWires.ExecutableInterfaces

section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) (c : Cfg)

theorem b27_l : (b27 K).l =
    [(cslot _ (tableL g.degree), sh K 21), (cslot _ (rL g.degree), sh K 10), (cslot _ (wL g.degree), sh K 11),
      (cslot _ (ENP.UStage.flagPort g.degree), sh K 31), (cslot _ (ENP.UStage.descPort g.degree), sh K 23),
      (cslot _ (ENP.UStage.queryPort g.degree), sh K 3)] := rfl

/-- The zero-padding capacities of stage 3: the clear driver's length on the query tape, `0` elsewhere. -/
noncomputable def caps27 (N : ℕ) : Fin (pU g).base.tapeCount → ℕ :=
  fun j => if j = cslot _ (ENP.UStage.queryPort g.degree) then N else 0

theorem uT_ge (d : ℕ) : 342 ≤ ENP.USupply.uTapes d := by unfold ENP.USupply.uTapes; omega

/-- **Piece 27, stage 3** (`sec:all-lengths`). -/
theorem ready27 (ν : ℕ) (z : BitInput (2 ^ ν)) {ℓ : ℕ} (hℓ : ℓ ≤ g.width s ν) (t : BitInput (2 ^ ℓ)) (W N : ℕ)
    (hb : 0 < g.bound s ν)
    (hW : originalWorkspace (g.width s ν) (g.bound s ν) (List.ofFn t).length (List.ofFn t).length ≤ W)
    (hsource : (DedupBytes.fields (ENP.unitPCP ℓ (boolFunctionTable (tableOracle t)))).length ≤ W)
    (htwo : 2 ^ g.width s ν ≤ W) (A : Fin (T K) → List Bool)
    (h21 : A (sh K 21) = RepairOrdinary.frame (List.ofFn t)) (h10 : A (sh K 10) = List.replicate (g.width s ν) true)
    (h11 : A (sh K 11) = List.replicate W true) (h31 : A (sh K 31) = []) (h23 : A (sh K 23) = [])
    (h3 : A (sh K 3) = List.replicate N false)
    (hblank : ∀ x : Fin (T K), off K 27 ≤ x.val → x.val < off K 28 → A x = []) :
    ∃ cost, cost ≤ 2 * ENP.UStage.cost g.degree ℓ (g.width s ν) W (boolFunctionTable (tableOracle t)) hℓ z + 2 ∧
      ∃ A' : Fin (T K) → List Bool,
        Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c 27)) cost A A' ∧
        (readTapeBit (A' (sh K 31)) 0 = true ↔ SmallOracle (g.matchPCP s ν hℓ t) g.degree z) ∧
        (∀ small : SmallOracle (g.matchPCP s ν hℓ t) g.degree z, A' (sh K 23) =
          RepairOrdinary.frame (canonicalBoundedCircuitDescription (g.bound s ν)
            (oracleSelector (g.matchPCP s ν hℓ t) g.degree z small).circuit)) ∧
        (∀ i : Fin 32, i ∉ [21, 10, 11, 31, 23, 3] → A' (sh K i) = A (sh K i)) ∧
        (∀ x : Fin (T K), off K 28 ≤ x.val → A' x = A x) := by
  obtain ⟨cst, hc, final, tr, hal, hflag, hdesc, _, _⟩ := ENP.UInst.stage3_run s g ν z hℓ t [] W hb hW hsource htwo
  obtain ⟨n', hn', hready, _⟩ := clocked_ready tr hal
  set p := ENP.UStage.program g.degree with hp
  set input := ENP.UStage.input g.degree (RepairOrdinary.frame (List.ofFn t) ++ []) (g.width s ν) W with hinput
  have hu := uT_ge g.degree
  -- the six listed ports
  have hqne : ∀ i : Fin p.base.tapeCount, i ≠ ENP.UStage.queryPort g.degree →
      cslot p i ≠ cslot p (ENP.UStage.queryPort g.degree) := fun i hi h => hi (cslot_injective p h)
  have hcap_ne : ∀ i : Fin p.base.tapeCount, i ≠ ENP.UStage.queryPort g.degree → caps27 N (cslot p i) = 0 := by
    intro i hi; unfold caps27; rw [if_neg (hqne i hi)]
  have hT_q : tableL g.degree ≠ ENP.UStage.queryPort g.degree := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have hR_q : rL g.degree ≠ ENP.UStage.queryPort g.degree := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have hW_q : wL g.degree ≠ ENP.UStage.queryPort g.degree := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have hF_q : ENP.UStage.flagPort g.degree ≠ ENP.UStage.queryPort g.degree := by
    intro h; have := congrArg Fin.val h; simp at this
  have hD_q : ENP.UStage.descPort g.degree ≠ ENP.UStage.queryPort g.degree := by
    intro h; have := congrArg Fin.val h; simp at this
  have hin_other : ∀ i : Fin p.base.tapeCount, i ≠ tableL g.degree → i ≠ rL g.degree → i ≠ wL g.degree →
      input i = [] := by
    intro i h1 h2 h3
    rw [hinput, uinput_eq, if_neg h1, if_neg h2, if_neg h3]
  have hF_in : input (ENP.UStage.flagPort g.degree) = [] := hin_other _
    (by intro h; have := congrArg Fin.val h; simp at this; omega)
    (by intro h; have := congrArg Fin.val h; simp at this; omega)
    (by intro h; have := congrArg Fin.val h; simp at this; omega)
  have hD_in : input (ENP.UStage.descPort g.degree) = [] := hin_other _
    (by intro h; have := congrArg Fin.val h; simp at this; omega)
    (by intro h; have := congrArg Fin.val h; simp at this; omega)
    (by intro h; have := congrArg Fin.val h; simp at this; omega)
  have hQ_in : input (ENP.UStage.queryPort g.degree) = [] := hin_other _
    (by intro h; have := congrArg Fin.val h; simp at this; omega)
    (by intro h; have := congrArg Fin.val h; simp at this; omega)
    (by intro h; have := congrArg Fin.val h; simp at this; omega)
  have hin : ∀ j, A ((b27 K).slot j) = ZeroPadding.pad (caps27 N j) (clockIn p input j) := by
    apply Bank.input
    · intro q hq
      rw [b27_l] at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hcap_ne _ hT_q, ZeroPadding.pad_zero, clockIn_src, hinput, uinput_eq, if_pos rfl, h21, List.append_nil]
      · rw [hcap_ne _ hR_q, ZeroPadding.pad_zero, clockIn_src, hinput, uinput_eq,
          if_neg (by intro h; have := congrArg Fin.val h; simp at this), if_pos rfl, h10]
      · rw [hcap_ne _ hW_q, ZeroPadding.pad_zero, clockIn_src, hinput, uinput_eq,
          if_neg (by intro h; have := congrArg Fin.val h; simp at this),
          if_neg (by intro h; have := congrArg Fin.val h; simp at this), if_pos rfl, h11]
      · rw [hcap_ne _ hF_q, ZeroPadding.pad_zero, clockIn_src, hF_in, h31]
      · rw [hcap_ne _ hD_q, ZeroPadding.pad_zero, clockIn_src, hD_in, h23]
      · simp only
        rw [clockIn_src, hQ_in, h3]
        unfold caps27
        rw [if_pos rfl]
        simp [ZeroPadding.pad]
    · intro j hj
      rw [b27_l] at hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hj
      obtain ⟨j1, j2, j3, j4, j5, j6⟩ := hj
      have hc0 : caps27 N j = 0 := by unfold caps27; rw [if_neg (Ne.symm j6)]
      rw [hc0, ZeroPadding.pad_zero]
      rcases clocked_cases p j with ⟨i, rfl⟩ | rfl | rfl
      · rw [clockIn_src]
        exact hin_other i (fun h => j1 (by rw [h])) (fun h => j2 (by rw [h])) (fun h => j3 (by rw [h]))
      · exact clockIn_clock p input
      · exact clockIn_reset p input
    · intro x hx1 hx2
      exact hblank x hx1 hx2
  have hqslot : (b27 K).slot (clocked p).queryTape = (ports K).queryTape := by
    rw [← cslot_query]
    exact Bank.slot_port (b27 K) (by rw [b27_l]; exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have hR := piece_oracle (o := RecoveryOracle.correctedSat) (ports K) hready (caps27 N) (b27 K).slot
    (b27 K).injective hqslot A hin
  have hcost : cst + (n' + 2) ≤
      2 * ENP.UStage.cost g.degree ℓ (g.width s ν) W (boolFunctionTable (tableOracle t)) hℓ z + 2 := by
    generalize ENP.UStage.cost g.degree ℓ (g.width s ν) W (boolFunctionTable (tableOracle t)) hℓ z = U at hc ⊢
    omega
  refine ⟨cst + (n' + 2), hcost, _, hR, ?_, ?_, ?_, ?_⟩
  · rw [Bank.install_port (b27 K) A _ (j := cslot _ (ENP.UStage.flagPort g.degree))
      (by rw [b27_l]; exact .tail _ (.tail _ (.tail _ (.head _))))]
    rw [show caps27 N (cslot (ENP.UStage.program g.degree) (ENP.UStage.flagPort g.degree)) = 0 from hcap_ne _ hF_q,
      ZeroPadding.pad_zero, clockOut_src]
    exact hflag
  · intro small
    rw [Bank.install_port (b27 K) A _ (j := cslot _ (ENP.UStage.descPort g.degree))
      (by rw [b27_l]; exact .tail _ (.tail _ (.tail _ (.tail _ (.head _)))))]
    rw [show caps27 N (cslot (ENP.UStage.program g.degree) (ENP.UStage.descPort g.degree)) = 0 from hcap_ne _ hD_q,
      ZeroPadding.pad_zero, clockOut_src]
    exact hdesc small
  · intro i hi
    have hlow : (sh K i).val < (b27 K).off := by
      have := off_ge K 27; have := i.isLt; simp only [sh_val]; show i.val < off K 27; omega
    rw [Bank.install_low (b27 K) A _ (sh K i) hlow]
    apply updates_not
    intro q hq
    rw [b27_l] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    obtain ⟨n21, n10, n11, n31, n23, n3⟩ := hi
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fun h => n21 ((sh_inj K _ _).mp h).symm
    · exact fun h => n10 ((sh_inj K _ _).mp h).symm
    · exact fun h => n11 ((sh_inj K _ _).mp h).symm
    · exact fun h => n31 ((sh_inj K _ _).mp h).symm
    · exact fun h => n23 ((sh_inj K _ _).mp h).symm
    · exact fun h => n3 ((sh_inj K _ _).mp h).symm
  · intro x hx
    apply Bank.install_high
    show off K 27 + sz K 27 ≤ x.val
    have : off K 28 = off K 27 + sz K 27 := rfl
    omega

end

end NearCubicGates.Close.Recovery.After
