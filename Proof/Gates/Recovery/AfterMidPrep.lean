import Proof.Gates.Recovery.AfterStep
import Proof.CaseAnalysis.CaseTwoBudget

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) (c : Cfg)

/-- Piece 18's log tape. -/
noncomputable abbrev log18 : Fin (T K) := blk K 18 (by decide) le_rfl

theorem log18_val : (log18 K).val = off K 18 := rfl

theorem tslot18_inj : Function.Injective (tslot K 18 (by decide) le_rfl (sh K 3) (sh K 15)) := by
  have := off_ge K 18
  intro a b h
  have hv := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [tslot, blk] at hv ⊢ <;> omega

/-- **Piece 18** (the query clear, paper §11.6 "SAT formulas" sharing one query tape): the shared query is erased to
`0^cap` with the driver `1^cap` on WC. -/
theorem piece18 (A : Fin (T K) → List Bool) (cap : ℕ) (h3 : (A (sh K 3)).length ≤ cap)
    (h15 : A (sh K 15) = List.replicate cap true) (hb : A (log18 K) = []) :
    OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) (2 * cap + 4 + 1) (start K c 18 A)
      (start K c 19 (Function.update (Function.update A (sh K 3) (List.replicate cap false)) (log18 K)
        (List.replicate (cap + 1) false))) := by
  have hr := clear_ready (tslot K 18 (by decide) le_rfl (sh K 3) (sh K 15)) (tslot18_inj K) A cap h3 h15 hb
  exact step_call K c (k := 18) (l := 19) (Ready.ordinary (ports K) hr)
    (fun q => next_plain K c 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)

/-- Installing a bank's outputs keeps every tape below its block that is not one of its ports. -/
theorem bank_keep {t : ℕ} (b : Bank (T K) t) (A : Fin (T K) → List Bool) (out : Fin t → List Bool) (x : Fin (T K))
    (hx : x.val < b.off) (hn : ∀ p ∈ b.l, p.2 ≠ x) : install b.slot A out x = A x := by
  rw [b.install_low A out x hx, updates_not out A hn]

theorem off_succ (k : ℕ) : off K (k + 1) = off K k + sz K k := rfl

theorem piece19 (A : Fin (T K) → List Bool) {R B : ℕ} (cb : BooleanCircuit R) (hc : cb.size ≤ B)
    (h14 : A (sh K 14) = RepairOrdinary.frame (OuterPCPRecovery.canonicalBoundedCircuitDescription B cb))
    (h7 : A (sh K 7) = List.replicate R true) (h8 : A (sh K 8) = List.replicate B true) (h16 : A (sh K 16) = [])
    (hb : ∀ x : Fin (T K), off K 19 ≤ x.val → A x = []) :
    ∃ time out, time ≤ CloseoutCaseTwo.Cold.budget B cb ∧
      OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) (time + 1) (start K c 19 A)
        (start K c 20 (install (convBank K).slot A out)) ∧
      out 132 = RepairOrdinary.frame (PCPPNative.descriptor cb) ∧
      out 1 = RepairOrdinary.frame (OuterPCPRecovery.canonicalBoundedCircuitDescription B cb) := by
  obtain ⟨out, hr, h132, -, h1, -⟩ := CloseoutCaseTwo.Cold.converter_run cb hc [] []
  obtain ⟨time, ht, hrr⟩ := exact_time hr
  have hin := (convBank K).input A (CloseoutCaseTwo.Cold.input []
      (RepairOrdinary.frame (OuterPCPRecovery.canonicalBoundedCircuitDescription B cb)) [] R B) (by
      intro p hp
      simp only [convBank, mkBank, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · simpa [CloseoutCaseTwo.Cold.input] using h14
      · simpa [CloseoutCaseTwo.Cold.input] using h7
      · simpa [CloseoutCaseTwo.Cold.input] using h8
      · simpa [CloseoutCaseTwo.Cold.input] using h16)
    (by
      intro j hj
      simp only [convBank, mkBank, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hj
      unfold CloseoutCaseTwo.Cold.input
      split_ifs with e0 e1 e2 e3 e4 <;> first | rfl | (exfalso; subst_vars; simp_all))
    (fun x hx _ => hb x hx)
  refine ⟨time, out, ht, ?_, h132, h1⟩
  exact step_call K c (k := 19) (l := 20) (piece_ordinary (ports K) hrr _ (convBank K).injective A hin)
    (fun q => next_plain K c 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)

/-- **Piece 20** (`unframe`, paper §11.6: the A-run reads the raw descriptor): `frame d` on FD (`16`) ↦ `d` on DESC
(`17`). -/
theorem piece20 (A : Fin (T K) → List Bool) (d : List Bool) (h16 : A (sh K 16) = RepairOrdinary.frame d)
    (h17 : A (sh K 17) = []) (hb : ∀ x : Fin (T K), off K 20 ≤ x.val → A x = []) :
    ∃ time out, time ≤ unframe.K * (d.length + 1) ∧
      OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) (time + 1) (start K c 20 A)
        (start K c 21 (install (ufBank K).slot A out)) ∧ out unframe.dst = d := by
  obtain ⟨out, hr, hd⟩ := unframe.run d
  obtain ⟨time, ht, hrr⟩ := exact_time hr
  have hin := (ufBank K).input A (oneBank unframe.src (RepairOrdinary.frame d)) (by
      intro p hp
      simp only [ufBank, mkBank, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · simpa [oneBank] using h16
      · simpa [oneBank, Ne.symm unframe.ne] using h17)
    (by
      intro j hj
      simp only [ufBank, mkBank, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hj
      simp [oneBank, Ne.symm hj.1])
    (fun x hx _ => hb x hx)
  refine ⟨time, out, ht, ?_, hd⟩
  exact step_call K c (k := 20) (l := 21) (piece_ordinary (ports K) hrr _ (ufBank K).injective A hin)
    (fun q => next_plain K c 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)

theorem piece21 (A : Fin (T K) → List Bool) (ν : ℕ) {m : ℕ} (B : BooleanCircuit m)
    (h17 : A (sh K 17) = PCPPNative.descriptor B) (h9 : A (sh K 9) = List.replicate ν true)
    (h18 : A (sh K 18) = []) (hb : ∀ x : Fin (T K), off K 21 ≤ x.val → A x = []) :
    ∃ time out, time ≤ (aR s g).K * (ν + 1) ^ (aR s g).e ∧
      OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) (time + 1) (start K c 21 A)
        (start K c 22 (install (b21 K).slot A out)) ∧
      out (aR s g).dIn = PCPPNative.descriptor B ∧ out (aR s g).nIn = List.replicate ν true ∧
      out (aR s g).wOut = (Outer.outC s.mw (g.sv s) ν B).word ∧
      (out (aR s g).wOut).length ≤ (PCPPNative.descriptor B).length + ν + (aR s g).K * (ν + 1) ^ (aR s g).e := by
  obtain ⟨out, hr, hdI, hnI, -, hwO⟩ := (aR s g).run ν m B
  have hlen := CheckedPCPP.Dock.ready_len hr ((PCPPNative.descriptor B).length + ν) (by
    intro i
    simp only [OuterM.aBank]
    split_ifs <;> simp)
  obtain ⟨time, ht, hrr⟩ := exact_time hr
  have hn := (aR s g).nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  have hin := (b21 K).input A (OuterM.aBank (aR s g).dIn (aR s g).nIn ν B) (by
      intro p hp
      simp only [b21, arBank, mkBank, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · simpa [OuterM.aBank] using h17
      · simpa [OuterM.aBank, Ne.symm hn.1.1] using h9
      · simpa [OuterM.aBank, Ne.symm hn.1.2.2, Ne.symm hn.2.1.2] using h18)
    (by
      intro j hj
      simp only [b21, arBank, mkBank, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hj
      simp [OuterM.aBank, Ne.symm hj.1, Ne.symm hj.2.1])
    (fun x hx _ => hb x hx)
  refine ⟨time, out, ht, ?_, hdI, hnI, hwO, hlen _⟩
  exact step_call K c (k := 21) (l := 22) (piece_ordinary (ports K) hrr _ (b21 K).injective A hin)
    (fun q => next_plain K c 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) q _)

end

end NearCubicGates.Close.Recovery.After
