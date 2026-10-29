import Proof.Gates.Recovery.AfterStep
import Proof.Gates.Recovery.CaseOneSem

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) (c : Cfg)

theorem b17_l : (b17 K).l = [(⟨0, by have := K.c1.large; have := K.c1.output.isLt; omega⟩, sh K 0),
    (⟨1, by have := K.c1.large; have := K.c1.output.isLt; omega⟩, sh K 1),
    (⟨2, by have := K.c1.large; have := K.c1.output.isLt; omega⟩, sh K 7), (K.c1.output, sh K 2)] := rfl

/-- **Piece 17, Case 1 (i)** (`sec:gadget-extract`, `sec:all-lengths`). -/
theorem caseOne_i_runs : ∃ C E : ℕ, ∀ (n : ℕ) (point : BitInput n) (ν : ℕ) (z : BitInput (2 ^ ν)) (post : List Bool)
    (A : Fin (T K) → List Bool), Live s g n ν → ¬ g.SrcExists s ν z →
    A (sh K 0) = RepairOrdinary.frame (List.ofFn z) ++ post →
    A (sh K 1) = RepairOrdinary.frame (List.ofFn point) →
    A (sh K 7) = List.replicate (g.width s ν) true →
    A (sh K 2) = [] →
    (∀ x : Fin (T K), off K 17 ≤ x.val → A x = []) →
    ∃ cost, cost ≤ C * (2 ^ n + 1) ^ E ∧ ∃ B : Fin (T K) → List Bool,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) cost (start K c 17 A) (stopAt K c B) ∧
      B (sh K 2) = RepairOrdinary.frame (g.gateCore s P (selectedAmplifier s.amplification g.degree) ν z
        (CloseoutLanguage.clauseWidth g.clauseDegree (g.width s ν)) g.positionLog n point).toNat.bits := by
  refine ⟨K.c1.C + 1, K.c1.E, ?_⟩
  intro n point ν z post A hL hS hZ hPT hQ hO hB
  obtain ⟨hνq, hqm, hmn⟩ := hL.width_le
  have hq1 : 1 ≤ g.width s ν := by have := hL.pos; omega
  have hqn : g.width s ν ≤ n := by omega
  have har : ((selectedAmplifier s.amplification g.degree).output (g.width s ν)
      (cycFn ν z (g.width s ν))).arity ≤ n :=
    (CaseOneSem.arity_fit s g _ hL.ampLarge ν _).trans (by omega)
  obtain ⟨out, hrun, hout⟩ := K.c1.run ν (g.width s ν) z post n point hq1 hqn har
  obtain ⟨time, htime, hready⟩ := exact_time hrun
  have hin : ∀ j, A ((b17 K).slot j) = Recovery.oneInput K.c1.t (RepairOrdinary.frame (List.ofFn z) ++ post)
      (RepairOrdinary.frame (List.ofFn point)) (g.width s ν) j := by
    apply Bank.input
    · intro p hp
      rw [b17_l] at hp
      have hl := K.c1.large
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · simpa [Recovery.oneInput, Recovery.threeWords] using hZ
      · simpa [Recovery.oneInput, Recovery.threeWords] using hPT
      · simpa [Recovery.oneInput, Recovery.threeWords] using hQ
      · simp only [Recovery.oneInput]
        rw [dif_neg (by omega)]
        exact hO
    · intro j hj
      rw [b17_l] at hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hj
      unfold Recovery.oneInput
      rw [dif_neg]
      intro hlt
      have h0 := hj.1
      have h1 := hj.2.1
      have h2 := hj.2.2.1
      interval_cases hv : j.val
      · exact h0 (Fin.ext (by simp [hv]))
      · exact h1 (Fin.ext (by simp [hv]))
      · exact h2 (Fin.ext (by simp [hv]))
    · intro x hx _
      exact hB x hx
  have hR := piece_ordinary (o := RecoveryOracle.correctedSat) (ports K) hready (b17 K).slot (b17 K).injective A hin
  have tr := step_stop K c (k := 17) hR (fun q => next_17 K c q _)
  refine ⟨time + 1, ?_, _, tr, ?_⟩
  · have h1 : 1 ≤ (2 ^ n + 1) ^ K.c1.E := Nat.one_le_pow _ _ (Nat.succ_pos _)
    nlinarith
  · rw [Bank.install_port (b17 K) A out (j := K.c1.output) (by rw [b17_l]; simp), hout,
      CaseOneSem.gateCore_caseOne_i s g P _ ν z _ _ n hS]

/-- **Piece 23, the exceptional slice** (`sec:all-lengths`). -/
theorem falseRuns (n : ℕ) (point : BitInput n) (ν : ℕ) (z : BitInput (2 ^ ν)) (A : Fin (T K) → List Bool)
    (h1 : g.SrcExists s ν z) (h2 : ¬ ∃ t, HonestTable (g.outC s ν (g.firstSrc s ν z h1)).circuit t)
    (hO : A (sh K 2) = []) (hB : ∀ x : Fin (T K), off K 23 ≤ x.val → A x = []) :
    ∃ B : Fin (T K) → List Bool,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) 5 (start K c 23 A) (stopAt K c B) ∧
      B (sh K 2) = RepairOrdinary.frame (g.gateCore s P (selectedAmplifier s.amplification g.degree) ν z
        (CloseoutLanguage.clauseWidth g.clauseDegree (g.width s ν)) g.positionLog n point).toNat.bits := by
  have hready := HierarchyFixedWord.word_ready [false]
  have hin : ∀ j, A ((fBank K).slot j) = (fun _ => ([] : List Bool)) j := by
    apply Bank.input
    · intro p hp
      simp only [fBank, mkBank, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact hO
    · intro j _; rfl
    · intro x hx _
      exact hB x hx
  have hR := piece_ordinary (o := RecoveryOracle.correctedSat) (ports K) hready (fBank K).slot (fBank K).injective A hin
  have tr := step_stop K c (k := 23) hR (fun q => next_23 K c q _)
  refine ⟨_, tr, ?_⟩
  rw [Bank.install_port (fBank K) A _ (j := 0) (x := sh K 2) (by simp [fBank, mkBank])]
  have hg : g.gateCore s P (selectedAmplifier s.amplification g.degree) ν z
      (CloseoutLanguage.clauseWidth g.clauseDegree (g.width s ν)) g.positionLog n = fun _ => false := by
    unfold GateParams.gateCore
    rw [dif_pos h1, dif_neg h2]
  rw [hg]
  rfl

end

end NearCubicGates.Close.Recovery.After
