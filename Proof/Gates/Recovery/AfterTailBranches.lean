import Proof.Gates.Recovery.AfterTailStageThree
import Proof.Gates.Recovery.CaseOneSem

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget NearCubicWires.ExecutableInterfaces

section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) (c : Cfg)

theorem b28_l : (b28 K).l = [(⟨0, by have := K.c1.large; have := K.c1.output.isLt; omega⟩, sh K 22),
    (⟨1, by have := K.c1.large; have := K.c1.output.isLt; omega⟩, sh K 1),
    (⟨2, by have := K.c1.large; have := K.c1.output.isLt; omega⟩, sh K 12), (K.c1.output, sh K 2)] := rfl

theorem b29_l : (b29 K).l = [((aR s g).dIn, sh K 17), ((aR s g).nIn, sh K 9), ((aR s g).wOut, sh K 24)] := rfl

theorem ht_l : (htBank K).l =
    [(⟨0, by have := K.ht.large; have := K.ht.output.isLt; omega⟩, sh K 24),
      (⟨1, by have := K.ht.large; have := K.ht.output.isLt; omega⟩, sh K 23),
      (⟨2, by have := K.ht.large; have := K.ht.output.isLt; omega⟩, sh K 1),
      (⟨3, by have := K.ht.large; have := K.ht.output.isLt; omega⟩, sh K 12),
      (⟨4, by have := K.ht.large; have := K.ht.output.isLt; omega⟩, sh K 13), (K.ht.output, sh K 2)] := rfl

/-- **Piece 28, Case 1 (iii)** (`sec:gadget-extract`, `sec:all-lengths`): the amplified table `O*` at the address. -/
theorem ready28 (n : ℕ) (point : BitInput n) {ℓ : ℕ} (t : BitInput (2 ^ ℓ)) (q : ℕ) (hq1 : 1 ≤ q) (hqn : q ≤ n)
    (har : ((selectedAmplifier s.amplification g.degree).output q (cycFn ℓ t q)).arity ≤ n)
    (A : Fin (T K) → List Bool) (h22 : A (sh K 22) = RepairOrdinary.frame (List.ofFn t))
    (hPT : A (sh K 1) = RepairOrdinary.frame (List.ofFn point)) (h12 : A (sh K 12) = List.replicate q true)
    (h2 : A (sh K 2) = []) (hblank : ∀ x : Fin (T K), off K 28 ≤ x.val → x.val < off K 29 → A x = []) :
    ∃ time, time ≤ K.c1.C * (2 ^ n + 1) ^ K.c1.E ∧ ∃ A' : Fin (T K) → List Bool,
      Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c 28)) time A A' ∧
      A' (sh K 2) = RepairOrdinary.frame
        (GateParams.amplified (selectedAmplifier s.amplification g.degree) q (cycFn ℓ t q) n point).toNat.bits := by
  obtain ⟨out, hrun, hout⟩ := K.c1.run ℓ q t [] n point hq1 hqn har
  obtain ⟨time, htime, hready⟩ := exact_time hrun
  have hin : ∀ j, A ((b28 K).slot j) = Recovery.oneInput K.c1.t (RepairOrdinary.frame (List.ofFn t) ++ [])
      (RepairOrdinary.frame (List.ofFn point)) q j := by
    apply Bank.input
    · intro p hp
      rw [b28_l] at hp
      have hl := K.c1.large
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · simpa [Recovery.oneInput, Recovery.threeWords] using h22
      · simpa [Recovery.oneInput, Recovery.threeWords] using hPT
      · simpa [Recovery.oneInput, Recovery.threeWords] using h12
      · simp only [Recovery.oneInput]
        rw [dif_neg (by omega)]
        exact h2
    · intro j hj
      rw [b28_l] at hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hj
      unfold Recovery.oneInput
      rw [dif_neg]
      intro hlt
      have h0 := hj.1
      have h1 := hj.2.1
      have h2' := hj.2.2.1
      interval_cases hv : j.val
      · exact h0 (Fin.ext (by simp [hv]))
      · exact h1 (Fin.ext (by simp [hv]))
      · exact h2' (Fin.ext (by simp [hv]))
    · intro x hx1 hx2
      exact hblank x hx1 hx2
  have hR := piece_ordinary (o := RecoveryOracle.correctedSat) (ports K) hready (b28 K).slot (b28 K).injective A hin
  refine ⟨time, htime, _, hR, ?_⟩
  rw [Bank.install_port (b28 K) A out (j := K.c1.output) (by rw [b28_l]; exact .tail _ (.tail _ (.tail _ (.head _)))),
    hout]

/-- **Piece 29, the A-run on `B*_src`** (`sec:all-lengths`, "the algorithm of imp:short-pcp is run deterministically on
`⟨B*_src⟩_ν`"): the word of `C_{⟨B⟩_ν}` on shared `24`. -/
theorem ready29 (ν : ℕ) {m : ℕ} (B : BooleanCircuit m) (A : Fin (T K) → List Bool)
    (h17 : A (sh K 17) = PCPPNative.descriptor B) (h9 : A (sh K 9) = List.replicate ν true) (h24 : A (sh K 24) = [])
    (hblank : ∀ x : Fin (T K), off K 29 ≤ x.val → x.val < off K 30 → A x = []) :
    ∃ time, time ≤ (aR s g).K * (ν + 1) ^ (aR s g).e ∧ ∃ A' : Fin (T K) → List Bool,
      Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c 29)) time A A' ∧
      A' (sh K 24) = (Outer.outC s.mw (g.sv s) ν B).word ∧
      (∀ i : Fin 32, i ∉ [17, 9, 24] → A' (sh K i) = A (sh K i)) ∧
      (∀ x : Fin (T K), off K 30 ≤ x.val → A' x = A x) := by
  obtain ⟨out, hrun, _, _, _, hw⟩ := (aR s g).run ν m B
  obtain ⟨time, htime, hready⟩ := exact_time hrun
  have hnd := (aR s g).nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hdn, hdf, hdw⟩, ⟨hnf, hnw⟩, hfw⟩ := hnd
  have hin : ∀ j, A ((b29 K).slot j) = OuterM.aBank (aR s g).dIn (aR s g).nIn ν B j := by
    apply Bank.input
    · intro p hp
      rw [b29_l] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · simp only [OuterM.aBank, if_pos rfl]; exact h17
      · simp only [OuterM.aBank, if_neg (Ne.symm hdn), if_pos rfl]; exact h9
      · simp only [OuterM.aBank, if_neg (Ne.symm hdw), if_neg (Ne.symm hnw)]; exact h24
    · intro j hj
      rw [b29_l] at hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hj
      simp only [OuterM.aBank, if_neg (Ne.symm hj.1), if_neg (Ne.symm hj.2.1)]
    · intro x hx1 hx2
      exact hblank x hx1 hx2
  have hR := piece_ordinary (o := RecoveryOracle.correctedSat) (ports K) hready (b29 K).slot (b29 K).injective A hin
  refine ⟨time, htime, _, hR, ?_, ?_, ?_⟩
  · rw [Bank.install_port (b29 K) A out (j := (aR s g).wOut) (by rw [b29_l]; exact .tail _ (.tail _ (.head _))), hw]
  · intro i hi
    have hlow : (sh K i).val < (b29 K).off := by
      have := off_ge K 29; have := i.isLt; simp only [sh_val]; show i.val < off K 29; omega
    rw [Bank.install_low (b29 K) A out (sh K i) hlow]
    apply updates_not
    intro p hp
    rw [b29_l] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    obtain ⟨n17, n9, n24⟩ := hi
    rcases hp with rfl | rfl | rfl
    · exact fun h => n17 ((sh_inj K _ _).mp h).symm
    · exact fun h => n9 ((sh_inj K _ _).mp h).symm
    · exact fun h => n24 ((sh_inj K _ _).mp h).symm
  · intro x hx
    apply Bank.install_high
    show off K 29 + sz K 29 ≤ x.val
    have : off K 30 = off K 29 + sz K 29 := rfl
    omega

/-- **Piece 30, the Case 2 producer** (`sec:all-lengths`): the gate core at the address. -/
theorem ready30 (n : ℕ) (point : BitInput n) (ν : ℕ) (z : BitInput (2 ^ ν)) (hνn : ν ≤ n)
    (hcut : K.ht.cutoff ≤ 2 ^ ν) (h : g.IsCaseTwo s ν z) (A : Fin (T K) → List Bool)
    (h24 : A (sh K 24) = (Outer.outC s.mw (g.sv s) ν (g.selectedPair s ν z h).src).word)
    (h23 : A (sh K 23) = RepairOrdinary.frame
      (OuterPCPRecovery.canonicalBoundedCircuitDescription (g.bound s ν) (g.selectedPair s ν z h).pf))
    (hPT : A (sh K 1) = RepairOrdinary.frame (List.ofFn point)) (h12 : A (sh K 12) = List.replicate (g.width s ν) true)
    (h13 : A (sh K 13) = List.replicate (g.bound s ν) true) (h2 : A (sh K 2) = [])
    (hblank : ∀ x : Fin (T K), off K 30 ≤ x.val → x.val < off K 31 → A x = []) :
    ∃ time, time ≤ K.ht.C * (2 ^ n + 1) ^ K.ht.E ∧ ∃ A' : Fin (T K) → List Bool,
      Ready RecoveryOracle.correctedSat ((ports K).program (pieces K c 30)) time A A' ∧
      A' (sh K 2) = RepairOrdinary.frame (g.gateCore s P (selectedAmplifier s.amplification g.degree) ν z
        (CloseoutLanguage.clauseWidth g.clauseDegree (g.width s ν)) g.positionLog n point).toNat.bits := by
  obtain ⟨out, hrun, hout⟩ := K.ht.run n point ν z hνn hcut h
  obtain ⟨time, htime, hready⟩ := exact_time hrun
  have hmw : CheckedPCPP.mwWord s g (2 ^ ν) (g.selectedPair s ν z h).src =
      (Outer.outC s.mw (g.sv s) ν (g.selectedPair s ν z h).src).word := by
    exact congrArg (fun k => (Outer.outC s.mw (g.sv s) k (g.selectedPair s ν z h).src).word)
      (Nat.log_pow (by norm_num) ν)
  have hin : ∀ j, A ((htBank K).slot j) = Recovery.portInput K.ht.t
      (CheckedPCPP.mwWord s g (2 ^ ν) (g.selectedPair s ν z h).src)
      (RepairOrdinary.frame (OuterPCPRecovery.canonicalBoundedCircuitDescription (g.bound s ν)
        (g.selectedPair s ν z h).pf))
      (RepairOrdinary.frame (List.ofFn point)) (g.width s ν) (g.bound s ν) j := by
    apply Bank.input
    · intro p hp
      rw [ht_l] at hp
      have hl := K.ht.large
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [Recovery.portInput, Recovery.fiveWords, hmw, h24]
      · simpa [Recovery.portInput, Recovery.fiveWords] using h23
      · simpa [Recovery.portInput, Recovery.fiveWords] using hPT
      · simpa [Recovery.portInput, Recovery.fiveWords] using h12
      · simpa [Recovery.portInput, Recovery.fiveWords] using h13
      · simp only [Recovery.portInput]
        rw [dif_neg (by omega)]
        exact h2
    · intro j hj
      rw [ht_l] at hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hj
      unfold Recovery.portInput
      rw [dif_neg]
      intro hlt
      obtain ⟨h0, h1, h2', h3, h4, _⟩ := hj
      interval_cases hv : j.val
      · exact h0 (Fin.ext (by simp [hv]))
      · exact h1 (Fin.ext (by simp [hv]))
      · exact h2' (Fin.ext (by simp [hv]))
      · exact h3 (Fin.ext (by simp [hv]))
      · exact h4 (Fin.ext (by simp [hv]))
    · intro x hx1 hx2
      exact hblank x hx1 hx2
  have hR := piece_ordinary (o := RecoveryOracle.correctedSat) (ports K) hready (htBank K).slot (htBank K).injective A hin
  refine ⟨time, htime, _, hR, ?_⟩
  rw [Bank.install_port (htBank K) A out (j := K.ht.output)
    (by rw [ht_l]; exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), hout]

end

end NearCubicGates.Close.Recovery.After
