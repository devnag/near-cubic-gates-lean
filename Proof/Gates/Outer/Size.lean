import Proof.Gates.Outer.Apply

set_option autoImplicit false

namespace NearCubicGates.Close.Outer

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.Bindings.MW20

variable {q ℓ : ℕ}

theorem substStep_length_le (B : BooleanCircuit q) (acc : List (BooleanNode q) × List ℕ) (nd : OracleNode ℓ ℓ) :
    (substStep B acc nd).1.length ≤ acc.1.length + (B.nodes.length + 1) := by
  cases nd <;> simp [substStep, substStepG, copyNodesFrom_length]

theorem substBuild_length_le (C : OracleCircuit ℓ ℓ) (B : BooleanCircuit q) :
    (substBuild C B).1.length ≤ 1 + C.nodes.length * (B.nodes.length + 1) := by
  unfold substBuild substBuildG
  have key : ∀ (nodes : List (OracleNode ℓ ℓ)) (acc : List (BooleanNode q) × List ℕ),
      (nodes.foldl (substStepG B inputMapD []) acc).1.length ≤
        acc.1.length + nodes.length * (B.nodes.length + 1) := by
    intro nodes
    induction nodes with
    | nil => intro acc; simp
    | cons nd rest ih =>
        intro acc
        simp only [List.foldl_cons, List.length_cons]
        have h1 := ih (substStepG B inputMapD [] acc nd)
        have h2 := substStep_length_le B acc nd
        unfold substStep at h2
        nlinarith
  simpa using key C.nodes ([.const false], [])

section
variable (mw : MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {G : ℕ}
  (SV : SuccinctVerifier H G)

/-- `|D_B| ≤ |C|·(|B_pf| + 1) + q + 2`. -/
theorem Dat_size_le (ν : ℕ) {N : ℕ} (B : OuterGuess (width mw SV N)) :
    (Dat mw SV ν B).D.size ≤ (outC mw SV ν B.src).circuit.size * (B.pf.size + 1) + width mw SV N + 2 := by
  have h1 := BooleanCircuit.padToArity_size_le (substCircuit (outC mw SV ν B.src).circuit B.pf)
  have h2 := substCircuit_size (outC mw SV ν B.src).circuit B.pf
  have h3 := substBuild_length_le (outC mw SV ν B.src).circuit B.pf
  show (substCircuit (outC mw SV ν B.src).circuit B.pf).padToArity.size ≤ _
  unfold OracleCircuit.size BooleanCircuit.size at *
  omega

/-- The import's size clause at the instance `⟨B_src⟩_ν`. -/
theorem outC_size_le (ν : ℕ) (hν : 1 ≤ ν) {m : ℕ} (B : BooleanCircuit m) :
    (outC mw SV ν B).circuit.size ≤ (alg mw SV).coefficient *
      (instLength G ν + natBitLength (SV.T (instLength G ν)) + 1) ^ (alg mw SV).sizeExp :=
  (alg mw SV).sizeBound (srcInput G ν B) (instLength_pos ν hν)

/-- `log₂ N ≤ q(N)`. -/
theorem log_le_width (N : ℕ) : Nat.log 2 N ≤ width mw SV N := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · rw [h0, Nat.log_zero_right]; exact Nat.zero_le _
  · exact le_widthOf k _ _ N (Nat.pow_log_le_self 2 (by omega))

/-- `|bin T_G(L_ν)|` is at most linear in `ν`, uniformly (a finite maximum below the onset). -/
theorem natBitLength_T_le : ∃ M : ℕ, ∀ ν, natBitLength (SV.T (instLength G ν)) ≤ M + (k + 2) * ν := by
  refine ⟨(Finset.range SV.onset).sup (fun ν => natBitLength (SV.T (instLength G ν))) +
    natBitLength SV.timeCoefficient + 1, fun ν => ?_⟩
  by_cases hν : ν < SV.onset
  · have := Finset.le_sup (f := fun ν => natBitLength (SV.T (instLength G ν))) (Finset.mem_range.mpr hν)
    omega
  · have hT := SV.timeBound ν (by omega)
    have hpow : (2 ^ ν) ^ (k + 2) = 2 ^ (ν * (k + 2)) := by rw [← pow_mul]
    rw [hpow] at hT
    -- natBitLength is monotone and natBitLength (c * 2^a) ≤ natBitLength c + a
    have hmono : natBitLength (SV.T (instLength G ν)) ≤ natBitLength (SV.timeCoefficient * 2 ^ (ν * (k + 2))) := by
      unfold natBitLength
      rcases Nat.eq_zero_or_pos (SV.T (instLength G ν)) with h0 | h0
      · rw [h0]; simp
      · have := Nat.log_mono_right (b := 2) hT
        omega
    have hmul : natBitLength (SV.timeCoefficient * 2 ^ (ν * (k + 2))) ≤
        natBitLength SV.timeCoefficient + ν * (k + 2) := by
      unfold natBitLength
      rcases Nat.eq_zero_or_pos SV.timeCoefficient with h0 | h0
      · rw [h0]; simp
      · have hc : SV.timeCoefficient < 2 ^ (Nat.log 2 SV.timeCoefficient + 1) :=
          Nat.lt_pow_succ_log_self (by norm_num) _
        have hlt : SV.timeCoefficient * 2 ^ (ν * (k + 2)) <
            2 ^ (Nat.log 2 SV.timeCoefficient + 1 + ν * (k + 2)) := by
          rw [pow_add]; exact Nat.mul_lt_mul_of_pos_right hc (by positivity)
        have := Nat.log_lt_of_lt_pow (by positivity) hlt
        omega
    nlinarith

end

end NearCubicGates.Close.Outer
