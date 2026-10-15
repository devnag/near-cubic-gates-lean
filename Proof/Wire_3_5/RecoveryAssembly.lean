import Proof.Wire_3_5.RecoveryEventual
import Proof.Wire_3_5.RecoverySlice
import Proof.CaseAnalysis.Parameters
import Bindings.CLW20_Lemma3_8

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Schedule NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.RepairSource.CloseoutLanguage (core clauseWidth)
open NearCubicWires.RepairSource.CloseoutSampledWitness (massCap)
open NearCubicWires.ComponentwiseCircuitRestriction (restrictedSymmetricDescriptionCap
  restrictedThresholdDescriptionCap)
open Filter

section Assembly
variable (l : Literals) (G : Split.Gate) (hG : GateRel l G) {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}
  (U : Split.UnionLeafAt (G.inputs kclk coef A a ha) (unionSetupS1 l G kclk coef A a ha))
  (P : FusedPrimitive (G.inputs kclk coef A a ha))

include hG in
/-- **The core of one source length is hard in both classes** at the gate constants. -/
theorem core_hard_at {N : ℕ} (z : BitInput N) (q n : ℕ)
    (hw : (recSetup l G kclk coef A a ha).pcp.nativeWidth N = q)
    (harity : ∀ oracle : BooleanCircuit ((recSetup l G kclk coef A a ha).pcp.nativeWidth N),
      ((recSetup l G kclk coef A a ha).request z oracle).arity = q)
    (hyes : recL l kclk N z = true) (hrej : ¬ (recMachine l G U P).accepts N z)
    (hacc : ∀ g : UnionGuess (recSetup l G kclk coef A a ha) z,
      UnionAccepts (recSetup l G kclk coef A a ha) P z g → (recMachine l G U P).accepts N z)
    (hfit : (G.budget kclk coef A a ha).FitsAt q)
    (hbud : recBudget l kclk q ≤ N / 16)
    (hQ : RecQ l G q) (hKcl : (gatePCPP l).coefficient * recKs l kclk ^ (gatePCPP l).degree ≤ q + 2)
    (hlen : recCopies (gateZeta_pos l) (gateZeta_lt l) q * (q + clauseWidth (recDG l) q + 1) ≤ n)
    (hn : n + 1 ≤ (q + 1) ^ 4) :
    (∀ circuit : SymmetricThresholdCircuit n, circuit.wireCount ≤ ⌊wireCap G.row.cap .sym q⌋₊ →
      agreement circuit.eval (core (recSetup l G kclk coef A a ha).pcp (gatePCPP l)
        (selectedAmplifier l.eightSources.amplification (recOracleDeg l)) z
        (recCopies (gateZeta_pos l) (gateZeta_lt l) q) (clauseWidth (recDG l) q) n) <
        1 / 2 + xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) q)) ∧
    (∀ circuit : ThresholdThresholdCircuit n, circuit.wireCount ≤ ⌊wireCap G.row.cap .thr q⌋₊ →
      agreement circuit.eval (core (recSetup l G kclk coef A a ha).pcp (gatePCPP l)
        (selectedAmplifier l.eightSources.amplification (recOracleDeg l)) z
        (recCopies (gateZeta_pos l) (gateZeta_lt l) q) (clauseWidth (recDG l) q) n) <
        1 / 2 + xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) q)) := by
  have hc := l.eightSources.amplification.stvExponentPositive
  have hq1 : 1 ≤ q := by have := hQ.two; omega
  have hQ1 : 528 ≤ q + 1 := by have := hQ.big; omega
  -- the request's size, the clause bits, the oracle code, the guess budget
  have hsize : ∀ oracle : BooleanCircuit ((recSetup l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recOracleDeg l)
        ((recSetup l G kclk coef A a ha).pcp.nativeWidth N) →
      ((recSetup l G kclk coef A a ha).request z oracle).circuit.size + 1 ≤ recKs l kclk * (q + 1) ^ recSigma l := by
    intro oracle hs
    have h := requestSize_le l G kclk coef A a ha z oracle hs
    calc _ ≤ recKs l kclk * ((recSetup l G kclk coef A a ha).pcp.nativeWidth N + 1) ^ recSigma l := h
      _ = recKs l kclk * (q + 1) ^ recSigma l := by rw [hw]
  have hcb : ∀ oracle : BooleanCircuit ((recSetup l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recSetup l G kclk coef A a ha).G
        ((recSetup l G kclk coef A a ha).pcp.nativeWidth N) →
      ((recSetup l G kclk coef A a ha).pcppOf z oracle).clauseBits ≤ clauseWidth (recDG l) q := by
    intro oracle hs
    have h1 := hsize oracle hs
    have hcc := (gatePCPP l).clauseCountBound ((recSetup l G kclk coef A a ha).request z oracle)
    apply clauseBits_le
    calc 2 ^ ((recSetup l G kclk coef A a ha).pcppOf z oracle).clauseBits
        ≤ (gatePCPP l).coefficient *
            (((recSetup l G kclk coef A a ha).request z oracle).circuit.size + 1) ^ (gatePCPP l).degree := hcc
      _ ≤ (gatePCPP l).coefficient * (recKs l kclk * (q + 1) ^ recSigma l) ^ (gatePCPP l).degree :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
      _ = ((gatePCPP l).coefficient * recKs l kclk ^ (gatePCPP l).degree) *
            (q + 1) ^ (recSigma l * (gatePCPP l).degree) := by
          rw [mul_pow, ← pow_mul]; ring
      _ ≤ (q + 2) * (q + 2) ^ (recSigma l * (gatePCPP l).degree) :=
          Nat.mul_le_mul hKcl (Nat.pow_le_pow_left (by omega) _)
      _ = (q + 2) ^ recDG l := by unfold recDG; ring
  have hO : ∀ oracle : BooleanCircuit ((recSetup l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recOracleDeg l)
        ((recSetup l G kclk coef A a ha).pcp.nativeWidth N) →
      (natWord (ExecutableInterfaces.encodeBooleanCircuit oracle)).length ≤ recKo l q := by
    intro oracle hs
    have h1 : oracle.size + 1 ≤ (q + 1) ^ recOracleExp l :=
      calc oracle.size + 1 ≤ ((recSetup l G kclk coef A a ha).pcp.nativeWidth N + 1) ^
            2 ^ RecoveryScheduleEnvelope.oracleDepth (recOracleDeg l) := oracleSize_le (recOracleDeg l) _ _ hs
        _ = (q + 1) ^ recOracleExp l := by rw [hw]; rfl
    have hg : q + 1 ≤ (q + 1) ^ recOracleExp l := Nat.le_self_pow (by unfold recOracleExp; positivity) _
    exact oracleCode_le oracle ((q + 1) ^ recOracleExp l + 4) (by omega) (by rw [hw]; omega) (by omega)
  have hbudget : ∀ oracle : BooleanCircuit ((recSetup l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recOracleDeg l)
        ((recSetup l G kclk coef A a ha).pcp.nativeWidth N) →
      1 + recKo l q + (((recSetup l G kclk coef A a ha).pcppOf z oracle).systematicBits +
        ((recSetup l G kclk coef A a ha).pcppOf z oracle).auxiliaryBits) * (G.row.sp q * (4 + recKc q)) ≤ N / 16 := by
    intro oracle hs
    have h1 := hsize oracle hs
    have hsys : ((recSetup l G kclk coef A a ha).pcppOf z oracle).systematicBits ≤
        (gatePCPP l).coefficient * (q + 1) ^ (gatePCPP l).degree :=
      calc _ ≤ (gatePCPP l).coefficient * (((recSetup l G kclk coef A a ha).request z oracle).arity + 1) ^
            (gatePCPP l).degree := (gatePCPP l).systematicBound ((recSetup l G kclk coef A a ha).request z oracle)
        _ = (gatePCPP l).coefficient * (q + 1) ^ (gatePCPP l).degree := by rw [harity oracle]
    have haux : ((recSetup l G kclk coef A a ha).pcppOf z oracle).auxiliaryBits ≤
        (gatePCPP l).coefficient * (recKs l kclk * (q + 1) ^ recSigma l) ^ (gatePCPP l).degree :=
      ((gatePCPP l).auxiliaryBound ((recSetup l G kclk coef A a ha).request z oracle)).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _))
    have hnv : ((recSetup l G kclk coef A a ha).pcppOf z oracle).systematicBits +
        ((recSetup l G kclk coef A a ha).pcppOf z oracle).auxiliaryBits ≤ recNv l kclk q := Nat.add_le_add hsys haux
    have hsp : G.row.sp q * (4 + recKc q) ≤ q * (4 + recKc q) := Nat.mul_le_mul_right _ hQ.sp
    calc _ ≤ 1 + recKo l q + recNv l kclk q * (q * (4 + recKc q)) :=
          Nat.add_le_add_left (Nat.mul_le_mul hnv hsp) _
      _ = recBudget l kclk q := rfl
      _ ≤ N / 16 := hbud
  -- the description envelopes
  have hLdS : ∀ oracle : BooleanCircuit ((recSetup l G kclk coef A a ha).pcp.nativeWidth N),
      restrictedSymmetricDescriptionCap ((recSetup l G kclk coef A a ha).request z oracle).arity
        (((recSetup l G kclk coef A a ha).request z oracle).arity + clauseWidth (recDG l) q + 1)
        (2 ^ symmetricDescriptionCap (((recSetup l G kclk coef A a ha).request z oracle).arity +
          clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .sym q⌋₊) ⌊wireCap G.row.cap .sym q⌋₊ ≤ (q + 1) ^ 26 := by
    intro oracle
    rw [harity oracle]
    have h := symLdesc_le (q + 1) (q + clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .sym q⌋₊ (by omega)
      (by have := hQ.cw; omega) hQ.capS.2
    simp only [Nat.add_sub_cancel] at h
    have h2 : 528 * (q + 1) ^ 12 ≤ (q + 1) ^ 26 :=
      calc 528 * (q + 1) ^ 12 ≤ (q + 1) * (q + 1) ^ 12 := Nat.mul_le_mul_right _ hQ1
        _ = (q + 1) ^ 13 := by ring
        _ ≤ (q + 1) ^ 26 := Nat.pow_le_pow_right (by omega) (by norm_num)
    exact h.trans h2
  have hLdT : ∀ oracle : BooleanCircuit ((recSetup l G kclk coef A a ha).pcp.nativeWidth N),
      restrictedThresholdDescriptionCap ((recSetup l G kclk coef A a ha).request z oracle).arity
        (((recSetup l G kclk coef A a ha).request z oracle).arity + clauseWidth (recDG l) q + 1)
        (2 ^ thresholdDescriptionCap (((recSetup l G kclk coef A a ha).request z oracle).arity +
          clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .thr q⌋₊)
        (thresholdDescriptionCap (((recSetup l G kclk coef A a ha).request z oracle).arity +
          clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .thr q⌋₊) ≤ (q + 1) ^ 26 := by
    intro oracle
    rw [harity oracle]
    have h := thrLdesc_le (q + 1) (q + clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .thr q⌋₊ (by omega)
      (by have := hQ.cw; omega) hQ.capT.2
    simp only [Nat.add_sub_cancel] at h
    have h2 : 75894 * (q + 1) ^ 25 ≤ (q + 1) ^ 26 :=
      calc 75894 * (q + 1) ^ 25 ≤ (q + 1) * (q + 1) ^ 25 := Nat.mul_le_mul_right _ hQ.big
        _ = (q + 1) ^ 26 := by ring
    exact h.trans h2
  -- Case 2's ledgers
  have ledS : ∀ oracle : BooleanCircuit ((recSetup l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recSetup l G kclk coef A a ha).G
        ((recSetup l G kclk coef A a ha).pcp.nativeWidth N) →
      CaseTwoLedger (recSetup l G kclk coef A a ha) z oracle .sym P (gateCParams1 l)
        (massCap (gateCParams1 l).ζ (recCopies (gateZeta_pos l) (gateZeta_lt l) q)) ⌊wireCap G.row.cap .sym q⌋₊
        (restrictedSymmetricDescriptionCap ((recSetup l G kclk coef A a ha).request z oracle).arity
          (((recSetup l G kclk coef A a ha).request z oracle).arity + clauseWidth (recDG l) q + 1)
          (2 ^ symmetricDescriptionCap (((recSetup l G kclk coef A a ha).request z oracle).arity +
            clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .sym q⌋₊) ⌊wireCap G.row.cap .sym q⌋₊) := by
    intro oracle hs
    exact ledger_at l G hG kclk coef A a ha P .sym z oracle q (harity oracle) hq1 hQ.star hfit _
      (Nat.floor_le (wireCap_nonneg _ _ _)) hQ.capS.2 hQ.capS.1 hQ.sp _ (hLdS oracle)
      (by unfold restrictedSymmetricDescriptionCap; exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
      hQ.xi hQ.hD (recKo l q) (recKc q) (hO oracle hs)
      (fun C hd => atomCode_le .sym C ((q + 1) ^ 26 + 4) (by omega) (by have := hLdS oracle; omega))
      (hbudget oracle hs)
  have ledT : ∀ oracle : BooleanCircuit ((recSetup l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recSetup l G kclk coef A a ha).G
        ((recSetup l G kclk coef A a ha).pcp.nativeWidth N) →
      CaseTwoLedger (recSetup l G kclk coef A a ha) z oracle .thr P (gateCParams1 l)
        (massCap (gateCParams1 l).ζ (recCopies (gateZeta_pos l) (gateZeta_lt l) q)) ⌊wireCap G.row.cap .thr q⌋₊
        (restrictedThresholdDescriptionCap ((recSetup l G kclk coef A a ha).request z oracle).arity
          (((recSetup l G kclk coef A a ha).request z oracle).arity + clauseWidth (recDG l) q + 1)
          (2 ^ thresholdDescriptionCap (((recSetup l G kclk coef A a ha).request z oracle).arity +
            clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .thr q⌋₊)
          (thresholdDescriptionCap (((recSetup l G kclk coef A a ha).request z oracle).arity +
            clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .thr q⌋₊)) := by
    intro oracle hs
    exact ledger_at l G hG kclk coef A a ha P .thr z oracle q (harity oracle) hq1 hQ.star hfit _
      (Nat.floor_le (wireCap_nonneg _ _ _)) hQ.capT.2 hQ.capT.1 hQ.sp _ (hLdT oracle)
      (by unfold restrictedThresholdDescriptionCap; exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
      hQ.xi hQ.hD (recKo l q) (recKc q) (hO oracle hs)
      (fun C hd => atomCode_le .thr C ((q + 1) ^ 26 + 4) (by omega) (by have := hLdT oracle; omega))
      (hbudget oracle hs)
  -- Case 1's conditions
  have hq' : 1 ≤ (recSetup l G kclk coef A a ha).pcp.nativeWidth N := by rw [hw]; exact hq1
  have hfit1 : ((selectedAmplifier l.eightSources.amplification (recOracleDeg l)).output
      (RecoveryCaseOneRequest.request (recSetup l G kclk coef A a ha).pcp z).inputArity
      (RecoveryCaseOneRequest.request (recSetup l G kclk coef A a ha).pcp z).function).arity ≤ n := by
    have hin : (RecoveryCaseOneRequest.request (recSetup l G kclk coef A a ha).pcp z).inputArity = q := hw
    have h := CloseoutParameters.arity_envelope (selectedAmplifier l.eightSources.amplification (recOracleDeg l))
      (recCopies (gateZeta_pos l) (gateZeta_lt l) q) _ (clauseWidth (recDG l) q) hQ.copies (by rw [hin]; exact hq1)
      (RecoveryCaseOneRequest.request (recSetup l G kclk coef A a ha).pcp z).function
    refine h.trans (le_of_eq_of_le ?_ hlen)
    rw [hin]
  have hsym1 : 40 * (n + ⌊wireCap G.row.cap .sym q⌋₊ + 2) ^ 4 ≤ integerFloorRoot
      l.eightSources.amplification.stvExponent (RecoveryScheduleEnvelope.oracleSizeBound
        (17 * l.eightSources.amplification.stvExponent) ((recSetup l G kclk coef A a ha).pcp.nativeWidth N)) := by
    rw [hw]
    exact caseOne_size _ hc q n _ 40 (by norm_num) hq1 hQ.pow17 (by have := hQ.capS.2; omega)
  have hthr1 : 50 * (n + ⌊wireCap G.row.cap .thr q⌋₊ + 2) ^ 4 ≤ integerFloorRoot
      l.eightSources.amplification.stvExponent (RecoveryScheduleEnvelope.oracleSizeBound
        (17 * l.eightSources.amplification.stvExponent) ((recSetup l G kclk coef A a ha).pcp.nativeWidth N)) := by
    rw [hw]
    exact caseOne_size _ hc q n _ 50 le_rfl hq1 hQ.pow17 (by have := hQ.capT.2; omega)
  have hadv1 : Real.rpow (RecoveryScheduleEnvelope.oracleSizeBound (17 * l.eightSources.amplification.stvExponent)
      ((recSetup l G kclk coef A a ha).pcp.nativeWidth N) : ℝ) (-(1 : ℝ) / l.eightSources.amplification.stvExponent) <
      xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) q) := by
    rw [hw]; exact hQ.adv1
  -- Case 2's conditions
  have hcopies : 1 ≤ recCopies (gateZeta_pos l) (gateZeta_lt l) q := by unfold recCopies; omega
  have hz0 : (0 : ℝ) < ((gateCParams1 l).ζ : ℝ) := by exact_mod_cast gateZeta_pos l
  have hz1 : ((gateCParams1 l).ζ : ℝ) < 1 / 2 := by
    have h : (((gateCParams1 l).ζ : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := Rat.cast_lt.mpr (gateZeta_lt l)
    rw [show ((1 / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  have heps : xorEpsilon ((gateCParams1 l).ζ : ℝ) (recCopies (gateZeta_pos l) (gateZeta_lt l) q) <
      xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) q) :=
    xorEpsilon_succ_lt _ hz0 hz1 _ (sched_spec (gateZeta_pos l) (gateZeta_lt l) (Lq q)).1
  have hfit2 : ∀ oracle : BooleanCircuit ((recSetup l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recSetup l G kclk coef A a ha).G
        ((recSetup l G kclk coef A a ha).pcp.nativeWidth N) →
      recCopies (gateZeta_pos l) (gateZeta_lt l) q *
        (((recSetup l G kclk coef A a ha).request z oracle).arity + clauseWidth (recDG l) q + 1) ≤ n := by
    intro oracle _
    rw [harity oracle]; exact hlen
  exact core_bounds (recSetup l G kclk coef A a ha) z P (gateCParams1 l) (recMachine l G U P) hacc hrej
    (recSetup_hind l G kclk coef A a ha z) (selectedAmplifier l.eightSources.amplification (recOracleDeg l))
    (recCopies (gateZeta_pos l) (gateZeta_lt l) q) (clauseWidth (recDG l) q) n ⌊wireCap G.row.cap .sym q⌋₊
    ⌊wireCap G.row.cap .thr q⌋₊ _ l.eightSources.normalization l.eightSources.expander
    Bindings.CLW20Lemma38.clw20_xor_source hq' (recSetup_complete l G kclk coef A a ha z hyes) hfit1 hsym1 hthr1
    hadv1 hcopies (gateZeta_pos l) (gateZeta_lt l) heps hcb hfit2 ledS ledT

end Assembly

end NearCubicWires.WireExponent3_5.Transfer
