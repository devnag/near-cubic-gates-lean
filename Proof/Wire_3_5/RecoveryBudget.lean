import Proof.Wire_3_5.RecoveryFacts
import Proof.Wire_3_5.RecoveryEnvelope
import Bindings.Williams14_Corollary4_4
import Proof.PCP.PCPPQueryBounds
import Proof.Packets.BudgetReaderCaps

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.RecoveryWitnessPolicy
open Filter

section Budget

theorem clog_le_self' (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

/-- `q(N) + 1 ≤ K·clog N + K` with `K = (kclk+2)(1+A) + 3A + 1`. -/
theorem nativeWidth_le_clog (kclk A' N : ℕ) :
    nativeWidth kclk A' N + 1 ≤ ((kclk + 2) * (1 + A') + 3 * A' + 1) * Nat.clog 2 N +
      ((kclk + 2) * (1 + A') + 3 * A' + 1) := by
  unfold nativeWidth
  have h1 : Nat.clog 2 (N ^ (kclk + 2)) ≤ (kclk + 2) * Nat.clog 2 N := clog_pow_le N (kclk + 2)
  have h2 : Nat.clog 2 (Nat.clog 2 (N ^ (kclk + 2)) + 2) ≤ Nat.clog 2 (N ^ (kclk + 2)) + 2 := clog_le_self' _
  have h3 : A' * Nat.clog 2 (Nat.clog 2 (N ^ (kclk + 2)) + 2) ≤ A' * ((kclk + 2) * Nat.clog 2 N + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-- **Every fixed polynomial of `q(N)` is eventually at most `⌊N/16⌋`** (`q(N) = O(log N)`). -/
theorem eventually_poly_le_div16 (kclk A' c d : ℕ) :
    ∀ᶠ N in atTop, c * (nativeWidth kclk A' N + 1) ^ d ≤ N / 16 := by
  set K := (kclk + 2) * (1 + A') + 3 * A' + 1 with hK
  have hclog : Tendsto (fun N => Nat.clog 2 N) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨2 ^ b, fun N hN => by
      calc b = Nat.clog 2 (2 ^ b) := (Nat.clog_pow 2 b (by norm_num)).symm
        _ ≤ Nat.clog 2 N := Nat.clog_mono_right 2 hN⟩
  have hev := hclog.eventually (eventually_mul_affine_pow_le_two_pow (32 * c) K K d)
  filter_upwards [hev, eventually_ge_atTop 2] with N h hN
  have hw := nativeWidth_le_clog kclk A' N
  have hpow : (nativeWidth kclk A' N + 1) ^ d ≤ (K * Nat.clog 2 N + K) ^ d := Nat.pow_le_pow_left hw d
  have hlt : 2 ^ (Nat.clog 2 N - 1) < N := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hpos : 1 ≤ Nat.clog 2 N := Nat.clog_pos (by norm_num) (by omega)
  have h2 : 2 ^ Nat.clog 2 N = 2 * 2 ^ (Nat.clog 2 N - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have h3 : 32 * c * (nativeWidth kclk A' N + 1) ^ d ≤ 2 ^ Nat.clog 2 N :=
    (Nat.mul_le_mul_left _ hpow).trans h
  have e : 32 * c * (nativeWidth kclk A' N + 1) ^ d = 2 * (c * (nativeWidth kclk A' N + 1) ^ d * 16) := by ring
  omega

/-- The code length of an oracle within the parameter `P`. -/
theorem oracleCode_le {w : ℕ} (oracle : BooleanCircuit w) (P : ℕ) (h4 : 4 ≤ P) (hw : w ≤ P) (hs : oracle.size ≤ P) :
    (natWord (ExecutableInterfaces.encodeBooleanCircuit oracle)).length ≤
      2 * canonicalBooleanCircuitCodeBitBound P + 1 := by
  rw [Bindings.Williams14.natWord_length]
  have := encodeBooleanCircuit_bits_le_parameter oracle h4 hw hs
  omega

/-- The code length of an atom within the description parameter `P`. -/
theorem atomCode_le (m : Mode) {n : ℕ} (C : m.Circuit n) (P : ℕ) (h4 : 4 ≤ P) (hd : m.descriptionBits C ≤ P) :
    (natWord (m.code C)).length ≤
      2 * (canonicalSymmetricCircuitCodeBitBound P + canonicalThresholdCircuitCodeBitBound P) + 1 := by
  rw [Bindings.Williams14.natWord_length]
  cases m
  · have := encodeNormalizedThresholdCircuit_bits_le_parameter C h4 hd
    show 2 * natBitLength (SupplierPipeline.encodeNormalizedThresholdThresholdCircuit C) + 1 ≤ _
    omega
  · have := encodeNormalizedSymmetricCircuit_bits_le_parameter C h4 hd
    show 2 * natBitLength (SupplierPipeline.encodeNormalizedSymmetricThresholdCircuit C) + 1 ≤ _
    omega

/-- The word of a grid sign is at most four bits. -/
theorem intWord_grid_le : ∀ σ ∈ ({-1, 0, 1} : Finset ℤ), (intWord σ).length ≤ 4 := by
  intro σ hσ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl <;> decide

end Budget

section Sizes
variable (l : Literals) (G : Split.Gate) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The size exponent `σ = 4e_Q + 2^{oracleDepth G} + 1` of the substituted request. -/
noncomputable def recSigma : ℕ :=
  4 * (gateSource l).degrees.queries + 2 ^ RecoveryScheduleEnvelope.oracleDepth (recOracleDeg l) + 1

noncomputable def recDG : ℕ := recSigma l * (gatePCPP l).degree + 1

/-- The hierarchy PCP's query exponent is the source's. -/
theorem hierarchyPCP_queries : (hierarchyPCP l (hierarchyOf (recL_inNTIME l kclk))).degrees.queries =
    (gateSource l).degrees.queries := rfl

/-- The recovery setup's query count is at most `C_H (q+1)^{e_Q}` at the padded width `q`. -/
theorem recQueryCount_le (N : ℕ) :
    (recSetup l G kclk coef A a ha).pcp.queryCount N ≤
      (hierarchyPCP l (hierarchyOf (recL_inNTIME l kclk))).data.coefficient *
        ((recSetup l G kclk coef A a ha).pcp.nativeWidth N + 1) ^ (gateSource l).degrees.queries := by
  have hq := (hierarchyPCP l (hierarchyOf (recL_inNTIME l kclk))).data.queryBound N
  have hw : (hierarchyPCP l (hierarchyOf (recL_inNTIME l kclk))).data.pcp.nativeWidth N ≤
      (recSetup l G kclk coef A a ha).pcp.nativeWidth N := le_max_left _ _
  refine hq.trans (Nat.mul_le_mul_left _ ?_)
  rw [← hierarchyPCP_queries l kclk]
  exact Nat.pow_le_pow_left (by omega) _

/-- The oracle size bound `q^G`: `oracleSizeBound G q + 1 ≤ (q+1)^{2^{oracleDepth G}}`. -/
theorem oracleSize_le (d w : ℕ) (o : ℕ) (ho : o ≤ RecoveryScheduleEnvelope.oracleSizeBound d w) :
    o + 1 ≤ (w + 1) ^ 2 ^ RecoveryScheduleEnvelope.oracleDepth d := by
  have := PolynomialClock.pairIter_add_one_le_pow (RecoveryScheduleEnvelope.oracleDepth d) w
  unfold RecoveryScheduleEnvelope.oracleSizeBound PolynomialClock.pairClock at ho
  omega

/-- The size arithmetic of the substituted request. -/
theorem size_arith (w Qc os cs dom CH eQ g σ minA : ℕ) (hQc : Qc ≤ CH * (w + 1) ^ eQ) (hos : os + 1 ≤ (w + 1) ^ g)
    (hcs : cs ≤ Qc * (2 * os + 1) + 3 * (2 * Qc) ^ 3 + 1) (hdom : dom ≤ w + minA) (h1 : eQ + g ≤ σ)
    (h3 : 3 * eQ ≤ σ) (h0 : 1 ≤ σ) :
    max cs dom + 1 ≤ (3 * CH + 24 * CH ^ 3 + minA + 3) * (w + 1) ^ σ := by
  have hw1 : 1 ≤ w + 1 := by omega
  have hp1 : (w + 1) ^ (eQ + g) ≤ (w + 1) ^ σ := Nat.pow_le_pow_right hw1 h1
  have hp3 : (w + 1) ^ (3 * eQ) ≤ (w + 1) ^ σ := Nat.pow_le_pow_right hw1 h3
  have hp0 : w + 1 ≤ (w + 1) ^ σ := by
    calc w + 1 = (w + 1) ^ 1 := (pow_one _).symm
      _ ≤ (w + 1) ^ σ := Nat.pow_le_pow_right hw1 h0
  have hone : 1 ≤ (w + 1) ^ σ := Nat.one_le_pow _ _ (by omega)
  have hQ1 : Qc * (2 * os + 1) ≤ 2 * CH * (w + 1) ^ σ := by
    calc Qc * (2 * os + 1) ≤ (CH * (w + 1) ^ eQ) * (2 * (w + 1) ^ g) := Nat.mul_le_mul hQc (by omega)
      _ = 2 * CH * (w + 1) ^ (eQ + g) := by rw [pow_add]; ring
      _ ≤ 2 * CH * (w + 1) ^ σ := Nat.mul_le_mul_left _ hp1
  have hQ3 : 3 * (2 * Qc) ^ 3 ≤ 24 * CH ^ 3 * (w + 1) ^ σ := by
    calc 3 * (2 * Qc) ^ 3 ≤ 3 * (2 * (CH * (w + 1) ^ eQ)) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
      _ = 24 * CH ^ 3 * (w + 1) ^ (3 * eQ) := by rw [show 3 * eQ = eQ * 3 by ring, pow_mul]; ring
      _ ≤ 24 * CH ^ 3 * (w + 1) ^ σ := Nat.mul_le_mul_left _ hp3
  have hmin : minA ≤ minA * (w + 1) ^ σ := Nat.le_mul_of_pos_right _ hone
  have hmax : max cs dom ≤ 2 * CH * (w + 1) ^ σ + 24 * CH ^ 3 * (w + 1) ^ σ + 1 + (w + minA) :=
    max_le (by omega) (by omega)
  have e : (3 * CH + 24 * CH ^ 3 + minA + 3) * (w + 1) ^ σ =
      3 * CH * (w + 1) ^ σ + 24 * CH ^ 3 * (w + 1) ^ σ + minA * (w + 1) ^ σ + 3 * (w + 1) ^ σ := by ring
  have hCH : 2 * CH * (w + 1) ^ σ ≤ 3 * CH * (w + 1) ^ σ := Nat.mul_le_mul_right _ (by omega)
  omega

theorem recSigma_ge : (gateSource l).degrees.queries + 2 ^ RecoveryScheduleEnvelope.oracleDepth (recOracleDeg l) ≤
      recSigma l ∧ 3 * (gateSource l).degrees.queries ≤ recSigma l ∧ 1 ≤ recSigma l := by
  unfold recSigma
  have := Nat.zero_le (2 ^ RecoveryScheduleEnvelope.oracleDepth (recOracleDeg l))
  omega

/-- **The substituted request's size** for an oracle within `q^G`: `size + 1 ≤ C·(q+1)^σ`. -/
theorem requestSize_le {N : ℕ} (z : BitInput N)
    (oracle : BooleanCircuit ((recSetup l G kclk coef A a ha).pcp.nativeWidth N))
    (hsize : oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recOracleDeg l)
      ((recSetup l G kclk coef A a ha).pcp.nativeWidth N)) :
    ((recSetup l G kclk coef A a ha).request z oracle).circuit.size + 1 ≤
      (3 * (hierarchyPCP l (hierarchyOf (recL_inNTIME l kclk))).data.coefficient +
        24 * (hierarchyPCP l (hierarchyOf (recL_inNTIME l kclk))).data.coefficient ^ 3 +
          (gatePCPP l).minimumArity + 3) *
        ((recSetup l G kclk coef A a ha).pcp.nativeWidth N + 1) ^ recSigma l := by
  obtain ⟨h1, h3, h0⟩ := recSigma_ge l
  have hreq := PCPPRequestBoundary.request_size (gatePCPP l)
    (PCPPSubstitution.compactSubstituted oracle ((recSetup l G kclk coef A a ha).pcp.queryAddressBits z)
      ((recSetup l G kclk coef A a ha).pcp.decision z fun _ => false))
  have hdom : PCPPRequestBoundary.domain (gatePCPP l) ((recSetup l G kclk coef A a ha).pcp.nativeWidth N) ≤
      (recSetup l G kclk coef A a ha).pcp.nativeWidth N + (gatePCPP l).minimumArity := by
    unfold PCPPRequestBoundary.domain; omega
  have key := size_arith _ _ _ _ _ _ _ _ _ _ (recQueryCount_le l G kclk coef A a ha N)
    (oracleSize_le (recOracleDeg l) _ oracle.size hsize)
    (PCPPSubstitution.compactSubstituted_size oracle ((recSetup l G kclk coef A a ha).pcp.queryAddressBits z)
      ((recSetup l G kclk coef A a ha).pcp.decision z fun _ => false)) hdom h1 h3 h0
  show (PCPPRequestBoundary.request (gatePCPP l) _).circuit.size + 1 ≤ _
  rw [hreq]
  exact key

end Sizes

end NearCubicWires.WireExponent3_5.Transfer
