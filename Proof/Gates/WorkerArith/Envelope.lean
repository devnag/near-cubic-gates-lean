import Proof.Gates.WorkerArith.GuessWordLengths
import Proof.Gates.Outer.Size
import Proof.Gates.WorkerArith.HotFuel
import Proof.Gates.Closure.ClauseRoom
import Proof.Gates.Setup.Growth
import Proof.Gates.Setup.ReadBound

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith.WorkerBounds

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.CloseoutLanguage NearCubicWires.PolynomialSchedule NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.ExecutableInterfaces NearCubicWires.CanonicalWitnessCodec
open NearCubicGates.Close NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer NearCubicGates.PublishedSources.PCPP
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Worker NearCubicGates.Close.Worker.Format

theorem budgetOf_le (η : ℚ) (q : ℕ) : Closure.budgetOf η q ≤ η.num.toNat * q ^ 3 := Nat.div_le_self _ _

theorem B0_le (q : ℕ) : Call.B0 q ≤ 4 * q * (q + 1) := by
  unfold Call.B0
  have : Nat.clog 2 (q + 1) ≤ q + 1 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  exact Nat.mul_le_mul_left _ this

theorem B0_pos (q : ℕ) (hq : 1 ≤ q) : 1 ≤ Call.B0 q := by
  unfold Call.B0
  have : 1 ≤ Nat.clog 2 (q + 1) := Nat.clog_pos (by norm_num) (by omega)
  have : 1 ≤ 4 * q := by omega
  nlinarith

section Env
variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) {B1 B2 : ℕ} (ctr : Counter B1 B2) (η : ℚ)

theorem guessEnvelope : ∃ onset : ℕ, ∀ N, onset ≤ N → ∀ (x : BitInput N) (G : Guess (width s g N)),
    G.SizeOK P x ctr (Closure.budgetOf η) →
    (encodeGuess s P g x G).length ≤ N / 16 ∧
      ∀ j < G.auxCount P x, (G.circuits j).coeffs.length = (G.circuits j).gates.length := by
  obtain ⟨F, hF, hFm⟩ := Closure.checked_m_le s P g
  obtain ⟨K, e, hsize⟩ := P.outputSize
  obtain ⟨Cw, kw, hw⟩ := ctr.witnessPoly
  let Mb : ℕ → ℕ := fun q => 2 ^ (g.clauseDegree + 1) * (q + 1) ^ g.clauseDegree
  let Ab : ℕ → ℕ := fun q => K * F q ^ e + Mb q
  let Cb : ℕ → ℕ := fun q => (η.num.toNat * q ^ 3 + 1) * ((q + 1) * (2 * (4 * q * (q + 1)) + 2) + 12)
  let Wb : ℕ → ℕ := fun q => 2 * (Cw * (q + 1) ^ kw) + 1
  let Phi : ℕ → ℕ := fun q => 2 * (2 * (8192 * (q + oracleSizeBound g.degree q + 4 + 1) ^ 10) + 1) + Ab q * Cb q +
    10 * Mb q * Wb q
  have pc := polynomiallyBounded_constant
  have pid := polynomiallyBounded_id
  have p1 : PolynomiallyBounded (fun q : ℕ => q + 1) := polynomiallyBounded_add pid (pc 1)
  have hMb : PolynomiallyBounded Mb := polynomiallyBounded_mul (pc _) (polynomiallyBounded_pow p1 _)
  have hAb : PolynomiallyBounded Ab :=
    polynomiallyBounded_add (polynomiallyBounded_mul (pc K) (polynomiallyBounded_pow hF e)) hMb
  have hCb : PolynomiallyBounded Cb :=
    polynomiallyBounded_mul (polynomiallyBounded_add (polynomiallyBounded_mul (pc _) (polynomiallyBounded_pow pid 3))
      (pc 1)) (polynomiallyBounded_add (polynomiallyBounded_mul p1 (polynomiallyBounded_add (polynomiallyBounded_mul
        (pc 2) (polynomiallyBounded_mul (polynomiallyBounded_mul (pc 4) pid) p1)) (pc 2))) (pc 12))
  have hWb : PolynomiallyBounded Wb :=
    polynomiallyBounded_add (polynomiallyBounded_mul (pc 2) (polynomiallyBounded_mul (pc Cw)
      (polynomiallyBounded_pow p1 kw))) (pc 1)
  have hO : PolynomiallyBounded (fun q => 2 * (8192 * (q + oracleSizeBound g.degree q + 4 + 1) ^ 10) + 1) :=
    polynomiallyBounded_add (polynomiallyBounded_mul (pc 2) (polynomiallyBounded_mul (pc 8192)
      (polynomiallyBounded_pow (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add pid
        (oracleSizeBound_polynomiallyBounded g.degree)) (pc 4)) (pc 1)) 10))) (pc 1)
  have hPhi : PolynomiallyBounded Phi :=
    polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_mul (pc 2) hO) (polynomiallyBounded_mul hAb hCb))
      (polynomiallyBounded_mul (polynomiallyBounded_mul (pc 10) hMb) hWb)
  obtain ⟨c, dd, -, hc⟩ := hPhi
  obtain ⟨N1, hN1⟩ := Setup.qpoly_le s g dd (16 * c)
  refine ⟨N1 + 4, fun N hN x G hG => ?_⟩
  obtain ⟨hsrc, hpf, hcirc, hwit⟩ := hG
  have hq2 : 2 ≤ width s g N := two_le_nativeWidth s g N (by omega)
  refine ⟨?_, fun j hj => ((hcirc j hj).1.1).symm⟩
  -- the pair
  have hp1 : natBitLength (encodeBooleanCircuit G.oracle.src) ≤
      8192 * (width s g N + oracleSizeBound g.degree (width s g N) + 4 + 1) ^ 10 :=
    (RecoveryWitnessPolicy.encodeBooleanCircuit_bits_le_parameter G.oracle.src (by omega) (by omega)
      (by omega)).trans (RepairOrdinary.PCPPRequestBoundary.canonical_circuit_bound _)
  have hp2 : natBitLength (encodeBooleanCircuit G.oracle.pf) ≤
      8192 * (width s g N + oracleSizeBound g.degree (width s g N) + 4 + 1) ^ 10 :=
    (RecoveryWitnessPolicy.encodeBooleanCircuit_bits_le_parameter G.oracle.pf (by omega) (by omega)
      (by omega)).trans (RepairOrdinary.PCPPRequestBoundary.canonical_circuit_bound _)
  have h1 : (numWord (encodeBooleanCircuit G.oracle.src)).length + (numWord (encodeBooleanCircuit G.oracle.pf)).length ≤
      2 * (2 * (8192 * (width s g N + oracleSizeBound g.degree (width s g N) + 4 + 1) ^ 10) + 1) := by
    rw [numWord_length, numWord_length]; omega
  -- the circuits
  have hM : gadgets s g N ≤ Mb (width s g N) := gadgets_le _ _
  have hm := hFm N x G.oracle hpf hq2 (by omega)
  have hpb : (pcpp s P g x G.oracle).proofBits ≤ K * F (width s g N) ^ e := by
    rw [pcpp_eq]
    exact (hsize _).1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm e))
  have haux : G.auxCount P x ≤ Ab (width s g N) := by
    show (pcpp s P g x G.oracle).proofBits + gadgets s g N ≤ _
    exact Nat.add_le_add hpb hM
  have hB0 : 1 ≤ Call.B0 (width s g N) := B0_pos _ (by omega)
  have hcw : ∀ a ∈ (List.range (G.auxCount P x)).map G.circuits, (circuitWordF a).length ≤ Cb (width s g N) := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    rw [List.mem_range] at hj
    obtain ⟨hwf, htw⟩ := hcirc j hj
    have h := circuitWordF_le hB0 (G.circuits j) hwf
    have h2 : (G.circuits j).topWeight + 1 ≤ η.num.toNat * width s g N ^ 3 + 1 :=
      Nat.add_le_add_right (htw.trans (budgetOf_le η _)) 1
    have h3 : (width s g N + 1) * (2 * Call.B0 (width s g N) + 2) + 12 ≤
        (width s g N + 1) * (2 * (4 * width s g N * (width s g N + 1)) + 2) + 12 := by
      have := B0_le (width s g N)
      have : 2 * Call.B0 (width s g N) + 2 ≤ 2 * (4 * width s g N * (width s g N + 1)) + 2 := by omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ this) 12
    exact h.trans (Nat.mul_le_mul h2 h3)
  have h2 := Setup.flatMap_len_le circuitWordF (Cb (width s g N)) _ hcw
  rw [List.length_map, List.length_range] at h2
  have h2' : (((List.range (G.auxCount P x)).map G.circuits).flatMap circuitWordF).length ≤
      Ab (width s g N) * Cb (width s g N) := h2.trans (Nat.mul_le_mul_right _ haux)
  -- the witnesses
  have hwl : ∀ a ∈ witnessList G (gadgets s g N), (fieldWord a).length ≤ Wb (width s g N) := by
    intro a ha
    unfold witnessList at ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    rw [List.mem_range] at hi
    rw [fieldWord_length]
    have h := hwit (i / 10) (by omega) ⟨i % 10, Nat.mod_lt _ (by norm_num)⟩
    have := hw (width s g N)
    show 2 * _ + 1 ≤ 2 * (Cw * (width s g N + 1) ^ kw) + 1
    omega
  have h3 := Setup.flatMap_len_le fieldWord (Wb (width s g N)) _ hwl
  have hwlen : (witnessList G (gadgets s g N)).length = 10 * gadgets s g N := by simp [witnessList]
  rw [hwlen] at h3
  have h3' : ((witnessList G (gadgets s g N)).flatMap fieldWord).length ≤ 10 * Mb (width s g N) * Wb (width s g N) :=
    h3.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hM))
  -- total
  have hlen : (encodeGuess s P g x G).length ≤ Phi (width s g N) := by
    unfold encodeGuess
    simp only [List.length_append]
    show _ ≤ 2 * (2 * (8192 * (width s g N + oracleSizeBound g.degree (width s g N) + 4 + 1) ^ 10) + 1) +
      Ab (width s g N) * Cb (width s g N) + 10 * Mb (width s g N) * Wb (width s g N)
    omega
  have h16 : 16 * Phi (width s g N) ≤ N := by
    have a := hN1 N (by omega)
    have b := Nat.mul_le_mul_left 16 (hc (width s g N))
    calc 16 * Phi (width s g N) ≤ 16 * (c * (width s g N + 1) ^ dd) := b
      _ = 16 * c * (width s g N + 1) ^ dd := by ring
      _ ≤ N := a
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  omega

end Env

end NearCubicGates.Close.WorkerArith.WorkerBounds
