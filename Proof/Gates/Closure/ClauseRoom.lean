import Proof.Gates.Closure.Supply
import Proof.Gates.Gadget.CheckedSize
import Proof.Gates.Outer.Size
import Proof.Foundations.PolynomialSchedule

set_option autoImplicit false

namespace NearCubicGates.Close.Closure

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.CloseoutLanguage NearCubicWires.PolynomialSchedule NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer NearCubicGates.PublishedSources.PCPP

theorem le_clog_of_pow_le {r X : ℕ} (h : 2 ^ r ≤ X) : r ≤ Nat.clog 2 X := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : X ≤ 2 ^ Nat.clog 2 X := Nat.le_pow_clog (by norm_num) X
  have h2 : 2 ^ Nat.clog 2 X < 2 ^ r := Nat.pow_lt_pow_right (by norm_num) hlt
  omega

section
variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams)
open NearCubicGates.Close.Worker

/-- The checked outer verifier has `poly(q)` nodes (`sec:gadget-machine`: "`D_B` is a circuit of size
`q^{O_{G,C_clk}(1)}` on `q`
inputs"; `Outer.Dat_size_le`, the import's size clause, `L_ν ≤ q^{G′}` and `|bin T_G(L_ν)| = O(q)`). -/
theorem checked_m_le : ∃ F : ℕ → ℕ, PolynomiallyBounded F ∧ ∀ (N : ℕ) (x : BitInput N)
    (B : Outer.OuterGuess (width s g N)), B.pf.size ≤ oracleSizeBound g.degree (width s g N) → 2 ≤ width s g N →
    2 ≤ N → (checkedCircuit P.code (substituted s g x B)).m + 1 ≤ F (width s g N) := by
  obtain ⟨KL, hKL⟩ := P.codeLength
  obtain ⟨Mt, hMt⟩ := Outer.natBitLength_T_le (g.sv s)
  let Ka := (Outer.alg s.mw (g.sv s)).coefficient
  let ea := (Outer.alg s.mw (g.sv s)).sizeExp
  let Cb : ℕ → ℕ := fun q => Ka * (q ^ (g.lenExp + 2) + Mt + (g.k + 2) * q + 1) ^ ea
  let F : ℕ → ℕ := fun q => Cb q * (oracleSizeBound g.degree q + 1) + q + 2 +
    KL * (q + 1) * (8 + 5 * q) + (q + KL * (q + 1)) + 1
  have pc := polynomiallyBounded_constant
  have pid := polynomiallyBounded_id
  have hCb : PolynomiallyBounded Cb :=
    polynomiallyBounded_mul (pc Ka) (polynomiallyBounded_pow (polynomiallyBounded_add (polynomiallyBounded_add
      (polynomiallyBounded_add (polynomiallyBounded_pow pid _) (pc Mt)) (polynomiallyBounded_mul (pc _) pid)) (pc 1)) ea)
  have hL : PolynomiallyBounded (fun q => KL * (q + 1)) :=
    polynomiallyBounded_mul (pc KL) (polynomiallyBounded_add pid (pc 1))
  have hF : PolynomiallyBounded F := by
    have h1 := polynomiallyBounded_mul hCb (polynomiallyBounded_add (oracleSizeBound_polynomiallyBounded g.degree)
      (pc 1))
    have h3 := polynomiallyBounded_mul hL (polynomiallyBounded_add (pc 8) (polynomiallyBounded_mul (pc 5) pid))
    exact polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
      (polynomiallyBounded_add h1 pid) (pc 2)) h3) (polynomiallyBounded_add pid hL)) (pc 1)
  refine ⟨F, hF, fun N x B hB hq2 hN2 => ?_⟩
  have hν1 : 1 ≤ nu N := by
    show 1 ≤ Nat.log 2 N
    exact Nat.le_log_of_pow_le (by norm_num) (by simpa using hN2)
  have hνq : nu N ≤ width s g N := Outer.log_le_width s.mw (g.sv s) N
  have hDn : (substituted s g x B).n = width s g N := rfl
  have hC := Outer.outC_size_le s.mw (g.sv s) (nu N) hν1 B.src
  have hLq : Outer.instLength g.lenExp (nu N) ≤ width s g N ^ (g.lenExp + 2) := Nat.pow_le_pow_left hνq _
  have hTq : natBitLength ((g.sv s).T (Outer.instLength g.lenExp (nu N))) ≤ Mt + (g.k + 2) * width s g N :=
    (hMt (nu N)).trans (by have := Nat.mul_le_mul_left (g.k + 2) hνq; omega)
  have hCq : (Outer.outC s.mw (g.sv s) (nu N) B.src).circuit.size ≤ Cb (width s g N) :=
    hC.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hDm : (substituted s g x B).m ≤ Cb (width s g N) * (oracleSizeBound g.degree (width s g N) + 1) +
      width s g N + 2 := by
    have h0 := Outer.Dat_size_le s.mw (g.sv s) (nu N) B
    have h1 : (Outer.outC s.mw (g.sv s) (nu N) B.src).circuit.size * (B.pf.size + 1) ≤
        Cb (width s g N) * (oracleSizeBound g.degree (width s g N) + 1) := Nat.mul_le_mul hCq (by omega)
    show (Outer.Dat s.mw (g.sv s) (nu N) B).D.size ≤ _
    exact h0.trans (Nat.add_le_add_right (Nat.add_le_add_right h1 _) _)
  have hLq' : P.code.length (substituted s g x B).n ≤ KL * (width s g N + 1) := hKL _ (by rw [hDn]; exact hq2)
  have h := checkedCircuit_m P.code (substituted s g x B)
  rw [hDn] at h hLq'
  have h5 : P.code.length (width s g N) * (8 + 5 * width s g N) ≤ KL * (width s g N + 1) * (8 + 5 * width s g N) :=
    Nat.mul_le_mul_right _ hLq'
  show (checkedCircuit P.code (substituted s g x B)).m + 1 ≤ Cb (width s g N) *
      (oracleSizeBound g.degree (width s g N) + 1) + width s g N + 2 +
      KL * (width s g N + 1) * (8 + 5 * width s g N) + (width s g N + KL * (width s g N + 1)) + 1
  omega

end

theorem clauseRoom (s : GateSources) (P : ThreeQueryPCPP) : ClauseRoom s P := by
  intro g
  obtain ⟨K, e, hsize⟩ := P.outputSize
  obtain ⟨F, hF, hFm⟩ := checked_m_le s P g
  obtain ⟨c, k, hc, hcb⟩ :=
    polynomiallyBounded_mul (polynomiallyBounded_constant K) (polynomiallyBounded_pow hF e)
  refine ⟨k + 1, max 2 c, by omega, ?_⟩
  intro N x B hB hq hN2
  have hq2 : 2 ≤ Worker.width s g N := (le_max_left _ _).trans hq
  have hqc : c ≤ Worker.width s g N := (le_max_right _ _).trans hq
  have hm := hFm N x B hB hq2 hN2
  have h2 : 2 ^ (P.output (checkedCircuit P.code (Worker.substituted s g x B))).randomBits ≤
      (Worker.width s g N + 2) ^ (k + 1) := by
    calc 2 ^ (P.output (checkedCircuit P.code (Worker.substituted s g x B))).randomBits
        ≤ K * ((checkedCircuit P.code (Worker.substituted s g x B)).m + 1) ^ e := (hsize _).2
      _ ≤ K * F (Worker.width s g N) ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm e)
      _ ≤ c * (Worker.width s g N + 1) ^ k := hcb _
      _ ≤ (Worker.width s g N + 2) * (Worker.width s g N + 2) ^ k :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) k)
      _ = (Worker.width s g N + 2) ^ (k + 1) := by ring
  exact le_clog_of_pow_le h2

end NearCubicGates.Close.Closure
