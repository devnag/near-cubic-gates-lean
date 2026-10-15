import Proof.Gates.Setup.Main
import Proof.Gates.Setup.Growth
import Proof.Gates.Setup.ReadBound
import Proof.CaseAnalysis.CloseoutWitnessOracleBudget
import Proof.Gates.Gadget.CheckedSize
import Proof.Gates.Outer.Size

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.CanonicalWitnessCodec
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu)

theorem frame_len (w : List Bool) : (RepairOrdinary.frame w).length = 2 * w.length + 1 := SubstitutedPoly.frame_len' w

/-- The cold decoder's budget, one exponent (`25`) for every field and width. -/
theorem cold_le {N : ℕ} (x : BitInput N) (field : List Bool) (q : ℕ) (hN : 2 ≤ N) (hf : 16 * field.length ≤ N)
    (hq : q ≤ N) :
    RepairOrdinary.CloseoutWitness.Oracle.budget (List.ofFn x) field q.bits ≤
      40000000000000000000000 * 2 ^ 25 * (N + 1) ^ 25 := by
  have h := RepairOrdinary.CloseoutWitness.Oracle.budget_polynomial (List.ofFn x) field q.bits (by simpa using hN)
    (by simpa using hf) (by rw [LitDecode.value_bits]; simpa using hq)
  rw [List.length_ofFn] at h
  have h2 : (N + 2) ^ 25 ≤ 2 ^ 25 * (N + 1) ^ 25 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) 25
  calc _ ≤ 40000000000000000000000 * (N + 2) ^ 25 := h
    _ ≤ 40000000000000000000000 * (2 ^ 25 * (N + 1) ^ 25) := Nat.mul_le_mul_left _ h2
    _ = _ := by ring

theorem desc_le {N : ℕ} (x : BitInput N) (field : List Bool) (n : ℕ) (c : BooleanCircuit n) (hN : 2 ≤ N)
    (hcap : 16 * field.length ≤ N) (hb : n.bits.length ≤ N + 1) (hdec : decodeBooleanCircuit n (value field) = some c) :
    (PCPPNative.descriptor c).length ≤
      2 * N + 2 * field.length + 2 * n.bits.length + n + 3 +
        RepairOrdinary.CloseoutWitness.Oracle.budget (List.ofFn x) field n.bits := by
  have hN' : 2 ≤ (List.ofFn x).length := by simpa using hN
  have hcap' : 16 * field.length ≤ (List.ofFn x).length := by simpa using hcap
  have hb' : n.bits.length ≤ (List.ofFn x).length + 1 := by simpa using hb
  obtain ⟨out, hr, -, hd⟩ := Worker.cold_ready (List.ofFn x) field n.bits hN' hcap' hb'
  have hv : value n.bits = n := LitDecode.value_bits n
  have hd' : ∀ c' : BooleanCircuit n, decodeBooleanCircuit n (value field) = some c' →
      out RepairOrdinary.CloseoutWitness.Oracle.descriptorSlot = PCPPNative.descriptor c' := by
    rw [hv] at hd; exact hd
  have hl := Dock.ready_len hr (2 * N + 2 * field.length + 2 * n.bits.length + n + 3) (fun j => by
    unfold Worker.coldIn
    split_ifs <;> simp <;> omega)
  have := hl RepairOrdinary.CloseoutWitness.Oracle.descriptorSlot
  rw [hd' c hdec] at this
  exact this

/-- The port bank holds only `h` and `d`. -/
theorem portBank_len (t : ℕ) (a b : Fin t) (h d : List Bool) (i : Fin t) :
    (portBank t a b h d i).length ≤ h.length + d.length := by
  unfold portBank; split_ifs <;> simp

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

/-- **The word of `C^O_{⟨B_src⟩_ν}`** is written by the A-run within its budget. -/
theorem mw_le (R : OuterM.ARun s.mw (g.sv s)) {N : ℕ} (B : BooleanCircuit (width s g N)) :
    (mwWord s g N B).length ≤ (PCPPNative.descriptor B).length + nu N + R.K * (nu N + 1) ^ R.e := by
  obtain ⟨out, hr, -, -, -, hw⟩ := R.run (nu N) (width s g N) B
  have hl := Dock.ready_len hr ((PCPPNative.descriptor B).length + nu N) (fun j => by
    unfold OuterM.aBank; split_ifs <;> simp)
  have := hl R.wOut
  rw [hw] at this
  exact this

/-- **The composite's outputs** are written within its fuel. -/
theorem comp_out_le (cf : CompFull s P g) {N : ℕ} (x : BitInput N) (B : Outer.OuterGuess (width s g N))
    (hq : 2 ≤ width s g N) :
    (pcpp s P g x B).word.length + (RepairOrdinary.frame (supportsWord P.code (width s g N))).length ≤
    2 * ((mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length +
      cf.C * ((mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length + width s g N + 1) ^ cf.e) := by
  obtain ⟨out, hr, -, hw, hs, -, -⟩ := cf.run x B hq
  have hl := Dock.ready_len hr _ (portBank_len cf.t cf.cIn cf.dIn (mwWord s g N B.src) (PCPPNative.descriptor B.pf))
  have h1 := hl cf.wOut
  have h2 := hl cf.sOut
  rw [hw] at h1
  rw [hs] at h2
  have h1' : (pcpp s P g x B).word.length ≤ (mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length +
      cf.C * ((mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length + width s g N + 1) ^ cf.e := h1
  have h2' : (RepairOrdinary.frame (supportsWord P.code (width s g N))).length ≤ (mwWord s g N B.src).length +
      (PCPPNative.descriptor B.pf).length +
      cf.C * ((mwWord s g N B.src).length + (PCPPNative.descriptor B.pf).length + width s g N + 1) ^ cf.e := h2
  omega

/-- **The size of the checked outer verifier.** -/
theorem checked_m_le {N : ℕ} (x : BitInput N) (B : Outer.OuterGuess (width s g N)) :
    (checkedCircuit P.code (Worker.substituted s g x B)).m ≤
      (Outer.outC s.mw (g.sv s) (nu N) B.src).circuit.size * (B.pf.size + 1) + width s g N + 2 +
        P.code.length (width s g N) * (8 + 5 * width s g N) + (width s g N + P.code.length (width s g N)) := by
  have h1 := checkedCircuit_m P.code (Worker.substituted s g x B)
  have h2 := Outer.Dat_size_le s.mw (g.sv s) (nu N) B
  have hn : (Worker.substituted s g x B).n = width s g N := rfl
  have hm : (Worker.substituted s g x B).m = (Outer.Dat s.mw (g.sv s) (nu N) B).D.size := rfl
  rw [hn, hm] at h1
  exact h1.trans (by unfold Worker.width at *; omega)

/-- **Every fixed polynomial in `⌊log₂ N⌋` is at most linear in `N`.** -/
theorem polylog_le (c d : ℕ) : ∃ C : ℕ, ∀ N, c * (nu N + 1) ^ d ≤ C * (N + 1) := by
  refine ⟨c * (d.factorial * 2 ^ d), fun N => ?_⟩
  have h1 : nu N ≤ Nat.log 2 (N + 1) := Nat.log_mono_right (by omega)
  have h2 := log_pow_le d N
  calc c * (nu N + 1) ^ d ≤ c * (Nat.log 2 (N + 1) + 1) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) d)
    _ ≤ c * (d.factorial * 2 ^ d * (N + 1)) := Nat.mul_le_mul_left _ h2
    _ = _ := by ring

/-- The import's circuit `C^O_{⟨B_src⟩_ν}` has polylogarithmic size (`ν ≥ 1`). -/
theorem outC_lin (g : GateParams) : ∃ C : ℕ, ∀ N, 1 ≤ nu N → ∀ {m : ℕ} (B : BooleanCircuit m),
    (Outer.outC s.mw (g.sv s) (nu N) B).circuit.size ≤ C * (N + 1) := by
  obtain ⟨M, hM⟩ := Outer.natBitLength_T_le (g.sv s)
  let A := Outer.alg s.mw (g.sv s)
  obtain ⟨C, hC⟩ := polylog_le (A.coefficient * (M + g.k + 4) ^ A.sizeExp) ((g.lenExp + 2) * A.sizeExp)
  refine ⟨C, fun N hν m B => ?_⟩
  have h1 := Outer.outC_size_le s.mw (g.sv s) (nu N) hν B
  have h2 := hM (nu N)
  have h3 : Outer.instLength g.lenExp (nu N) + natBitLength ((g.sv s).T (Outer.instLength g.lenExp (nu N))) + 1 ≤
      (M + g.k + 4) * (nu N + 1) ^ (g.lenExp + 2) := by
    have hI : Outer.instLength g.lenExp (nu N) = nu N ^ (g.lenExp + 2) := rfl
    rw [hI] at h2 ⊢
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = (nu N + 1) ^ (g.lenExp + 2) := ⟨_, rfl⟩
    have hp1 : 1 ≤ Q := by rw [hQ]; exact Nat.one_le_pow _ _ (by omega)
    have hp2 : nu N ^ (g.lenExp + 2) ≤ Q := by rw [hQ]; exact Nat.pow_le_pow_left (by omega) _
    have hp3 : nu N + 1 ≤ Q := by rw [hQ]; exact Nat.le_self_pow (by omega) _
    have h4 : (g.k + 2) * nu N ≤ (g.k + 2) * Q := Nat.mul_le_mul_left _ (by omega)
    have h5 : M ≤ M * Q := Nat.le_mul_of_pos_right _ hp1
    have e : (M + g.k + 4) * Q = M * Q + (g.k + 2) * Q + 2 * Q := by ring
    rw [← hQ, e]
    omega
  calc (Outer.outC s.mw (g.sv s) (nu N) B).circuit.size
      ≤ A.coefficient * (Outer.instLength g.lenExp (nu N) +
          natBitLength ((g.sv s).T (Outer.instLength g.lenExp (nu N))) + 1) ^ A.sizeExp := h1
    _ ≤ A.coefficient * ((M + g.k + 4) * (nu N + 1) ^ (g.lenExp + 2)) ^ A.sizeExp :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 _)
    _ = A.coefficient * (M + g.k + 4) ^ A.sizeExp * (nu N + 1) ^ ((g.lenExp + 2) * A.sizeExp) := by
        rw [mul_pow, ← pow_mul]; ring
    _ ≤ C * (N + 1) := hC N

end NearCubicGates.Close.Setup
