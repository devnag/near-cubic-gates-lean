import NineInputs
import SourceAdapters.Proximity.CircuitRepresentation
import SourceAdapters.Machine.OrdinaryToTM2
import Bindings.TuringBridge.OutputFree
import Proof.Foundations.OrdinaryMachine
import Mathlib.Tactic

/-!
Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": polynomial-time source query algorithms print addresses
of polynomial bit length. This follows from actual execution and output size,
using the proved ordinary-to-stack simulation; no TM2 machines are composed.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicGates.Published.CW19Proximity

theorem source_output_length {Request : Type} (input output : Request → List Bool)
    (h : SourcePolyTime input output) :
    ∃ C d : ℕ, ∀ request,
      (output request).length ≤ C * ((input request).length + 1) ^ d := by
  obtain ⟨K, e, ⟨W⟩⟩ := h
  let M := Machine.tm2InTime (ea := input) (eb := id) (f := output)
    W (fun n => K * (n + 1) ^ e) (fun _ => le_rfl)
  let S := Bindings.Sim.maxStmtSize M.tm
  refine ⟨1 + 9 * (K + 1) * S, e + 1, fun request => ?_⟩
  let L := (input request).length
  have hout := Bindings.Sim.output_length_le M request
  change (output request).length ≤ L + 9 * (L + K * (L + 1) ^ e + 1) * S at hout
  have htime := Machine.poly_bound K e L
  have hmul := Nat.mul_le_mul_right S htime
  have hL : L ≤ (L + 1) ^ (e + 1) :=
    (Nat.le_succ L).trans (Nat.le_self_pow (by omega) _)
  change (output request).length ≤ (1 + 9 * (K + 1) * S) * (L + 1) ^ (e + 1)
  nlinarith

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": every source proof address has polynomial bit length in its
actual request, including the circuit, old coins and query index. -/
theorem query_address_length {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (hquery : SourcePolyTime (queryRequestWord (V := V))
      (fun p => queryAddressWord ((V p.1).query p.2.1 p.2.2))) :
    ∃ C d : ℕ, ∀ p : QueryRequest V, ∀ address : ℕ,
      (V p.1).query p.2.1 p.2.2 = .inr address →
      address.bits.length ≤ C * ((queryRequestWord p).length + 1) ^ d := by
  obtain ⟨C, d, hlength⟩ := source_output_length _ _ hquery
  refine ⟨C, d, fun p address haddress => ?_⟩
  have h := hlength p
  rw [haddress] at h
  simp only [queryAddressWord, List.length_cons, RepairOrdinary.frame_length] at h
  omega

theorem query_request_length {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) (p : QueryRequest V) :
    (queryRequestWord p).length ≤
      (sourceCircuitWord p.1).length + 2 * (V p.1).randomBits + 2 * q + 2 := by
  have hcoin : p.2.1.val.bits.length ≤ (V p.1).randomBits := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr p.2.1.isLt
  have hindex : p.2.2.val.bits.length ≤ q := by
    rw [Nat.size_eq_bits_len]
    have hs : Nat.size p.2.2.val ≤ p.2.2.val := Nat.size_le.mpr Nat.lt_two_pow_self
    have hq := (V p.1).queryCount_le p.2.1
    have hj := p.2.2.isLt
    omega
  simp only [queryRequestWord, List.length_append, RepairOrdinary.frame_length]
  omega

theorem query_request_source_bound {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) (a : ℕ)
    (hr : ∀ C, (V C).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord C).length + 2))
    (p : QueryRequest V) :
    (queryRequestWord p).length + 1 ≤
      (2 * a + 2 * q + 4) * ((sourceCircuitWord p.1).length + 2) := by
  have hrequest := query_request_length V p
  have hlog : Nat.clog 2 ((sourceCircuitWord p.1).length + 2) ≤
      (sourceCircuitWord p.1).length + 2 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hr' := (hr p.1).trans (Nat.mul_le_mul_left a hlog)
  nlinarith

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": queried source proof addresses have polynomial bit length
in the companion's node count, including zero/small arities. -/
theorem query_address_target_bound {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) (a : ℕ)
    (hr : ∀ C, (V C).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord C).length + 2))
    (hquery : SourcePolyTime (queryRequestWord (V := V))
      (fun p => queryAddressWord ((V p.1).query p.2.1 p.2.2))) :
    ∃ K e : ℕ, ∀ C : Bindings.CLW20Lemma311.Circuit,
      ∀ coins j address, (V (sourceCircuit C)).query coins j = .inr address →
        address.bits.length ≤ K * (C.m + 1) ^ e := by
  obtain ⟨K, d, hlength⟩ := query_address_length V hquery
  let A := (2 * a + 2 * q + 4) * 13
  refine ⟨K * A ^ d, 2 * d, fun C coins j address haddress => ?_⟩
  let p : QueryRequest V := ⟨sourceCircuit C, coins, j⟩
  have hsource := source_word_length_target C
  have hone : 1 ≤ (C.m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hword : (sourceCircuitWord (sourceCircuit C)).length + 2 ≤ 13 * (C.m + 1) ^ 2 := by
    nlinarith
  have hrequest := (query_request_source_bound V a hr p).trans
    (Nat.mul_le_mul_left (2 * a + 2 * q + 4) hword)
  have hreq : (queryRequestWord p).length + 1 ≤ A * (C.m + 1) ^ 2 := by
    simpa only [A, Nat.mul_assoc] using hrequest
  calc
    address.bits.length ≤ K * ((queryRequestWord p).length + 1) ^ d := hlength p address haddress
    _ ≤ K * (A * (C.m + 1) ^ 2) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hreq d)
    _ = (K * A ^ d) * (C.m + 1) ^ (2 * d) := by
      simp only [mul_pow, pow_mul]
      ring

end NearCubicGates.Adapters.Proximity
