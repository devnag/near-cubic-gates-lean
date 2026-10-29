import SourceAdapters.Proximity.HonestSource
import SourceAdapters.Proximity.SourceGrowth
import SourceAdapters.Joins.HonestRestriction
import Proof.Gates.Cells.OutLen

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": numerical resources are bounded by the actual
prepared honest input. Proof length is bounded by an existing ordinary run. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestPreparationSizes

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicGates.Published.CW19Proximity
open NearCubicGates.Adapters.Joins Growth

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)

def measure (p : AcceptedSourceInput) : ℕ := (preparedHonestInput V p).length

theorem source_length (p : AcceptedSourceInput) : (sourceCircuitWord p.1).length ≤ measure V p := by
  simp only [measure, preparedHonestInput, List.length_append, frame_length]
  omega

theorem input_length (p : AcceptedSourceInput) : p.1.arity ≤ measure V p := by
  simp only [measure, preparedHonestInput, List.length_append, frame_length, List.length_ofFn]
  omega

theorem accepted_length (p : AcceptedSourceInput) : (acceptedSourceWord p).length ≤ measure V p := by
  simp only [measure, preparedHonestInput, acceptedSourceWord, List.length_append, frame_length]
  omega

theorem address_word_length (p : AcceptedSourceInput) :
    (trimAddressWord (clauseTrimRequest V p.1)).length ≤ measure V p := by
  simp only [measure, preparedHonestInput, List.length_append]
  omega

theorem schedule_length (p : AcceptedSourceInput) :
    (trimSortedAddresses (clauseTrimRequest V p.1)).length ≤ measure V p := by
  have hs := length_le_flatMap_natWord (trimSortedAddresses (clauseTrimRequest V p.1))
  have ha := address_word_length V p
  simp only [trimAddressWord, List.length_append] at ha
  omega

theorem transfer (f : SourceCircuit → ℕ) (h : Bounded SourceCallee.sourceMeasure f) :
    Bounded (measure V) (fun p => f p.1) := by
  obtain ⟨K, e, hK⟩ := h
  refine ⟨K, e, fun p => (hK p.1).trans ?_⟩
  exact Nat.mul_le_mul_left K (Nat.pow_le_pow_left (Nat.add_le_add_right (source_length V p) 1) e)

theorem arity_bounded : Bounded (measure V) (fun p => p.1.arity) :=
  bounded_size.mono (input_length V)

theorem schedule_bounded : Bounded (measure V) (fun p =>
    (trimSortedAddresses (clauseTrimRequest V p.1)).length) := bounded_size.mono (schedule_length V)

theorem random_bounded (a : ℕ)
    (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2)) :
    Bounded (measure V) (fun p => (V p.1).randomBits) :=
  transfer V _ (SourceCallee.random_bounded V a hr)

theorem coins_bounded (a : ℕ)
    (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2)) :
    Bounded (measure V) (fun p => 2 ^ (V p.1).randomBits) :=
  transfer V _ (SourceCallee.coins_bounded V a hr)

theorem request_cap_bounded (a : ℕ) : Bounded (measure V)
    (fun p => SourceCallee.requestCap q a (sourceCircuitWord p.1).length) :=
  transfer V _ (SourceCallee.requestCap_bounded q a)

theorem call_budget_bounded (a K e : ℕ) : Bounded (measure V)
    (fun p => SourceCallee.callBudgetCap q a K e (sourceCircuitWord p.1).length) :=
  transfer V _ (SourceCallee.callBudgetCap_bounded q a K e)

theorem auxiliary_cap_bounded (a : ℕ)
    (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2)) :
    Bounded (measure V) (fun p => SourceCallee.auxiliaryCap q (V p.1).randomBits) :=
  transfer V _ (SourceCallee.auxiliaryCap_bounded V a hr)

theorem honest_request_length (p : AcceptedSourceInput) :
    (proofCallInput V (HonestSource.request V p)).length = 2 + (acceptedSourceWord p).length := by
  have hw : proofCallInput V (HonestSource.request V p) = [true, false] ++ acceptedSourceWord p := rfl
  rw [hw, List.length_append]
  rfl

theorem honest_request_bounded : Bounded (measure V)
    (fun p => (proofCallInput V (HonestSource.request V p)).length) :=
  ((bounded_const 2).add bounded_size).mono (fun p => by rw [honest_request_length]; exact Nat.add_le_add_left (accepted_length V p) 2)

theorem honest_budget_bounded (K e : ℕ) : Bounded (measure V)
    (fun p => K * ((proofCallInput V (HonestSource.request V p)).length + 1) ^ e) :=
  (bounded_const K).mul (((honest_request_bounded V).add (bounded_const 1)).pow e)

theorem proof_size_bounded (proofSize : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1)) (K e : ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofSize honest)
      (fun r => K * ((proofCallInput V r).length + 1) ^ e)) :
    Bounded (measure V) (fun p => proofSize p.1) := by
  apply (honest_budget_bounded V K e).mono
  intro p
  have h := NearCubicGates.Close.Cells.wf_out_len P (HonestSource.request V p)
  have ho : normalizedProofOutput V proofSize honest (HonestSource.request V p) = frame (List.ofFn (honest p)) := rfl
  rw [ho, frame_length, List.length_ofFn] at h
  omega

end NearCubicGates.Adapters.Proximity.HonestPreparationSizes
