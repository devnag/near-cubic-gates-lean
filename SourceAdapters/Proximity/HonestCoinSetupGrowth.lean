import SourceAdapters.Proximity.HonestCoinSetup
import SourceAdapters.Proximity.HonestPreparationSizes

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": numerical demands and the checked randomness
setup clock are polynomial in the exact prepared honest input. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestCoinSetup

open NearCubicWires NearCubicGates.Published.CW19Proximity Growth
open HonestPreparationSizes (measure)

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)

def demand (K e : ℕ) (p : AcceptedSourceInput) : ℕ :=
  (V p.1).randomBits + predicateBlockBits q + (sourceCircuitWord p.1).length +
    K * ((proofCallInput V (SourceCallee.randomRequest V p.1)).length + 1) ^ e + 10

theorem request_length (p : AcceptedSourceInput) :
    (proofCallInput V (SourceCallee.randomRequest V p.1)).length = 2 + (sourceCircuitWord p.1).length := by
  rw [SourceCallee.random_input, List.length_append]
  rfl

theorem bounds (K e : ℕ) (p : AcceptedSourceInput) (Wd Lk Bk : ℕ)
    (hw : demand V K e p ≤ Wd) (hl : demand V K e p ≤ Lk) (hb : demand V K e p ≤ Bk) :
    4 ≤ 2 ^ Wd ∧ (proofCallInput V (SourceCallee.randomRequest V p.1)).length ≤ Lk ∧
    K * ((proofCallInput V (SourceCallee.randomRequest V p.1)).length + 1) ^ e ≤ Bk ∧
    (V p.1).randomBits.bits.length + 1 ≤ Wd ∧ (V p.1).randomBits < Wd ∧
    (V p.1).randomBits + predicateBlockBits q < 2 ^ Wd := by
  have he := Nat.lt_two_pow_self (n := Wd)
  have hbits := SourceCallee.bits_length_le (V p.1).randomBits
  simp only [demand] at hw hl hb
  rw [request_length] at hw hl hb ⊢
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem demand_bounded (a K e : ℕ)
    (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2)) :
    Bounded (measure V) (demand V K e) := by
  have hrand := HonestPreparationSizes.random_bounded V a hr
  have hs : Bounded (measure V) (fun p => (sourceCircuitWord p.1).length) :=
    bounded_size.mono (HonestPreparationSizes.source_length V)
  have hrq : Bounded (measure V) (fun p => (proofCallInput V (SourceCallee.randomRequest V p.1)).length) := by
    simpa only [request_length] using (bounded_const 2).add hs
  exact ((((hrand.add (bounded_const (predicateBlockBits q))).add hs).add
    ((bounded_const K).mul ((hrq.add (bounded_const 1)).pow e))).add (bounded_const 10))

theorem cost_bounded (a : ℕ)
    (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2))
    (Lk Bk : AcceptedSourceInput → ℕ) (hL : Bounded (measure V) Lk) (hB : Bounded (measure V) Bk) :
    Bounded (measure V) (fun p => cost q (V p.1).randomBits (sourceCircuitWord p.1).length (Lk p) (Bk p)) := by
  have hrand := HonestPreparationSizes.random_bounded V a hr
  have hrbits := hrand.mono (fun p => SourceCallee.bits_length_le (V p.1).randomBits)
  have hs : Bounded (measure V) (fun p => (sourceCircuitWord p.1).length) :=
    bounded_size.mono (HonestPreparationSizes.source_length V)
  have hcall := ((((bounded_const 15).mul hs).add hL).add hB).add ((bounded_const 10).mul hrbits)
  exact ((hcall.add ((bounded_const 5).mul hrand)).add
    (bounded_const (2 * predicateBlockBits q))).add (bounded_const 47)

end NearCubicGates.Adapters.Proximity.HonestCoinSetup
