import Proof.Gates.ENP.TableSeed

set_option autoImplicit false

namespace NearCubicGates.Close.ENP.TEmit

open NearCubicWires NearCubicWires.Bindings.MW20

def SeedsCostPoly : Prop :=
  ∃ K e : ℕ, ∀ {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post : List Bool),
    TCirc.T ℓ * (seedCostC C + 4) + 1 ≤ K * (2 ^ ℓ + ((OracleOutput.word ⟨ℓ, C⟩) ++ post).length + 1) ^ e

theorem seedsRuns_of (hB : TBytesSpec) (hP : SeedsCostPoly) : SeedsRuns := by
  obtain ⟨K, e, hK⟩ := hP
  exact ⟨K, e, fun {ℓ} C post => ⟨seedCapSum C, TCirc.T ℓ * (seedCostC C + 4) + 1, hK C post,
    fun cap hcap => seedsLoop_exec hB C post cap hcap⟩⟩

end NearCubicGates.Close.ENP.TEmit
