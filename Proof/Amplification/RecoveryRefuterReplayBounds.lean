import Proof.Amplification.RecoveryEncodedNPVerifier
import Proof.MachineModel.OrdinarySourceSATLiftRequest
import Proof.Foundations.HierarchySourceContract

/-! Derive the physical lifted-refuter budget from the selected source and
its actual polynomial clock; no runtime bound is a new input premise. -/
namespace NearCubicWires.RepairSource.RecoveryRefuterReplay
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficient (sourceC sourceD descriptionLength clockC : Nat) :=
  (sourceC*(descriptionLength+3)^sourceD)*(clockC+1)^sourceD
def degree (sourceD clockD : Nat) := clockD*sourceD

theorem source_bound (sourceC sourceD descriptionLength clockC clockD t n : Nat)
    (hn : n≤t) (ht : t≤clockC*(n+1)^clockD) :
    sourceC*(t+n+descriptionLength+1)^sourceD ≤
      coefficient sourceC sourceD descriptionLength clockC*(n+1)^degree sourceD clockD := by
  have hp : 1≤(n+1)^clockD := Nat.one_le_pow _ _ (by omega)
  have ha : t+1≤(clockC+1)*(n+1)^clockD := by nlinarith only [ht,hp]
  calc
    _ ≤ (sourceC*(descriptionLength+3)^sourceD)*(t+1)^sourceD :=
      refuter_fixed_machine_budget _ _ _ _ _ hn
    _ ≤ (sourceC*(descriptionLength+3)^sourceD)*((clockC+1)*(n+1)^clockD)^sourceD :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ha sourceD)
    _ = _ := by simp only [coefficient,degree,mul_pow,←pow_mul]; ring

end NearCubicWires.RepairSource.RecoveryRefuterReplay
