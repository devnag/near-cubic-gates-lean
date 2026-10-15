import Proof.Amplification.RecoveryTseitinRun

/-! The shared original free-input tautology is physically encoded from
one retained framed index. Both copies of its positive literal are actual
field copies. This endpoint is reusable by both recovery formulas. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinTautology
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryTseitinKernel CircuitInputCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def signs : Fin 3→Bool := ![true,false,true]
def sources : Fin 3→Fin 3 := fun _=>0
def capacity (index : Nat) := RecoveryTseitin.capacity (Prepare.literals signs (fun _=>index))
noncomputable def machine := kernel signs sources

theorem tautology_run (cap log index : Nat) (ambient : Fin 239→List Bool) (padding : List Bool)
    (hcap : capacity index ≤ cap) (hb : Bounded cap ambient)
    (hd : ambient 3=List.replicate cap true) (hl : ambient 4=List.replicate log false)
    (hz : log ≤ cap+1) (hi : ambient 0=RepairOrdinary.frame index.bits++padding) :
    ∃ out : Fin 239→List Bool,
      ClockJoin.ReadyRun machine (16*cap) ambient out ∧
      out clauseSlot=ZeroPadding.pad cap (RepairOrdinary.frame (Encodable.encode (circuitInputTautology index)).bits) ∧
      (∀ i : Fin 239,i.val<3 → out i=ambient i) ∧
      out 3=List.replicate cap true ∧ out 4=List.replicate (cap+1) false ∧ Bounded cap out := by
  have h := clause_run cap log signs sources (fun _=>index) ambient (fun _=>padding)
    hcap hb hd hl hz (by intro k; exact hi)
  exact h

end NearCubicWires.RepairSource.RecoveryTseitinTautology
