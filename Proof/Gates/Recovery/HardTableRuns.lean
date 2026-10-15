import Proof.Gates.CheckedPCPP.Composite
import Proof.MachineModel.ClockJoin
import Proof.Foundations.OuterPCPRecovery

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicGates.Close.Gadget
open NearCubicGates.Close.Transfer

/-- The five input words of the Case 2 producer: the word of `C_{⟨B*_src⟩_ν}`, the recovered description of `B*_pf`,
the final address, unary `q`, unary `B`. -/
def fiveWords (word description address : List Bool) (R B : ℕ) : Fin 5 → List Bool :=
  ![word, description, address, List.replicate R true, List.replicate B true]

/-- The producer's entry bank: the five words on the ports `j ↦ j`, every other tape empty. -/
def portInput (t : ℕ) (word description address : List Bool) (R B : ℕ) : Fin t → List Bool :=
  fun i => if h : i.val < 5 then fiveWords word description address R B ⟨i.val, h⟩ else []

def HardTableRuns : Prop :=
  ∀ (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams),
    ∃ (t states : ℕ) (machine : LocalBitMultitape.Machine t states) (output : Fin t), 5 ≤ output.val ∧
    ∃ cutoff C E : ℕ, ∀ (n : ℕ) (point : BitInput n) (ν : ℕ) (z : BitInput (2 ^ ν)), ν ≤ n → cutoff ≤ 2 ^ ν →
      ∀ h : g.IsCaseTwo s ν z,
      ∃ out, ClockJoin.ReadyRun machine (C * (2 ^ n + 1) ^ E)
        (portInput t (CheckedPCPP.mwWord s g (2 ^ ν) (g.selectedPair s ν z h).src)
          (RepairOrdinary.frame (OuterPCPRecovery.canonicalBoundedCircuitDescription (g.bound s ν)
            (g.selectedPair s ν z h).pf))
          (RepairOrdinary.frame (List.ofFn point)) (g.width s ν) (g.bound s ν)) out ∧
        out output = RepairOrdinary.frame (g.gateCore s P (selectedAmplifier s.amplification g.degree) ν z
          (CloseoutLanguage.clauseWidth g.clauseDegree (g.width s ν)) g.positionLog n point).toNat.bits

end NearCubicGates.Close.Recovery
