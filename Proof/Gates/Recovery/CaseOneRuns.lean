import Proof.Gates.Interfaces.Transfer
import Proof.MachineModel.ClockJoin

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.ExecutableInterfaces NearCubicGates.Close.Transfer

/-- The periodic function on `q` address bits given by a table `w` of length `2^a`: `w` at the first `a` address bits
(`false` past `q`) — the common form of Case 1 (i) `X_z` and Case 1 (iii) `O*` (paper v2 §11.5). -/
def cycFn (a : ℕ) (w : BitInput (2 ^ a)) (q : ℕ) : BoolFunction q := fun r =>
  w (binaryAddress fun j : Fin a => if h : j.val < q then r ⟨j.val, h⟩ else false)

/-- The three input words of the Case 1 machine: the framed table (with any suffix), the framed final address, `1^q`. -/
def threeWords (table address : List Bool) (q : ℕ) : Fin 3 → List Bool :=
  ![table, address, List.replicate q true]

/-- The Case 1 machine's entry bank: the three words on the ports `j ↦ j`, every other tape empty. -/
def oneInput (t : ℕ) (table address : List Bool) (q : ℕ) : Fin t → List Bool :=
  fun i => if h : i.val < 3 then threeWords table address q ⟨i.val, h⟩ else []

/-- **The Case 1 machine (statement, (a′) form; paper v2 §11.5–§11.6).** For every schedule amplifier, one fixed
machine, started on `frame (List.ofFn w) ++ rest`, `frame (List.ofFn point)` and `1^q`, returns the framed value at
`point` of the amplified periodic function `cycFn a w q`, padded to the final arity `n` (`GateParams.amplified`),
whenever `1 ≤ q ≤ n` and the amplified arity fits `n`, within `C·(2^n+1)^E`. -/
def CaseOneRuns : Prop :=
  ∀ {c d : ℕ} (amplifier : OrdinaryScheduleAmplifier c d),
    ∃ (t states : ℕ) (machine : LocalBitMultitape.Machine t states) (output : Fin t), 3 ≤ output.val ∧
    ∃ C E : ℕ, ∀ (a q : ℕ) (w : BitInput (2 ^ a)) (rest : List Bool) (n : ℕ) (point : BitInput n),
      1 ≤ q → q ≤ n → (amplifier.output q (cycFn a w q)).arity ≤ n →
      ∃ out, ClockJoin.ReadyRun machine (C * (2 ^ n + 1) ^ E)
        (oneInput t (RepairOrdinary.frame (List.ofFn w) ++ rest) (RepairOrdinary.frame (List.ofFn point)) q) out ∧
        out output = RepairOrdinary.frame (GateParams.amplified amplifier q (cycFn a w q) n point).toNat.bits

end NearCubicGates.Close.Recovery
