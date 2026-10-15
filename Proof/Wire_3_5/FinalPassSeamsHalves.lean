import Proof.Wire_3_5.FinalPassSeamsBank2
import Proof.Wire_3_5.FinalPassSeamsProg3
import Proof.Wire_3_5.FinalPassAssemblyDock3

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Bank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.PrimAsm.S5Seam NearCubicWires.WireExponent3_5.Split

/-- **The core half's target, generic in the bank**, rooms `mT l`, `mC l`, at every call family. -/
abbrev CoreHalfGen2 (Sw : SymWords) (mT mC : Literals → ℕ) : Type :=
  ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
    HalfGen2 (fun L : S5Lay Sw.nw => S5CoreB3 l F kclk coef A a ha Sw L) (mT l) (mC l)

/-- **The out machine's target, generic in the layout**: an `mX`-tape room inside the blank scratch set, off the
output and number tapes. -/
abbrev OutGen (mX : ℕ) : Type :=
  ∀ (t : ℕ) (o tN tD : Fin t) (sc : Fin t → Bool) (e : Fin mX ↪ Fin t), (∀ i, sc (e i) = true) →
    (∀ i, e i ≠ o ∧ e i ≠ tN ∧ e i ≠ tD) → o ≠ tN → o ≠ tD → tN ≠ tD → OutMachine2 t o tN tD sc

end NearCubicWires.WireExponent3_5.FinalPass.Bank
