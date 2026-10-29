import Proof.Gates.Succinct.SubstitutionRun
import Proof.Gates.Succinct.SubstitutionPre
import Proof.Gates.Succinct.SubstitutionEnd
import Proof.Gates.Succinct.SubstitutionPost
import Proof.Gates.Succinct.SubstitutionInputNode
import Proof.Gates.Succinct.SubstitutionReadyOfRun

set_option autoImplicit false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Succinct NearCubicGates.Close.Outer

/-- `C`'s input nodes in the emission loop (`sec:gadget-machine`, `D_B`: an input gate of `C` is copied). -/
theorem kind1OK (o : OracleOutput) {q : ℕ} (B : BooleanCircuit q) : Kind1OK (capH o B) o B :=
  fun _ _ _ h j hk => kind1 h j hk

theorem substRun : SubstRunSpec := substRun_of preSpec (postSpec_of endOutSpec) costSpec kind1OK

theorem substReady : SubstReadySpec := substReady_of_run substRun

end NearCubicGates.Close.Succinct.SubstMachine
