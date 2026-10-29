import SourceAdapters.Routing.TermsMachineMain
import SourceAdapters.Routing.CoordinateMachineInputRunner

/-!
# Polynomial-time ordinary printing of the exact terms circuit

The construction in `lem:generator`: the fixed printer counts and then emits every
literal circuit gate. The ordinary wrapper pays for framing, width allocation
and compilation in the physical length of the raw request.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine

open Joins CoordinateMachine

/-- A fixed ordinary program with a uniform polynomial bound on raw request length. -/
noncomputable def termsProgram :
    NearCubicWires.RepairOrdinary.WordFunction {p : TermsReq // TermsOk p}
      (fun p => termsInput p.1 p.2) (fun p => termsOutput p.1 p.2)
      (fun p => ordinaryCoefficient Main.program *
        ((termsInput p.1 p.2).length + 1) ^ ordinaryDegree Main.program) :=
  polynomialProgram (fun p : {p : TermsReq // TermsOk p} => termsInput p.1 p.2)
    (fun p => termsOutput p.1 p.2) Main.program Main.program_wf
    (fun p => (Main.main_spec p.1 p.2).2) (fun p => (Main.main_spec p.1 p.2).1)

/-- The full terms-circuit interface, with no source or execution assumptions. -/
theorem termsCircuitWF : Joins.TermsCircuitWF :=
  ⟨ordinaryCoefficient Main.program, ordinaryDegree Main.program, ⟨termsProgram⟩⟩

end NearCubicGates.Adapters.Routing.TermsMachine
