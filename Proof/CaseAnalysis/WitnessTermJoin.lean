import Proof.CaseAnalysis.WitnessTermWidth

/-! Keep the actual term parser's large control type opaque at the
loader-to-parser handoff. This is only a configuration projection. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermJoin
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem restart_embedded {t e a b : ℕ} (p : Machine t b)
    (c : Configuration (t+e) a) (input : Fin t→List Bool)
    (heads : Fin e→ℕ) (extra : Fin e→List Bool)
    (hh : c.heads=Fin.addCases (m:=t) (n:=e) (motive:=fun _=>ℕ) (fun _=>0) heads)
    (ht : c.tapes=Fin.addCases (m:=t) (n:=e) (motive:=fun _=>List Bool) input extra) :
    Composition.restart c (TapeEmbedding.machine e p).start=
      TapeEmbedding.config heads extra (initialConfiguration p input):=
  configuration_ext rfl hh ht

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermJoin
