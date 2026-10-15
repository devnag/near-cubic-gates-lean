import Proof.Gates.Worker.TermsGlue
import Proof.Gates.CheckedPCPP.LitDecode

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Interfaces
open NearCubicGates.Close.CheckedPCPP.LitDecode (litVar litNeg)

variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams)

namespace Guess
variable {s g} {N : ℕ} (x : BitInput N) (G : Guess (width s g N))

/-- The operand of a literal from its decoded variable and sign. -/
theorem literalParts_eq (l : Literal (G.Arity P x)) :
    G.literalParts P x l = (decide (litNeg l ≠ 0),
      if litVar l < sysCount s P g x G.oracle then Atom.sys (litVar l) else Atom.aux (litVar l - sysCount s P g x G.oracle)) := by
  cases l with
  | positive i => simp [literalParts, atomOf, literalNeg, literalVar, litNeg, litVar]
  | negative i => simp [literalParts, atomOf, literalNeg, literalVar, litNeg, litVar]

variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) (w : List Bool)

theorem termParts_sys (f : Bool) (u : ℕ) :
    G.termParts P x ctr ω w [(f, .sys u)] = (f, (parityMean (G.sysSupport P x u), 0)) := by
  simp [termParts]

theorem termParts_aux (f : Bool) (j : ℕ) :
    G.termParts P x ctr ω w [(f, .aux j)] = (f, ctr.value (G.singleCall ω j ∅) w) := by
  simp [termParts]

theorem termParts_sys_sys (f1 f2 : Bool) (u v : ℕ) :
    G.termParts P x ctr ω w [(f1, .sys u), (f2, .sys v)] =
      (xor f1 f2, (parityMean (symmDiff (G.sysSupport P x u) (G.sysSupport P x v)), 0)) := by
  simp [termParts]

theorem termParts_sys_aux (f1 f2 : Bool) (u j : ℕ) :
    G.termParts P x ctr ω w [(f1, .sys u), (f2, .aux j)] =
      (xor f1 f2, ctr.value (G.singleCall ω j (G.sysSupport P x u)) w) := by
  simp [termParts]

theorem termParts_aux_sys (f1 f2 : Bool) (j u : ℕ) :
    G.termParts P x ctr ω w [(f1, .aux j), (f2, .sys u)] =
      (xor f1 f2, ctr.value (G.singleCall ω j (G.sysSupport P x u)) w) := by
  simp [termParts]

theorem termParts_aux_aux (f1 f2 : Bool) (i j : ℕ) :
    G.termParts P x ctr ω w [(f1, .aux i), (f2, .aux j)] =
      (xor f1 f2, if i = j then (0, 0) else ctr.value (G.pairCall ω i j) w) := by
  simp [termParts]

end Guess

end NearCubicGates.Close.Worker
