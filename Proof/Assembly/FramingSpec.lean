import Proof.Assembly.LoopPlan
import Proof.Hierarchy.CompetitorRawRecordEmit

/-! Fixed complete-Datum copier interface consumed by the new enclosing parent.
The finite field list depends only on the fixed printer, not on runtime rows.
Entry fields are physically framed and zero-padded; producing those fields
and their capacities is the preceding row stage, not advice supplied here.
All field buffers/cursors and the copier counter are preserved. Only the
append-only descriptor grows. There is no per-row accumulator rewind. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

namespace DatumCopier
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit
open NearCubicWires.SourceInterfaces

def target (t : Nat) : Fin (t+2) := (0 : Fin 2).natAdd t
def counter (t : Nat) : Fin (t+2) := (1 : Fin 2).natAdd t
def fieldSlots (t : Nat) : List (Fin (t+2)) :=
  (List.finRange t).map (fun j => j.castAdd 2)

def fields {t : Nat} (A : Fin t → List Bool) : Fin (t+2) → List Bool :=
  Fin.addCases A (fun _ : Fin 2 => [])

def heads (t : Nat) (out : List Bool) : Fin (t+2) → Nat :=
  Fin.addCases (fun _ : Fin t => 0) ![out.length,0]

def bank {t : Nat} (A : Fin t → List Bool) (out : List Bool) (cap : Nat) :
    Fin (t+2) → List Bool :=
  Fin.addCases (fun j => frame (A j)) ![out,List.replicate cap false]

def word {t : Nat} (A : Fin t → List Bool) :=
  (List.finRange t).flatMap (fun j => frame (A j))

noncomputable def machine (t : Nat) := listProgram (target t) (counter t) (fieldSlots t)
def budget {t : Nat} (A : Fin t → List Bool) := listCost (fields A) (fieldSlots t)

/-- Reusable field capacities. Descriptor and copier counter receive no new
padding; the counter already has its explicit paid cap-length zero backing. -/
def reserves {t : Nat} (F : Fin t → Nat) : Fin (t+2) → Nat :=
  Fin.addCases F (fun _ : Fin 2 => 0)

def paddedBank {t : Nat} (F : Fin t → Nat) (A : Fin t → List Bool)
    (out : List Bool) (cap : Nat) : Fin (t+2) → List Bool :=
  Fin.addCases (fun j => ZeroPadding.pad (F j) (frame (A j))) ![out,List.replicate cap false]

/-- The actual consumer's entire bank, including its prescribed blank fields.
Producing each framed word remains the row field producer's paid duty. -/
noncomputable def datumFields (a : WilliamsAlgorithm) (d : P1TopDownPaidReusable.Datum) :=
  P1TopDownPaidReloadCore.input a d.row d.C d.Q d.select

noncomputable def datumMachine (a : WilliamsAlgorithm) := machine (P1TopDownPaidPayload.tapes a)
noncomputable def datumBudget (a : WilliamsAlgorithm) (d : P1TopDownPaidReusable.Datum) :=
  budget (datumFields a d)

/-- Complete correctness of this particular fixed candidate framer. -/
noncomputable def Correct : Prop :=
  ∀ (a : WilliamsAlgorithm) (d : P1TopDownPaidReusable.Datum)
    (F : Fin (P1TopDownPaidPayload.tapes a) → Nat) (out : List Bool) (cap : Nat),
    (∀ j, 2*(datumFields a d j).length+1 ≤ cap) →
    Step (datumMachine a) (datumBudget a d) (heads _ out)
      (paddedBank F (datumFields a d) out cap)
      (heads _ (out++d.word a)) (paddedBank F (datumFields a d) (out++d.word a) cap)

end DatumCopier
