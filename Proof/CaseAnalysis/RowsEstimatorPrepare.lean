import Proof.CaseAnalysis.CloseoutRowsEstimatorFields
import Proof.CaseAnalysis.RowsEstimatorHeader

/-! Cold row preparation. Raw d, p, parity and the actual cut bytes are
all inputs; both cut-count and byte-count words are physically produced. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Prepare
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fieldSlots : Fin 10→Fin 64:=![0,54,55,56,57,58,59,60,61,62]
def scanSlots : Fin 5→Fin 64:=![52,61,34,53,63]
def input (row : EquationRow.Input) (i : Fin 64):=
  if i=0 then List.replicate row.d true else if i=17 then List.replicate row.p true
  else if i=52 then Header.stream row else if i=54 then [row.odd] else []
noncomputable def middle (row : EquationRow.Input):=install fieldSlots (input row) (Fields.output row.d row.odd)
noncomputable def output (row : EquationRow.Input):=install scanSlots (middle row) (Scan.output row)
noncomputable def first:=RecoveryFocus.machine fieldSlots Fields.machine
noncomputable def last:=RecoveryFocus.machine scanSlots Scan.readyMachine
noncomputable def machine:=Composition.machine first last
def budget (row : EquationRow.Input):=Fields.budget row.d row.odd+1+(2*Scan.ticks row+2)

theorem field_input (row : EquationRow.Input) (j : Fin 10) :
    input row (fieldSlots j)=Fields.input row.d row.odd j:=by
  fin_cases j <;> rfl

theorem scan_input (row : EquationRow.Input) (j : Fin 5) :
    middle row (scanSlots j)=Scan.readyInput row j:=by
  fin_cases j
  · exact (install_other fieldSlots _ _ _ (by decide)).trans (by rfl)
  · exact (install_slot fieldSlots (by decide) _ _ 8).trans (by rfl)
  · exact (install_other fieldSlots _ _ _ (by decide)).trans (by rfl)
  · exact (install_other fieldSlots _ _ _ (by decide)).trans (by rfl)
  · exact (install_other fieldSlots _ _ _ (by decide)).trans (by rfl)

theorem ready (row : EquationRow.Input) :
    ClockJoin.ReadyRun machine (budget row) (input row) (output row):=
  ClockJoin.join _ _ _ _ _ _ _
    ((Fields.ready row.d row.odd).focus fieldSlots (by decide) (input row) (field_input row))
    ((Scan.ready row).focus scanSlots (by decide) (middle row) (scan_input row))

theorem header_input (row : EquationRow.Input) (i : Fin 55) :
    output row (i.castAdd 9)=Header.input row i:=by
  fin_cases i
  all_goals first
    | exact (install_slot scanSlots (by decide) _ _ 0).trans (by rfl)
    | exact (install_slot scanSlots (by decide) _ _ 2).trans (by rfl)
    | exact (install_slot scanSlots (by decide) _ _ 3).trans (by rfl)
    | exact ((install_other scanSlots _ _ _ (by decide)).trans
        (install_slot fieldSlots (by decide) _ _ 0)).trans (by rfl)
    | exact ((install_other scanSlots _ _ _ (by decide)).trans
        (install_slot fieldSlots (by decide) _ _ 1)).trans (by rfl)
    | exact ((install_other scanSlots _ _ _ (by decide)).trans
        (install_other fieldSlots _ _ _ (by decide))).trans (by rfl)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Prepare
