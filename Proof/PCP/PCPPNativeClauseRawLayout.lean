import Proof.PCP.PCPPNativeClauseRawRun

/-! Literal tape ABI of the raw-count clause consumer. No prepared padding
or auxiliary count/capacity driver is hidden in its input. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseRawRun
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data (source : List Bool) (stride p n C base accumulator : ℕ) (out : List Bool) (M : ℕ)
    (i : Fin 58) : List Bool :=
  if i=4 then UnaryTemplate.tape stride else if i=5 then List.replicate p true
  else if i=6 then List.replicate n true else if i=13 then source
  else if i=26 then List.replicate base true else if i=27 then List.replicate accumulator true
  else if i=47 then out else if i=52 then List.replicate C true
  else if i=53 then List.replicate M true else []
def heads (pos : ℕ) (out : List Bool) (i : Fin 58) :=
  if i=13 then pos else if i=47 then out.length else 0

theorem input_data (source : List Bool) (pos stride p n C base accumulator : ℕ) (out : List Bool) (M : ℕ) :
    (entry source pos stride p n C base accumulator out M).tapes=data source stride p n C base accumulator out M := by
  funext i
  fin_cases i
  all_goals first | rfl | exact ZeroPadding.pad_zero _ |
    exact (ZeroPadding.pad_zero _).trans (ZeroPadding.pad_zero _)

theorem input_heads (source : List Bool) (pos stride p n C base accumulator : ℕ) (out : List Bool) (M : ℕ) :
    (entry source pos stride p n C base accumulator out M).heads=heads pos out := by
  funext i
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.PCPPNativeClauseRawRun
