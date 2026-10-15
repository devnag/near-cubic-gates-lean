import Proof.CaseAnalysis.RowsIntegerStorage

/-! A tape-only projection of the checked integer entry keeps subsequent
physical joins independent of its large control-state expression. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerReady
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (w : ℕ) (bits out : List Bool) (i : Fin 215):=
  if i=213 then out else if i=0 then ZeroPadding.pad (capacity w) (frame bits)
    else List.replicate (capacity w) false

theorem entry_tapes (w : ℕ) (bits out : List Bool) (i : Fin 215) :
    (entry w bits out).tapes i=tapes w bits out i:=by
  by_cases h213:i=213
  · subst i
    exact entry_output w bits out
  by_cases h0:i=0
  · subst i
    exact entry_source w bits out
  have h: (entry w bits out).tapes i=List.replicate (capacity w) false:=
    (entry_bits_other w bits [] out i h0).trans (entry_blank w out i h213)
  exact h.trans (by simp only [tapes,if_neg h213,if_neg h0])

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerReady
