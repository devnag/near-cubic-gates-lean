import Proof.PCP.PCPPNativeClauseQueryLayout
import Proof.PCP.PCPPNativeQueryConjunctionRetained
import Proof.PCP.PCPPNativeOracleScalars

/-! The same original oracle retained by the Q-loop feeds the real footer
scalar program, whose two outputs are the original M-loop's scalar ports. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseOracle
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scalarSlots (i : Fin 27) : Fin 363 :=
  if i=0 then 95 else if i=18 then 1 else if i=22 then 284 else if i=25 then 283 else i.natAdd 336
def clauseSlots (i : Fin 58) : Fin 363 := (PCPPNativeClauseQuery.slots i).castAdd 27
theorem scalar_injective : Function.Injective scalarSlots := by decide
theorem clause_injective : Function.Injective clauseSlots := by
  intro i j h
  apply PCPPNativeClauseQuery.slots_injective
  exact Fin.ext (congrArg (fun i : Fin 363=>i.val) h)
def extra (fields : List Bool) (i : Fin 85) : List Bool := if i=13 then fields else []
def input (old : Fin 278→List Bool) (fields : List Bool) : Fin 363→List Bool :=
  Fin.addCases (m:=278) (n:=85) (motive:=fun _=>List Bool) old (extra fields)
def heads (old : Fin 278→ℕ) : Fin 363→ℕ :=
  Fin.addCases (m:=278) (n:=85) (motive:=fun _=>ℕ) old (fun _=>0)
noncomputable def first := TapeEmbedding.machine 85 PCPPNativeQueryConjunction.machine
noncomputable def second := RecoveryFocus.machine scalarSlots PCPPNativeOracleScalars.machine
noncomputable def last := RecoveryFocus.machine clauseSlots PCPPNativeClauseRawRun.machine
noncomputable def machine := Composition.machine (Composition.machine first second) last

theorem scalar_data (old : Fin 278→List Bool) (fields bits : List Bool) (s : ℕ)
    (ho : old 95=bits) (hs : old 1=List.replicate s true) (i : Fin 27) :
    input old fields (scalarSlots i)=PCPPNativeOracleScalars.input bits s i := by
  fin_cases i
  all_goals first | exact ho | exact hs | rfl

theorem scalar_heads (old : Fin 278→ℕ) (ho : old 95=0) (hs : old 1=0) (i : Fin 27) :
    heads old (scalarSlots i)=0 := by
  fin_cases i
  all_goals first | exact ho | exact hs | rfl

theorem clause_away (i : Fin 58) (hi5 : i≠5) (hi6 : i≠6) : ∀ j,scalarSlots j≠clauseSlots i := by
  fin_cases i
  all_goals first | exact False.elim (hi5 rfl) | exact False.elim (hi6 rfl) | decide

theorem clause_other (old : Fin 278→List Bool) (fields : List Bool) (p n : ℕ)
    (i : Fin 58) (hi5 : i≠5) (hi6 : i≠6) :
    input old fields (clauseSlots i)=PCPPNativeClauseQuery.tapes old fields p n (PCPPNativeClauseQuery.slots i) := by
  fin_cases i
  all_goals first | exact False.elim (hi5 rfl) | exact False.elim (hi6 rfl) | rfl

theorem clause_head (old : Fin 278→ℕ) (i : Fin 58) :
    heads old (clauseSlots i)=PCPPNativeClauseQuery.heads old (PCPPNativeClauseQuery.slots i) := by
  fin_cases i <;> rfl

theorem scalar_away14 : ∀ j,scalarSlots j≠14 := by decide
theorem scalar_away16 : ∀ j,scalarSlots j≠16 := by decide
theorem clause_away14 : ∀ j,clauseSlots j≠14 := by decide
theorem clause_away16 : ∀ j,clauseSlots j≠16 := by decide

end NearCubicWires.RepairOrdinary.PCPPNativeClauseOracle
