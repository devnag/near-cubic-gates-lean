import Proof.CaseAnalysis.RowsOriginalWriter

/-! A complete fixed template is written into the ordinary factor-loop
input buffer, then its append cursor returns with a paid log. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalWriter
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def readyMachine (factors : List (Fin 2)):=MaskedReset.machine (machine factors) (fun i=>decide (i=2))
def readyData (C : ℕ) (indices : Fin 2→ℕ) (word : List Bool) : Fin 5→List Bool:=
  Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool)
    (fun i=>if i=2 then ZeroPadding.pad C word else data C indices word i) (fun _=>List.replicate C false)

theorem ready_run (C B : ℕ) (indices : Fin 2→ℕ) (factors : List (Fin 2))
    (hb : ∀ side,indices side≤B) (hl : factors.length≤4) (hc : 8*B+37≤C) :
    Step (readyMachine factors) (2*budget indices factors+2) (fun _=>0) (readyData C indices [])
      (fun _=>0) (readyData C indices (indicesWord indices factors)) := by
  have raw:=run C indices factors [] (by intro side;have h:=hb side;omega)
  have padded:=raw.pad (fun i=>if i=2 then C else 0)
  have reset:=padded.mask (cap:=C) (fun i=>decide (i=2)) (by
    intro i hi
    have he : i=2:=of_decide_eq_true hi
    subst i;rfl) ((budget_bound indices factors B hb hl).trans hc)
  apply (reset.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i
  all_goals simp [readyData,heads,data,Fin.addCases,ZeroPadding.pad_zero]

theorem ready_budget (C B : ℕ) (indices : Fin 2→ℕ) (factors : List (Fin 2))
    (hb : ∀ side,indices side≤B) (hl : factors.length≤4) (hc : 8*B+37≤C) :
    Step (readyMachine factors) (16*B+76) (fun _=>0) (readyData C indices [])
      (fun _=>0) (readyData C indices (indicesWord indices factors)) := by
  have h:=budget_bound indices factors B hb hl
  exact (ready_run C B indices factors hb hl hc).enlarge (by omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalWriter
