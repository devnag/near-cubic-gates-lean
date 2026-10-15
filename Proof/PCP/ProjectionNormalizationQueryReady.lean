import Proof.PCP.ProjectionNormalizationDrivers

/-! The complete padded query stream with one output-only rewind. All
physical dimension drivers and the retained source cursor survive. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.QueryReady
open SourceInterfaces ExecutableInterfaces LocalBitMultitape RepairOrdinary VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacities (padding : ℕ) : Fin 6 → ℕ := fun i => if i=3 then padding+2 else 0
def selected (i : Fin 6) : Bool := decide (i=1)
noncomputable def machine := MaskedReset.machine Queries.machine selected
noncomputable def entry (p : RawProjectionPCP) (R Q : ℕ) :=
  Rewind.recording (ZeroPadding.config (capacities (R-p.width))
    (Queries.cfg Queries.machine.start p.word (QueryBytes.header p).length []
      p.width (R-p.width) p.queries ((Q-p.queries)*R))) 0
def sourcePos (p : RawProjectionPCP) :=
  (QueryBytes.header p).length+(Rows.stream (QueryBytes.rowsBits (queryRows p))).length
def output (p : RawProjectionPCP) (R Q : ℕ) := QueryBytes.framedCodes (normalizedRows p R Q).flatten
def budget (p : RawProjectionPCP) (R Q : ℕ) := 2*QueryBytes.budget p R Q+2

theorem query_run (p : RawProjectionPCP) (R Q : ℕ) :
    ∃ r,runFrom machine (budget p R Q) (entry p R Q)=some r ∧ r.steps ≤ budget p R Q ∧
      r.final.tapes 0=p.word ∧ r.final.tapes 1=output p R Q ∧
      (∀ i,r.final.heads i=if i=0 then sourcePos p else if i=2 ∨ i=3 ∨ i=4 ∨ i=5 then 1 else 0) := by
  obtain ⟨base,hb,hbf,hbs⟩ := QueryBytes.query_run p R Q []
  obtain ⟨a,ha,haf,hat,_⟩ := ZeroPadding.run_config Queries.machine (capacities (R-p.width)) _ _ base hb
  have hhead : ∀ i,selected i=true → a.final.heads i ≤ a.steps := by
    intro i hi
    have he : i=1 := by simpa only [selected,decide_eq_true_eq] using hi
    subst i
    have h := SelectiveReset.prefix_head (prefix_of_run Queries.machine _ _ a ha).1 1
    simpa [ZeroPadding.config,Queries.cfg] using h
  obtain ⟨r,hr,hf,hs,_⟩ := MaskedReset.reset_run Queries.machine selected _ _ a ha hhead
  have bound : 2*a.steps+2 ≤ budget p R Q := by dsimp only [budget]; omega
  have hm := runFrom_moreFuel machine _ (budget p R Q-(2*a.steps+2)) _ r hr
  rw [Nat.add_sub_of_le bound] at hm
  refine ⟨r,hm,hs.le.trans bound,?_,?_,?_⟩
  · rw [hf,haf,hbf]
    simp [SelectiveReset.finished,Rewind.config,ZeroPadding.config,capacities,Queries.cfg,Fin.addCases]
  · rw [hf,haf,hbf]
    simp [SelectiveReset.finished,Rewind.config,ZeroPadding.config,capacities,Queries.cfg,Fin.addCases,output]
  · intro i
    rw [hf,haf,hbf]
    fin_cases i <;>
      simp [SelectiveReset.finished,Rewind.config,selected,ZeroPadding.config,Queries.cfg,sourcePos,Fin.addCases]

end NearCubicWires.RepairSource.ProjectionNormalization.QueryReady
