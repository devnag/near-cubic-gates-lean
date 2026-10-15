import Proof.CaseAnalysis.RowsRawProductRow

/-! After a product row the left stream advances once. This is the
source-only projection of the checked monomial copier, with the identical
finite control and instruction count and no discarded output buffer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawMonomialSkip
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 1 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q bits=>if q=0 then some ⟨if bits 0 then 1 else 2,fun _=>none,fun _=>.right⟩
    else if q=1 then some ⟨if bits 0 then 1 else 0,fun _=>none,fun _=>.right⟩ else none
def project (c : Configuration 2 3) : Configuration 1 3:=
  ⟨c.control,fun _=>c.heads 0,fun _=>c.tapes 0⟩

theorem step_project (c d : Configuration 2 3)
    (hs : step CloseoutRowsRawMonomialCopy.machine c=some d) :
    step machine (project c)=some (project d) := by
  rcases c with ⟨q,H,A⟩
  fin_cases q
  all_goals cases hread:readTapeBit (A 0) (H 0)
  all_goals simp [step,CloseoutRowsRawMonomialCopy.machine,Configuration.scanned,hread] at hs
  all_goals subst d
  all_goals
    simp [step,machine,project,Configuration.scanned,hread]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i;simp [applyAction,HeadMove.apply]
    · funext i;fin_cases i;rfl

theorem cells (c : Configuration 2 3) : (project c).tapeCells≤c.tapeCells := by
  simp [Configuration.tapeCells,project,Fin.sum_univ_two]

theorem prefix_project {space n : ℕ} {c d : Configuration 2 3}
    (h : Prefix CloseoutRowsRawMonomialCopy.machine space n c d) :
    Prefix machine space n (project c) (project d) := by
  induction h with
  | refl c hc=>exact Prefix.refl _ ((cells c).trans hc)
  | step hc hn hs _ ih=>
    exact Prefix.step ((cells _).trans hc) hn (step_project _ _ hs) ih

theorem skip_run (m : List ℕ) (pre tail : List Bool) :
    Step machine ((m.flatMap ExtIncidence.block).length+1)
      (fun _=>pre.length) (fun _=>pre++m.flatMap ExtIncidence.block++false::tail)
      (fun _=>pre.length+(m.flatMap ExtIncidence.block).length+1)
      (fun _=>pre++m.flatMap ExtIncidence.block++false::tail) := by
  obtain ⟨raw,hr,rf,rs⟩:=CloseoutRowsRawMonomialCopy.copy_run m pre tail []
  obtain ⟨hp,_hh⟩:=prefix_of_run CloseoutRowsRawMonomialCopy.machine _ _ raw hr
  have trace:=prefix_project hp
  rw [rf] at trace
  have bound:=SortMatrix.final_cells hp
  rw [rf] at bound
  obtain ⟨r,rr,rfinal,_⟩:=trace.run (by rfl) ((cells _).trans bound)
  rw [rs] at rr
  exact Step.of_run rr (congrArg Configuration.heads rfinal) (congrArg Configuration.tapes rfinal)

end NearCubicWires.RepairOrdinary.CloseoutRowsRawMonomialSkip
