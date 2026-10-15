import Proof.Hierarchy.CompetitorCrossTableBounds
import Proof.MachineModel.OrdinaryMatrixScorePower

/-! Cold request headers and the actual U=2^d producer at reusable endpoints.
Only the existing header and power machines execute, each with its paid reset. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossRequestHeaders
open LocalBitMultitape RecoveryRootRound SignedSortKey RepairRepresentation
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The request word after `d` and `p`: the gate count, the weight count, the columns of `φ`, the cuts
(`MatrixScoreBatch.header`). -/
def suffix (r : Request) :=
  natWord r.Gates++natWord r.width++MatrixScorePhi.columnsWord r.width r.cols++r.cuts.flatMap (MatrixScoreBatch.cutWord r.p)
def input (r : Request) : Fin 24 → List Bool :=
  Fin.addCases (m := 23) (n := 1) (motive := fun _ => List Bool)
    (MatrixScoreHeaders.input (MatrixScoreBatch.word r)) (fun _ => [])
noncomputable def machine := Rewind.machine MatrixScoreHeaders.machine
def budget (r : Request) := 2*MatrixScoreHeaders.budget r.d r.p (suffix r)+2

theorem headers_run (r : Request) : ∃ out,ClockJoin.ReadyRun machine (budget r) (input r) out ∧
    out 0=MatrixScoreBatch.physicalInput r ∧ out 12=UnaryTemplate.tape r.d ∧
    out 22=UnaryTemplate.tape r.p := by
  obtain ⟨base,hb,h0,_,_,_,_,_,_,_,hd,_,_,_,_,_,hp,_,hs⟩ := MatrixScoreHeaders.headers_run r.d r.p (suffix r)
  have he : natWord r.d++natWord r.p++suffix r=MatrixScoreBatch.word r := by
    simp [suffix,MatrixScoreBatch.word,MatrixScoreBatch.header,List.append_assoc]
  rw [he] at hb h0
  obtain ⟨actual,ha,ht,hh,has,_⟩ := Rewind.reset_run MatrixScoreHeaders.machine _ _ base hb
  have hbound : 2*base.steps+2 ≤ budget r := by unfold budget;omega
  have hmore := run_moreFuel machine (2*base.steps+2) (budget r-(2*base.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le hbound] at hmore
  refine ⟨actual.final.tapes,⟨actual,hmore,rfl,hh,has.le.trans hbound⟩,?_,?_,?_⟩
  · exact (ht 0).trans h0
  · exact (ht 12).trans hd
  · exact (ht 22).trans hp

noncomputable def powerMachine := Rewind.machine MatrixScorePower.machine
def powerInput (d : ℕ) : Fin 15 → List Bool :=
  Fin.addCases (m := 14) (n := 1) (motive := fun _ => List Bool) (MatrixScorePower.input d) (fun _ => [])
def powerBudget (d : ℕ) := 2*MatrixScorePower.budget d+2

theorem power_run (d : ℕ) : ∃ out,ClockJoin.ReadyRun powerMachine (powerBudget d) (powerInput d) out ∧
    out 0=List.replicate d true ∧ out 2=List.replicate (d+3) true ∧ out 13=UnaryTemplate.tape (2^d) := by
  obtain ⟨base,hb,h0,h2,_,h13,_,_,hs⟩ := MatrixScorePower.power_run d
  obtain ⟨actual,ha,ht,hh,has,_⟩ := Rewind.reset_run MatrixScorePower.machine _ _ base hb
  have hbound : 2*base.steps+2 ≤ powerBudget d := by unfold powerBudget;omega
  have hmore := run_moreFuel powerMachine (2*base.steps+2) (powerBudget d-(2*base.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le hbound] at hmore
  exact ⟨actual.final.tapes,⟨actual,hmore,rfl,hh,has.le.trans hbound⟩,(ht 0).trans h0,(ht 2).trans h2,(ht 13).trans h13⟩

end NearCubicWires.RepairOrdinary.CompetitorCrossRequestHeaders
