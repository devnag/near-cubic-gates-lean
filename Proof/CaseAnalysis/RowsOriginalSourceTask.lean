import Proof.CaseAnalysis.RowsOriginalTask
import Proof.CaseAnalysis.RowsOriginalDock

/-! One ordinary source-backed action reads the original clause and
executes its selected fixed template, producing exact original-term tuples. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSourceTask
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SourceInterfaces RepairRepresentation
open CloseoutRowsOriginalClause CloseoutRowsOriginalMonomial
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def indices {n : ℕ} (p : TwoLiteralClause n) : Fin 2→ℕ:=![index p.left,index p.right]
def control {n : ℕ} (S : ℕ) (p : TwoLiteralClause n) : Fin 4→Bool:=
  ![negative p.left,negative p.right,decide (S ≤ index p.left),decide (S ≤ index p.right)]
noncomputable def machine (t : CloseoutRowsOriginalTask.Task):=Composition.machine
  (TapeEmbedding.machine 16 CloseoutRowsOriginalSource.machine)
  (RecoveryFocus.machine CloseoutRowsOriginalDock.slots (CloseoutRowsOriginalTask.machine t))
def sourceCost (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (i : Fin (2^(a.output r).clauseBits)) (P : ℕ):=
  let p:=((a.output r).clauses i)
  let S:=(a.output r).systematicBits
  PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity)+1+
    CloseoutRowsOriginalPair.cleanBudget (index p.left) (index p.right) P (negative p.left) (negative p.right)+1+
    (CloseoutCaseTwo.Metadata.budget r (a.output r)+1+
      CloseoutCaseTwo.VariablePrep.budget (index p.left) S+1+CloseoutCaseTwo.VariablePrep.budget (index p.right) S)

theorem run (t : CloseoutRowsOriginalTask.Task) (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (i : Fin (2^(a.output r).clauseBits)) (cs : List (List (List ℕ))) (P B W : ℕ)
    (hB : 1≤B) (count : ∀ p∈cs,p.length≤B) (width : ∀ p∈cs,(ExtIncidence.stream p).length≤W)
    (hi : ∀ side,indices ((a.output r).clauses i) side<cs.length)
    (hp : rowC cs B W≤P)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses i).left)
      (index ((a.output r).clauses i).right) (negative ((a.output r).clauses i).left)
      (negative ((a.output r).clauses i).right)+1≤P) :
    let Q:=PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)
    let p:=((a.output r).clauses i)
    let bits:=control (a.output r).systematicBits p
    let row:=CloseoutRowsOriginalTask.row t bits
    ∃ out,Step (machine t) (sourceCost a r i P+1+(CloseoutRowsOriginalBranches.cost cs B W+4))
      CloseoutRowsOriginalDock.heads
      (CloseoutRowsOriginalDock.data (rowC cs B W) cs
        (CloseoutRowsOriginalClassify.data P (CloseoutRowsOriginalClause.data P
          (PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity i.val Q []))))
      (dockH CloseoutRowsOriginalDock.slots CloseoutRowsOriginalDock.heads
        (CloseoutRowsOriginalBranches.outHeads row (indices p))) out ∧
      out 94=ZeroPadding.pad (rowC cs B W)
        (ExtIncidence.stream (value cs (row.factors.map (indices p)) (CloseoutRowsOriginalBranches.valid cs (indices p) hi row) [[]])) ∧
      out 103=ZeroPadding.pad (rowC cs B W) (CloseoutRowsOriginalMetadata.rho row) ∧
      out 104=ZeroPadding.pad (rowC cs B W) (CloseoutRowsOriginalMetadata.count row) ∧
      out 105=ZeroPadding.pad (rowC cs B W) (CloseoutRowsOriginalMetadata.parity row) ∧
      (∀ j : Fin 19,out (j.castAdd 88)=PCPPQueryIndexPadding.clauseData
        (pcppOutput r (a.output r)) r.arity i.val Q
        (natListWord [literalIndex p.left,literalIndex p.right]) j) ∧
      out 44=List.replicate P true ∧ out 92=CloseoutRowsRawAtomSeek.cacheWord cs := by
  dsimp only
  obtain ⟨A,ha,cache,il,sl,ir,sr,_sys,_li,la,_ri,ra,driver⟩:=CloseoutRowsOriginalSource.run a r i P hc
  let idx:=indices ((a.output r).clauses i)
  let bits:=control (a.output r).systematicBits ((a.output r).clauses i)
  have fields : ∀ j,A (CloseoutRowsOriginalDock.sourceSlots j)=CloseoutRowsOriginalDock.sourceWords P idx bits j := by
    intro j;fin_cases j
    · exact il
    · exact ir
    · exact sl
    · exact sr
    · exact la
    · exact ra
  have first:=ha.embed (fun _ : Fin 16=>0) (CloseoutRowsOriginalDock.extra (rowC cs B W) cs)
  have raw:=CloseoutRowsOriginalTask.run t cs idx bits B W hB count width hi
  have last:=CloseoutRowsOriginalDock.run (CloseoutRowsOriginalTask.machine t) (rowC cs B W) P cs idx bits A _ _ raw hp fields
  refine ⟨_,first.seq last,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (install_slot CloseoutRowsOriginalDock.slots CloseoutRowsOriginalDock.injective _ _ 3).trans (ZeroPadding.pad_zero _)
  · exact (install_slot CloseoutRowsOriginalDock.slots CloseoutRowsOriginalDock.injective _ _ 14).trans (ZeroPadding.pad_zero _)
  · exact (install_slot CloseoutRowsOriginalDock.slots CloseoutRowsOriginalDock.injective _ _ 15).trans (ZeroPadding.pad_zero _)
  · exact (install_slot CloseoutRowsOriginalDock.slots CloseoutRowsOriginalDock.injective _ _ 16).trans (ZeroPadding.pad_zero _)
  · intro j
    rw [install_other CloseoutRowsOriginalDock.slots _ _ _ (by
      intro k he
      have hv:=congrArg Fin.val he
      have hk : 19≤(CloseoutRowsOriginalDock.slots k).val:=by fin_cases k <;>decide
      have hj:=j.isLt
      simp only [Fin.val_castAdd] at hv;omega)]
    exact (Fin.addCases_left (j.castAdd 72)).trans (cache j)
  · rw [install_other CloseoutRowsOriginalDock.slots _ _ _ (by decide)]
    exact (Fin.addCases_left (44 : Fin 91)).trans driver
  · exact (install_slot CloseoutRowsOriginalDock.slots CloseoutRowsOriginalDock.injective _ _ 1).trans (ZeroPadding.pad_zero _)

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSourceTask
