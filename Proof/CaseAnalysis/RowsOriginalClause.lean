import Proof.CaseAnalysis.RowsOriginalPairClean
import Proof.CaseAnalysis.RowsOriginalTemplates
import Proof.PCP.PCPPQueryIndexPadding

/-! The source's SAME cached PCPP clause query feeds the actual signed-pair
parser. No original proof-coordinate stream is supplied separately. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound RepairRepresentation SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def index {n : ℕ} (l : Literal n):=(ComponentwiseBranchExtraction.literalIndex l).val
def negative {n : ℕ} (l : Literal n):=ComponentwiseBranchExtraction.literalNegated l

theorem literal_code {n : ℕ} (l : Literal n) : literalIndex l=2*index l+(negative l).toNat := by
  cases l <;> simp [literalIndex,index,negative,ComponentwiseBranchExtraction.literalIndex,
    ComponentwiseBranchExtraction.literalNegated]

def slots (i : Fin 28) : Fin 46:=if i=0 then 15 else ⟨i.val+18,by omega⟩
theorem injective : Function.Injective slots := by
  intro i j h
  have hv:=congrArg Fin.val h
  simp only [slots] at hv
  split_ifs at hv <;>apply Fin.ext <;>simp_all only [Fin.ext_iff] <;>omega
def extra (C : ℕ) (j : Fin 27):=CloseoutRowsOriginalPair.cleanInput C [] j.succ
def heads : Fin 46→ℕ:=Fin.addCases (m:=19) (n:=27) (motive:=fun _=>ℕ) PCPPQueryClauseReuse.heads (fun _=>0)
def data (C : ℕ) (A : Fin 19→List Bool) : Fin 46→List Bool:=
  Fin.addCases (m:=19) (n:=27) (motive:=fun _=>List Bool) A (extra C)
noncomputable def query:=TapeEmbedding.machine 27 PCPPQueryClauseReuse.machine
noncomputable def parse:=RecoveryFocus.machine slots CloseoutRowsOriginalPair.clean
noncomputable def machine:=Composition.machine query parse

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (i : Fin (2^(a.output r).clauseBits)) (C : ℕ)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses i).left)
      (index ((a.output r).clauses i).right) (negative ((a.output r).clauses i).left)
      (negative ((a.output r).clauses i).right)+1≤C) :
    let Q:=PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)
    let p:=((a.output r).clauses i)
    let A:=PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity i.val Q
      (natListWord [literalIndex p.left,literalIndex p.right])
    ∃ out,Step machine (PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity)+1+
      CloseoutRowsOriginalPair.cleanBudget (index p.left) (index p.right) C (negative p.left) (negative p.right))
      heads (data C (PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity i.val Q [])) heads out ∧
      (∀ j,out (j.castAdd 27)=A j) ∧
      out 29=ZeroPadding.pad C (List.replicate (index p.left) true) ∧
      out 30=ZeroPadding.pad C [negative p.left] ∧
      out 41=ZeroPadding.pad C (List.replicate (index p.right) true) ∧
      out 42=ZeroPadding.pad C [negative p.right] ∧ out 44=List.replicate C true := by
  dsimp only
  let Q:=PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)
  let p:=((a.output r).clauses i)
  let A:=PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity i.val Q
    (natListWord [literalIndex p.left,literalIndex p.right])
  have packet : natListWord [literalIndex p.left,literalIndex p.right]=
      CloseoutRowsOriginalPair.word (index p.left) (index p.right) (negative p.left) (negative p.right) := by
    rw [literal_code p.left,literal_code p.right];rfl
  obtain ⟨base,hbase,bt,bh,_⟩:=PCPPQueryIndexPadding.clause_run a r i
  rw [PCPPQueryIndexPadding.clause_entry] at hbase
  have first:=(Step.of_run hbase bh bt).embed (fun _ : Fin 27=>0) (extra C)
  have raw:=CloseoutRowsOriginalPair.clean_run (index p.left) (index p.right) C (negative p.left) (negative p.right) hc
  have padded:=raw.pad (fun j=>if j=0 then Q else 0)
  have last:=padded.dock slots injective heads (data C A) (by intro j;fin_cases j <;>rfl) (by
    intro j;fin_cases j
    · change ZeroPadding.pad Q (natListWord [literalIndex p.left,literalIndex p.right])=_
      rw [packet];rfl
    all_goals exact (ZeroPadding.pad_zero _).symm)
  have hh : dockH slots heads (fun _=>0)=heads := by
    apply dockH_existing
    intro j;fin_cases j <;>rfl
  have whole:=first.seq (last.congr hh rfl)
  refine ⟨_,whole,?_,?_,?_,?_,?_,?_⟩
  · intro j
    by_cases h15 : j=15
    · subst j
      exact (install_slot slots injective _ _ 0).trans (by
        change ZeroPadding.pad Q (CloseoutRowsOriginalPair.word _ _ _ _)=_
        rw [←packet];rfl)
    · rw [install_other slots _ _ _ (by
        intro k he
        have hv:=congrArg Fin.val he
        have bound:=j.isLt
        have neq : j.val≠15:=fun h=>h15 (Fin.ext h)
        by_cases hk : k=0
        · subst k;change 15=j.val at hv;omega
        · have kp : k.val≠0:=fun h=>hk (Fin.ext h)
          simp only [slots,hk,↓reduceIte,Fin.val_mk,Fin.val_castAdd] at hv;omega)]
      exact Fin.addCases_left j
  all_goals first
  | exact (install_slot slots injective _ _ 11).trans (ZeroPadding.pad_zero _)
  | exact (install_slot slots injective _ _ 12).trans (ZeroPadding.pad_zero _)
  | exact (install_slot slots injective _ _ 23).trans (ZeroPadding.pad_zero _)
  | exact (install_slot slots injective _ _ 24).trans (ZeroPadding.pad_zero _)
  | exact (install_slot slots injective _ _ 26).trans (ZeroPadding.pad_zero _)

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause
