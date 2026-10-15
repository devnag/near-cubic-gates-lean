import Proof.MachineModel.TopDownWorkspaceSelectedEntryFacts
import Proof.CaseAnalysis.FinalAdmittedEntry

/-! Highest grouped source-header count and append initialization, reused
unchanged from the existing admitted entry. Its fixed local bank can be docked
without including the prologue's nonzero-head clause-envelope counter. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedEntryCount
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary SourceInterfaces RepairRepresentation
open RecoveryRootRound RepairSource.VerifierDecoding
open private NearCubicWires.RepairOrdinary.CloseoutFinalC10AdmittedEntry.count_append from Proof.CaseAnalysis.FinalAdmittedEntry
noncomputable section

def cache (i : Fin 19) : Fin 116 := i.castAdd 97

def count (i : Fin 74) : Fin 116 := ⟨if i.val<19 then i.val else i.val+1,by have:=i.isLt;split_ifs <;>omega⟩

def append (i : Fin 42) : Fin 116 := ⟨if i.val=0 then 19 else 74+i.val,by have:=i.isLt;split_ifs <;>omega⟩

def input (A : Fin 19→List Bool) (b : Nat) (i : Fin 116) : List Bool :=
  if h:i.val<19 then A ⟨i.val,h⟩ else if i.val=19 then List.replicate b true else []

theorem count_injective : Function.Injective count := by
  intro i j he
  have hv:=congrArg Fin.val he
  dsimp only [count] at hv
  split_ifs at hv <;>apply Fin.ext <;>omega

theorem append_injective : Function.Injective append := by
  intro i j he
  have hv:=congrArg Fin.val he
  dsimp only [append] at hv
  split_ifs at hv <;>apply Fin.ext <;>omega

theorem count_append_disjoint (i : Fin 74) (j : Fin 42) : count i≠append j := by
  intro he
  have hv:=congrArg Fin.val he
  have hi:=i.isLt
  have hj:=j.isLt
  dsimp only [count,append] at hv
  split_ifs at hv <;>omega

def machine := Composition.machine
  (DecompositionCountPosition.move (fun i : Fin 116=>if i=cache 13 ∨ i=cache 14 then .right else .stay))
  (Composition.machine (RecoveryFocus.machine count CloseoutRowsOriginalCount.machine)
    (Composition.machine
      (DecompositionCountPosition.move (fun i : Fin 116=>if i=cache 13 ∨ i=cache 14 then .left else .stay))
      (RecoveryFocus.machine append CloseoutFinalC10AppendWorkspaceInit.machine)))

def cacheData (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) : Fin 19→List Bool :=
  PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
    (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) []

def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (b : Nat) : Nat :=
  CloseoutRowsOriginalCount.budget r (a.output r)+CloseoutFinalC10AppendWorkspaceInit.budget b+5

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (b : Nat) :
    ∃ A,Step machine (budget a r b) (fun _=>0) (input (cacheData a r) b) (fun _=>0) A ∧
      (∀j,A (cache j)=cacheData a r j) ∧
      A (count 28)=UnaryTemplate.tape (a.output r).systematicBits ∧
      A (count 70)=UnaryTemplate.tape (2^(a.output r).clauseBits) ∧
      A (count 72)=List.replicate (2^(a.output r).clauseBits) true ∧
      A (append 0)=List.replicate b true ∧
      A (append 20)=UnaryTemplate.tape (20*b+22) ∧
      A (append 39)=List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false ∧
      A (append 40)=List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false ∧
      (∀v,(∀i,count i≠v) → (∀i,append i≠v) → A v=input (cacheData a r) b v) := by
  have first : ∀j:Fin 19,count (j.castAdd 55)=cache j := by
    intro j
    apply Fin.ext
    simp only [count,Fin.val_castAdd,if_pos j.isLt,cache]
  apply NearCubicWires.RepairOrdinary.CloseoutFinalC10AdmittedEntry.count_append
    116 cache count append (cacheData a r) (2^(a.output r).clauseBits) (a.output r).systematicBits
    b (CloseoutRowsOriginalCount.budget r (a.output r)) (input (cacheData a r) b)
    count_injective first append_injective count_append_disjoint
  · exact CloseoutRowsOriginalCount.run_with_systematic r (a.output r) PCPPQueryClauseReuse.heads
      (cacheData a r) rfl rfl rfl rfl
  · intro j
    simp only [input,cache,Fin.val_castAdd,dif_pos j.isLt]
  · intro j
    have hj:=j.isLt
    simp only [input,count,Fin.val_natAdd,show ¬19+j.val<19 by omega,if_false]
    rw [dif_neg (by omega),if_neg (by omega)]
  · intro j
    by_cases hj:j.val=0
    · simp [input,append,hj,CloseoutFinalC10AppendWorkspaceInit.input]
    · simp only [append,hj,if_false,input]
      rw [dif_neg (by omega),if_neg (by omega)]
      simp only [CloseoutFinalC10AppendWorkspaceInit.input,hj,if_false]

end
end NearCubicWires.P1TopDown.WorkspaceSelectedEntryCount
