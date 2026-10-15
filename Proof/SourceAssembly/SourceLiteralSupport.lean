import Proof.SourceAssembly.SourceLiteralRefs
import Proof.CaseAnalysis.RowsSupportCircuitJoin

/- Actual reference templates alias the support reader index. Clause index14 and
queried pair15 are untouched; the two support results use cleared cache3/4. -/
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyLiteralSupport
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound
noncomputable section
attribute [local irreducible] PCPPQuerySupportReuse.machine
abbrev H := SourceAssemblyLiteralRefs.heads

def refPort (side : Bool) : Fin 91 := if side then 87 else 83
def flagPort (side : Bool) : Fin 91 := if side then 89 else 85
def outPort (side : Bool) : Fin 91 := if side then 4 else 3
def slots (side : Bool) : Fin 9→Fin 91 := ![0,1,2,13,outPort side,refPort side,16,17,18]
theorem injective (side : Bool) : Function.Injective (slots side) := by cases side <;>decide
def move (side : Bool) (right : Bool) := DecompositionCountPosition.move
  (fun i : Fin 91=>if i=refPort side then (if right then .right else .left) else .stay)
def middleH (side : Bool) (i : Fin 91) := if i=refPort side then 1 else H i
def reader (side : Bool) := RecoveryFocus.machine (slots side) PCPPQuerySupportReuse.machine
def readMachine (side : Bool) := Composition.machine (move side true)
  (Composition.machine (reader side) (move side false))
def caps (C : Nat) (i : Fin 9) := if i=5 then C else 0
def words (source : List Bool) (q k Q C : Nat) (bits : List Bool) (i : Fin 9) :=
  ZeroPadding.pad (caps C i) (PCPPQuerySupportReuse.data source q k Q bits i)
def result (side : Bool) (Q : Nat) (bits : List Bool) (A : Fin 91→List Bool) :=
  fun i=>if i=outPort side then ZeroPadding.pad Q bits else A i

theorem install_words (side : Bool) (source : List Bool) (q k Q C : Nat) (bits : List Bool)
    (A : Fin 91→List Bool) (hA : ∀ i,A (slots side i)=words source q k Q C [] i) :
    install (slots side) A (words source q k Q C bits)=result side Q bits A := by
  apply HierarchyWidth.install_eq (slots side) (injective side)
  · intro i
    by_cases hi : i=4
    · subst i
      cases side <;>simp [result,slots,outPort,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero]
    · have ne : slots side i≠outPort side := by
        intro he
        have h : slots side i=slots side 4 := he
        exact hi (injective side h)
      simp only [result,ne,if_false]
      rw [hA i]
      unfold words
      congr 1
      fin_cases i <;>first | rfl | exact False.elim (hi rfl)
  · intro i hi
    have ne : i≠outPort side := by intro he;exact hi 4 (by simp [slots,he])
    simp [result,ne]

theorem move_right (side : Bool) (A : Fin 91→List Bool) :
    Step (move side true) 1 H A (middleH side) A := by
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run
    (fun i : Fin 91=>if i=refPort side then .right else .stay) H A
  apply Step.of_run hr
  · rw [hf];funext i;cases side <;>fin_cases i <;>rfl
  · rw [hf]
theorem move_left (side : Bool) (A : Fin 91→List Bool) :
    Step (move side false) 1 (middleH side) A H A := by
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run
    (fun i : Fin 91=>if i=refPort side then .left else .stay) (middleH side) A
  apply Step.of_run hr
  · rw [hf];funext i;cases side <;>fin_cases i <;>rfl
  · rw [hf]

theorem read_run (side : Bool) (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (k : Fin (a.output r).systematicBits) (C : Nat) (A : Fin 91→List Bool)
    (hA : ∀ i,A (slots side i)=words (pcppOutput r (a.output r)) r.arity k.val
      (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) C [] i) :
    Step (readMachine side) (PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity)+4)
      H A H (result side (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity))
        (PCPPQuerySupport.mask r (a.output r) k) A) := by
  let Q:=PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)
  let bits:=PCPPQuerySupport.mask r (a.output r) k
  obtain ⟨raw,hr,rt,rh,_⟩:=PCPPQueryCachedBounds.support_run a r k
  rw [PCPPQuerySupportReuse.entry_literal] at hr
  have padded:=(Step.of_run hr rh rt).pad (caps C)
  have selected : ∀ i,middleH side (slots side i)=PCPPQuerySupportReuse.heads i := by
    intro i;cases side <;>fin_cases i <;>rfl
  have docked:=padded.dock (slots side) (injective side) (middleH side) A selected hA
  have finalH : dockH (slots side) (middleH side) PCPPQuerySupportReuse.heads=middleH side :=
    dockH_existing _ _ _ selected
  have finalA := install_words side (pcppOutput r (a.output r)) r.arity k.val Q C bits A hA
  have last:=(docked.congr finalH finalA).seq (move_left side _)
  have all:=(move_right side A).seq last
  have ht : 1+1+(PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity)+1+1)=
      PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity)+4 := by omega
  rw [ht] at all
  exact all

end
end SourceAssemblyLiteralSupport
