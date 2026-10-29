import Proof.SourceAssembly.SourceLiteralSupport

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyLiteralSupport
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound
noncomputable section
attribute [local irreducible] PCPPQuerySupportReuse.machine

def idle : Machine 91 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def test (side : Bool) (bs : Fin 91→Bool) := !(bs (flagPort side))
def machine (side : Bool) := CloseoutRowsGateColdPair.machine idle (readMachine side) (test side)
def value (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (k : Nat) :=
  if hk : k < (a.output r).systematicBits then PCPPQuerySupport.mask r (a.output r) ⟨k,hk⟩ else []
theorem idle_run (A : Fin 91→List Bool) : Step idle 0 H A H A := by
  exact Step.of_run (rfl : runFrom idle 0 ⟨0,H,A⟩=some ⟨⟨0,H,A⟩,0,(⟨0,H,A⟩ : Configuration 91 1).tapeCells⟩) rfl rfl

theorem cases_run {t u v : Nat} (p : Machine t u) (q : Machine t v)
    (f : Nat) (H : Fin t→Nat) (A B : Fin t→List Bool)
    (P : Prop) [Decidable P] (F : P→Fin t→List Bool)
    (test : (Fin t→Bool)→Bool)
    (hp : Step p 0 H A H A)
    (hq : ∀ h : P,Step q f H A H (F h))
    (ht : test (fun i=>readTapeBit (A i) (H i))=decide P)
    (hy : ∀ h : P,F h=B) (hn : ¬P→A=B) :
    Step (CloseoutRowsGateColdPair.machine p q test) (f+2) H A H B := by
  by_cases h : P
  · exact ((CloseoutRowsSupportStream.guarded_step hp (hq h) test (by rw [ht];simp [h])).enlarge
      (by omega)).congr rfl (hy h)
  · exact ((CloseoutRowsSupportStream.rejected_step q hp test (by rw [ht];simp [h])).enlarge
      (by omega)).congr rfl (hn h)

theorem observed (side : Bool) (S k C : Nat) (A : Fin 91→List Bool)
    (hflag : A (flagPort side)=ZeroPadding.pad C [decide (S ≤ k)]) :
    test side (fun i=>readTapeBit (A i) (H i))=decide (k < S) := by
  change (!(readTapeBit (A (flagPort side)) (H (flagPort side))))=_
  have hz : H (flagPort side)=0 := by cases side <;>rfl
  rw [hz,hflag,ZeroPadding.read_pad]
  by_cases hk : k < S
  · simp [readTapeBit,hk,Nat.not_le.mpr hk]
  · simp [readTapeBit,hk,Nat.le_of_not_gt hk]

theorem empty_result (side : Bool) (source : List Bool) (q k Q C : Nat) (A : Fin 91→List Bool)
    (hA : ∀ i,A (slots side i)=words source q k Q C [] i) : A=result side Q [] A := by
  funext i
  by_cases hi : i=outPort side
  · subst i
    simp only [result,ite_true]
    have h:=hA 4
    cases side <;>simpa [slots,words,caps,PCPPQuerySupportReuse.data,ZeroPadding.pad_zero] using h
  · simp [result,hi]

theorem positive_value (side : Bool) (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (k Q : Nat) (A : Fin 91→List Bool) (h : k < (a.output r).systematicBits) :
    result side Q (PCPPQuerySupport.mask r (a.output r) ⟨k,h⟩) A=result side Q (value a r k) A := by
  rw [value,dif_pos h]

theorem negative_value (side : Bool) (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (k C : Nat) (A : Fin 91→List Bool)
    (hA : ∀ i,A (slots side i)=words (pcppOutput r (a.output r)) r.arity k
      (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) C [] i)
    (h : ¬k < (a.output r).systematicBits) :
    A=result side (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) (value a r k) A := by
  rw [value,dif_neg h]
  exact empty_result side _ _ _ _ _ A hA

theorem run (side : Bool) (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (k C : Nat) (A : Fin 91→List Bool)
    (hA : ∀ i,A (slots side i)=words (pcppOutput r (a.output r)) r.arity k
      (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) C [] i)
    (hflag : A (flagPort side)=ZeroPadding.pad C [decide ((a.output r).systematicBits ≤ k)]) :
    Step (machine side) (PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity)+6)
      H A H (result side (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) (value a r k) A) := by
  exact cases_run idle (readMachine side)
    (PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity)+4) H A
    (result side (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) (value a r k) A)
    (k < (a.output r).systematicBits)
    (fun h=>result side (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity))
      (PCPPQuerySupport.mask r (a.output r) ⟨k,h⟩) A) (test side) (idle_run A)
    (fun h=>read_run side a r ⟨k,h⟩ C A hA)
    (observed side _ k C A hflag)
    (positive_value side a r k _ A)
    (negative_value side a r k C A hA)

end
end SourceAssemblyLiteralSupport
