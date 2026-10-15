import Proof.SourceAssembly.SourceSymmetricCanonical

/- Reusable THR staircase index production from the actual retained unary
counter. The produced framed native index is consumed before the22-tape erase. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyThresholdIndex
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
noncomputable section

def extra (q j : Nat) : Fin 4→List Bool:=![List.replicate (Capacity.value q) true,
  List.replicate (Capacity.value q+1) false,List.replicate (Capacity.value q) false,
  UWalkUnary.source (Capacity.value q) j]
def input (q j : Nat) : Fin 26→List Bool:=Fin.addCases (motive:=fun _=>List Bool)
  (fun _ : Fin 22=>List.replicate (Capacity.value q) false) (extra q j)
def prepared (q j : Nat) : Fin 26→List Bool:=Fin.addCases (motive:=fun _=>List Bool)
  (Natural.input q j) (extra q j)
def heads (i : Fin 26):=if i=25 then 1 else 0
def copySlots : Fin 3→Fin 26:=![25,0,24]
def direction (right : Bool) (i : Fin 26):=if i=25 then (if right then HeadMove.right else .left) else .stay
def left:=DecompositionCountPosition.move (direction false)
def right:=DecompositionCountPosition.move (direction true)
def copy:=RecoveryFocus.machine copySlots (UWalkUnary.machine false false)
def natural:=TapeEmbedding.machine 4 Natural.machine
def machine:=Composition.machine left (Composition.machine copy (Composition.machine right natural))
def budget (j : Nat):=2*j+11+Natural.budget j

theorem copy_run (q j : Nat) (hj : j≤q) :
    Step copy (2*j+6) (fun _=>0) (input q j) (fun _=>0) (prepared q j) := by
  have hC:j+2≤Capacity.value q:=by unfold Capacity.value;nlinarith
  obtain ⟨rr,hr,ht,hh,hs⟩:=UWalkUnary.ready false false (Capacity.value q) j
  have base : Step (UWalkUnary.machine false false) (2*j+6) (fun _=>0)
      (UWalkUnary.input (Capacity.value q) j) (fun _=>0) (UWalkUnary.result false false (Capacity.value q) j):=
    ⟨rr,hr,funext hh,ht,hs⟩
  have raw:=base.pad (![0,Capacity.value q,Capacity.value q])
  have actual : Step (UWalkUnary.machine false false) (2*j+6) (fun _=>0)
      (![UWalkUnary.source (Capacity.value q) j,List.replicate (Capacity.value q) false,List.replicate (Capacity.value q) false])
      (fun _=>0) (![UWalkUnary.source (Capacity.value q) j,ZeroPadding.pad (Capacity.value q) (List.replicate j true),List.replicate (Capacity.value q) false]) := by
    apply raw.congr_in rfl ?_ |>.congr rfl ?_
    · funext i;fin_cases i <;>simp [UWalkUnary.input,ZeroPadding.pad]
    · funext i;fin_cases i
      · simp [UWalkUnary.result,ZeroPadding.pad_zero]
      · rfl
      · change ZeroPadding.pad (Capacity.value q) (List.replicate (j+2) false)=List.replicate (Capacity.value q) false
        simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add,Nat.add_sub_of_le hC]
  refine CloseoutRowsEstimator.SubstitutionDock.run _ copySlots (by decide) _ _ _ _ _ _ _ _ actual
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro i;rfl
  · intro i;fin_cases i <;>rfl
  · intro i;rfl
  · intro i;fin_cases i
    · rfl
    · rfl
    · rfl
  · intro i _;rfl
  · intro i
    refine Fin.addCases (m:=22) (n:=4) ?_ ?_ i
    · intro k hi
      have hk:k≠0:=by intro he;subst k;exact hi 1 rfl
      simp only [input,prepared,Fin.addCases_left,Natural.input]
      change List.replicate (Capacity.value q) false=ZeroPadding.pad (Capacity.value q) (Natural.source j k)
      simp [Natural.source,hk,ZeroPadding.pad]
    · intro k _;simp only [input,prepared,Fin.addCases_right]

theorem move_left (q j : Nat) : Step left 1 heads (input q j) (fun _=>0) (input q j) := by
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run (direction false) heads (input q j)
  apply Step.of_run hr ?_ (by rw [hf])
  rw [hf];funext i;by_cases hi:i=25 <;>simp [direction,heads,HeadMove.apply,hi]

theorem move_right (q j : Nat) : Step right 1 (fun _=>0) (prepared q j) heads (prepared q j) := by
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run (direction true) (fun _=>0) (prepared q j)
  apply Step.of_run hr ?_ (by rw [hf])
  rw [hf];funext i;by_cases hi:i=25 <;>simp [direction,heads,HeadMove.apply,hi]

theorem run (q j : Nat) (hj : j≤q) : ∃ A,
    Step machine (budget j) heads (input q j) heads A ∧
      A 20=ZeroPadding.pad (Capacity.value q) (frame (natWord j)) ∧
      (∀ i : Fin 22,(A (i.castAdd 4)).length=Capacity.value q) ∧
      (∀ i : Fin 4,A (i.natAdd 22)=extra q j i) := by
  obtain ⟨B,hb,h20,_h17,hsize⟩:=Natural.native_run q j hj
  have hs : (Fin.addCases (motive:=fun _=>Nat) (fun _ : Fin 22=>0)
      (![0,0,0,1]))=heads := by funext i;fin_cases i <;>rfl
  obtain ⟨rr,hr,ht,hh,hs0⟩:=hb
  have base : Step Natural.machine (Natural.budget j) (fun _=>0) (Natural.input q j) (fun _=>0) B:=
    ⟨rr,hr,funext hh,ht,hs0⟩
  have last:=base.embed (![0,0,0,1]) (extra q j)
  rw [hs] at last
  refine ⟨_,((move_left q j).seq ((copy_run q j hj).seq ((move_right q j).seq last))).enlarge
    (by unfold budget;omega),?_,?_,?_⟩
  · exact h20
  · intro i;simpa only [Fin.addCases_left] using hsize i
  · intro i;simp only [Fin.addCases_right]

end
end SourceAssemblyThresholdIndex
