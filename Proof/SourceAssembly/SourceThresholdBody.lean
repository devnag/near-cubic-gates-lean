import Proof.SourceAssembly.SourceThresholdGate

/- Reusable physical THR staircase body: produce native j, append one gate
and its original support, erase only bounded private scratch, increment j. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace SourceAssemblyThresholdBody
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding CloseoutRowsEstimator
noncomputable section

def extra (q : Nat) (bits : List Bool) (out : Fin 2→List Bool) : Fin 6→List Bool:=
  ![frame (natWord q),frame (weights bits),frame bits,out 0,out 1,List.replicate (Capacity.value q) false]
def extraHeads (out : Fin 2→List Bool) : Fin 6→Nat:=![0,0,0,(out 0).length,(out 1).length,0]
def H (out : Fin 2→List Bool) (i : Fin 32):=
  if i=25 then 1 else if i=29 then (out 0).length else if i=30 then (out 1).length else 0
def store (B : Fin 26→List Bool) (q : Nat) (bits : List Bool) (out : Fin 2→List Bool) (i : Fin 32):=
  if h:i.val<26 then B ⟨i.val,h⟩ else
  if i=26 then frame (natWord q) else if i=27 then frame (weights bits) else if i=28 then frame bits else
  if i=29 then out 0 else if i=30 then out 1 else List.replicate (Capacity.value q) false
def A (q j : Nat) (bits : List Bool) (out : Fin 2→List Bool):=
  store (SourceAssemblyThresholdIndex.input q j) q bits out
def gateSlots : Fin 7→Fin 32:=![26,27,28,20,29,30,31]
def eraseSlots (i : Fin 24) : Fin 32:=i.castAdd 8
def counterSlots : Fin 1→Fin 32:=![25]
def first:=TapeEmbedding.machine 6 SourceAssemblyThresholdIndex.machine
def gate:=RecoveryFocus.machine gateSlots SourceAssemblyThresholdGate.machine
def erase:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 22)
def increment:=RecoveryFocus.machine counterSlots Counter.machine
def machine:=Composition.machine first (Composition.machine gate (Composition.machine erase increment))
def budget (q j : Nat) (bits : List Bool):=SourceAssemblyThresholdIndex.budget j+
  SourceAssemblyThresholdGate.budget q j bits+2*Capacity.value q+2*j+9

theorem gate_run (q j : Nat) (bits : List Bool) (out : Fin 2→List Bool) (B : Fin 26→List Bool)
    (hj : j≤q) (hlen : bits.length=q)
    (h20 : B 20=ZeroPadding.pad (Capacity.value q) (frame (natWord j))) :
    Step gate (SourceAssemblyThresholdGate.budget q j bits)
      (H out) (store B q bits out)
      (H (fun i=>out i++SourceAssemblyThresholdGate.emitted q j bits i))
      (store B q bits (fun i=>out i++SourceAssemblyThresholdGate.emitted q j bits i)) := by
  have hn:natBitLength j≤j+1:=Nat.add_le_add_right (Nat.log_le_self 2 j) 1
  have nq:natBitLength q≤q+1:=Nat.add_le_add_right (Nat.log_le_self 2 q) 1
  have hq:2*(natWord q).length+1≤Capacity.value q:=SourceAssemblySymmetricQuery.capacity_fit q
  have hw:2*(weights bits).length+1≤Capacity.value q:=by rw [weights_length,hlen];unfold Capacity.value;nlinarith
  have hjj:2*(natWord j).length+1≤Capacity.value q:=by rw [DecompositionSource.natWord_length];unfold Capacity.value;nlinarith
  have hb:2*bits.length+1≤Capacity.value q:=by rw [hlen];unfold Capacity.value;nlinarith
  let tail:=List.replicate (Capacity.value q-(frame (natWord j)).length) false
  have localStep:=SourceAssemblyThresholdGate.run q j (Capacity.value q) bits tail out hq hw hjj hb
  refine SubstitutionDock.run _ gateSlots (by decide) _ _ _ _ _ _ _ _ localStep ?_ ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i
    · rfl
    · rfl
    · rfl
    · exact h20
    · rfl
    · rfl
    · rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i
    · rfl
    · rfl
    · rfl
    · exact h20
    · rfl
    · rfl
    · rfl
  · intro i hi
    have h29:i≠29:=fun he=>hi 4 he.symm
    have h30:i≠30:=fun he=>hi 5 he.symm
    simp only [H,h29,h30,if_false]
  · intro i hi
    have h29:i≠29:=fun he=>hi 4 he.symm
    have h30:i≠30:=fun he=>hi 5 he.symm
    simp only [store,h29,h30,if_false]

theorem erase_run (q j : Nat) (bits : List Bool) (out : Fin 2→List Bool) (B : Fin 26→List Bool)
    (hsize : ∀ i : Fin 22,(B (i.castAdd 4)).length=Capacity.value q)
    (he : ∀ i : Fin 4,B (i.natAdd 22)=SourceAssemblyThresholdIndex.extra q j i) :
    Step erase (2*Capacity.value q+4) (H out) (store B q bits out) (H out) (A q j bits out) := by
  have raw:=Step.of_ready (RecoveryScratchErase.erase_ready (Capacity.value q) (Capacity.value q+1)
    (fun i : Fin 22=>B (i.castAdd 4)) (fun i=>(hsize i).le))
  simp only [Nat.max_self] at raw
  refine SubstitutionDock.run _ eraseSlots (by decide) _ _ _ _ _ _ _ _ raw ?_ ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact he 0
    · exact he 1
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i _;rfl
  · intro i hi
    by_cases hs:i.val<24
    · exact False.elim (hi ⟨i.val,hs⟩ (Fin.ext rfl))
    · have hv:=i.isLt
      interval_cases h:i.val
      · have heq:i=⟨24,by decide⟩:=Fin.ext h
        subst i
        exact he 2
      · have heq:i=⟨25,by decide⟩:=Fin.ext h
        subst i
        exact he 3
      · have heq:i=⟨26,by decide⟩:=Fin.ext h
        subst i
        rfl
      · have heq:i=⟨27,by decide⟩:=Fin.ext h
        subst i
        rfl
      · have heq:i=⟨28,by decide⟩:=Fin.ext h
        subst i
        rfl
      · have heq:i=⟨29,by decide⟩:=Fin.ext h
        subst i
        rfl
      · have heq:i=⟨30,by decide⟩:=Fin.ext h
        subst i
        rfl
      · have heq:i=⟨31,by decide⟩:=Fin.ext h
        subst i
        rfl

theorem index_other (q j : Nat) (i : Fin 26) (hi : i≠25) :
    SourceAssemblyThresholdIndex.input q j i=
      SourceAssemblyThresholdIndex.input q (j+1) i := by
  revert hi
  refine Fin.addCases (m:=22) (n:=4) ?_ ?_ i
  · intro k _;simp only [SourceAssemblyThresholdIndex.input,Fin.addCases_left]
  · intro k hi;fin_cases k
    · rfl
    · rfl
    · rfl
    · exact False.elim (hi rfl)

theorem increment_run (q j : Nat) (bits : List Bool) (out : Fin 2→List Bool) :
    Step increment (2*j+2) (H out) (A q j bits out) (H out) (A q (j+1) bits out) := by
  have raw:=(Counter.increment_run j).pad (fun _=>Capacity.value q)
  refine SubstitutionDock.run _ counterSlots (by decide) _ _ _ _ _ _ _ _ raw ?_ ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i _;rfl
  · intro i hi
    have h25:i≠25:=fun he=>hi 0 he.symm
    by_cases hs:i.val<26
    · simp only [A,store,dif_pos hs]
      apply index_other
      intro he
      apply h25
      exact Fin.ext (congrArg (fun k : Fin 26=>k.val) he)
    · simp only [A,store,dif_neg hs]

theorem run (q j : Nat) (bits : List Bool) (out : Fin 2→List Bool)
    (hj : j≤q) (hlen : bits.length=q) :
    Step machine (budget q j bits) (H out) (A q j bits out)
      (H (fun i=>out i++SourceAssemblyThresholdGate.emitted q j bits i))
      (A q (j+1) bits (fun i=>out i++SourceAssemblyThresholdGate.emitted q j bits i)) := by
  obtain ⟨B,hb,h20,hsize,he⟩:=SourceAssemblyThresholdIndex.run q j hj
  have firstStep : Step first (SourceAssemblyThresholdIndex.budget j)
      (H out) (A q j bits out) (H out) (store B q bits out) := by
    apply (hb.embed (extraHeads out) (extra q bits out)).congr_in ?_ ?_ |>.congr ?_ ?_
    all_goals funext i;fin_cases i <;>rfl
  exact (firstStep.seq ((gate_run q j bits out B hj hlen h20).seq
    ((erase_run q j bits _ B hsize he).seq (increment_run q j bits _)))).enlarge (by unfold budget;omega)

end
end SourceAssemblyThresholdBody
