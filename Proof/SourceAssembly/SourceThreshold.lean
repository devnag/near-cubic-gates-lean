import Proof.SourceAssembly.SourceThresholdLoop

/- Allocate the finite staircase scratch bank from the retained real C driver,
boot both count heads, and run the reusable loop. C never includes query backing. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace SourceAssemblyThresholdCold
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding RecoveryExecution
noncomputable section

def input (q n : Nat) (bits : List Bool) (i : Fin 33):=
  if i=22 then List.replicate (Capacity.value q) true else if i=26 then frame (natWord q) else
  if i=27 then frame (weights bits) else if i=28 then frame bits else if i=32 then CompareMachine.word n else []
def heads (q : Nat) (bits : List Bool) (j : Nat) : Fin 33→Nat:=Fin.addCases (motive:=fun _=>Nat)
  (SourceAssemblyThresholdBody.H (SourceAssemblyThresholdLoop.outputs q bits j)) (fun _ : Fin 1=>1)
def words (q n : Nat) (bits : List Bool) (j : Nat) : Fin 33→List Bool:=Fin.addCases (motive:=fun _=>List Bool)
  (SourceAssemblyThresholdBody.A q j bits (SourceAssemblyThresholdLoop.outputs q bits j))
  (fun _ : Fin 1=>CompareMachine.word n)
def slots (i : Fin 27) : Fin 33:=if h:i.val<22 then ⟨i.val,by omega⟩ else
  if i=22 then 24 else if i=23 then 25 else if i=24 then 31 else if i=25 then 22 else 23
def allocate:=RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 25)
def direction (i : Fin 33):=if i=25 ∨ i=32 then HeadMove.right else .stay
def boot:=DecompositionCountPosition.move direction
def machine:=Composition.machine allocate (Composition.machine boot SourceAssemblyThresholdLoop.machine)
def budget (q n : Nat):=2*Capacity.value q+7+SourceAssemblyThresholdLoop.budget q n

theorem zero_counter (q : Nat) : UWalkUnary.source (Capacity.value q) 0=List.replicate (Capacity.value q) false := by
  have hc:1≤Capacity.value q:=Nat.succ_le_of_lt (by unfold Capacity.value;positivity)
  simp only [UWalkUnary.source,ZeroPadding.pad,CompareMachine.word,List.replicate_zero,
    List.length_cons,List.length_nil,Nat.zero_add,List.singleton_append]
  change List.replicate ((Capacity.value q-1)+1) false=List.replicate (Capacity.value q) false
  rw [Nat.sub_add_cancel hc]

theorem allocate_run (q n : Nat) (bits : List Bool) :
    Step allocate (2*Capacity.value q+4) (fun _=>0) (input q n bits) (fun _=>0) (words q n bits 0) := by
  have raw:=Step.of_ready (RecoveryScratchErase.erase_ready (Capacity.value q) 0
    (fun _ : Fin 25=>[]) (by simp))
  simp only [Nat.zero_max] at raw
  refine CloseoutRowsEstimator.SubstitutionDock.run _ slots (by decide) _ _ _ _ _ _ _ _ raw ?_ ?_ ?_ ?_ ?_ ?_
  · intro i;rfl
  · intro i;fin_cases i <;>rfl
  · intro i;rfl
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
    · rfl
    · change UWalkUnary.source (Capacity.value q) 0=List.replicate (Capacity.value q) false
      exact zero_counter q
    · rfl
    · rfl
    · rfl
  · intro i _;rfl
  · intro i hi
    by_cases hs:i.val<22
    · exact False.elim (hi ⟨i.val,by omega⟩ (by apply Fin.ext;simp [slots,hs]))
    · have hv:=i.isLt
      interval_cases h:i.val
      · have heq:i=⟨22,by decide⟩:=Fin.ext h
        subst i
        exact False.elim (hi 25 rfl)
      · have heq:i=⟨23,by decide⟩:=Fin.ext h
        subst i
        exact False.elim (hi 26 rfl)
      · have heq:i=⟨24,by decide⟩:=Fin.ext h
        subst i
        exact False.elim (hi 22 rfl)
      · have heq:i=⟨25,by decide⟩:=Fin.ext h
        subst i
        exact False.elim (hi 23 rfl)
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
        exact False.elim (hi 24 rfl)
      · have heq:i=⟨32,by decide⟩:=Fin.ext h
        subst i
        rfl

theorem boot_run (q n : Nat) (bits : List Bool) :
    Step boot 1 (fun _=>0) (words q n bits 0) (heads q bits 0) (words q n bits 0) := by
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run direction (fun _=>0) (words q n bits 0)
  apply Step.of_run hr ?_ (by rw [hf])
  rw [hf];funext i;fin_cases i <;>simp [direction,HeadMove.apply,heads,
    SourceAssemblyThresholdBody.H,SourceAssemblyThresholdLoop.outputs] <;>rfl

theorem loop_run (q n : Nat) (bits : List Bool) (hn : n≤q) (hlen : bits.length=q) :
    Step SourceAssemblyThresholdLoop.machine
      (SourceAssemblyThresholdLoop.budget q n)
      (heads q bits 0) (words q n bits 0) (heads q bits n) (words q n bits n) := by
  obtain ⟨r,hr,hf,_⟩:=SourceAssemblyThresholdLoop.run q n bits hn hlen
  have he : RepeatMachine.cfg 0 (SourceAssemblyThresholdLoop.source
      SourceAssemblyThresholdBody.machine q bits 0) n 1=
      RecoveryCalls.restarted SourceAssemblyThresholdLoop.machine (heads q bits 0) (words q n bits 0) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      refine Fin.addCases (m:=32) (n:=1) ?_ ?_ i
      · intro k;simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
          SourceAssemblyThresholdLoop.source,words,RecoveryCalls.restarted,Fin.addCases_left]
      · intro k;simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
          SourceAssemblyThresholdLoop.source,words,RecoveryCalls.restarted,Fin.addCases_right]
  rw [he] at hr
  apply Step.of_run hr
  · rw [hf];rfl
  · rw [hf];funext i
    refine Fin.addCases (m:=32) (n:=1) ?_ ?_ i
    · intro k;simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
        SourceAssemblyThresholdLoop.source,words,Fin.addCases_left]
    · intro k;simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
        SourceAssemblyThresholdLoop.source,words,Fin.addCases_right]

theorem run (q n : Nat) (bits : List Bool) (hn : n≤q) (hlen : bits.length=q) :
    Step machine (budget q n) (fun _=>0) (input q n bits) (heads q bits n) (words q n bits n) := by
  exact ((allocate_run q n bits).seq ((boot_run q n bits).seq (loop_run q n bits hn hlen))).enlarge
    (by unfold budget;omega)

end
end SourceAssemblyThresholdCold
