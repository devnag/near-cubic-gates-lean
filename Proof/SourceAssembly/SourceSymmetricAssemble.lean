import Proof.SourceAssembly.SourceSymmetricHeader

/- Assemble one native circuit from its physically produced count/TOP and
same-count native/support streams. All three copies are actual machine runs. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace SourceAssemblySymmetricAssemble
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open CloseoutRowsEstimatorParity RecoveryRootRound RepairSource.VerifierDecoding
open CloseoutRowsTupleSeek (GatePair nativeWord supportWord)
noncomputable section

def natSlots : Fin 3→Fin 8:=![0,7,5]
def topSlots : Fin 2→Fin 8:=![1,5]
def pairSlots : Fin 5→Fin 8:=![2,5,3,6,4]
def first:=RecoveryFocus.machine natSlots (PCPPQueryField.machine true)
def middle:=RecoveryFocus.machine topSlots (CloseoutRowsTupleSeek.frameMachine true)
def last:=RecoveryFocus.machine pairSlots (CloseoutRowsTupleSeek.pairsMachine true)
def machine:=Composition.machine first (Composition.machine middle last)
def prefixWord (top : List Bool) (gs : List GatePair):=natWord gs.length++frame top
def circuitWord (top : List Bool) (gs : List GatePair):=prefixWord top gs++nativeWord gs

def H (top : List Bool) (gs : List GatePair) (stage : Nat) (i : Fin 8) : Nat:=
  if i=0 then (if stage=0 then 0 else (natWord gs.length).length) else
  if i=1 then (if stage<2 then 0 else (frame top).length) else
  if i=2 then (if stage<3 then 0 else (nativeWord gs).length) else
  if i=3 then (if stage<3 then 0 else (supportWord gs).length) else
  if i=4 then 1 else
  if i=5 then (if stage=0 then 0 else if stage=1 then (natWord gs.length).length else if stage=2 then (prefixWord top gs).length else (circuitWord top gs).length) else
  if i=6 then (if stage<3 then 0 else (supportWord gs).length) else 0
def A (top : List Bool) (gs : List GatePair) (stage : Nat) (i : Fin 8) : List Bool:=
  if i=0 then natWord gs.length else if i=1 then frame top else if i=2 then nativeWord gs else
  if i=3 then supportWord gs else if i=4 then CompareMachine.word gs.length else
  if i=5 then (if stage=0 then [] else if stage=1 then natWord gs.length else if stage=2 then prefixWord top gs else circuitWord top gs) else
  if i=6 then (if stage<3 then [] else supportWord gs) else
  (if stage=0 then [] else PCPPQueryField.saved gs.length [])
def budget (top : List Bool) (gs : List GatePair):=
  2*natBitLength gs.length+2*top.length+CloseoutRowsTupleSeek.pairsCost gs+6

theorem nat_run (n : Nat) : Step (PCPPQueryField.machine true) (2*natBitLength n+3)
    (![0,0,0]) (![natWord n,[],[]])
    (![(natWord n).length,0,(natWord n).length]) (![natWord n,PCPPQueryField.saved n [],natWord n]) := by
  obtain ⟨r,hr,hf,hs⟩:=PCPPQueryField.nat_run true [] [] [] [] n
  simp only [List.nil_append,List.append_nil,List.length_nil,PCPPQueryField.selected,ite_true] at hr hf
  refine ⟨r,hr,?_,?_,hs.le⟩
  · rw [hf]
    change ![0+2*natBitLength n+1,0,(natWord n).length]=_
    simp only [Nat.zero_add,DecompositionSource.natWord_length]
  · rw [hf]
    rfl

attribute [local irreducible] natWord CompareMachine.word PCPPQueryField.saved
  CloseoutRowsTupleSeek.nativeWord CloseoutRowsTupleSeek.supportWord
theorem first_run (top : List Bool) (gs : List GatePair) :
    Step first (2*natBitLength gs.length+3) (H top gs 0) (A top gs 0) (H top gs 1) (A top gs 1) := by
  refine CloseoutRowsEstimator.SubstitutionDock.run (PCPPQueryField.machine true) natSlots (by decide)
    ![0,0,0] ![(natWord gs.length).length,0,(natWord gs.length).length]
    ![natWord gs.length,[],[]] ![natWord gs.length,PCPPQueryField.saved gs.length [],natWord gs.length]
    (H top gs 0) (H top gs 1) (A top gs 0) (A top gs 1) (nat_run gs.length)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;>simp only [H,A,natSlots,Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk] <;>rfl
  · intro i;fin_cases i <;>simp only [H,A,natSlots,Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk] <;>rfl
  · intro i;fin_cases i <;>simp only [H,A,natSlots,Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk] <;>rfl
  · intro i;fin_cases i <;>simp only [H,A,natSlots,Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk] <;>rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi 0 rfl)
    · simp only [H,A,natSlots,Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk]
      rfl
    · simp only [H,A,natSlots,Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk]
      rfl
    · simp only [H,A,natSlots,Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk]
      rfl
    · simp only [H,A,natSlots,Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk]
      rfl
    · exact False.elim (hi 2 rfl)
    · simp only [H,A,natSlots,Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk]
      rfl
    · exact False.elim (hi 1 rfl)
  · intro i hi
    fin_cases i
    · exact False.elim (hi 0 rfl)
    · simp only [H,A,natSlots,Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk]
      rfl
    · simp only [H,A,natSlots,Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk]
      rfl
    · simp only [H,A,natSlots,Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk]
      rfl
    · simp only [H,A,natSlots,Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk]
      rfl
    · exact False.elim (hi 2 rfl)
    · simp only [H,A,natSlots,Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceFinMk]
      rfl
    · exact False.elim (hi 1 rfl)

theorem middle_run (top : List Bool) (gs : List GatePair) :
    Step middle (2*top.length+1) (H top gs 1) (A top gs 1) (H top gs 2) (A top gs 2) := by
  have localStep:=CloseoutRowsTupleSeek.frame_run true [] top [] (natWord gs.length)
  simp only [List.nil_append,List.append_nil,CloseoutRowsTupleSeek.selected,ite_true,List.length_nil,Nat.zero_add] at localStep
  refine CloseoutRowsEstimator.SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ localStep
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro i;fin_cases i <;>rfl)
  | (intro i hi;fin_cases i <;>first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | rfl)

theorem pair_run (top : List Bool) (gs : List GatePair) :
    Step (CloseoutRowsTupleSeek.pairsMachine true) (CloseoutRowsTupleSeek.pairsCost gs)
      (![0,(prefixWord top gs).length,0,0,1])
      (![nativeWord gs,prefixWord top gs,supportWord gs,[],CompareMachine.word gs.length])
      (![(nativeWord gs).length,(circuitWord top gs).length,(supportWord gs).length,(supportWord gs).length,1])
      (![nativeWord gs,circuitWord top gs,supportWord gs,supportWord gs,CompareMachine.word gs.length]) := by
  obtain ⟨r,hr,hf,_⟩:=CloseoutRowsTupleSeek.pairs_run true gs [] [] [] [] (prefixWord top gs) []
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add,
    CloseoutRowsTupleSeek.selected,ite_true] at hr hf
  have hi : CloseoutRowsTupleSeek.pairsCfg true 0 (nativeWord gs) (supportWord gs) 0 0
      (prefixWord top gs) [] gs.length 1=RecoveryCalls.restarted (CloseoutRowsTupleSeek.pairsMachine true)
        ![0,(prefixWord top gs).length,0,0,1]
        ![nativeWord gs,prefixWord top gs,supportWord gs,[],CompareMachine.word gs.length] := by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;>simp [CloseoutRowsTupleSeek.pairsCfg,CloseoutRowsTupleSeek.pairEntry,
        RepeatMachine.cfg,controlConfig,TapeEmbedding.config,CloseoutRowsTupleSeek.pairData,
        CloseoutRowsTupleSeek.fieldData,RecoveryCalls.restarted] <;>rfl
  rw [hi] at hr
  apply Step.of_run hr
  · rw [hf];funext i;fin_cases i <;>rfl
  · rw [hf];funext i;fin_cases i <;>simp [CloseoutRowsTupleSeek.pairsCfg,CloseoutRowsTupleSeek.pairEntry,
      RepeatMachine.cfg,controlConfig,TapeEmbedding.config,CloseoutRowsTupleSeek.pairData,
      CloseoutRowsTupleSeek.fieldData,circuitWord] <;>rfl

theorem last_run (top : List Bool) (gs : List GatePair) :
    Step last (CloseoutRowsTupleSeek.pairsCost gs) (H top gs 2) (A top gs 2) (H top gs 3) (A top gs 3) := by
  refine CloseoutRowsEstimator.SubstitutionDock.run _ _ (by decide) _ _ _ _ _ _ _ _ (pair_run top gs)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
  | (intro i;fin_cases i <;>rfl)
  | (intro i hi;fin_cases i <;>first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl) | exact False.elim (hi 4 rfl) | rfl)

theorem run (top : List Bool) (gs : List GatePair) :
    Step machine (budget top gs) (H top gs 0) (A top gs 0) (H top gs 3) (A top gs 3) := by
  exact ((first_run top gs).seq ((middle_run top gs).seq (last_run top gs))).enlarge (by unfold budget;omega)

end
end SourceAssemblySymmetricAssemble
