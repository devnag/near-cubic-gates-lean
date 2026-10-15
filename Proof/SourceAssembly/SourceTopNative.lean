import Proof.SourceAssembly.SourceTopExtract

/- The complete paid TOP pipeline starts from the retained native circuit
stream and ends at the exact framed child payload used by Request.topWord. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyTopNative
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open DecompositionSource ExecutableInterfaces RecoveryRootRound CompilerSemantics
open PacketProduction
noncomputable section

abbrev entryTapes (a : DecompositionAlgorithm) := (Counted.tapes a+2)+2
abbrev tapes (a : DecompositionAlgorithm) := 4+entryTapes a

def slots (a : DecompositionAlgorithm) (i : Fin (entryTapes a)) : Fin (tapes a) :=
  if i.val=0 then (2 : Fin 4).castAdd (entryTapes a) else i.natAdd 4

theorem slots_injective (a : DecompositionAlgorithm) : Function.Injective (slots a) := by
  intro i j he
  apply Fin.ext
  have hv:=congrArg Fin.val he
  dsimp only [slots] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd] at hv <;> omega

theorem extend_single {m n : Nat} (hm : 0 < m) (word : List Bool) (f : Fin m→List Bool)
    (hf : ∀ i,f i=if i.val=0 then word else []) :
    ∀ i : Fin (m+n),Fin.addCases f (fun _ : Fin n=>[]) i=if i.val=0 then word else [] := by
  intro i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · by_cases hj : j.val=0
    · simp only [Fin.addCases_left,Fin.val_castAdd,hj,if_true]
      simpa only [hj,if_true] using hf j
    · simp only [Fin.addCases_left,Fin.val_castAdd,hj,if_false]
      simpa only [hj,if_false] using hf j
  · simp only [Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega)]

theorem entry_input (a : DecompositionAlgorithm) (r : ExactDecompositionRequest)
    (i : Fin (entryTapes a)) :
    AppendOutputFrame.input (Counted.input a r) i=if i.val=0 then frame (thresholdWord r.gate) else [] := by
  have hcall : ∀ j,Call.input a r j=if j.val=0 then frame (thresholdWord r.gate) else [] := by
    apply extend_single (by decide)
    intro j
    simp [Prepare.input,thresholdWord,Call.tail]
  have hcount : ∀ j,Counted.input a r j=if j.val=0 then frame (thresholdWord r.gate) else [] :=
    extend_single (by unfold Call.tapes;omega) _ _ hcall
  exact extend_single (n:=2) (by unfold Counted.tapes Call.tapes;omega) _ _
    (extend_single (n:=1) (by unfold Counted.tapes Call.tapes;omega) _ _
      (extend_single (n:=1) (by unfold Counted.tapes Call.tapes;omega) _ _ hcount)) i

def first (a : DecompositionAlgorithm) := TapeEmbedding.machine (entryTapes a) SourceAssemblyTopExtract.machine
def last (a : DecompositionAlgorithm) := RecoveryFocus.machine (slots a) (SourceAssemblyTopEntry.machine a)
def machine (a : DecompositionAlgorithm) := Composition.machine (first a) (last a)
def input (a : DecompositionAlgorithm) (n : Nat) (r : ExactDecompositionRequest) (tail : List Bool) : Fin (tapes a) → List Bool :=
  fun i=>Fin.addCases (m:=4) (n:=entryTapes a) (motive:=fun _=>List Bool)
    (fun j=>Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool)
      (SourceAssemblyTopExtract.input n (thresholdWord r.gate) tail) (fun _=>[]) j)
    (fun _=>[]) i
def budget (a : DecompositionAlgorithm) (n : Nat) (r : ExactDecompositionRequest) :=
  SourceAssemblyTopExtract.budget n (thresholdWord r.gate)+1+SourceAssemblyTopEntry.budget a r

theorem run (a : DecompositionAlgorithm) (n : Nat) (r : ExactDecompositionRequest) (tail : List Bool) :
    ∃ A, Step (machine a) (budget a n r) (fun _=>0) (input a n r tail) (fun _=>0) A ∧
      A (slots a ((0 : Fin 2).natAdd (Counted.tapes a+2)))=frame (Entry.output a r) ∧
      A 0=natWord n++frame (thresholdWord r.gate)++tail := by
  obtain ⟨B,firstRun,native,top⟩:=SourceAssemblyTopExtract.run n (thresholdWord r.gate) tail
  let bank : Fin (tapes a)→List Bool := Fin.addCases B (fun _ : Fin (entryTapes a)=>[])
  have firstStep : Step (first a) (SourceAssemblyTopExtract.budget n (thresholdWord r.gate)) (fun _=>0)
      (input a n r tail) (fun _=>0) bank :=
    ((firstRun.embed (fun _ : Fin (entryTapes a)=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;> simp only [Fin.addCases_left,Fin.addCases_right]) rfl).congr
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;> simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  obtain ⟨C,entryRun,child⟩:=SourceAssemblyTopEntry.framed_run a r
  have hbank : ∀ i,bank (slots a i)=AppendOutputFrame.input (Counted.input a r) i := by
    intro i
    rw [entry_input]
    by_cases hi : i.val=0
    · simpa only [bank,slots,hi,if_true,Fin.addCases_left] using top
    · simp only [bank,slots,hi,if_false,Fin.addCases_right]
  have lastStep:=entryRun.dock (slots a) (slots_injective a) (fun _=>0) bank
    (by intro i;rfl) hbank
  have all:=firstStep.seq lastStep
  refine ⟨install (slots a) bank C,all.congr ?_ rfl,?_,?_⟩
  · funext i
    unfold dockH
    split <;> rfl
  · rw [install_slot _ (slots_injective a)]
    exact child
  · rw [install_other (slots a) bank C 0 (by
      intro j he
      have hv:=congrArg Fin.val he
      change (slots a j).val=0 at hv
      dsimp only [slots] at hv
      split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd] at hv <;> omega)]
    exact native

theorem threshold_run (a : DecompositionAlgorithm) {q : Nat}
    (c : SupplierPipeline.NormalizedThresholdThresholdCircuit q) :
    ∃ A, Step (machine a)
      (budget a c.top.wireCount ⟨c.top.support.card,nonStrictAsStrict (SupplierPipeline.retainedTopGate c)⟩)
      (fun _=>0)
      (fun i=>if i.val=0 then thrWord c else []) (fun _=>0) A ∧
      A (slots a ((0 : Fin 2).natAdd (Counted.tapes a+2)))=
        frame (natWord c.top.support.card++exactListWord (ThresholdRows.children a c)) ∧ A 0=thrWord c := by
  have h:=run a c.top.wireCount
    ⟨c.top.support.card,nonStrictAsStrict (SupplierPipeline.retainedTopGate c)⟩
    ((List.ofFn (fun i=>c.bottom (SupplierPipeline.retainedTopIndex c i))).flatMap
      (fun g=>frame (bottomWord g)))
  obtain ⟨A,hs,ho⟩:=h
  refine ⟨A,hs.congr_in rfl ?_,ho.1,ho.2⟩
  funext i
  unfold input
  apply extend_single (by decide) (thrWord c) _ ?_ i
  intro j
  refine Fin.addCases (m:=3) (n:=1) (fun k=>?_) (fun k=>?_) j
  · fin_cases k <;> rfl
  · fin_cases k;rfl

end
end SourceAssemblyTopNative
