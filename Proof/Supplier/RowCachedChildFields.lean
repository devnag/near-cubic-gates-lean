import Proof.Supplier.RowNativeCoordinateAppend

/-! Missing scratch projections of the existing cached-child positioner.
This uses its unchanged header/record machines and their accepted receipts. -/
namespace NearCubicWires.RepairOrdinary.RowCachedChildFields
open LocalBitMultitape RepairRepresentation DecompositionSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def prior {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) := (gs.take i).flatMap exactWord
def backing {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) :=
  Records.savedList (gs.take i) (PCPPQueryField.saved gs.length [])
def heads {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) : Fin 5 → ℕ :=
  ![(natWord gs.length).length+(prior gs i).length,0,(prior gs i).length,1,1]
def tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) : Fin 5 → List Bool :=
  ![exactListWord gs,backing gs i,prior gs i,UnaryTemplate.tape n,UnaryTemplate.tape i]

theorem position_run {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i≤gs.length) :
    ∃ r,runFrom DecompositionCachedChild.machine (DecompositionCachedChild.budget gs i)
      (DecompositionCachedChild.entry gs i)=some r ∧
      r.final.heads=heads gs i ∧ r.final.tapes=tapes gs i ∧
      r.steps=DecompositionCachedChild.budget gs i := by
  let before := gs.take i
  let tail := (gs.drop i).flatMap exactWord
  have hlen : before.length=i := by simp only [before,List.length_take,Nat.min_eq_left hi]
  have hword : natWord gs.length++before.flatMap exactWord++tail=exactListWord gs := by
    rw [List.append_assoc,←List.flatMap_append]
    simp only [before,List.take_append_drop,exactListWord]
  obtain ⟨base,hb,bf,bs⟩ := PCPPQueryField.nat_run false [] (gs.flatMap exactWord) [] [] gs.length
  simp only [List.nil_append,List.length_nil] at hb
  let eh : Fin 2 → ℕ := fun _ => 1
  let et : Fin 2 → List Bool := ![UnaryTemplate.tape n,UnaryTemplate.tape i]
  let prep := TapeEmbedding.receipt eh et base
  have hp := TapeEmbedding.run_embed (PCPPQueryField.machine false) eh et _ _ base hb
  obtain ⟨last,hl,lt,lh,ls⟩ := Records.padded_run before (natWord gs.length) tail
    (PCPPQueryField.saved gs.length []) []
  rw [hword,hlen] at hl lt
  rw [hlen] at ls
  simp only [List.nil_append,List.length_nil] at hl lt lh
  have hc : (⟨Records.machine.start,
      ![(natWord gs.length).length,0,0,1,1],
      ![exactListWord gs,PCPPQueryField.saved gs.length [],[],UnaryTemplate.tape n,UnaryTemplate.tape i]⟩ :
      Configuration 5 (Fintype.card (RepairSource.VerifierDecoding.RepeatMachine.Control (Records.innerStates+6))))=
      Composition.restart prep.final Records.machine.start := by
    dsimp only [prep,TapeEmbedding.receipt]
    rw [bf]
    apply configuration_ext
    · rfl
    · funext j
      fin_cases j <;> simp [Composition.restart,TapeEmbedding.config,PCPPQueryField.payload,
        PCPPQueryField.cfg,PCPPQueryField.selected,eh,DecompositionSource.natWord_length] <;> rfl
    · funext j
      fin_cases j <;> simp [Composition.restart,TapeEmbedding.config,PCPPQueryField.payload,
        PCPPQueryField.cfg,PCPPQueryField.selected,et,exactListWord,PCPPQueryField.saved] <;> rfl
  rw [hc] at hl
  have whole := Composition.run_join DecompositionCachedChild.header Records.machine _ _ _ prep last hp hl
  have he : Composition.leftConfig _ (TapeEmbedding.config eh et
      (PCPPQueryField.cfg 0 (natWord gs.length++gs.flatMap exactWord) 0 [] 0 []))=
      DecompositionCachedChild.entry gs i := by
    apply configuration_ext
    · rfl
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
  rw [he] at whole
  have time : (2*natBitLength gs.length+3)+1+
      ((before.flatMap exactWord).length+(6*n+10)*i+3)=DecompositionCachedChild.budget gs i := by
    dsimp only [DecompositionCachedChild.budget,before]
    omega
  rw [time] at whole
  refine ⟨Composition.joinedReceipt prep last,whole,?_,?_,?_⟩
  · change last.final.heads=heads gs i
    rw [lh]
    rfl
  · change last.final.tapes=tapes gs i
    rw [lt]
    rfl
  · change base.steps+1+last.steps=_
    rw [bs,ls,time]

end NearCubicWires.RepairOrdinary.RowCachedChildFields
