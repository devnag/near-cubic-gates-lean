import Proof.Hierarchy.CompetitorCountEntry
import Proof.MachineModel.ClockScalarFields

/-! Actual whole count producer from raw cells, physical native/scalar widths
and the physical cell-count word. All work tapes initially are blank. A paid
zero-scalar constructor feeds the sequential count loop; its scratch is reused.
Producing the three dimension words is the enclosing matrix caller's work. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountProducer
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (b w : ℕ) (xs : List ℕ) : Fin 11 → List Bool :=
  fun i => match i.val with
    | 0 => CompetitorCountFold.raw b xs
    | 1 => List.replicate b true
    | 2 => List.replicate w true
    | 8 => CompareMachine.word xs.length
    | _ => []
def zeroSlots : Fin 5 → Fin 11 := ![2,10,5,9,4]
noncomputable def zeroProgram := RecoveryFocus.machine zeroSlots ClockNormalize.machine
noncomputable def foldProgram := TapeEmbedding.machine 2 CompetitorCountEntry.machine
noncomputable def machine := Composition.machine zeroProgram foldProgram
def budget (w n : ℕ) := n*(16*w+20)+4*w+10

theorem zero_ready (b w : ℕ) (xs : List ℕ) :
    ∃ out,ClockJoin.ReadyRun zeroProgram (4*w+4) (input b w xs) out ∧
      (∀ i : Fin 9,out (i.castAdd 2)=CompetitorCountEntry.input b w xs i) := by
  obtain ⟨r,hr,h0,_,h2,_,h4,hh,hs⟩ := ClockScalarFields.zero_run w
  have hready : ClockJoin.ReadyRun ClockNormalize.machine (4*w+4) (ClockScalarFields.zeroInput w) r.final.tapes :=
    ⟨r,hr,rfl,hh,hs.le⟩
  have hfocus := CompetitorRationalProducts.bounded_focus zeroSlots (by decide) _ _ _ hready (input b w xs)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨install zeroSlots (input b w xs) r.final.tapes,hfocus,?_⟩
  intro i; fin_cases i
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact (install_slot zeroSlots (by decide) _ _ 0).trans h0
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact (install_slot zeroSlots (by decide) _ _ 4).trans h4
  · exact (install_slot zeroSlots (by decide) _ _ 2).trans h2
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact install_other zeroSlots _ _ _ (by decide)

theorem fold_run (b w : ℕ) (xs : List ℕ) (middle : Fin 11 → List Bool)
    (hm : ∀ i : Fin 9,middle (i.castAdd 2)=CompetitorCountEntry.input b w xs i)
    (hw : b≤w) (hx : ∀ x∈xs,x<2^b) (hfit : xs.sum<2^w) :
    ∃ r : ExecutionReceipt 11 (2+Fintype.card (RepeatMachine.Control 17)),
      run foldProgram (xs.length*(16*w+20)+5) middle=some r ∧
      r.final.tapes 5=frame (binary w xs.sum) ∧
      r.final.tapes 0=CompetitorCountFold.raw b xs ∧
      r.steps=xs.length*(16*w+20)+5 := by
  obtain ⟨base,hr,h5,h0,hs⟩ := CompetitorCountEntry.entry_run b w xs hw hx hfit
  let extra : Fin 2 → List Bool := fun i => middle (i.natAdd 9)
  have hrun := TapeEmbedding.run_embed CompetitorCountEntry.machine (fun _ : Fin 2 => 0) extra _ _ base hr
  have hi : TapeEmbedding.config (fun _ : Fin 2 => 0) extra
      (initialConfiguration CompetitorCountEntry.machine (CompetitorCountEntry.input b w xs))=
      initialConfiguration foldProgram middle := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [TapeEmbedding.config,initialConfiguration,Fin.addCases_left] using (hm j).symm
      · simp only [TapeEmbedding.config,initialConfiguration,Fin.addCases_right,extra]
  rw [hi] at hrun
  exact ⟨TapeEmbedding.receipt (fun _ : Fin 2 => 0) extra base,hrun,h5,h0,hs⟩

theorem producer_run (b w : ℕ) (xs : List ℕ)
    (hw : b≤w) (hx : ∀ x∈xs,x<2^b) (hfit : xs.sum<2^w) :
    ∃ r : ExecutionReceipt 11 (6+(2+Fintype.card (RepeatMachine.Control 17))),
      run machine (budget w xs.length) (input b w xs)=some r ∧
      r.final.tapes 5=frame (binary w xs.sum) ∧
      r.final.tapes 0=CompetitorCountFold.raw b xs ∧
      r.steps≤budget w xs.length := by
  obtain ⟨middle,hzero,hm⟩ := zero_ready b w xs
  obtain ⟨zero,hz,hzt,hzh,hzs⟩ := hzero
  obtain ⟨fold,hf,hf5,hf0,hfs⟩ := fold_run b w xs middle hm hw hx hfit
  have he : Composition.restart zero.final foldProgram.start=initialConfiguration foldProgram middle := by
    apply configuration_ext
    · rfl
    · exact funext hzh
    · exact hzt
  have hf' : runFrom foldProgram (xs.length*(16*w+20)+5)
      (Composition.restart zero.final foldProgram.start)=some fold := by
    rw [he]
    exact hf
  have hall := Composition.run_join zeroProgram foldProgram (4*w+4) (xs.length*(16*w+20)+5)
    _ zero fold hz hf'
  have ht : (4*w+4)+1+(xs.length*(16*w+20)+5)=budget w xs.length := by unfold budget; omega
  rw [ht] at hall
  refine ⟨Composition.joinedReceipt zero fold,hall,hf5,hf0,?_⟩
  change zero.steps+1+fold.steps≤budget w xs.length
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CompetitorCountProducer
