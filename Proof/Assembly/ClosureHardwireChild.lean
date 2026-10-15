import Proof.Assembly.FinalNaturalHardwireScoreInputs
import Proof.Assembly.FinalNaturalHardwireWeightDock

/-! A.12's physical hardwired child, assembled from the existing native
weight, frozen-score and target workers. Runtime membership and assignment
masks remain inputs; they are different words. All counters and workspace
are explicit, and the machine does not depend on the gate or assignment. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.HardwireChild
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation RepairSource RepairSource.CloseoutFinal VerifierDecoding
open SupplierPipeline SupplierEstimator
open C10NaturalHardwireWeights (weightWord gateItems)

noncomputable def scoreTarget := Composition.machine C10NaturalHardwireScoreInputs.machine
  (TapeEmbedding.machine 5 C10NaturalHardwireTarget.machine)
noncomputable def scoreTargetBudget {q : Nat} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) (w C : Nat) :=
  C10NaturalHardwireScoreInputs.budget (C10NaturalHardwireScore.items live g y) w C + 1 +
    C10NaturalHardwireTarget.budget g.target w

variable {q : Nat} (live : Finset (Fin q)) (g : ExactThresholdGate q)
  (y : BitInput live.card) (tail out : List Bool) (w C D : Nat)
  (hw : ∀ x ∈ C10NaturalHardwireScore.items live g y, natBitLength x.1.natAbs ≤ w)
  (hc : 8*w+12 ≤ C)
  (hp : C10NaturalHardwireScore.positiveSum (C10NaturalHardwireScore.items live g y) < 2^w)
  (hn : CloseoutRowsPoolMinimum.negSum (C10NaturalHardwireScore.items live g y) < 2^w)
  (hD : C10NaturalHardwireScore.loopBudget (C10NaturalHardwireScore.items live g y) w C ≤ D)
  (ht : natBitLength g.target.natAbs ≤ w)
  (hpt : C10NaturalHardwireTarget.pPart g.target
    (CloseoutRowsPoolMinimum.liveSum (C10NaturalHardwireScore.items live g y)) < 2^w)
  (hnt : C10NaturalHardwireTarget.nPart g.target
    (C10NaturalHardwireScore.selectedSum (C10NaturalHardwireScore.items live g y)) < 2^w)

include hw hc hp hn hD ht hpt hnt in
theorem scoreTarget_run : ∃ result : Fin 44 → List Bool,
    Step scoreTarget (scoreTargetBudget live g y w C)
      (C10NaturalHardwireScoreInputs.heads out 0 0)
      (C10NaturalHardwireScoreInputs.data (exactWord g++tail)
        (List.ofFn (C10NaturalHardwireScore.frozenMask live y)) out w C D q 0 0)
      (C10NaturalHardwireScoreInputs.heads
        (out++intWord (C10SupplierRowInput.hardwire live g y).target) (exactWord g).length q)
      result ∧ result 0=exactWord g++tail ∧
      result 34=out++intWord (C10SupplierRowInput.hardwire live g y).target := by
  have first := C10NaturalHardwireScoreInputs.hardwire_scores live g y tail [] out w C D hw hc hp hn hD
  simp only [List.append_nil] at first
  obtain ⟨result,last,hs,ho⟩ := C10NaturalHardwireTarget.hardwire_run live g y
    (weightWord g) tail out w C ht hc hpt hnt
  have last := last.embed (![q,0,0,1,0] : Fin 5 → Nat)
    (C10NaturalHardwireScoreInputs.extra (List.ofFn (C10NaturalHardwireScore.frozenMask live y)) C D q)
  have hin : Fin.addCases (motive:=fun _=>Nat) (C10NaturalHardwireTarget.heads (weightWord g).length out)
      (![q,0,0,1,0] : Fin 5 → Nat) = C10NaturalHardwireScoreInputs.heads out (weightWord g).length q := by
    funext i; fin_cases i <;> rfl
  have hout : Fin.addCases (motive:=fun _=>Nat)
      (C10NaturalHardwireTarget.heads ((weightWord g).length+(intWord g.target).length)
        (out++intWord (C10SupplierRowInput.hardwire live g y).target))
      (![q,0,0,1,0] : Fin 5 → Nat) =
      C10NaturalHardwireScoreInputs.heads (out++intWord (C10SupplierRowInput.hardwire live g y).target)
        (exactWord g).length q := by
    have he : (weightWord g).length+(intWord g.target).length=(exactWord g).length := by
      simp only [weightWord,exactWord,List.length_append]
    rw [he]
    funext i; fin_cases i <;> rfl
  have source : weightWord g++intWord g.target++tail=exactWord g++tail := rfl
  rw [source] at last hs
  have joined := first.seq ((last.congr_in hin rfl).congr hout rfl)
  exact ⟨_,joined,hs,ho⟩

def weightSlots : Fin 6 → Fin 48 := ![0,44,34,45,46,47]
def resetWeights : Fin 5 → Bool := fun i=>decide (i=0 ∨ i=3)
noncomputable def weights := RecoveryFocus.machine weightSlots
  (MaskedReset.machine C10NaturalHardwireWeights.loop resetWeights)
noncomputable def machine := Composition.machine weights (TapeEmbedding.machine 4 scoreTarget)
def extra (backing membership : List Bool) (q E : Nat) : Fin 4 → List Bool :=
  ![backing,membership,CompareMachine.word q,List.replicate E false]
def heads (out : List Bool) (pos mpos : Nat) : Fin 48 → Nat :=
  Fin.addCases (motive:=fun _=>Nat) (C10NaturalHardwireScoreInputs.heads out pos mpos) (![0,0,1,0] : Fin 4 → Nat)
noncomputable def data (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) (tail backing out : List Bool) (w C D E : Nat) : Fin 48 → List Bool :=
  Fin.addCases (motive:=fun _=>List Bool)
    (C10NaturalHardwireScoreInputs.data (exactWord g++tail)
      (List.ofFn (C10NaturalHardwireScore.frozenMask live y)) out w C D q 0 0)
    (extra backing (CloseoutRowsGateSupport.gateMembers live) q E)
noncomputable def budget := 2*C10NaturalHardwireWeights.loopBudget (gateItems g live)+2+1+
  scoreTargetBudget live g y w C

theorem weights_run (backing : List Bool) (E : Nat)
    (hE : C10NaturalHardwireWeights.loopBudget (gateItems g live)≤E) :
    Step weights (2*C10NaturalHardwireWeights.loopBudget (gateItems g live)+2)
      (heads out 0 0) (data live g y tail backing out w C D E)
      (heads (out++weightWord (C10SupplierRowInput.hardwire live g y)) 0 0)
      (data live g y tail (CloseoutRowsPoolWeight.saved (gateItems g live) backing)
        (out++weightWord (C10SupplierRowInput.hardwire live g y)) w C D E) := by
  have wr := C10NaturalHardwireWeightDock.weight_step g live y [] tail backing out
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at wr
  have actual := (wr.mask resetWeights (by intro j hj;fin_cases j <;> first | rfl | contradiction) hE).focus
    weightSlots (by decide) (heads out 0 0) (data live g y tail backing out w C D E)
  refine (actual.congr_in
    (dockH_existing weightSlots _ _ (by intro j;fin_cases j <;> rfl))
    (install_existing weightSlots _ _ (by intro j;fin_cases j <;> rfl))).congr ?_ ?_
  · apply funext
    intro i
    fin_cases i <;> first
      | exact dockH_slot weightSlots (by decide) _ _ 0
      | exact dockH_slot weightSlots (by decide) _ _ 1
      | exact dockH_slot weightSlots (by decide) _ _ 2
      | exact dockH_slot weightSlots (by decide) _ _ 3
      | exact dockH_slot weightSlots (by decide) _ _ 4
      | exact dockH_slot weightSlots (by decide) _ _ 5
      | exact dockH_other weightSlots _ _ _ (by decide)
  · apply HierarchyAllocation.install_eq weightSlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl)

include hw hc hp hn hD ht hpt hnt in
theorem child_run (backing : List Bool) (E : Nat)
    (hE : C10NaturalHardwireWeights.loopBudget (gateItems g live)≤E) :
    ∃ result : Fin 48 → List Bool,
      Step machine (budget live g y w C) (heads out 0 0)
        (data live g y tail backing out w C D E)
        (heads (out++exactWord (C10SupplierRowInput.hardwire live g y)) (exactWord g).length q) result ∧
      result 0=exactWord g++tail ∧ result 34=out++exactWord (C10SupplierRowInput.hardwire live g y) := by
  have first := weights_run live g y tail out w C D backing E hE
  obtain ⟨result,last,hs,ho⟩ := scoreTarget_run live g y tail
    (out++weightWord (C10SupplierRowInput.hardwire live g y)) w C D hw hc hp hn hD ht hpt hnt
  have last := last.embed (![0,0,1,0] : Fin 4 → Nat)
    (extra (CloseoutRowsPoolWeight.saved (gateItems g live) backing)
      (CloseoutRowsGateSupport.gateMembers live) q E)
  have joined := first.seq last
  have word : (out++weightWord (C10SupplierRowInput.hardwire live g y))++
      intWord (C10SupplierRowInput.hardwire live g y).target =
      out++exactWord (C10SupplierRowInput.hardwire live g y) := by
    simp only [exactWord,weightWord,List.append_assoc]
  refine ⟨_,joined.congr ?_ rfl,hs,ho.trans word⟩
  exact congrArg (fun output=>heads output (exactWord g).length q) word

end NearCubicWires.P1Closure.HardwireChild
