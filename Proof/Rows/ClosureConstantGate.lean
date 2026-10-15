import Proof.Rows.RowsPoolRequestWriter

/-! The missing X/C frozen-gate computation: retain the original arity,
zero live weights and shift the strict threshold by the minimum live score.
Only original fields, membership and bounded workspace are inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.ConstantGate
open LocalBitMultitape RepairOrdinary RecoveryRootRound RecoveryExecution ExtDecompositionBatch
open RepairRepresentation RepairSource CloseoutFinal VerifierDecoding
open SupplierPipeline CloseoutRowsPoolWeight

noncomputable def score := C10NaturalHardwireScoreInputs.negative
noncomputable def scoreTarget := Composition.machine score (TapeEmbedding.machine 5 C10NaturalHardwireTarget.machine)
def scoreBudget (xs : List Item) (w C : Nat) := CloseoutRowsPoolMinimum.loopBudget xs w C
def scoreTargetBudget (xs : List Item) (z : Int) (w C : Nat) :=
  scoreBudget xs w C+1+C10NaturalHardwireTarget.budget z w

theorem score_run (xs : List Item) (tail out : List Bool) (w C D : Nat)
    (hw : ∀ x∈xs,natBitLength x.1.natAbs≤w) (hc : 8*w+12≤C)
    (hn : CloseoutRowsPoolMinimum.negSum xs<2^w) :
    Step score (scoreBudget xs w C) (C10NaturalHardwireScoreInputs.heads out 0 0)
      (C10NaturalHardwireScoreInputs.data (word xs++tail) (mask xs) out w C D xs.length 0 0)
      (C10NaturalHardwireScoreInputs.heads out (word xs).length xs.length)
      (C10NaturalHardwireScoreInputs.data (word xs++tail) (mask xs) out w C D xs.length
        0 (CloseoutRowsPoolMinimum.liveSum xs)) := by
  obtain ⟨r,hr,hf,_⟩ := CloseoutRowsPoolMinimum.minimum_run xs [] tail [] [] w C 0 hw hc (by simpa using hn)
  have base := CloseoutFinalPool.step_of_repeat CloseoutRowsPoolMinimum.body (fun _ _=>true)
    (CloseoutRowsPoolMinimum.loopBudget xs w C)
    ⟨CloseoutRowsPoolMinimum.body.start,CloseoutRowsPoolMinimum.heads 0 0,
      CloseoutRowsPoolMinimum.data (word xs++tail) (mask xs) w C 0⟩
    ⟨CloseoutRowsPoolMinimum.body.start,CloseoutRowsPoolMinimum.heads (word xs).length xs.length,
      CloseoutRowsPoolMinimum.data (word xs++tail) (mask xs) w C (CloseoutRowsPoolMinimum.liveSum xs)⟩
    xs.length 1 1 r
    (by simpa only [CloseoutRowsPoolMinimum.loop,CloseoutRowsPoolMinimum.cfg,List.nil_append,List.append_nil,List.length_nil] using hr)
    (by simpa only [CloseoutRowsPoolMinimum.loop,CloseoutRowsPoolMinimum.cfg,List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] using hf)
  have call := base.dock C10NaturalHardwireScoreInputs.negativeSlots (by decide)
    (C10NaturalHardwireScoreInputs.heads out 0 0)
    (C10NaturalHardwireScoreInputs.data (word xs++tail) (mask xs) out w C D xs.length 0 0)
    (by intro j;fin_cases j <;>rfl) (by intro j;fin_cases j <;>rfl)
  refine call.congr ?_ ?_
  · funext i
    by_cases hi : ∃ j,C10NaturalHardwireScoreInputs.negativeSlots j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [dockH_slot _ (by decide)]
      fin_cases j <;>rfl
    · rw [dockH_other _ _ _ i (by simpa using hi)]
      have h0 : i≠0 := fun h=>hi ⟨0,h.symm⟩
      have h39 : i≠39 := fun h=>hi ⟨13,h.symm⟩
      simp only [C10NaturalHardwireScoreInputs.heads,if_neg h0,if_neg h39]
  · apply HierarchyAllocation.install_eq C10NaturalHardwireScoreInputs.negativeSlots (by decide)
    · intro j;fin_cases j <;>rfl
    · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 14 rfl)

theorem scoreTarget_run (xs : List Item) (z : Int) (tail out : List Bool) (w C D : Nat)
    (hw : ∀ x∈xs,natBitLength x.1.natAbs≤w) (hc : 8*w+12≤C)
    (hn : CloseoutRowsPoolMinimum.negSum xs<2^w) (hz : natBitLength z.natAbs≤w)
    (hp : C10NaturalHardwireTarget.pPart z (CloseoutRowsPoolMinimum.liveSum xs)<2^w)
    (hneg : C10NaturalHardwireTarget.nPart z 0<2^w) :
    ∃ result : Fin 44 → List Bool,
      Step scoreTarget (scoreTargetBudget xs z w C) (C10NaturalHardwireScoreInputs.heads out 0 0)
        (C10NaturalHardwireScoreInputs.data (word xs++intWord z++tail) (mask xs) out w C D xs.length 0 0)
        (C10NaturalHardwireScoreInputs.heads (out++intWord (z+CloseoutRowsPoolMinimum.liveSum xs))
          ((word xs).length+(intWord z).length) xs.length) result ∧
      result 0=word xs++intWord z++tail ∧
      result 34=out++intWord (z+CloseoutRowsPoolMinimum.liveSum xs) := by
  have first := score_run xs (intWord z++tail) out w C D hw hc hn
  obtain ⟨result,last,hs,ho⟩ := C10NaturalHardwireTarget.target_run (word xs) tail out z w C 0
    (CloseoutRowsPoolMinimum.liveSum xs) hz hc hp hneg
  simp only [Nat.cast_zero,Int.sub_zero] at last ho
  have last := last.embed (![xs.length,0,0,1,0] : Fin 5 → Nat)
    (C10NaturalHardwireScoreInputs.extra (mask xs) C D xs.length)
  have hi : Fin.addCases (motive:=fun _=>Nat) (C10NaturalHardwireTarget.heads (word xs).length out)
      (![xs.length,0,0,1,0] : Fin 5 → Nat)=
      C10NaturalHardwireScoreInputs.heads out (word xs).length xs.length := by funext i;fin_cases i <;>rfl
  have hf : Fin.addCases (motive:=fun _=>Nat)
      (C10NaturalHardwireTarget.heads ((word xs).length+(intWord z).length)
        (out++intWord (z+CloseoutRowsPoolMinimum.liveSum xs)))
      (![xs.length,0,0,1,0] : Fin 5 → Nat)=
      C10NaturalHardwireScoreInputs.heads (out++intWord (z+CloseoutRowsPoolMinimum.liveSum xs))
        ((word xs).length+(intWord z).length) xs.length := by funext i;fin_cases i <;>rfl
  rw [←List.append_assoc] at first
  exact ⟨_,first.seq ((last.congr_in hi rfl).congr hf rfl),hs,ho⟩

def data (xs : List Item) (z : Int) (tail backing out : List Bool) (w C D E : Nat) : Fin 48 → List Bool :=
  Fin.addCases (motive:=fun _=>List Bool)
    (C10NaturalHardwireScoreInputs.data (word xs++intWord z++tail) (mask xs) out w C D xs.length 0 0)
    (HardwireChild.extra backing (mask xs) xs.length E)
noncomputable def weights := RecoveryFocus.machine HardwireChild.weightSlots
  (MaskedReset.machine CloseoutRowsPoolWeight.loop HardwireChild.resetWeights)
noncomputable def machine := Composition.machine weights (TapeEmbedding.machine 4 scoreTarget)
def budget (xs : List Item) (z : Int) (w C : Nat) :=
  2*CloseoutRowsPoolWeight.loopBudget xs+3+scoreTargetBudget xs z w C

theorem weight_step (xs : List Item) (tail backing out : List Bool) :
    Step CloseoutRowsPoolWeight.loop (CloseoutRowsPoolWeight.loopBudget xs)
      (CloseoutFinalPool.wH 0 0 out)
      (CloseoutFinalPool.wT (word xs++tail) backing out (mask xs) xs.length)
      (CloseoutFinalPool.wH (word xs).length xs.length (out++emitted xs))
      (CloseoutFinalPool.wT (word xs++tail) (saved xs backing) (out++emitted xs) (mask xs) xs.length) := by
  obtain ⟨r,hr,hf,_⟩ := weights_run xs [] tail backing out [] []
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at hr hf
  exact CloseoutFinalPool.step_of_repeat body (fun _ _=>true) (loopBudget xs)
    ⟨body.start,heads 0 0 out,CloseoutRowsPoolWeight.data (word xs++tail) backing out (mask xs)⟩
    ⟨body.start,heads (word xs).length xs.length (out++emitted xs),
      CloseoutRowsPoolWeight.data (word xs++tail) (saved xs backing) (out++emitted xs) (mask xs)⟩
    xs.length 1 1 r hr hf

theorem weights_run (xs : List Item) (z : Int) (tail backing out : List Bool) (w C D E : Nat)
    (hE : CloseoutRowsPoolWeight.loopBudget xs≤E) :
    Step weights (2*CloseoutRowsPoolWeight.loopBudget xs+2)
      (HardwireChild.heads out 0 0) (data xs z tail backing out w C D E)
      (HardwireChild.heads (out++emitted xs) 0 0)
      (data xs z tail (saved xs backing) (out++emitted xs) w C D E) := by
  have wr := weight_step xs (intWord z++tail) backing out
  rw [←List.append_assoc] at wr
  have actual := (wr.mask HardwireChild.resetWeights
    (by intro j hj;fin_cases j <;>first | rfl | contradiction) hE).focus
    HardwireChild.weightSlots (by decide) (HardwireChild.heads out 0 0) (data xs z tail backing out w C D E)
  refine (actual.congr_in
    (dockH_existing _ _ _ (by intro j;fin_cases j <;>rfl))
    (install_existing _ _ _ (by intro j;fin_cases j <;>rfl))).congr ?_ ?_
  · funext i
    fin_cases i <;> first
      | exact dockH_slot HardwireChild.weightSlots (by decide) _ _ 0
      | exact dockH_slot HardwireChild.weightSlots (by decide) _ _ 1
      | exact dockH_slot HardwireChild.weightSlots (by decide) _ _ 2
      | exact dockH_slot HardwireChild.weightSlots (by decide) _ _ 3
      | exact dockH_slot HardwireChild.weightSlots (by decide) _ _ 4
      | exact dockH_slot HardwireChild.weightSlots (by decide) _ _ 5
      | exact dockH_other HardwireChild.weightSlots _ _ _ (by decide)
  · apply HierarchyAllocation.install_eq HardwireChild.weightSlots (by decide)
    · intro j;fin_cases j <;>rfl
    · intro i hi;fin_cases i <;>first | rfl | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl)

theorem run (xs : List Item) (z : Int) (tail backing out : List Bool) (w C D E : Nat)
    (hw : ∀ x∈xs,natBitLength x.1.natAbs≤w) (hc : 8*w+12≤C)
    (hn : CloseoutRowsPoolMinimum.negSum xs<2^w) (hz : natBitLength z.natAbs≤w)
    (hp : C10NaturalHardwireTarget.pPart z (CloseoutRowsPoolMinimum.liveSum xs)<2^w)
    (hneg : C10NaturalHardwireTarget.nPart z 0<2^w)
    (hE : CloseoutRowsPoolWeight.loopBudget xs≤E) :
    ∃ result : Fin 48 → List Bool,
      Step machine (budget xs z w C) (HardwireChild.heads out 0 0)
        (data xs z tail backing out w C D E)
        (HardwireChild.heads (out++emitted xs++intWord (z+CloseoutRowsPoolMinimum.liveSum xs))
          ((word xs).length+(intWord z).length) xs.length) result ∧
      result 0=word xs++intWord z++tail ∧
      result 34=out++emitted xs++intWord (z+CloseoutRowsPoolMinimum.liveSum xs) := by
  have first := weights_run xs z tail backing out w C D E hE
  obtain ⟨result,last,hs,ho⟩ := scoreTarget_run xs z tail (out++emitted xs) w C D hw hc hn hz hp hneg
  have last := last.embed (![0,0,1,0] : Fin 4 → Nat)
    (HardwireChild.extra (saved xs backing) (mask xs) xs.length E)
  exact ⟨_,first.seq last,hs,ho⟩

/-- Literal frozen native request fields, retaining q weight coordinates. -/
theorem constant_fields {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q) :
    CloseoutRowsCircuitBottom.nativeWord (CloseoutRowsUniversal.constantSupportedGate live g)=
      natWord q++emitted (CloseoutRowsPoolMinimum.items g.gate live)++
        intWord (g.gate.threshold-1+CloseoutRowsPoolMinimum.liveSum (CloseoutRowsPoolMinimum.items g.gate live)) := by
  rw [CloseoutRowsPoolWriter.constant_native,CloseoutRowsPoolMinimum.strict_threshold,List.append_assoc]

end NearCubicWires.P1Closure.ConstantGate
