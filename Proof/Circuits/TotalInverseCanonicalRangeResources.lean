import Proof.Circuits.TotalInverseCanonicalCompilerQuantitativeFrontier
import Proof.Circuits.TotalInverseCanonicalCompiledBodyRun

/-! # Canonical structural-callee and range resources

This module freezes the six width consumers of the guarded structural atom
range.  The compiler-dependent callee width is separated exactly from the
same callee at compiler width zero; the remaining five range heads are kept at
their actual definitions.
-/

namespace NearCubicWires.TotalInverseCanonicalRangeResources

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedRunnerBudgetDomination
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.TotalInverseCanonicalCompilerResources
open NearCubicWires.TotalInverseCanonicalCompilerRuns
open NearCubicWires.ValidatorPolynomialDomination

open private structuralFormulaPipelineBitBudgets from
  Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

/-! ## 1. The compiler-dependent callee head -/

set_option maxHeartbeats 800000 in
-- Normalizing the six-entry public pipeline budget exposes one max identity.
theorem structuralAtomCalleeBits_le_compiler_max_zero
    (machineInputLength : ℕ) (outputs : List ℕ)
    (width count bound index compilerBits : ℕ) :
    structuralAtomCalleeBits machineInputLength outputs width count bound index
        compilerBits ≤
      max compilerBits
        (structuralAtomCalleeBits machineInputLength outputs width count bound
          index 0) := by
  simp only [structuralAtomCalleeBits, occurrenceStageBits,
    structuralFormulaPipelineBits, structuralFormulaPipelineBitBudgets,
    preserveRightBits, List.foldr_cons, List.foldr_nil]
  omega

noncomputable def totalInverseCanonicalStructuralCalleeLocalBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) : ℕ :=
  structuralAtomCalleeBits target
    (projectionRunnerCallOutputs pcp
      (inverseScheduleInput contracts clockDepth machine advantageExponent
        target))
    (pcp.nativeWidth
      (inverseScheduleLength contracts clockDepth advantageExponent target))
    (pcp.queryCount
      (inverseScheduleLength contracts clockDepth advantageExponent target))
    (inverseScheduleBound contracts clockDepth advantageExponent target)
    index 0

noncomputable def totalInverseCanonicalStructuralCalleeBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) : ℕ :=
  structuralAtomCalleeBits target
    (projectionRunnerCallOutputs pcp
      (inverseScheduleInput contracts clockDepth machine advantageExponent
        target))
    (pcp.nativeWidth
      (inverseScheduleLength contracts clockDepth advantageExponent target))
    (pcp.queryCount
      (inverseScheduleLength contracts clockDepth advantageExponent target))
    (inverseScheduleBound contracts clockDepth advantageExponent target)
    index
    (totalInverseCanonicalCompilerBits contracts clockDepth machine
      advantageExponent pcp target index)

theorem totalInverseCanonicalStructuralCalleeBits_le
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ) :
    totalInverseCanonicalStructuralCalleeBits contracts clockDepth machine
        advantageExponent pcp target index ≤
      max
        (totalInverseCanonicalCompilerBits contracts clockDepth machine
          advantageExponent pcp target index)
        (totalInverseCanonicalStructuralCalleeLocalBits contracts clockDepth
          machine advantageExponent pcp target index) := by
  exact structuralAtomCalleeBits_le_compiler_max_zero _ _ _ _ _ _ _

/-! ## 2. The exact six-way range -/

noncomputable def totalInverseCanonicalRangeBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) : ℕ :=
  max 1 <| max (natBitLength target) <| max
    (generatedBalancedRangeRequiredBits target
      (inverseAtomCount contracts clockDepth machine advantageExponent pcp
        target)
      (inverseAtomContext contracts clockDepth machine advantageExponent pcp
        target)) <| max
    (natBitLength
      (encodeBalancedList
        (balancedRangeRequestAtoms target
          (inverseAtomContext contracts clockDepth machine advantageExponent pcp
            target)
          0
          (inverseAtomCount contracts clockDepth machine advantageExponent pcp
            target)))) <| max
    (balancedCallRequiredBits
      (fun request =>
        structuralAtomValue pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            target)
          (inverseScheduleBound contracts clockDepth advantageExponent target)
          (structuralAtomRequestIndex request))
      (balancedRangeRequestAtoms target
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          target)
        0
        (inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target)))
    ((Finset.range
      (inverseAtomCount contracts clockDepth machine advantageExponent pcp
        target)).sup
      (totalInverseCanonicalStructuralCalleeBits contracts clockDepth machine
        advantageExponent pcp target))

theorem totalInverseCanonicalRangeBits_positive
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    1 ≤ totalInverseCanonicalRangeBits contracts clockDepth machine
      advantageExponent pcp target := by
  exact le_max_left _ _

theorem totalInverseCanonicalRangeBits_length
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    natBitLength target ≤ totalInverseCanonicalRangeBits contracts clockDepth
      machine advantageExponent pcp target := by
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem totalInverseCanonicalRangeBits_generated
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    generatedBalancedRangeRequiredBits target
        (inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target)
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          target) ≤
      totalInverseCanonicalRangeBits contracts clockDepth machine
        advantageExponent pcp target := by
  unfold totalInverseCanonicalRangeBits
  omega

theorem totalInverseCanonicalRangeBits_list
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    natBitLength
        (encodeBalancedList
          (balancedRangeRequestAtoms target
            (inverseAtomContext contracts clockDepth machine advantageExponent
              pcp target)
            0
            (inverseAtomCount contracts clockDepth machine advantageExponent
              pcp target))) ≤
      totalInverseCanonicalRangeBits contracts clockDepth machine
        advantageExponent pcp target := by
  unfold totalInverseCanonicalRangeBits
  omega

theorem totalInverseCanonicalRangeBits_call
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    balancedCallRequiredBits
        (fun request =>
          structuralAtomValue pcp
            (inverseScheduleInput contracts clockDepth machine
              advantageExponent target)
            (inverseScheduleBound contracts clockDepth advantageExponent target)
            (structuralAtomRequestIndex request))
        (balancedRangeRequestAtoms target
          (inverseAtomContext contracts clockDepth machine advantageExponent pcp
            target)
          0
          (inverseAtomCount contracts clockDepth machine advantageExponent pcp
            target)) ≤
      totalInverseCanonicalRangeBits contracts clockDepth machine
        advantageExponent pcp target := by
  unfold totalInverseCanonicalRangeBits
  omega

theorem totalInverseCanonicalRangeBits_callee
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target index : ℕ)
    (hindex : index <
      inverseAtomCount contracts clockDepth machine advantageExponent pcp
        target) :
    totalInverseCanonicalStructuralCalleeBits contracts clockDepth machine
        advantageExponent pcp target index ≤
      totalInverseCanonicalRangeBits contracts clockDepth machine
        advantageExponent pcp target := by
  unfold totalInverseCanonicalRangeBits
  have hsup := Finset.le_sup
    (f := totalInverseCanonicalStructuralCalleeBits contracts clockDepth machine
      advantageExponent pcp target)
    (Finset.mem_range.mpr hindex)
  omega

/-! ## 3. Polynomial closure of the range -/

def CanonicalRangeLocalHeadsDominated
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (degree : ℕ) : Prop :=
  let measureOf := fun target : ℕ => max 1 target
  Dominated (fun target => natBitLength target) measureOf degree ∧
    Dominated (fun target =>
      generatedBalancedRangeRequiredBits target
        (inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target)
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          target)) measureOf degree ∧
    Dominated (fun target =>
      natBitLength
        (encodeBalancedList
          (balancedRangeRequestAtoms target
            (inverseAtomContext contracts clockDepth machine advantageExponent
              pcp target)
            0
            (inverseAtomCount contracts clockDepth machine advantageExponent
              pcp target)))) measureOf degree ∧
    Dominated (fun target =>
      balancedCallRequiredBits
        (fun request =>
          structuralAtomValue pcp
            (inverseScheduleInput contracts clockDepth machine
              advantageExponent target)
            (inverseScheduleBound contracts clockDepth advantageExponent target)
            (structuralAtomRequestIndex request))
        (balancedRangeRequestAtoms target
          (inverseAtomContext contracts clockDepth machine advantageExponent pcp
            target)
          0
          (inverseAtomCount contracts clockDepth machine advantageExponent pcp
            target))) measureOf degree ∧
    (∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalStructuralCalleeLocalBits contracts clockDepth
          machine advantageExponent pcp) coefficient degree)

theorem totalInverseCanonicalRangeBits_dominated
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (degree : ℕ)
    (hcompiler : ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalCompilerBits contracts clockDepth machine
          advantageExponent pcp) coefficient degree)
    (hlocals : CanonicalRangeLocalHeadsDominated contracts clockDepth machine
      advantageExponent pcp degree) :
    ∃ coefficient, ∀ target,
      PolyBounded
        (totalInverseCanonicalRangeBits contracts clockDepth machine
          advantageExponent pcp target)
        (max 1 target) coefficient degree := by
  rcases hcompiler with ⟨compilerCoefficient, hcompiler⟩
  rcases hlocals with
    ⟨hlength, hgenerated, hlist, hcall, localCoefficient, hlocal⟩
  rcases hlength with ⟨lengthCoefficient, hlength⟩
  rcases hgenerated with ⟨generatedCoefficient, hgenerated⟩
  rcases hlist with ⟨listCoefficient, hlist⟩
  rcases hcall with ⟨callCoefficient, hcall⟩
  let calleeCoefficient := max compilerCoefficient localCoefficient
  let coefficient := max 1 <| max lengthCoefficient <| max
    generatedCoefficient <| max listCoefficient <| max callCoefficient
    calleeCoefficient
  refine ⟨coefficient, fun target => ?_⟩
  have hcallee : ∀ index,
      index < inverseAtomCount contracts clockDepth machine advantageExponent
          pcp target →
      PolyBounded
        (totalInverseCanonicalStructuralCalleeBits contracts clockDepth machine
          advantageExponent pcp target index)
        (max 1 target) calleeCoefficient degree := by
    intro index hindex
    exact ((hcompiler target index hindex).max
      (hlocal target index hindex)).mono
        (totalInverseCanonicalStructuralCalleeBits_le contracts clockDepth
          machine advantageExponent pcp target index)
  have hsup : PolyBounded
      ((Finset.range
        (inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target)).sup
        (totalInverseCanonicalStructuralCalleeBits contracts clockDepth machine
          advantageExponent pcp target))
      (max 1 target) calleeCoefficient degree := by
    unfold PolyBounded
    apply Finset.sup_le
    intro index hindex
    exact hcallee index (Finset.mem_range.mp hindex)
  have hone : PolyBounded 1 (max 1 target) 1 degree :=
    polyBounded_const 1 _ _
  have hall := hone.max ((hlength target).max
    ((hgenerated target).max ((hlist target).max
      ((hcall target).max hsup))))
  have hall' : PolyBounded
      (max 1 (max (natBitLength target)
        (max
          (generatedBalancedRangeRequiredBits target
            (inverseAtomCount contracts clockDepth machine advantageExponent
              pcp target)
            (inverseAtomContext contracts clockDepth machine advantageExponent
              pcp target))
          (max
            (natBitLength
              (encodeBalancedList
                (balancedRangeRequestAtoms target
                  (inverseAtomContext contracts clockDepth machine
                    advantageExponent pcp target)
                  0
                  (inverseAtomCount contracts clockDepth machine
                    advantageExponent pcp target))))
            (max
              (balancedCallRequiredBits
                (fun request =>
                  structuralAtomValue pcp
                    (inverseScheduleInput contracts clockDepth machine
                      advantageExponent target)
                    (inverseScheduleBound contracts clockDepth
                      advantageExponent target)
                    (structuralAtomRequestIndex request))
                (balancedRangeRequestAtoms target
                  (inverseAtomContext contracts clockDepth machine
                    advantageExponent pcp target)
                  0
                  (inverseAtomCount contracts clockDepth machine
                    advantageExponent pcp target)))
              ((Finset.range
                (inverseAtomCount contracts clockDepth machine
                  advantageExponent pcp target)).sup
                (totalInverseCanonicalStructuralCalleeBits contracts clockDepth
                  machine advantageExponent pcp target)))))))
      (max 1 target) coefficient degree := hall.coefficient_mono (by
    dsimp only [coefficient, calleeCoefficient]
    omega)
  simpa only [totalInverseCanonicalRangeBits] using hall'

end NearCubicWires.TotalInverseCanonicalRangeResources
