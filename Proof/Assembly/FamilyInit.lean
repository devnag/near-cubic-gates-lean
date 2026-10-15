import Proof.Assembly.GeneratedPrefixRecipe

/-! A concrete two-stage generator: descriptor/scalar production followed by
one blank-bank initializer. The initializer is uniform in runtime values.
Its certified physical interface and cost are consumed by the front proof.
No input or execution witness is inserted into the literal theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace FamilyInitGenerator
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NativeRecipes

/-- Values are runtime data, not parameters of the initializer's code.
The front also physically computes the N*b driver. -/
structure Scalars where
  S : Nat
  R : Nat
  B : Nat
  b : Nat
  v : Nat
  N : Nat

@[irreducible] noncomputable def initTapes (a : WilliamsAlgorithm) : Nat := r_tapes a+7

def drivers (m : Scalars) : Fin 7 → List Bool :=
  ![CompareMachine.word m.S, CompareMachine.word m.R,
    CompareMachine.word m.B, CompareMachine.word m.b,
    CompareMachine.word m.v, CompareMachine.word m.N,
    CompareMachine.word (m.N*m.b)]

noncomputable def sourcePort (a : WilliamsAlgorithm) : Fin (r_tapes a) :=
  ⟨P1TopDownPaidPayload.tapes a+3, by unfold r_tapes; omega⟩

noncomputable def entryH (a : WilliamsAlgorithm) : Fin (initTapes a) → Nat := by
  unfold initTapes
  exact Fin.addCases (fun _ : Fin (r_tapes a) => 0) (fun _ : Fin 7 => 1)

/-- Family destinations are genuinely blank, except the retained descriptor
stream already at its final source port. All seven numeric drivers are paid
outputs of the preceding stage. No private log occupies a required-empty port. -/
noncomputable def entry (a : WilliamsAlgorithm) (m : Scalars) (D : List Bool) :
    Fin (initTapes a) → List Bool := by
  unfold initTapes
  exact Fin.addCases (fun i : Fin (r_tapes a) => if i=sourcePort a then D else []) (drivers m)

noncomputable def familyBank (a : WilliamsAlgorithm) (m : Scalars) (D : List Bool) :
    Fin (r_tapes a) → List Bool :=
  Fin.addCases
    (Fin.addCases (P1TopDownPaidReusable.bank a D m.S m.R m.B [])
      (fun _ : Fin 1 => CompareMachine.word m.N))
    (P1TopDownPaidFamilySum.extra m.b m.v m.N)

noncomputable def exitH (a : WilliamsAlgorithm) : Fin (initTapes a) → Nat := by
  unfold initTapes
  exact Fin.addCases (r_inputH a [] 0 0 0 0) (fun _ : Fin 7 => 1)

noncomputable def exitT (a : WilliamsAlgorithm) (m : Scalars) (D : List Bool) :
    Fin (initTapes a) → List Bool := by
  unfold initTapes
  exact Fin.addCases (familyBank a m D) (drivers m)

/-- A fixed linear allowance for all blank allocation, copies, framing and
head restoration. It is charged once per whole generated family. -/
noncomputable def initFuel (a : WilliamsAlgorithm) (m : Scalars) : Nat :=
  1000*(r_tapes a+1)*(m.S+m.R+m.B+m.b+m.v+m.N+m.N*m.b+1)

structure Initializer (a : WilliamsAlgorithm) where
  states : Nat
  machine : Machine (initTapes a) states
  run : ∀ (m : Scalars) (D : List Bool),
    Step machine (initFuel a m) (entryH a) (entry a m D) (exitH a) (exitT a m D)

abbrev InitializerFamily := (a : WilliamsAlgorithm) → Initializer a

/-- A fixed focus: family ports retain their numbers; the seven drivers are
scratch ports after the nine input fields and denominator. -/
noncomputable def initSlots (a : WilliamsAlgorithm) (scratch : Nat) :
    Fin (initTapes a) → Fin (NativeFamilyGenerator.tapes a (7+scratch)) :=
  fun i => ⟨if i.val < r_tapes a then i.val else i.val+10, by
    have h := i.isLt
    unfold initTapes at h
    unfold NativeFamilyGenerator.tapes
    split_ifs <;> omega⟩

/-- Prefix code starts at the actual nine-word Input bank. Its result carries
semantic fields and its complete physical exit, before initialization. -/
structure PrefixCode where
  printer : WilliamsAlgorithm
  scratch : Nat
  states : Nat
  machine : Machine (NativeFamilyGenerator.tapes printer (7+scratch)) states
  policy : NativeFamilyGenerator.Policy
  result : NativeFamilyGenerator.Input → NativeFamilyGenerator.Result (NativeFamilyGenerator.tapes printer (7+scratch))

noncomputable def scalars (g : PrefixCode) (i : NativeFamilyGenerator.Input) : Scalars :=
  let r := g.result i
  ⟨r.S,r.R,r.B,r.rowWidth,i.recordWidth,r.ds.length⟩

noncomputable def descriptor (g : PrefixCode) (i : NativeFamilyGenerator.Input) : List Bool :=
  (g.result i).ds.flatMap (P1TopDownPaidReusable.Datum.word g.printer)

/-- The only assembled code is the actual front followed by this fixed
physical initializer. Result banks are their actual common endpoints. -/
noncomputable def assemble (g : PrefixCode) (init : Initializer g.printer) : NativeFamilyGenerator.Data :=
  { printer := g.printer
    scratch := 7+g.scratch
    states := _
    machine := Composition.machine g.machine
      (RecoveryFocus.machine (initSlots g.printer g.scratch) init.machine)
    policy := g.policy
    result := fun i =>
      { g.result i with
        fuel := (g.result i).fuel+1+initFuel g.printer (scalars g i)
        H := dockH (initSlots g.printer g.scratch) (g.result i).H (exitH g.printer)
        A := install (initSlots g.printer g.scratch) (g.result i).A
          (exitT g.printer (scalars g i) (descriptor g i)) } }

/-- Explicit physical junction required of front output; this is not an
assumed input in the final theorem. The front implementation proves it from
its real Step. The denominator lies outside the initializer focus. -/
noncomputable def PrefixReady (g : PrefixCode) (i : NativeFamilyGenerator.Input) : Prop :=
  (∀ j, (g.result i).H (initSlots g.printer g.scratch j)=entryH g.printer j) ∧
  (∀ j, (g.result i).A (initSlots g.printer g.scratch j)=
    entry g.printer (scalars g i) (descriptor g i) j) ∧
  (g.result i).H (NativeFamilyGenerator.denominatorPort g.printer (7+g.scratch))=0 ∧
  (g.result i).A (NativeFamilyGenerator.denominatorPort g.printer (7+g.scratch))=
    RepairOrdinary.frame (natWord (g.result i).denominator)

/-- This certificate keeps the full current correctness obligation attached
to the concrete front, including active/terminal behavior and the initializer
charge. Its universally quantified initializer has a fixed exact entry/exit
and fuel, so no compatible implementation choice is guessed here. -/
structure Prefix (sources : EightSources) where
  code : PrefixCode
  correct : ∀ init : Initializer code.printer, NativeFamilyGenerator.Correct sources (assemble code init)

abbrev GlobalPrefix := (sources : EightSources) → (gamma : Real) →
  (hg : 0<gamma) → (hh : gamma<1/2) → (p : Parameters sources gamma) → Prefix sources

noncomputable def globalData (initializers : InitializerFamily) (front : GlobalPrefix) :
    GeneratedPrefixRecipes.GlobalData :=
  fun sources gamma hg hh p =>
    let g := front sources gamma hg hh p
    assemble g.code (initializers g.code.printer)

theorem globalCorrect (initializers : InitializerFamily) (front : GlobalPrefix) :
    GeneratedPrefixRecipes.GlobalCorrect (globalData initializers front) := by
  intro sources gamma hg hh p
  exact (front sources gamma hg hh p).correct
    (initializers (front sources gamma hg hh p).code.printer)

end FamilyInitGenerator
