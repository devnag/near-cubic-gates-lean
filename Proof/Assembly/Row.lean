import Proof.Assembly.Header
import Proof.Assembly.Framing

/-! A fixed physical row transaction. The header writer and complete descriptor
framer are closed programs. The three remaining stages are shared ordinary
machines, with explicit full-bank joins and their own paid fuel. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PhysicalRowTransaction
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open FixedLivePackets
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section
namespace Frame
abbrev fields := DatumCopier.datumFields
abbrev heads := DatumCopier.heads
abbrev bank {t : Nat} := @DatumCopier.paddedBank t
abbrev machine := DatumCopier.datumMachine
abbrev budget := DatumCopier.datumBudget
def targetReserve (t reserve : Nat) (i : Fin (t+2)) : Nat :=
  if i.val=t then reserve else 0
end Frame

/-- Chosen with the source-global ordinary code, before every row/input. -/
structure Code (printer : WilliamsAlgorithm) (t : Nat) where
  prepareStates : Nat
  prepare : Machine t prepareStates
  completeStates : Nat
  complete : Machine t completeStates
  cleanupStates : Nat
  cleanup : Machine t cleanupStates
  headerSlots : Fin 440 → Fin t
  headerInjective : Function.Injective headerSlots
  frameSlots : Fin (P1TopDownPaidPayload.tapes printer+2) → Fin t
  frameInjective : Function.Injective frameSlots

def machine {printer : WilliamsAlgorithm} {t : Nat} (c : Code printer t) :=
  Composition.machine c.prepare
    (Composition.machine (RecoveryFocus.machine c.headerSlots ColdHeaderWriter.machine)
      (Composition.machine c.complete
        (Composition.machine (RecoveryFocus.machine c.frameSlots (Frame.machine printer)) c.cleanup)))

/-- Full states at the joins; these are specified by the enclosing runtime input.
They are not precomputed advice: Ready requires the actual producing Steps. -/
structure Banks (printer : WilliamsAlgorithm) (t : Nat) where
  entryH : Fin t → Nat
  entryA : Fin t → List Bool
  headerReserve : Fin 440 → Nat
  descriptorReserve : Nat
  headerH : Fin t → Nat
  headerA : Fin t → List Bool
  frameH : Fin t → Nat
  frameA : Fin t → List Bool
  fieldReserve : Fin (P1TopDownPaidPayload.tapes printer) → Nat
  copyCap : Nat
  exitH : Fin t → Nat
  exitA : Fin t → List Bool
  prepareFuel : Nat
  completeFuel : Nat
  cleanupFuel : Nat

variable {q L t : Nat} (printer : WilliamsAlgorithm) (c : Code printer t)
  (a : DecompositionAlgorithm) (F : Packets.Family q L) (g : Packets.Geometry F)
  (layout : Packets.Layout a F g) (r : Packets.Row F.occurrences L) (hr : r ∈ F.rows)
  (facts : Packets.PacketFacts a F g r) (b : Banks printer t) (out pre tail : List Bool)

def headerInH := dockH c.headerSlots b.headerH (CompactColdFamily.ambientH [] pre)
def headerInA := install c.headerSlots b.headerA (fun i => ZeroPadding.pad (b.headerReserve i) (ColdHeaderWriter.input a F g layout r [] pre tail i))
def headerOutH := dockH c.headerSlots b.headerH (ColdHeaderWriter.finalHeads a F g layout r [] pre tail)
def headerOutA := install c.headerSlots b.headerA (fun i => ZeroPadding.pad (b.headerReserve i) (ColdHeaderWriter.finalTapes a F g layout r [] pre tail i))
def frameInH := dockH c.frameSlots b.frameH (Frame.heads _ out)
def frameInA := install c.frameSlots b.frameA
  (fun i => ZeroPadding.pad (Frame.targetReserve (P1TopDownPaidPayload.tapes printer) b.descriptorReserve i)
    (Frame.bank b.fieldReserve (Frame.fields printer (Packets.datum a F g layout r hr facts)) out b.copyCap i))
def frameOutH := dockH c.frameSlots b.frameH
  (Frame.heads _ (out++(Packets.datum a F g layout r hr facts).word printer))
def frameOutA := install c.frameSlots b.frameA
  (fun i => ZeroPadding.pad (Frame.targetReserve (P1TopDownPaidPayload.tapes printer) b.descriptorReserve i)
    (Frame.bank b.fieldReserve (Frame.fields printer (Packets.datum a F g layout r hr facts))
      (out++(Packets.datum a F g layout r hr facts).word printer) b.copyCap i))

def budget := b.prepareFuel+1+(ColdHeaderWriter.budget a F g layout r+1+
  (b.completeFuel+1+(Frame.budget printer (Packets.datum a F g layout r hr facts)+1+b.cleanupFuel)))

/-- Specific remaining physical joins. Header production and descriptor framing
are absent because run below proves them for this fixed code. -/
def Ready : Prop :=
  (∀ i, 2*(Frame.fields printer (Packets.datum a F g layout r hr facts) i).length+1 ≤ b.copyCap) ∧
  Step c.prepare b.prepareFuel b.entryH b.entryA
    (headerInH printer c b pre) (headerInA printer c a F g layout r b pre tail) ∧
  Step c.complete b.completeFuel
    (headerOutH printer c a F g layout r b pre tail) (headerOutA printer c a F g layout r b pre tail)
    (frameInH printer c b out) (frameInA printer c a F g layout r hr facts b out) ∧
  Step c.cleanup b.cleanupFuel
    (frameOutH printer c a F g layout r hr facts b out) (frameOutA printer c a F g layout r hr facts b out)
    b.exitH b.exitA

theorem run (ready : Ready printer c a F g layout r hr facts b out pre tail) :
    Step (machine c) (budget printer a F g layout r hr facts b) b.entryH b.entryA b.exitH b.exitA := by
  obtain ⟨cap,prepare,complete,cleanup⟩ := ready
  have header := ((ColdHeaderWriter.run a F g layout r hr facts [] pre tail).1.pad b.headerReserve).focus
    c.headerSlots c.headerInjective b.headerH b.headerA
  have frame := ((FramingPortClasses.correct printer
    (Packets.datum a F g layout r hr facts) b.fieldReserve out b.copyCap cap).pad
      (Frame.targetReserve (P1TopDownPaidPayload.tapes printer) b.descriptorReserve)).focus
    c.frameSlots c.frameInjective b.frameH b.frameA
  exact prepare.seq (header.seq (complete.seq (frame.seq cleanup)))

end
end PhysicalRowTransaction
