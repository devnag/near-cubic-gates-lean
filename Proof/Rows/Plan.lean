import Proof.Assembly.RowProduction
import Proof.Amplification.RecoveryScratchErase
import Proof.Amplification.RecoveryRowLookupTapes

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace LinearEraserBank
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open FixedLivePackets PacketProduction
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

def clearInput {m : Nat} (K logCapacity : Nat) (A : Fin m → List Bool) :
    Fin (m+1+1) → List Bool :=
  Fin.addCases (Fin.addCases A (fun _ : Fin 1 => List.replicate K true))
    (fun _ : Fin 1 => List.replicate logCapacity false)

def clearOutput (m K logCapacity : Nat) : Fin (m+1+1) → List Bool :=
  clearInput K logCapacity (fun _ : Fin m => List.replicate K false)

/-- A bank equality certificate for one concrete linear eraser, not an
assumed cleanup execution. Larger false tails are left outside its scan. -/
structure ClearBank {t m : Nat} (slots : Fin (m+1+1) → Fin t)
    (H J : Fin t → Nat) (A B : Fin t → List Bool) where
  cap : Nat
  logCapacity : Nat
  logical : Fin m → List Bool
  reserve : Fin (m+1+1) → Nat
  fits : ∀ i, (logical i).length ≤ cap
  logFits : cap+1 ≤ logCapacity
  heads : ∀ i, H (slots i)=0
  input : ∀ i, A (slots i)=ZeroPadding.pad (reserve i)
    (clearInput cap logCapacity logical i)
  finalHeads : J=H
  finalTapes : B=install slots A (fun i => ZeroPadding.pad (reserve i)
    (clearOutput m cap logCapacity i))

theorem clear_run {t m : Nat} (slots : Fin (m+1+1) → Fin t)
    (hinj : Function.Injective slots) {H J : Fin t → Nat}
    {A B : Fin t → List Bool} (h : ClearBank slots H J A B) :
    Step (RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine m))
      (2*h.cap+4) H A J B := by
  obtain ⟨receipt,run,tapes,heads,steps⟩ :=
    RecoveryScratchErase.erase_ready h.cap h.logCapacity h.logical h.fits
  have base := Step.of_run run (funext heads) tapes
  have he : max h.logCapacity (h.cap+1)=h.logCapacity := max_eq_left h.logFits
  rw [he] at base
  change Step (RecoveryScratchErase.resetMachine m) (2*h.cap+4) (fun _ => 0)
    (clearInput h.cap h.logCapacity h.logical) (fun _ => 0)
    (clearOutput m h.cap h.logCapacity) at base
  have focused := (base.pad h.reserve).focus slots hinj H A
  have hi : dockH slots H (fun _ => 0)=H := dockH_existing slots H _ h.heads
  have ai : install slots A (fun i => ZeroPadding.pad (h.reserve i)
      (clearInput h.cap h.logCapacity h.logical i))=A :=
    install_existing slots A _ h.input
  exact (focused.congr_in hi ai).congr (hi.trans h.finalHeads.symm) h.finalTapes.symm

def program {printer : WilliamsAlgorithm} {privateWork m completeStates : Nat}
    (slots : Fin (m+1+1) → Fin (rowTapes printer privateWork))
    (complete : Machine (rowTapes printer privateWork) completeStates) :
    SharedRowLayout.Program printer (rowWork privateWork) where
  completeStates := completeStates
  complete := complete
  cleanupStates := 4
  cleanup := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine m)

/-- The remaining source-global constructor supplies two actual programs:
initialization from the public words, and completion of the two changing
fields. Cleanup is already the fixed machine proved above. Its scalar, heads,
backing and exact next-bank equations remain explicit obligations here. -/
structure Core (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (printer : WilliamsAlgorithm) where
  privateWork : Nat
  coefficient : Nat
  degree : Nat
  positive : 0 < coefficient
  mutableTapes : Nat
  slots : Fin (mutableTapes+1+1) → Fin (rowTapes printer privateWork)
  injective : Function.Injective slots
  completeStates : Nat
  complete : Machine (rowTapes printer privateWork) completeStates
  initializeStates : Nat
  initializer : Machine (rowTapes printer privateWork+1) initializeStates
  state : (r : Request) →
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) →
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) →
    RowCaps → ExternalRowFamily.State (t:=rowTapes printer privateWork) printer
  initial : ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
    let entry := ExternalRowFamily.entry printer
      (SharedRowLayout.code (program slots complete)) (r.family a)
      (state r layout facts caps)
    Step initializer (rowInitBudget a coefficient degree r layout.w layout.degree layout.C caps)
      (fun _ => 0) (rowPublicInput selector a printer privateWork r layout caps)
      entry.heads entry.tapes
  completeReady : ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
    ∀ j : Fin (r.family a).rows.attach.length, ∀ out,
    let s := state r layout facts caps
    let g := geometryOf selector a r
    let row := ExternalRowFamily.rowAt (r.family a) j
    let b := ExternalRowFamily.rowBanks printer a (r.family a) g layout facts s j.val out
    let c := SharedRowLayout.code (program slots complete)
    b.prepareFuel=0 ∧
    b.entryH=PhysicalRowTransaction.headerInH printer c b
      (ExternalRowFamily.rawBefore a (r.family a) g j.val) ∧
    b.entryA=PhysicalRowTransaction.headerInA printer c a (r.family a) g layout row.val b
      (ExternalRowFamily.rawBefore a (r.family a) g j.val)
      (ExternalRowFamily.rawAfter a (r.family a) g j.val) ∧
    (∀ i,2*(PhysicalRowTransaction.Frame.fields printer
      (Packets.datum a (r.family a) g layout row.val row.property (facts row.val row.property)) i).length+1≤b.copyCap) ∧
    Step complete b.completeFuel
      (PhysicalRowTransaction.headerOutH printer c a (r.family a) g layout row.val b
        (ExternalRowFamily.rawBefore a (r.family a) g j.val)
        (ExternalRowFamily.rawAfter a (r.family a) g j.val))
      (PhysicalRowTransaction.headerOutA printer c a (r.family a) g layout row.val b
        (ExternalRowFamily.rawBefore a (r.family a) g j.val)
        (ExternalRowFamily.rawAfter a (r.family a) g j.val))
      (PhysicalRowTransaction.frameInH printer c b out)
      (PhysicalRowTransaction.frameInA printer c a (r.family a) g layout row.val row.property
        (facts row.val row.property) b out) ∧
    ∃ clear : ClearBank slots
      (PhysicalRowTransaction.frameOutH printer c a (r.family a) g layout row.val row.property
        (facts row.val row.property) b out)
      b.exitH
      (PhysicalRowTransaction.frameOutA printer c a (r.family a) g layout row.val row.property
        (facts row.val row.property) b out)
      b.exitA,
      2*clear.cap+4≤b.cleanupFuel ∧
      PhysicalRowTransaction.budget printer a (r.family a) g layout row.val row.property
        (facts row.val row.property) b ≤ s.rowFuel
  descriptor : ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
    ∀ j, j≤(r.family a).rows.length → ∀ out,
    let port := SharedRowLayout.descriptor printer (rowWork privateWork)
    (state r layout facts caps).heads j out port=out.length ∧
    (state r layout facts caps).tapes j out port=ZeroPadding.pad caps.descriptorReserve out
  cost : ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
    (state r layout facts caps).rowFuel≤rowBudget a coefficient degree r layout.C caps

def assembleCore {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} (core : Core selector a printer) :
    RowProducer selector a printer where
  privateWork := core.privateWork
  coefficient := core.coefficient
  degree := core.degree
  positive := core.positive
  program := program core.slots core.complete
  initializeStates := core.initializeStates
  initializer := core.initializer
  state := core.state
  initial := core.initial
  ready := by
    intro r layout facts caps good j out
    obtain ⟨fuel,heads,bank,cap,complete,clear,bound,rowCost⟩ :=
      core.completeReady r layout facts caps good j out
    exact ⟨fuel,heads,bank,cap,complete,
      (clear_run core.slots core.injective clear).enlarge bound,rowCost⟩
  descriptor := core.descriptor
  cost := core.cost

def Construction (selector : CyclicChoice.Laws) : Prop :=
  ∀ (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm), Nonempty (Core selector a printer)

theorem assemble (selector : CyclicChoice.Laws) (build : Construction selector) :
    RowConstruction selector := by
  intro a printer
  obtain ⟨core⟩ := build a printer
  exact ⟨assembleCore core⟩

end
end LinearEraserBank
