import Proof.Assembly.Cycle

/-! The shared row layout has no preparation pass. Entry is already the exact
cold Header bank. The descriptor target is append-only and outside the Header
block; cleanup must leave the next exact ready bank. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace SharedRowLayout
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open FixedLivePackets
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

abbrev tapes (printer : WilliamsAlgorithm) (work : Nat) :=
  440+(P1TopDownPaidPayload.tapes printer+2)+work

def headerSlots (printer : WilliamsAlgorithm) (work : Nat) (i : Fin 440) :
    Fin (tapes printer work) := (i.castAdd (P1TopDownPaidPayload.tapes printer+2)).castAdd work
def frameSlots (printer : WilliamsAlgorithm) (work : Nat)
    (i : Fin (P1TopDownPaidPayload.tapes printer+2)) : Fin (tapes printer work) :=
  (i.natAdd 440).castAdd work

theorem header_injective (printer : WilliamsAlgorithm) (work : Nat) :
    Function.Injective (headerSlots printer work) := by
  intro i j h
  have he := congrArg (fun x : Fin (tapes printer work) => x.val) h
  exact Fin.ext he
theorem frame_injective (printer : WilliamsAlgorithm) (work : Nat) :
    Function.Injective (frameSlots printer work) := by
  intro i j h
  have he := congrArg Fin.val h
  change 440+i.val=440+j.val at he
  exact Fin.ext (by omega)

def descriptor (printer : WilliamsAlgorithm) (work : Nat) : Fin (tapes printer work) :=
  frameSlots printer work (DatumCopier.target (P1TopDownPaidPayload.tapes printer))

/-- Only the genuinely unfinished row producers remain program choices. -/
structure Program (printer : WilliamsAlgorithm) (work : Nat) where
  completeStates : Nat
  complete : Machine (tapes printer work) completeStates
  cleanupStates : Nat
  cleanup : Machine (tapes printer work) cleanupStates

def code {printer : WilliamsAlgorithm} {work : Nat} (p : Program printer work) :
    PhysicalRowTransaction.Code printer (tapes printer work) where
  prepareStates := 1
  prepare := CompetitorRawFieldEmit.halt _
  completeStates := p.completeStates
  complete := p.complete
  cleanupStates := p.cleanupStates
  cleanup := p.cleanup
  headerSlots := headerSlots printer work
  headerInjective := header_injective printer work
  frameSlots := frameSlots printer work
  frameInjective := frame_injective printer work

theorem halt_run {t : Nat} (H : Fin t→Nat) (A : Fin t→List Bool) :
    Step (CompetitorRawFieldEmit.halt t) 0 H A H A := by
  let c : Configuration t 1 := ⟨0,H,A⟩
  let r : ExecutionReceipt t 1 := ⟨c,0,c.tapeCells⟩
  exact ⟨r,rfl,rfl,rfl,Nat.le_refl 0⟩

variable {q L work : Nat} (printer : WilliamsAlgorithm) (p : Program printer work)
  (a : DecompositionAlgorithm) (F : Packets.Family q L) (g : Packets.Geometry F)
  (layout : Packets.Layout a F g) (facts : ∀ r∈F.rows,Packets.PacketFacts a F g r)
  (s : ExternalRowFamily.State (t:=tapes printer work) printer)

/-- The only row Steps still owed are actual completion and cleanup. The
entry equalities are what makes the zero-fuel identity preparation sound. -/
def Ready : Prop :=
  ∀ j : Fin F.rows.attach.length, ∀ out,
  let r := ExternalRowFamily.rowAt F j
  let b := ExternalRowFamily.rowBanks printer a F g layout facts s j.val out
  b.prepareFuel=0 ∧
  b.entryH=PhysicalRowTransaction.headerInH printer (code p) b
    (ExternalRowFamily.rawBefore a F g j.val) ∧
  b.entryA=PhysicalRowTransaction.headerInA printer (code p) a F g layout r.val b
    (ExternalRowFamily.rawBefore a F g j.val)
    (ExternalRowFamily.rawAfter a F g j.val) ∧
  (∀ i,2*(PhysicalRowTransaction.Frame.fields printer
    (Packets.datum a F g layout r.val r.property (facts r.val r.property)) i).length+1≤b.copyCap) ∧
  Step p.complete b.completeFuel
    (PhysicalRowTransaction.headerOutH printer (code p) a F g layout r.val b
      (ExternalRowFamily.rawBefore a F g j.val) (ExternalRowFamily.rawAfter a F g j.val))
    (PhysicalRowTransaction.headerOutA printer (code p) a F g layout r.val b
      (ExternalRowFamily.rawBefore a F g j.val) (ExternalRowFamily.rawAfter a F g j.val))
    (PhysicalRowTransaction.frameInH printer (code p) b out)
    (PhysicalRowTransaction.frameInA printer (code p) a F g layout r.val r.property (facts r.val r.property) b out) ∧
  Step p.cleanup b.cleanupFuel
    (PhysicalRowTransaction.frameOutH printer (code p) a F g layout r.val r.property (facts r.val r.property) b out)
    (PhysicalRowTransaction.frameOutA printer (code p) a F g layout r.val r.property (facts r.val r.property) b out)
    b.exitH b.exitA ∧
  PhysicalRowTransaction.budget printer a F g layout r.val r.property (facts r.val r.property) b ≤ s.rowFuel

theorem ready (h : Ready printer p a F g layout facts s) :
    ExternalRowFamily.Ready printer (code p) a F g layout facts s := by
  intro j out
  obtain ⟨fuel,heads,bank,cap,complete,cleanup,bound⟩ := h j out
  refine ⟨⟨cap,?_,complete,cleanup⟩,bound⟩
  rw [fuel,←heads,←bank]
  exact halt_run _ _
end
end SharedRowLayout
