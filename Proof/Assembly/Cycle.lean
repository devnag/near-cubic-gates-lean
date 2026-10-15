import Proof.Assembly.Family

/-! One source-global preparation/refill program is certified by its actual
normalized-row loop and its two boundary programs. The produced ds is exactly
the caller's fixed dataList, never an arbitrary supplier. All fuel and every
ambient tape/head remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace RefillCycle
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open FixedLivePackets
noncomputable section

structure Code {printer : WilliamsAlgorithm} {t : Nat}
    (row : PhysicalRowTransaction.Code printer t) (U : Nat) where
  slots : Fin (t+1) → Fin U
  injective : Function.Injective slots
  beforeStates : Nat
  before : Machine U beforeStates
  afterStates : Nat
  after : Machine U afterStates

def machine {printer : WilliamsAlgorithm} {t U : Nat}
    {row : PhysicalRowTransaction.Code printer t} (c : Code row U) :=
  Composition.machine c.before
    (Composition.machine (RecoveryFocus.machine c.slots (ExternalRowFamily.machine printer row)) c.after)

/-- A single jointly chosen cycle, not separate existential machines per stage.
The program identity is tied to the caller's already chosen physical program.
Only the two entry/exit joins and the three row-stage Steps remain; the paid
header, framer, repeat control and zero-family exhaustion are proved below. -/
def Spec {printer : WilliamsAlgorithm} {t U : Nat}
    {row : PhysicalRowTransaction.Code printer t} (c : Code row U)
    (ds : List P1TopDownPaidReusable.Datum) (fuel : Nat) (H H' : Fin U → Nat)
    (A A' : Fin U → List Bool) : Prop :=
  ∃ (q L : Nat) (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (g : Packets.Geometry F) (layout : Packets.Layout a F g)
    (facts : ∀ r ∈ F.rows, Packets.PacketFacts a F g r),
    ds = dataList a F g layout facts ∧
  ∃ (s : ExternalRowFamily.State (t:=t) printer)
    (familyReserve : Fin (t+1) → Nat)
    (ambientH : Fin U → Nat) (ambientA : Fin U → List Bool)
    (beforeFuel afterFuel : Nat),
    Step c.before beforeFuel H A
      (dockH c.slots ambientH (ExternalRowFamily.entry printer row F s).heads)
      (install c.slots ambientA (fun i => ZeroPadding.pad (familyReserve i) ((ExternalRowFamily.entry printer row F s).tapes i))) ∧
    ExternalRowFamily.Ready printer row a F g layout facts s ∧
    Step c.after afterFuel
      (dockH c.slots ambientH (ExternalRowFamily.exit printer row a F g layout facts s).heads)
      (install c.slots ambientA (fun i => ZeroPadding.pad (familyReserve i) ((ExternalRowFamily.exit printer row a F g layout facts s).tapes i)))
      H' A' ∧
    beforeFuel+1+(ExternalRowFamily.budget printer F s+1+afterFuel) ≤ fuel

theorem run {printer : WilliamsAlgorithm} {t U : Nat}
    {row : PhysicalRowTransaction.Code printer t} (c : Code row U)
    (ds : List P1TopDownPaidReusable.Datum) (fuel : Nat) (H H' : Fin U → Nat)
    (A A' : Fin U → List Bool) (spec : Spec c ds fuel H H' A A') :
    Step (machine c) fuel H A H' A' := by
  obtain ⟨q,L,a,F,g,layout,facts,_hds,s,familyReserve,ambientH,ambientA,
    beforeFuel,afterFuel,before,rows,after,bound⟩ := spec
  have middle := ((ExternalRowFamily.run printer row a F g layout facts s rows).pad familyReserve).focus
    c.slots c.injective ambientH ambientA
  exact (before.seq (middle.seq after)).enlarge bound

end
end RefillCycle
