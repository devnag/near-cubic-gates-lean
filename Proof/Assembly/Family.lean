import Proof.Assembly.Row
import Proof.CaseAnalysis.RowsDegreeLoop

/-! The exact external-row family, with one fixed row body and a paid runtime
repeat driver. Each normalized packet family is consumed once; the descriptor
only grows. The terminal and zero-row cases use the existing driver rewind. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace ExternalRowFamily
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open FixedLivePackets
attribute [local irreducible] P1TopDownPaidPayload.tapes
namespace Row
abbrev Code := PhysicalRowTransaction.Code
abbrev Banks := PhysicalRowTransaction.Banks
end Row
noncomputable section

variable {q L t : Nat} (printer : WilliamsAlgorithm) (c : Row.Code printer t)
  (a : DecompositionAlgorithm) (F : Packets.Family q L) (g : Packets.Geometry F)
  (layout : Packets.Layout a F g) (facts : ∀ r ∈ F.rows, Packets.PacketFacts a F g r)

abbrev machine := CloseoutRowsDegreeLoop.machine (PhysicalRowTransaction.machine c)

def rawWord (r : Packets.Row F.occurrences L) :=
  (Packets.packets a F g r).flatMap P1CompactNativeFamily.rawWord

def rawBefore (j : Nat) := (F.rows.take j).flatMap (rawWord a F g)
def rawAfter (j : Nat) := (F.rows.drop (j+1)).flatMap (rawWord a F g)

def words := (dataList a F g layout facts).map (P1TopDownPaidReusable.Datum.word printer)
def emit (j : Nat) := (words printer a F g layout facts).getD j []

def rowAt (j : Fin F.rows.attach.length) := F.rows.attach[j.val]
def datumAt (j : Fin F.rows.attach.length) :=
  Packets.datum a F g layout (rowAt F j).val (rowAt F j).property
    (facts (rowAt F j).val (rowAt F j).property)

theorem word_at (j : Fin F.rows.attach.length) :
    emit printer a F g layout facts j.val = (datumAt a F g layout facts j).word printer := by
  have hj : j.val < (words printer a F g layout facts).length := by
    simpa only [words,dataList,List.length_map] using j.isLt
  rw [emit,List.getD_eq_getElem _ _ hj]
  simp only [words,dataList,List.getElem_map,datumAt,rowAt]

/-- Runtime bank fields, all bound to one family and row index. Code remains in c. -/
structure State where
  heads : Nat → List Bool → Fin t → Nat
  tapes : Nat → List Bool → Fin t → List Bool
  headerReserve : Nat → Fin 440 → Nat
  descriptorReserve : Nat → Nat
  headerHeads : Nat → List Bool → Fin t → Nat
  headerTapes : Nat → List Bool → Fin t → List Bool
  frameHeads : Nat → List Bool → Fin t → Nat
  frameTapes : Nat → List Bool → Fin t → List Bool
  fieldReserve : Nat → Fin (P1TopDownPaidPayload.tapes printer) → Nat
  copyCap : Nat → Nat
  prepareFuel : Nat → Nat
  completeFuel : Nat → Nat
  cleanupFuel : Nat → Nat
  rowFuel : Nat

variable (s : State (t:=t) printer)

def rowBanks (j : Nat) (out : List Bool) : Row.Banks printer t where
  entryH := s.heads j out
  entryA := s.tapes j out
  headerReserve := s.headerReserve j
  descriptorReserve := s.descriptorReserve j
  headerH := s.headerHeads j out
  headerA := s.headerTapes j out
  frameH := s.frameHeads j out
  frameA := s.frameTapes j out
  fieldReserve := s.fieldReserve j
  copyCap := s.copyCap j
  exitH := s.heads (j+1) (out++emit printer a F g layout facts j)
  exitA := s.tapes (j+1) (out++emit printer a F g layout facts j)
  prepareFuel := s.prepareFuel j
  completeFuel := s.completeFuel j
  cleanupFuel := s.cleanupFuel j

def Ready : Prop :=
  ∀ j : Fin F.rows.attach.length, ∀ out,
    PhysicalRowTransaction.Ready printer c a F g layout
      (rowAt F j).val (rowAt F j).property (facts (rowAt F j).val (rowAt F j).property)
      (rowBanks printer a F g layout facts s j.val out) out
      (rawBefore a F g j.val) (rawAfter a F g j.val) ∧
    PhysicalRowTransaction.budget printer a F g layout
      (rowAt F j).val (rowAt F j).property (facts (rowAt F j).val (rowAt F j).property)
      (rowBanks printer a F g layout facts s j.val out) ≤ s.rowFuel

def rowConfig (j : Nat) (out : List Bool) :=
  (⟨(PhysicalRowTransaction.machine c).start,s.heads j out,s.tapes j out⟩ : Configuration t _)

def entry := RepeatMachine.cfg 0 (rowConfig printer c s 0 []) F.rows.attach.length 1
def exit := RepeatMachine.cfg 3
  (rowConfig printer c s F.rows.attach.length ((dataList a F g layout facts).flatMap
    (P1TopDownPaidReusable.Datum.word printer))) F.rows.attach.length 1

def budget := F.rows.attach.length*(s.rowFuel+3)+3

theorem run (ready : Ready printer c a F g layout facts s) :
    Step (machine printer c) (budget printer F s)
      (entry printer c F s).heads (entry printer c F s).tapes
      (exit printer c a F g layout facts s).heads (exit printer c a F g layout facts s).tapes := by
  have supplier : ∀ j < F.rows.attach.length, ∀ out,
      Step (PhysicalRowTransaction.machine c) s.rowFuel
        (s.heads j out) (s.tapes j out)
        (s.heads (j+1) (out++emit printer a F g layout facts j))
        (s.tapes (j+1) (out++emit printer a F g layout facts j)) := by
    intro j hj out
    have h := ready ⟨j,hj⟩ out
    exact (PhysicalRowTransaction.run printer c a F g layout
      (rowAt F ⟨j,hj⟩).val (rowAt F ⟨j,hj⟩).property
      (facts (rowAt F ⟨j,hj⟩).val (rowAt F ⟨j,hj⟩).property)
      (rowBanks printer a F g layout facts s j out) out
      (rawBefore a F g j) (rawAfter a F g j) h.1).enlarge h.2
  obtain ⟨result,run,final,_cost⟩ := CloseoutRowsDegreeLoop.loop_run
    (PhysicalRowTransaction.machine c) (rowConfig printer c s)
    (emit printer a F g layout facts) s.rowFuel F.rows.attach.length
    (by intros; rfl) supplier []
  have he : (List.range F.rows.attach.length).flatMap (emit printer a F g layout facts) =
      (dataList a F g layout facts).flatMap (P1TopDownPaidReusable.Datum.word printer) := by
    have length : (words printer a F g layout facts).length = F.rows.attach.length := by
      simp only [words,dataList,List.length_map]
    rw [←length]
    change (List.range (words printer a F g layout facts).length).flatMap
      (fun j => (words printer a F g layout facts).getD j []) = _
    simpa only [words,List.flatMap_def] using
      C10ExternalRowLoop.flatten_getD (words printer a F g layout facts)
  simp only [List.nil_append,he] at final
  exact Step.of_run run (congrArg Configuration.heads final) (congrArg Configuration.tapes final)

end
end ExternalRowFamily
