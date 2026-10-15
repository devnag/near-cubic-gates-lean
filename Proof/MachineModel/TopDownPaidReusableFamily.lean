import Proof.MachineModel.TopDownPaidReusable

/-! The actual full-state hrow application: source k is the retained complete
framed row stream at its kth consumed prefix, fixed templates and zero-backed
private storage. The only growing word is the raw count output. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReusable
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open P1TopDownPaidPayload (estimate port tapes)
attribute [local irreducible] CompetitorCrossScheduler.producer machine
  P1TopDownPaidReloadCore.rawMachine P1TopDownPaidReusableBody.machine

structure Datum where
  row : EquationRow.Input
  C : Nat
  Q : Nat
  f : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Nat
  select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool

noncomputable def Datum.word (a : WilliamsAlgorithm) (d : Datum) := P1TopDownPaidReusable.word a d.row d.C d.Q d.select
noncomputable def Datum.emit (d : Datum) :=
  SignedSortKey.binary (scalarWidth (EquationRow.request d.row) d.Q)
    (selected (CompetitorSelectedCells.cells d.row.odd d.f d.select)).sum
noncomputable def Datum.budget (a : WilliamsAlgorithm) (B S : Nat) (d : Datum) :=
  P1TopDownPaidReusable.budget a d.row d.C d.Q B S d.select

structure Valid (a : WilliamsAlgorithm) (B R S : Nat) (d : Datum) : Prop where
  capacity : (Header.stream d.row).length≤d.C
  precision : d.Q≤(EquationRow.request d.row).p
  values : ∀ i j,d.f i j<2^d.Q
  meaning : ∀ i : Fin ((EquationRow.request d.row).U*(EquationRow.request d.row).U),
    Int.ModEq ((2 : Int)^d.Q)
      (SupplierPrinter.weightedDominance (leftScore (EquationRow.request d.row))
        (rightScore (EquationRow.request d.row)) (weight (EquationRow.request d.row)) i.divNat i.modNat)
      (d.f i.divNat i.modNat)
  rewind : P1TopDownPaidReloadCore.fuel a d.row d.C d.Q≤R
  buffer : RowPayload.budget (scalarWidth (EquationRow.request d.row) d.Q)≤B
  reset : B+1≤R
  workspace : P1TopDownPaidReloadCore.budget a d.row d.C d.Q B+1≤S
  bufferWorkspace : B≤S

noncomputable def source (a : WilliamsAlgorithm) (ds : List Datum) (S R B : Nat)
    (k : Nat) (out : List Bool) :=
  (⟨(machine a).start,heads a ((ds.take k).flatMap (Datum.word a)).length out,
    bank a (ds.flatMap (Datum.word a)) S R B out⟩ : Configuration _ _)

set_option maxHeartbeats 1000000 in
theorem hrow (a : WilliamsAlgorithm) (ds : List Datum) (dflt : Datum) (S R B cost : Nat)
    (hv : ∀ k (hk : k<ds.length),Valid a B R S ds[k])
    (hb : ∀ k (hk : k<ds.length),(ds[k]).budget a B S≤cost)
    (k : Nat) (hk : k<ds.length) (out : List Bool) :
    ∃ r,runFrom (machine a) cost (source a ds S R B k out)=some r ∧
      r.final.heads=(source a ds S R B (k+1) (out++(ds.getD k dflt).emit)).heads ∧
      r.final.tapes=(source a ds S R B (k+1) (out++(ds.getD k dflt).emit)).tapes ∧
      r.steps≤cost := by
  apply C10RowFrameJoin.hrow_of_step (machine a) (source a ds S R B)
    (fun k=>(ds.getD k dflt).emit) cost ds.length (by intros;rfl) ?_ k hk out
  intro j hj output
  let d:=ds[j]
  have v:=hv j hj
  have step:=run a d.row d.C d.Q B R S d.f d.select
    ((ds.take j).flatMap (Datum.word a)) ((ds.drop (j+1)).flatMap (Datum.word a)) output
    v.capacity v.precision v.values v.meaning v.rewind v.buffer v.reset v.workspace v.bufferWorkspace
  have split : (ds.take j).flatMap (Datum.word a)++d.word a++
      (ds.drop (j+1)).flatMap (Datum.word a)=ds.flatMap (Datum.word a) := by
    have he : ds.take j++ds[j]::ds.drop (j+1)=ds := by
      rw [List.cons_getElem_drop_succ,List.take_append_drop]
    have h:=congrArg (List.flatMap (Datum.word a)) he
    simpa only [List.flatMap_append,List.flatMap_cons,List.append_assoc] using h
  have advance : ((ds.take (j+1)).flatMap (Datum.word a)).length=
      ((ds.take j).flatMap (Datum.word a)).length+(d.word a).length := by
    have he:=List.take_concat_get' ds j hj
    have h:=congrArg (fun xs=>(xs.flatMap (Datum.word a)).length) he
    simpa only [List.flatMap_append,List.flatMap_singleton,List.length_append] using h.symm
  have get : ds.getD j dflt=d := List.getD_eq_getElem ds dflt hj
  have step' := step.enlarge (hb j hj)
  change Step (machine a) cost
    (heads a ((ds.take j).flatMap (Datum.word a)).length output)
    (bank a ((ds.take j).flatMap (Datum.word a)++d.word a++(ds.drop (j+1)).flatMap (Datum.word a)) S R B output)
    (heads a (((ds.take j).flatMap (Datum.word a)).length+(d.word a).length) (output++d.emit))
    (bank a ((ds.take j).flatMap (Datum.word a)++d.word a++(ds.drop (j+1)).flatMap (Datum.word a)) S R B (output++d.emit)) at step'
  rw [split,←advance] at step'
  simpa only [source,get] using step'

end NearCubicWires.P1TopDownPaidReusable
