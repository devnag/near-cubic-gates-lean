import Proof.Hierarchy.CompetitorCountBanksPrefix

/-! Narrow transport into the fixed complete cross-table after same-bank
production. The prefix stays abstract, and the disjoint exact same bank is
retained through the actual cross-table run. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountBanks
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation
open MatrixScoreBatch (Request)
open CompetitorPlaneTable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def field (p : Program) (j : Fin 61) := native p (CompetitorCrossScheduler.fieldSlots p j)
def tableNative (p : Program) (i : Fin 35) := crossSlots p (CompetitorCrossTableCold.native i)
def heads (p : Program) (pos : ℕ) (i : Fin (tapes p)) := if i.val=93 then pos else 0

theorem cross_heads (p : Program) (pos : ℕ) (i : Fin 120) :
    CompetitorCrossTableCold.heads pos i=heads p pos (crossSlots p i) :=
  CompetitorCrossScheduler.cross_heads p pos i

theorem cross_avoids_zero (p : Program) (i : Fin 120) : crossSlots p i≠field p 0 := by
  intro h
  exact CompetitorCrossScheduler.cross_avoids_zero p i ((native_injective p) h)

theorem cross_avoids_u (p : Program) (i : Fin 120) : crossSlots p i≠field p 44 := by
  intro h
  exact CompetitorCrossScheduler.cross_avoids_u p i ((native_injective p) h)

theorem outside_heads (p : Program) (pos : ℕ) (i : Fin (tapes p))
    (hn : ∀ j,crossSlots p j≠i) : heads p pos i=0 := by
  have hi : i.val≠93 := by
    intro hv
    exact hn 32 (Fin.ext hv.symm)
  exact if_neg hi

theorem dock_cold {s : ℕ} (p : Program) (firstMachine : Machine (tapes p) s) (fuel : ℕ)
    (r : Request) (prepared : Fin (tapes p) → List Bool)
    (hrun : ClockJoin.ReadyRun firstMachine fuel (input p r) prepared)
    (fi : ∀ i,prepared (crossSlots p i)=CompetitorCrossTablePrepare.input
      (natBitLength r.U) (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p (MatrixScoreBatch.output r) i)
    (f0 : prepared (field p 0)=MatrixScoreBatch.physicalInput r)
    (fU : prepared (field p 44)=UnaryTemplate.tape r.U)
    (fbank : prepared (bank p)=sameWord r) : ∃ actual out,
    run (Composition.machine firstMachine (RecoveryFocus.machine (crossSlots p) CompetitorCrossTableCold.machine))
      (fuel+1+CompetitorCrossTableCold.budget (natBitLength r.U)
        (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p) (input p r)=some actual ∧
    actual.steps ≤ fuel+1+CompetitorCrossTableCold.budget (natBitLength r.U)
      (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p ∧
    actual.final.heads=heads p (MatrixScoreBatch.output r).length ∧
    (∀ i : Fin 35,actual.final.tapes (tableNative p i)=CompetitorPlaneTableEntry.tapes out r.p i) ∧
    TableContext (natBitLength r.U) (CompetitorPlaneWidth.width (natBitLength r.U) r.p)
      (CompetitorCrossStateMeaning.state r) out ∧
    Bounded (natBitLength r.U) r.p (2*r.p) (CompetitorCrossStateMeaning.state r) ∧
    actual.final.tapes (field p 0)=MatrixScoreBatch.physicalInput r ∧
    actual.final.tapes (field p 44)=UnaryTemplate.tape r.U ∧
    actual.final.tapes (bank p)=sameWord r := by
  obtain ⟨first,hf,ft,fh,fs⟩ := hrun
  obtain ⟨child,out,hc,cs,ch,ct,context,_,_,_,bounded⟩ := CompetitorCrossTableCold.cold_run
    (natBitLength r.U) r.p (CompetitorMatrixPlaneTable.planes r)
    (by simp [CompetitorMatrixPlaneTable.planes]) (CompetitorMatrixPlaneTable.valid_planes r)
  have plen : (CompetitorMatrixPlaneTable.planes r).length=r.p := by simp [CompetitorMatrixPlaneTable.planes]
  simp only [plen,CompetitorMatrixPlaneTable.output_stream] at hc cs ch ct bounded
  obtain ⟨last,hl,_,ls,lh,lt,other⟩ := RecoveryFocus.dock (crossSlots p)
    (cross_injective p) CompetitorCrossTableCold.machine _ first.final.heads first.final.tapes
    (initialConfiguration CompetitorCrossTableCold.machine (CompetitorCrossTablePrepare.input
      (natBitLength r.U) (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p (MatrixScoreBatch.output r)))
    (by intro i;exact fh _) (by intro i;rw [ft];exact fi i) child hc
  change runFrom (RecoveryFocus.machine (crossSlots p) CompetitorCrossTableCold.machine) (CompetitorCrossTableCold.budget (natBitLength r.U)
    (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p)
    (Composition.restart first.final (RecoveryFocus.machine (crossSlots p) CompetitorCrossTableCold.machine).start)=some last at hl
  have hwhole := Composition.run_join firstMachine (RecoveryFocus.machine (crossSlots p) CompetitorCrossTableCold.machine) _ _ _ first last hf hl
  refine ⟨Composition.joinedReceipt first last,out,hwhole,?_,?_,?_,context,bounded,?_,?_,?_⟩
  · change first.steps+1+last.steps ≤ (fuel+1+CompetitorCrossTableCold.budget (natBitLength r.U) (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p)
    rw [ls]
    omega
  · change last.final.heads=heads p (MatrixScoreBatch.output r).length
    funext i
    by_cases hi : ∃ j,crossSlots p j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [lh,ch]
      exact cross_heads p _ j
    · have hn : ∀ j,crossSlots p j≠i := by intro j hj;exact hi ⟨j,hj⟩
      rw [(other i hn).1,fh,outside_heads p _ i hn]
  · intro i
    exact (lt (CompetitorCrossTableCold.native i)).trans (ct i)
  · exact (other (field p 0) (cross_avoids_zero p)).2.trans (by rw [ft];exact f0)
  · exact (other (field p 44) (cross_avoids_u p)).2.trans (by rw [ft];exact fU)

  · exact (other (bank p) (cross_avoids_bank p)).2.trans (by rw [ft];exact fbank)

end NearCubicWires.RepairOrdinary.CompetitorCountBanks
