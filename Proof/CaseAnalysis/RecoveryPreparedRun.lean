import Proof.CaseAnalysis.RecoveryPreparedLayout

/-! Execute the complete physical initialization of the original graph
bank, including every scalar load, backing sweep and finite-driver move. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdPrepared
open LocalBitMultitape RecoveryRootRound BoundedOracleStructuralCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def drivers:=RecoveryFocus.machine driverSlots RecoveryBoundedColdDrivers.machine
noncomputable def first:=Composition.machine RecoveryBoundedColdScalarMetadata.machine RecoveryBoundedColdWork.machine
noncomputable def prepared:=Composition.machine first drivers
noncomputable def machine:=Composition.machine prepared RecoveryBoundedColdPosition.machine
def preparedBudget (B : ℕ):=4096*(B+2)
def budget (B : ℕ):=8192*(B+2)

theorem metadata_ready (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool)
    (hn : ∀ j,RecoveryBoundedColdScalarMetadata.values q bound C Q clauses j≤B)
    (hB : 2*(q+bound+1)+8≤B) :
    ClockJoin.ReadyRun RecoveryBoundedColdScalarMetadata.machine (RecoveryBoundedColdScalarMetadata.budget B)
      (input q bound C Q clauses B proj source) (metadataData q bound C Q clauses B proj source) := by
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedColdScalarMetadata.metadata_run
    (input q bound C Q clauses B proj source) (fun _=>0) q bound C Q clauses B
    (source_input _ _ _ _ _ _ _ _) (metadata_input _ _ _ _ _ _ _ _) (by intro j;rfl) (by intro j;rfl) hn hB
  exact ⟨r,rr,rt,fun j=>congrFun rh j,rs⟩

theorem work_ready (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool) :
    ClockJoin.ReadyRun RecoveryBoundedColdWork.machine (2*B+4)
      (metadataData q bound C Q clauses B proj source) (workData q bound C Q clauses B proj source) := by
  obtain ⟨r,rr,rh,rt,rs⟩:=RecoveryBoundedColdWork.work_run B
    (metadataData q bound C Q clauses B proj source) (fun _=>0)
    (work_input _ _ _ _ _ _ _ _) (by intro j;rfl)
  exact ⟨r,rr,rt,fun j=>congrFun rh j,rs⟩

theorem prepared_ready (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool)
    (hn : ∀ j,RecoveryBoundedColdScalarMetadata.values q bound C Q clauses j≤B)
    (hmeta : 2*(q+bound+1)+8≤B) (hbound : bound+3≤B)
    (hprod : rowWidth q bound*(2*(bound+1)+3)+2≤B) :
    ClockJoin.ReadyRun prepared (preparedBudget B)
      (input q bound C Q clauses B proj source) (preparedData q bound C Q clauses B proj source) := by
  have a:=ClockJoin.join RecoveryBoundedColdScalarMetadata.machine RecoveryBoundedColdWork.machine _ _ _ _ _
    (metadata_ready q bound C Q clauses B proj source hn hmeta) (work_ready q bound C Q clauses B proj source)
  have d:=(RecoveryBoundedColdDrivers.ready bound (rowWidth q bound) B hbound hprod).focus
    driverSlots driver_injective (workData q bound C Q clauses B proj source)
    (drivers_input _ _ _ _ _ _ _ _)
  have h:=ClockJoin.join first drivers _ _ _ _ _ a d
  exact ClockJoin.enlarge _ _ _ _ _ h (by
    unfold RecoveryBoundedColdScalarMetadata.budget RecoveryBoundedColdDrivers.budget preparedBudget
    omega)

theorem prepared_run (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool)
    (hn : ∀ j,RecoveryBoundedColdScalarMetadata.values q bound C Q clauses j≤B)
    (hmeta : 2*(q+bound+1)+8≤B) (hbound : bound+3≤B)
    (hprod : rowWidth q bound*(2*(bound+1)+3)+2≤B) :
    ∃ r,run machine (budget B) (input q bound C Q clauses B proj source)=some r ∧
      r.steps≤budget B ∧ r.final.heads=RecoveryBoundedColdPosition.positioned (fun _=>0) ∧
      r.final.tapes=preparedData q bound C Q clauses B proj source := by
  obtain ⟨a,ha,atapes,ah,as⟩:=prepared_ready q bound C Q clauses B proj source hn hmeta hbound hprod
  obtain ⟨b,hb,bh,bt,bs⟩:=RecoveryBoundedColdPosition.position_run
    (preparedData q bound C Q clauses B proj source) (fun _=>0) (by intro j;rfl)
  have hb' : runFrom RecoveryBoundedColdPosition.machine 2
      (Composition.restart a.final RecoveryBoundedColdPosition.machine.start)=some b := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=_
    rw [show a.final.heads=(fun _=>0) from funext ah,atapes]
    exact hb
  have h:=Composition.run_join prepared RecoveryBoundedColdPosition.machine _ _ _ a b ha hb'
  have fit : preparedBudget B+1+2≤budget B := by unfold preparedBudget budget;omega
  have whole:=runFrom_moreFuel machine _ (budget B-(preparedBudget B+1+2)) _ _ h
  rw [Nat.add_sub_of_le fit] at whole
  exact ⟨Composition.joinedReceipt a b,whole,by change a.steps+1+b.steps≤budget B;omega,bh,bt⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdPrepared
