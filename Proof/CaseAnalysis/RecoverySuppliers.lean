import Proof.CaseAnalysis.RecoverySuppliersRetained

/-! The actual original hierarchy word and paid W supply the complete cold
recovery bank. The four physical calls and three bridge transitions are paid. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization RecoveryRootRound
open VerifierDecoding RecoveryScheduleEnvelope CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def first (k d CH Cpad : ℕ) (code : List Bool):=
  Composition.machine (countMachine source k d CH Cpad code) (capacityMachine source k d)
def second (k d CH Cpad : ℕ) (code : List Bool):=
  Composition.machine (first source k d CH Cpad code) (projectionMachine source k d)
def machine (k d CH Cpad : ℕ) (code : List Bool):=
  Composition.machine (second source k d CH Cpad code) (fullMachine source k d)
def budget (k d CH Cpad : ℕ) (code x : List Bool) (W : ℕ):=
  RecoveryBoundedColdHierarchyDock.Count.budget source k CH Cpad code x+1+
    RecoveryCapacityDrivers.budget W+1+
    RecoveryProjectionCold.budget (HierarchyStreams.R source k CH Cpad code x)
      (HierarchyStreams.Q source k CH Cpad code x) (RecoveryCapacityDrivers.capacityB W)+1+
    RecoveryFullBound.budget d (HierarchyStreams.R source k CH Cpad code x)
def output (k d CH Cpad : ℕ) (code x : List Bool) (W : ℕ) : Fin 158→List Bool:=
  let R:=HierarchyStreams.R source k CH Cpad code x
  let Q:=HierarchyStreams.Q source k CH Cpad code x
  let p:=source.output (HierarchyStreams.request k CH Cpad code x)
  let B:=RecoveryCapacityDrivers.capacityB W
  RecoveryBoundedColdPrepared.input R (oracleSizeBound d R) (RecoveryCapacityDrivers.capacityC W)
    Q (Codec.clauses p).length B (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) B)
    (DedupBytes.fields p)

private theorem restart_after {t a b c : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b)
    (state : Fin c) (H : Fin t→ℕ) (A : Fin t→List Bool)
    (hh : s.final.heads=H) (ht : s.final.tapes=A) :
    Composition.restart (Composition.joinedReceipt r s).final state=⟨state,H,A⟩:=by
  simp only [Composition.restart,Composition.joinedReceipt,Composition.rightConfig,hh,ht]

theorem cold_run (k d CH Cpad : ℕ) (code x bound : List Bool) (W : ℕ) (hpad : k+3 ≤ Cpad) :
    ∃ r,run (machine source k d CH Cpad code) (budget source k d CH Cpad code x W)
      (input source k d (frame x++frame bound) W)=some r ∧
      r.steps ≤ budget source k d CH Cpad code x W ∧
      (∀ i : Fin 158,r.final.heads (old source k d i)=0) ∧
      (∀ i : Fin 158,r.final.tapes (old source k d i)=output source k d CH Cpad code x W i) ∧
      r.final.tapes (hierarchyPort source k d)=frame x++frame bound ∧
      r.final.heads (hierarchyPort source k d)=0 ∧
      r.final.tapes (wPort source k d)=List.replicate W true ∧
      r.final.heads (wPort source k d)=0:=by
  let R:=HierarchyStreams.R source k CH Cpad code x
  let Q:=HierarchyStreams.Q source k CH Cpad code x
  let p:=source.output (HierarchyStreams.request k CH Cpad code x)
  let B:=RecoveryCapacityDrivers.capacityB W
  let word:=frame x++frame bound
  obtain ⟨r0,h0,hs0,hfields,hheads,hblank,hfar⟩:=count_run source k d CH Cpad code x bound W hpad
  let A:=r0.final.tapes
  let H:=r0.final.heads
  have hft (i : Fin (tapes source k d)) (hi : base source k ≤ i.val) : A i=input source k d word W i:=(hfar i hi).2
  have hfh (i : Fin (tapes source k d)) (hi : base source k ≤ i.val) : H i=0:=(hfar i hi).1
  have hr : A (rBitsPort source k d)=frame R.bits:=hfields.width
  have hq : A (qBitsPort source k d)=frame Q.bits:=hfields.queries
  have hquery : A (old source k d 106)=QueryBytes.framedCodes (normalizedRows p R Q).flatten:=hfields.queryStream
  have hhr : H (rBitsPort source k d)=0:=hfields.widthHead
  have hhq : H (qBitsPort source k d)=0:=hfields.queriesHead
  obtain ⟨C,r1,h1,hs1,hh1,ht1,hCW,hCC,hCB,hCL⟩:=
    capacity_run source k d word W A H hblank hft hheads hfh
  obtain ⟨P,r2,h2,hs2,hh2,ht2,hbank,hrows,hPR,hPQ,hPB⟩:=
    projection_run source k d R Q B word W p A H C hr hq hquery hCB hblank hft hheads hhr hhq hfh
  obtain ⟨F,r3,h3,hs3,hh3,ht3,hFR,hraw,hcompare⟩:=
    full_run source k d R word W A H C P hPR hblank hft hheads hfh
  have h01:=Composition.run_join (countMachine source k d CH Cpad code) (capacityMachine source k d)
    (RecoveryBoundedColdHierarchyDock.Count.budget source k CH Cpad code x)
    (RecoveryCapacityDrivers.budget W) _ r0 r1 h0 h1
  have h012:=Composition.run_join (first source k d CH Cpad code) (projectionMachine source k d)
    (RecoveryBoundedColdHierarchyDock.Count.budget source k CH Cpad code x+1+RecoveryCapacityDrivers.budget W)
    (RecoveryProjectionCold.budget R Q B) _ (Composition.joinedReceipt r0 r1) r2 h01 (by
      rw [restart_after r0 r1 (projectionMachine source k d).start H
        (capacityData source k d A C) hh1 ht1]
      exact h2)
  have h0123:=Composition.run_join (second source k d CH Cpad code) (fullMachine source k d)
    (RecoveryBoundedColdHierarchyDock.Count.budget source k CH Cpad code x+1+RecoveryCapacityDrivers.budget W+1+
      RecoveryProjectionCold.budget R Q B) (RecoveryFullBound.budget d R) _
    (Composition.joinedReceipt (Composition.joinedReceipt r0 r1) r2) r3 h012 (by
      rw [restart_after (Composition.joinedReceipt r0 r1) r2 (fullMachine source k d).start H
        (projectionData source k d A C P) hh2 ht2]
      exact h3)
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt (Composition.joinedReceipt r0 r1) r2) r3,
    h0123,?_,?_,?_,?_,?_,?_,?_⟩
  · change r0.steps+1+r1.steps+1+r2.steps+1+r3.steps ≤
      RecoveryBoundedColdHierarchyDock.Count.budget source k CH Cpad code x+1+
        RecoveryCapacityDrivers.budget W+1+RecoveryProjectionCold.budget R Q B+1+RecoveryFullBound.budget d R
    omega
  · intro i
    change r3.final.heads (old source k d i)=0
    rw [hh3]
    exact hheads i
  · intro i
    change r3.final.tapes (old source k d i)=_
    rw [ht3]
    exact prepared_data source k d R (oracleSizeBound d R) (RecoveryCapacityDrivers.capacityC W) Q
      (Codec.clauses p).length B (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) B)
      (DedupBytes.fields p) A C P F hblank hfields.clauseStream hfields.rawClauses hCC hCL
      hbank hrows hPQ hPB hFR hraw hcompare i
  · change r3.final.tapes (hierarchyPort source k d)=word
    rw [ht3,final_hierarchy]
    exact hfields.input
  · change r3.final.heads (hierarchyPort source k d)=0
    rw [hh3]
    exact hfields.inputHead
  · change r3.final.tapes (wPort source k d)=List.replicate W true
    rw [ht3,final_w]
    exact hCW
  · change r3.final.heads (wPort source k d)=0
    rw [hh3]
    exact hfh _ (by rfl)

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
