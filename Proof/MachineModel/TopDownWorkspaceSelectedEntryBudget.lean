import Proof.MachineModel.TopDownWorkspaceSelectedEntryReady
import Proof.CaseAnalysis.WitnessBoundedFamilyPreHierarchy

/-! The original cached header supplies a fixed-source polynomial bound for
the actual count initializer. Its degree is fixed before the hierarchy; the
prologue and append schedule are charged separately from hot supplier calls. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedEntryBudget
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary RecoveryRootRound
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.ProjectionNormalization PaddedRunnerBudgetClosure
open RepairSource.SelectedRecoveryIntegration
open WorkspaceSelectedEntry (size)
noncomputable section

def headerBound (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) (G n : Nat) :=
  n+a.minimumArity+FamilyResources.countBound
    (FamilyResources.countCoefficient a source.coefficient source.degrees.queries G)
    (FamilyResources.countDegree a source.coefficient source.degrees.queries G) n+1

def countEnvelope (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) (G n : Nat) := 2000*(headerBound source a G n+1)^2

theorem countEnvelope_polynomial (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) (G : Nat) : SourcePoly (countEnvelope source a G) := by
  change SourcePoly (fun n=>countEnvelope source a G n)
  unfold countEnvelope headerBound FamilyResources.countBound
  have hc:= (sourcePoly_pow (sourcePoly_id.add (polyDominated_const 1))
    (FamilyResources.countDegree a source.coefficient source.degrees.queries G)).const_mul
      (FamilyResources.countCoefficient a source.coefficient source.degrees.queries G)
  exact (sourcePoly_pow ((((sourcePoly_id.add (polyDominated_const a.minimumArity)).add hc).add
    (polyDominated_const 1)).add (polyDominated_const 1)) 2).const_mul 2000

theorem metadata_bound {n0 : Nat} (rq : PCPPRequest n0) (pcpp : PointwisePCPP rq.circuit)
    (M : Nat) (hq : rq.arity≤M) (hs : pcpp.systematicBits≤M)
    (ha : pcpp.auxiliaryBits≤M) (hc : pcpp.clauseBits≤M) :
    CloseoutCaseTwo.Metadata.budget rq pcpp≤1000*(M+1)^2 := by
  have bs:=PCPPQueryCost.natural_le _ _ hs
  have ba:=PCPPQueryCost.natural_le _ _ ha
  have bc:=PCPPQueryCost.natural_le _ _ hc
  unfold CloseoutCaseTwo.Metadata.budget CloseoutCaseTwo.Shape.budget
    CloseoutCaseTwo.Shape.rawBudget PCPPNativeNodeRead.budget
  norm_num only [PCPPQueryField.fieldCost,show natBitLength 3=2 by decide]
  nlinarith

theorem count_bound {n0 : Nat} (rq : PCPPRequest n0) (pcpp : PointwisePCPP rq.circuit)
    (M : Nat) (hq : rq.arity≤M) (hs : pcpp.systematicBits≤M)
    (ha : pcpp.auxiliaryBits≤M) (hc : 2^pcpp.clauseBits≤M) :
    CloseoutRowsOriginalCount.budget rq pcpp≤2000*(M+1)^2 := by
  have hb : pcpp.clauseBits≤M := (Nat.lt_two_pow_self).le.trans hc
  have hmeta:=metadata_bound rq pcpp M hq hs ha hb
  have power:=(C10EngineFuelSeam.power_budget_le pcpp.clauseBits).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 200 (Nat.add_le_add_right hb 1)) (Nat.add_le_add_right hc 1))
  unfold CloseoutRowsOriginalCount.budget
  nlinarith

theorem actual_count_bound (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) (k CH Cpad G : Nat) (code : List Bool)
    {n : Nat} (x : BitInput n) (hpad : k+3≤Cpad)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)))
    (hR : SelectedOracle.width source k CH Cpad code (List.ofFn x)≤n)
    (ho : oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G
      (SelectedOracle.width source k CH Cpad code (List.ofFn x))) :
    let rq:=ColdNative.request source a k CH Cpad code x hpad oracle
    CloseoutRowsOriginalCount.budget rq (a.output rq)≤countEnvelope source a G n := by
  intro rq
  let pcp:=SelectedStreams.pcp source k CH Cpad code (List.ofFn x)
  let R:=SelectedOracle.width source k CH Cpad code (List.ofFn x)
  let Q:=SelectedStreams.queries source k CH Cpad code (List.ofFn x)
  let hrp:=PCPPNativeHierarchyNodes.width_fits source k CH Cpad code x hpad
  let hqp:=PCPPNativeHierarchyNodes.queries_fit source k CH Cpad code x hpad
  let projections:=(pcp.normalized R Q hrp hqp).queryAddressBits x
  let formula:=(pcp.normalized R Q hrp hqp).decision x (fun _=>false)
  have identity:rq=PCPPSubstitution.sourceRequest a oracle projections formula:=rfl
  have short:=CloseoutSourceCounts.short_counts a oracle projections formula
    source.coefficient source.degrees.queries G (ColdFamilyGuards.query_bound source k CH Cpad code (List.ofFn x)) ho
  have upper:=FamilyResources.counts_bound a source.coefficient source.degrees.queries G R n hR
  have counts : (a.output rq).systematicBits+(a.output rq).auxiliaryBits≤headerBound source a G n ∧
      2^(a.output rq).clauseBits≤headerBound source a G n := by
    rw [identity]
    unfold headerBound
    exact ⟨short.1.trans (upper.trans (by omega)),short.2.trans (upper.trans (by omega))⟩
  have arity:rq.arity≤headerBound source a G n := by
    change max R a.minimumArity≤_
    unfold headerBound
    exact max_le (by omega) (by omega)
  exact count_bound rq (a.output rq) _ arity (by omega) (by omega) counts.2

theorem append_polylog (sources : EightSources) (k r : Nat) :
    C10EngineFuelSeam.Polylog (fun n=>CloseoutFinalC10AppendWorkspaceInit.budget
      (C10PartsSchedule.entryWidthSchedule sources k r n)) := by
  open C10EngineFuelSeam in
  have hw : Polylog (C10PartsSchedule.entryWidthSchedule sources k r) :=
    polylog_add (polylog_const _) (polylog_pow
      (polylog_add (polylog_widthAt sources k) (polylog_const 1)) r)
  have hpoly : Polylog (fun n=>762*(C10PartsSchedule.entryWidthSchedule sources k r n)^2+
      2958*C10PartsSchedule.entryWidthSchedule sources k r n+3448) :=
    polylog_add (polylog_add (polylog_mul (polylog_const 762) (polylog_pow hw 2))
      (polylog_mul (polylog_const 2958) hw)) (polylog_const 3448)
  exact polylog_mono (fun n=>(CloseoutFinalC10AppendWorkspaceInit.budget_eq _).le) hpoly

theorem append_bound (sources : EightSources) (k r : Nat) :
    ∃ onset,∀ n,onset≤n → CloseoutFinalC10AppendWorkspaceInit.budget
      (C10PartsSchedule.entryWidthSchedule sources k r n)≤(n+1)^2 := by
  obtain ⟨C,d,hd⟩:=append_polylog sources k r
  obtain ⟨onset,honset⟩:=C10FuelRepin.poly_polylog_le_polyFuel 0 C d 1 2 (by omega) (by omega)
  refine ⟨onset,fun n hn=>(hd n).trans ?_⟩
  simpa only [pow_zero,one_mul,C10FuelRepin.polyFuel] using honset n hn

def envelope (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r n : Nat) :=
  C10EngineFuelSeam.enginePreFuel sources k r p.clauseDegree n+
    countEnvelope (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources) p.degree n+
    CloseoutFinalC10AppendWorkspaceInit.budget (C10PartsSchedule.entryWidthSchedule sources k r n)+10

theorem admitted_width (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : C10LegalAdmission.passed sources p
      (WorkspaceGuardedWorker.reference k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits=true) :
    SelectedOracle.width (fixedProjection sources) k
      (SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
      (padding sources k (PolynomialClock.ordinaryClock k))
      (SelectedSource.code sources k (PolynomialClock.ordinaryClock k)) (List.ofFn x)≤n := by
  have passed:=(BoundedFamily.passed_exact (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources) k
    (SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
    (padding sources k (PolynomialClock.ordinaryClock k)) (WorkspaceSelectedAdmission.coldCutoff sources)
    p.clauseDegree p.degree p.copies 1 1 (CompetitorRationalGap.zeta (constantsOf sources))
    (SelectedSource.code sources k (PolynomialClock.ordinaryClock k)) x bits (Nat.le_max_right _ _)).mp hp
  have live:=ColdFamilyGuards.live (fixedProjection sources) k
    (SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
    (padding sources k (PolynomialClock.ordinaryClock k)) (WorkspaceSelectedAdmission.coldCutoff sources)
    p.degree (SelectedSource.code sources k (PolynomialClock.ordinaryClock k)) (List.ofFn x)
    (BoundedFields.oracle bits) passed.2.2.1
  simpa only [List.length_ofFn] using live.2.1

/-- This is the literal fuel of EntryReady.run at its actual request. -/
theorem actual_fuel_le (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r n : Nat) (x : BitInput n) (bits : List Bool)
    (oracle : BooleanCircuit (SelectedOracle.width (fixedProjection sources) k
      (SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
      (padding sources k (PolynomialClock.ordinaryClock k))
      (SelectedSource.code sources k (PolynomialClock.ordinaryClock k)) (List.ofFn x)))
    (hp : C10LegalAdmission.passed sources p
      (WorkspaceGuardedWorker.reference k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits=true)
    (ho : oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound p.degree
      (SelectedOracle.width (fixedProjection sources) k
        (SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
        (padding sources k (PolynomialClock.ordinaryClock k))
        (SelectedSource.code sources k (PolynomialClock.ordinaryClock k)) (List.ofFn x))) :
    let rq:=ColdNative.request (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources) k
      (SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
      (padding sources k (PolynomialClock.ordinaryClock k))
      (SelectedSource.code sources k (PolynomialClock.ordinaryClock k)) x (Nat.le_max_right _ _) oracle
    C10EngineFuelSeam.enginePreFuel sources k r p.clauseDegree n+
      WorkspaceSelectedEntryCount.budget (CloseoutLanguage.selectedPCPP sources) rq
        (C10PartsSchedule.entryWidthSchedule sources k r n)+5≤envelope sources p k r n := by
  intro rq
  have h:=actual_count_bound (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources) k
    (SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
    (padding sources k (PolynomialClock.ordinaryClock k)) p.degree
    (SelectedSource.code sources k (PolynomialClock.ordinaryClock k)) x (Nat.le_max_right _ _) oracle
    (admitted_width sources p k n x bits hp) ho
  unfold WorkspaceSelectedEntryCount.budget envelope
  dsimp only [rq] at *
  omega

/-- The exponent is selected before both k and the eventual width schedule r.
The coefficient and finite onset may depend on these fixed program choices. -/
theorem degree_before_hierarchy (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) :
    ∃ degree,∀ k r,∃ coefficient onset,∀ n,onset≤n →
      envelope sources p k r n≤coefficient*(n+1)^degree := by
  obtain ⟨d,C,hC⟩:=countEnvelope_polynomial (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources) p.degree
  refine ⟨max d 2,fun k r=>?_⟩
  obtain ⟨A,hA⟩:=WorkspaceSelectedEntry.resource sources k r p.clauseDegree
  obtain ⟨B,hB⟩:=append_bound sources k r
  refine ⟨C+12,max A B,fun n hn=>?_⟩
  have pre:=hA n ((Nat.le_max_left _ _).trans hn)
  have app:=hB n ((Nat.le_max_right _ _).trans hn)
  have count:=hC n
  have hd: (n+1)^d≤(n+1)^max d 2:=Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
  have h2: (n+1)^2≤(n+1)^max d 2:=Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
  have count':=count.trans (Nat.mul_le_mul_left C hd)
  have hp:1≤(n+1)^max d 2:=Nat.one_le_pow _ _ (by omega)
  unfold envelope
  nlinarith

end
end NearCubicWires.P1TopDown.WorkspaceSelectedEntryBudget
