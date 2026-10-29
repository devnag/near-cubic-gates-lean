import Proof.Assembly.SourceSpec
import Proof.MachineModel.ControllerCappedRuntime
import Proof.MachineModel.TopDownPaidFamilySum
import Proof.Hierarchy.CompetitorRawRecordEmit
import Proof.CaseAnalysis.FinalSingleAppend
import Proof.MachineModel.TopDownPaidFamilyReserves

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open NativeRecipes
namespace NativeFamilyGenerator

structure Policy where
  width : Bool → Nat → Nat → Nat → Nat
  degree : Bool → Nat → Nat → Nat → Nat
  cacheCoefficient : Nat
  cacheDegree : Nat
  inputCoefficient : Nat
  inputDegree : Nat
  sourceCoefficient : Nat
  sourceDegree : Nat
  syntaxCoefficient : Nat
  syntaxDegree : Nat
  tableCoefficient : Nat
  tableDegree : Nat

structure Input where
  native : List Bool
  support : List Bool
  count : List Bool
  q : Nat
  L : Nat
  target : Nat
  recordWidth : Nat
  mode : Bool
  active : Bool

def inputWords (i : Input) : Fin 9 → List Bool :=
  ![i.native,i.support,i.count,UnaryTemplate.tape i.q,
    UnaryTemplate.tape i.L,UnaryTemplate.tape i.target,
    UnaryTemplate.tape i.recordWidth,[i.mode],[i.active]]

noncomputable def inputOf {q : Nat} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} (atoms : List (C10TotalDecode.Atom pcpp))
    (L target recordWidth : Nat) (mode active : Bool) : Input :=
  ⟨atoms.flatMap (fun a=>IndexFetchProgram.atomWords mode a 0),
   atoms.flatMap (fun a=>IndexFetchProgram.atomWords mode a 1),
   atoms.flatMap (fun a=>IndexFetchProgram.atomWords mode a 3),
   q,L,target,recordWidth,mode,active⟩

noncomputable abbrev SymAdmissible (sources : EightSources)
 (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
 (L target recordWidth : Nat) (policy : Policy) : Prop :=
let a := decompositionOf sources
let target := fun _ : Nat => target
∃ (s : Nat),
let w := policy.width true r.q L (target 0)

let degree := policy.degree true r.q L (target 0)

∃ (harity : (s+1)/2+s/2=(normalizedLiveSet (symmetricFourfoldOccurrences r) L)ᶜ.card),
∃ (hs : 67 ≤ s),
∃ (hpos : 1 ≤ w),
∃ (hload : 200*((normalizedLiveSet (symmetricFourfoldOccurrences r) L).card+
    w*((normalizedLiveSet (symmetricFourfoldOccurrences r) L).card+2)) ≤ s),
∃ (hmon : ∀ x∈pairList L target r,
    (CloseoutRowsUniversal.lower a (normalizedLiveSet (symmetricFourfoldOccurrences r) L)
      (symmetricFourfoldOccurrences r) (familyPolynomial L target r x.1 x.2)).length<2^w),
∃ (hdegree : ∀ x∈pairList L target r,
    RawMonomialDegreeAtMost degree (familyPolynomial L target r x.1 x.2)),
let c := policy.cacheCoefficient
let e := policy.cacheDegree

∃ (hcache : CompactBounds.radix a (normalizedLiveSet (symmetricFourfoldOccurrences r) L)
    (symmetricFourfoldOccurrences r) ≤ c*(r.q+1)^e),
∃ (hdeg : degree ≤ r.q+1),
P1TopDownFamilyShape.commonWidth a (normalizedLiveSet (symmetricFourfoldOccurrences r) L)
  (symmetricFourfoldOccurrences r) s harity degree ≤ recordWidth ∧
 CloseoutFinalC10SupplierAccuracy.rowAnswer (symmetricFourfoldRows (expanderOf sources) L target)
  r.q r.circuits < 2^recordWidth

noncomputable abbrev ThrAdmissible (sources : EightSources)
 (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
 (L target recordWidth : Nat) (policy : Policy) : Prop :=
let a := decompositionOf sources
let listDen := CloseoutFinalC10ThresholdRows.listDenominator a r target
let cutoff := CloseoutFinalC10ThresholdRows.primeCutoff a r target
∃ (s : Nat),
let w := policy.width false r.q L target

let degree := policy.degree false r.q L target

∃ (harity : (s+1)/2+s/2=(normalizedLiveSet (thresholdFourfoldOccurrences r) L)ᶜ.card),
∃ (hs : 67 ≤ s),
∃ (hpos : 1 ≤ w),
∃ (hload : 200*((normalizedLiveSet (thresholdFourfoldOccurrences r) L).card+
    w*((normalizedLiveSet (thresholdFourfoldOccurrences r) L).card+2)) ≤ s),
∃ (hmon : ∀ (sel : ThresholdRows.Selection a r) (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) L listDen)
    (offset : Fin prime.val),
    (CloseoutRowsUniversal.lower a (normalizedLiveSet (thresholdFourfoldOccurrences r) L)
      (thresholdFourfoldOccurrences r) (thresholdRow a r sel L listDen prime.val offset.val sample)).length<2^w),
∃ (hdegree : ∀ (sel : ThresholdRows.Selection a r) (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) L listDen)
    (offset : Fin prime.val),
    RawMonomialDegreeAtMost degree (thresholdRow a r sel L listDen prime.val offset.val sample)),
let c := policy.cacheCoefficient
let e := policy.cacheDegree

∃ (hcache : CompactBounds.radix a (normalizedLiveSet (thresholdFourfoldOccurrences r) L)
    (thresholdFourfoldOccurrences r) ≤ c*(r.q+1)^e),
∃ (hdeg : degree ≤ r.q+1),
P1TopDownFamilyShape.commonWidth a (normalizedLiveSet (thresholdFourfoldOccurrences r) L)
  (thresholdFourfoldOccurrences r) s harity degree ≤ recordWidth ∧
 C10ThresholdNaturalSum.nativeNumerator a r L listDen cutoff < 2^recordWidth

noncomputable abbrev Admissible (sources : EightSources) (policy : Policy)
 {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
 (atoms : List (C10TotalDecode.Atom pcpp)) (L target recordWidth : Nat) (mode : Bool) : Prop :=
 atoms.length ≤ 4 ∧
 (∀ atom∈atoms,C10NaturalModeAtoms.ModeAtom mode atom) ∧
 (∀ j : Fin 9,(inputWords (inputOf atoms L target recordWidth mode true) j).length ≤
  policy.inputCoefficient*(q+1)^policy.inputDegree) ∧
 if mode then SymAdmissible sources ⟨q,atoms.map C10NaturalModeAtoms.nativeSymmetricAtom⟩
  L target recordWidth policy
 else ThrAdmissible sources ⟨q,atoms.map C10NaturalModeAtoms.nativeThresholdAtom⟩
  L target recordWidth policy

@[irreducible] noncomputable def tapes (printer : WilliamsAlgorithm) (scratch : Nat) : Nat :=
 r_tapes printer+(10+scratch)

noncomputable def inputBank (printer : WilliamsAlgorithm) (scratch : Nat) (i : Input) :
 Fin (tapes printer scratch) → List Bool := by
 unfold tapes
 exact Fin.addCases (fun _=>[]) (fun j : Fin (10+scratch)=>
  if h : j.val<9 then inputWords i ⟨j.val,h⟩ else [])

structure Result (t : Nat) where
 ds : List P1TopDownPaidReusable.Datum
 S : Nat
 R : Nat
 B : Nat
 rowWidth : Nat
 total : Nat
 denominator : Nat
 residual : Nat
 fuel : Nat
 H : Fin t → Nat
 A : Fin t → List Bool

/-- Package chosen with the recipe's global parameters, before runtime input.
The semantic result depends only on the actual encoded words in Input. -/
structure Data where
 printer : WilliamsAlgorithm
 scratch : Nat
 states : Nat
 machine : Machine (tapes printer scratch) states
 policy : Policy
 result : Input → Result (tapes printer scratch)

/-- Explicit additive per-row bound. The syntax template term may be absorbed
into a table envelope only by the enclosing full ledger; it is not called
2^{o(q)}. Setup/finalization cost is retained separately. -/
def rowBudget (p : Policy) (i : Input) (s : Nat) : Nat :=
 p.sourceCoefficient*(i.q+1)^p.sourceDegree +
 p.syntaxCoefficient*2^(s/8)*(i.q+1)^p.syntaxDegree +
 p.tableCoefficient*2^s*(i.q+1)^p.tableDegree

noncomputable def familyPort (printer : WilliamsAlgorithm) (scratch : Nat)
 (j : Fin (r_tapes printer)) : Fin (tapes printer scratch) :=
 ⟨j.val,by unfold tapes;have h:=j.isLt;omega⟩

noncomputable def denominatorPort (printer : WilliamsAlgorithm) (scratch : Nat) :
 Fin (tapes printer scratch) := ⟨r_tapes printer+9,by unfold tapes;omega⟩

/-- The exact physical output, including the encoder's denominator word.
Original payload is protected outside this focused local bank. -/
noncomputable abbrev Produced (g : Data) (i : Input) : Prop :=
 let r := g.result i
 Step g.machine r.fuel (fun _=>0) (inputBank g.printer g.scratch i) r.H r.A ∧
 (∀ j : Fin (r_tapes g.printer),
  r.H (familyPort g.printer g.scratch j) =
   r_inputH g.printer r.ds r.S r.R r.B r.ds.length j) ∧
 (∀ j : Fin (r_tapes g.printer),
  r.A (familyPort g.printer g.scratch j) =
   r_inputT g.printer r.ds r.S r.R r.B r.rowWidth i.recordWidth r.ds.length j) ∧
 r.H (denominatorPort g.printer g.scratch)=0 ∧
 r.A (denominatorPort g.printer g.scratch)=RepairOrdinary.frame (natWord r.denominator)

noncomputable abbrev Envelope (g : Data) (i : Input) : Prop :=
 ∀ j : Fin 9,(inputWords i j).length ≤
  g.policy.inputCoefficient*(i.q+1)^g.policy.inputDegree

noncomputable abbrev LiveCorrect (sources : EightSources) (g : Data) : Prop :=
 ∀ {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
  (atoms : List (C10TotalDecode.Atom pcpp)) (L target recordWidth : Nat) (mode : Bool),
 Admissible sources g.policy atoms L target recordWidth mode →
 let i := inputOf atoms L target recordWidth mode true
 let r := g.result i
 Produced g i ∧
 NativeRows sources L target mode atoms g.printer r.S r.R r.B r.rowWidth r.ds r.total r.denominator ∧
 r.rowWidth ≤ recordWidth ∧ r.total < 2^recordWidth ∧
 r.residual = (if mode then
   (normalizedLiveSet (symmetricFourfoldOccurrences
     (⟨q,atoms.map C10NaturalModeAtoms.nativeSymmetricAtom⟩ : FourfoldRequest NormalizedSymmetricThresholdCircuit)) L)ᶜ.card
  else (normalizedLiveSet (thresholdFourfoldOccurrences
     (⟨q,atoms.map C10NaturalModeAtoms.nativeThresholdAtom⟩ : FourfoldRequest NormalizedThresholdThresholdCircuit)) L)ᶜ.card) ∧
 r.S=workspace g.printer (driverCapacity g.printer q r.residual g.policy.cacheCoefficient g.policy.cacheDegree) ∧
 r.R=rewind g.printer (driverCapacity g.printer q r.residual g.policy.cacheCoefficient g.policy.cacheDegree) ∧
 r.B=buffer (driverCapacity g.printer q r.residual g.policy.cacheCoefficient g.policy.cacheDegree) ∧
 r.fuel ≤ (r.ds.length+1)*(rowBudget g.policy i r.residual+5)+3 ∧
 f_budget g.printer r.S r.rowWidth recordWidth r.ds.length ≤
  (r.ds.length+1)*(rowBudget g.policy i r.residual+5)+3

/-- Terminal performs paid cleanup and builds the harmless empty family bank;
no NativeRows witness and no execution of the family machine is requested. -/
noncomputable abbrev TerminalCorrect (g : Data) : Prop :=
 ∀ (q L target recordWidth : Nat) (mode : Bool),
 let i : Input := ⟨[],[],[],q,L,target,recordWidth,mode,false⟩
 Envelope g i →
 let r := g.result i
 Produced g i ∧ r.ds=[] ∧ r.residual=0 ∧
 r.fuel ≤ g.policy.sourceCoefficient*(q+1)^g.policy.sourceDegree

noncomputable abbrev Correct (sources : EightSources) (g : Data) : Prop :=
 LiveCorrect sources g ∧ TerminalCorrect g

end NativeFamilyGenerator
