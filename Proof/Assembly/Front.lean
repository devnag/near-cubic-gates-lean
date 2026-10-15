import Proof.Assembly.FamilyInit

/-! Exact physical prefix/initializer junction. Native production is stated
as an actual Step from the nine input words, with a complete PrefixReady bank.
The bridge obligation proves the physical join and retains all semantic and
resource fields of the existing full generator contract. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

namespace PrefixInitializerFront
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPipeline
open NativeRecipes FamilyInitGenerator
open NativeFamilyGenerator
open P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

/-- Actual resident prefix output, before the separately charged initializer.
No intermediate tape is granted as initial advice. -/
noncomputable abbrev FrontProduced (g : PrefixCode) (i : Input) : Prop :=
 let r := g.result i
 Step g.machine r.fuel (fun _=>0) (inputBank g.printer (7+g.scratch) i) r.H r.A ∧
 PrefixReady g i

noncomputable abbrev FrontEnvelope (g : PrefixCode) (i : Input) : Prop :=
 ∀ j : Fin 9,(inputWords i j).length ≤
  g.policy.inputCoefficient*(i.q+1)^g.policy.inputDegree

noncomputable abbrev LiveFront (sources : EightSources) (g : PrefixCode) : Prop :=
 ∀ {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
  (atoms : List (C10TotalDecode.Atom pcpp)) (L target recordWidth : Nat) (mode : Bool),
 Admissible sources g.policy atoms L target recordWidth mode →
 let i := inputOf atoms L target recordWidth mode true
 let r := g.result i
 FrontProduced g i ∧
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
 (r.fuel+1+initFuel g.printer (scalars g i)) ≤ (r.ds.length+1)*(rowBudget g.policy i r.residual+5)+3 ∧
 f_budget g.printer r.S r.rowWidth recordWidth r.ds.length ≤
  (r.ds.length+1)*(rowBudget g.policy i r.residual+5)+3

noncomputable abbrev TerminalFront (g : PrefixCode) : Prop :=
 ∀ (q L target recordWidth : Nat) (mode : Bool),
 let i : Input := ⟨[],[],[],q,L,target,recordWidth,mode,false⟩
 FrontEnvelope g i →
 let r := g.result i
 FrontProduced g i ∧ r.ds=[] ∧ r.residual=0 ∧
 (r.fuel+1+initFuel g.printer (scalars g i)) ≤ g.policy.sourceCoefficient*(q+1)^g.policy.sourceDegree

/-- Native construction owns both cases and every scalar/reserve/budget. -/
structure Front (sources : EightSources) where
 code : PrefixCode
 live : LiveFront sources code
 terminal : TerminalFront code

/-- One genuine physical composition theorem. It consumes only the exact
prefix Step and bank invariant, the initializer's run, and preserved meanings.
It must prove slot injectivity, family projection and denominator preservation.
This is an open local proof obligation, not a new final assumption. -/
def AssemblyCertificate : Prop :=
 ∀ (sources : EightSources) (g : PrefixCode), LiveFront sources g →
 TerminalFront g → ∀ init : Initializer g.printer,
 NativeFamilyGenerator.Correct sources (assemble g init)

abbrev GlobalFront := (sources : EightSources) → (gamma : Real) →
 (hg : 0<gamma) → (hh : gamma<1/2) → (p : Parameters sources gamma) → Front sources

noncomputable def globalPrefix (bridge : AssemblyCertificate) (front : GlobalFront) :
 GlobalPrefix := fun sources gamma hg hh p =>
 let f := front sources gamma hg hh p
 { code := f.code, correct := bridge sources f.code f.live f.terminal }

end PrefixInitializerFront
