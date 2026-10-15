import Proof.Assembly.Ready
import Proof.Assembly.ClosureBinaryCacheRun
import Proof.Hierarchy.CompetitorRecordRewind

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace CachedFamilyLoader
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open FixedLivePackets
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

structure Program {printer : WilliamsAlgorithm} {work : Nat}
    (row : SharedRowLayout.Program printer work) (U : Nat) where
  familySlots : Fin (SharedRowLayout.tapes printer work+1)→Fin U
  familyInjective : Function.Injective familySlots
  poolSlots : Fin 373→Fin U
  poolInjective : Function.Injective poolSlots
  rewindSlots : Fin 3→Fin U
  rewindInjective : Function.Injective rewindSlots
  directSource : rewindSlots 0=familySlots ((SharedRowLayout.descriptor printer work).castAdd 1)
  seedStates : Nat
  seed : Machine U seedStates
  setupStates : Nat
  setup : Machine U setupStates
  finishStates : Nat
  finish : Machine U finishStates

def before {printer : WilliamsAlgorithm} {work U : Nat}
    {row : SharedRowLayout.Program printer work} (p : Program row U) :=
  Composition.machine p.seed
    (Composition.machine (RecoveryFocus.machine p.poolSlots BinaryCacheColdRun.machine) p.setup)
def after {printer : WilliamsAlgorithm} {work U : Nat}
    {row : SharedRowLayout.Program printer work} (p : Program row U) :=
  Composition.machine (RecoveryFocus.machine p.rewindSlots CompetitorRecordRewind.machine) p.finish

def code {printer : WilliamsAlgorithm} {work U : Nat}
    {row : SharedRowLayout.Program printer work} (p : Program row U) :
    RefillCycle.Code (SharedRowLayout.code row) U where
  slots := p.familySlots
  injective := p.familyInjective
  beforeStates := _
  before := before p
  afterStates := _
  after := after p

def cacheArgs {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L) :
    BinaryCacheColdJoin.Args q :=
  ⟨Packets.live F,C10SupplierRowInput.childList a (Packets.live F) F.occurrences⟩

theorem cache_word {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (g : Packets.Geometry F) :
    BinaryCacheColdRun.output (cacheArgs a F) 34=exactListWord (Packets.pool a F g) :=
  BinaryCacheColdRun.c10_output a (Packets.live F) F.occurrences (Packets.residual F) g.arity

def descriptorWord (printer : WilliamsAlgorithm) (ds : List P1TopDownPaidReusable.Datum) :=
  ds.flatMap (P1TopDownPaidReusable.Datum.word printer)

def Spec {printer : WilliamsAlgorithm} {work U : Nat}
    {row : SharedRowLayout.Program printer work} (p : Program row U)
    (ds : List P1TopDownPaidReusable.Datum) (fuel : Nat) (H H' : Fin U→Nat)
    (A A' : Fin U→List Bool) : Prop :=
  ∃ (q L : Nat) (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (g : Packets.Geometry F) (layout : Packets.Layout a F g)
    (facts : ∀ r∈F.rows,Packets.PacketFacts a F g r),
  ds=dataList a F g layout facts ∧
  ∃ (s : ExternalRowFamily.State (t:=SharedRowLayout.tapes printer work) printer)
    (poolReserve : Fin 373→Nat)
    (familyReserve : Fin (SharedRowLayout.tapes printer work+1)→Nat)
    (poolH : Fin U→Nat) (poolA : Fin U→List Bool)
    (ambientH : Fin U→Nat) (ambientA : Fin U→List Bool)
    (seedFuel setupFuel finishFuel rewindCap descriptorReserve : Nat),
  let entry := ExternalRowFamily.entry printer (SharedRowLayout.code row) F s
  let final := ExternalRowFamily.exit printer (SharedRowLayout.code row) a F g layout facts s
  let finalH := dockH p.familySlots ambientH final.heads
  let finalA := install p.familySlots ambientA (fun i=>ZeroPadding.pad (familyReserve i) (final.tapes i))
  let pos := (descriptorWord printer ds).length
  let word := ZeroPadding.pad descriptorReserve (descriptorWord printer ds)
  let rewindReserve : Fin 3→Nat := ![0,0,rewindCap]
  Step p.seed seedFuel H A
    (dockH p.poolSlots poolH (fun _=>0))
    (install p.poolSlots poolA (fun i=>ZeroPadding.pad (poolReserve i) (BinaryCacheColdRun.input (cacheArgs a F) i))) ∧
  Step p.setup setupFuel
    (dockH p.poolSlots poolH (fun _=>0))
    (install p.poolSlots poolA (fun i=>ZeroPadding.pad (poolReserve i) (BinaryCacheColdRun.output (cacheArgs a F) i)))
    (dockH p.familySlots ambientH entry.heads) (install p.familySlots ambientA (fun i=>ZeroPadding.pad (familyReserve i) (entry.tapes i))) ∧
  SharedRowLayout.Ready printer row a F g layout facts s ∧
  pos≤rewindCap ∧
  (∀ i,finalH (p.rewindSlots i)=(CompetitorRecordRewind.cfg 0 word pos rewindCap 0 0 []).heads i) ∧
  (∀ i,finalA (p.rewindSlots i)=ZeroPadding.pad (rewindReserve i) ((CompetitorRecordRewind.cfg 0 word pos rewindCap 0 0 []).tapes i)) ∧
  Step p.finish finishFuel
    (dockH p.rewindSlots finalH (CompetitorRecordRewind.cfg 2 word 0 rewindCap 0 0 (List.replicate rewindCap false)).heads)
    (install p.rewindSlots finalA (fun i=>ZeroPadding.pad (rewindReserve i) ((CompetitorRecordRewind.cfg 2 word 0 rewindCap 0 0 (List.replicate rewindCap false)).tapes i)))
    H' A' ∧
  seedFuel+1+(BinaryCacheColdRun.budget (cacheArgs a F)+1+setupFuel)+1+
    (ExternalRowFamily.budget printer F s+1+(2*rewindCap+2+1+finishFuel))≤fuel

theorem projection {printer : WilliamsAlgorithm} {work U : Nat}
    {row : SharedRowLayout.Program printer work} (p : Program row U)
    (ds : List P1TopDownPaidReusable.Datum) (fuel : Nat) (H H' : Fin U→Nat)
    (A A' : Fin U→List Bool) (h : Spec p ds fuel H H' A A') :
    RefillCycle.Spec (code p) ds fuel H H' A A' := by
  obtain ⟨q,L,a,F,g,layout,facts,hds,s,poolReserve,familyReserve,poolH,poolA,ambientH,ambientA,
    seedFuel,setupFuel,finishFuel,rewindCap,descriptorReserve,seed,setup,rows,cap,heads,bank,finish,bound⟩ := h
  have pool := ((BinaryCacheColdRun.c10_run a (Packets.live F) F.occurrences
    (Packets.residual F) g.arity).1.pad poolReserve).focus p.poolSlots p.poolInjective poolH poolA
  have first := seed.seq (pool.seq setup)
  obtain ⟨receipt,hr,final,_cost⟩ := CompetitorRecordRewind.rewind_run
    (ZeroPadding.pad descriptorReserve (descriptorWord printer ds)) rewindCap (descriptorWord printer ds).length cap
  have rewind := ((Step.of_run hr (congrArg Configuration.heads final)
    (congrArg Configuration.tapes final)).pad (![0,0,rewindCap] : Fin 3→Nat)).dock p.rewindSlots p.rewindInjective _ _ heads bank
  have last := rewind.seq finish
  exact ⟨q,L,a,F,g,layout,facts,hds,s,familyReserve,ambientH,ambientA,
    seedFuel+1+(BinaryCacheColdRun.budget (cacheArgs a F)+1+setupFuel),
    2*rewindCap+2+1+finishFuel,first,
    SharedRowLayout.ready printer row a F g layout facts s rows,last,bound⟩

theorem run {printer : WilliamsAlgorithm} {work U : Nat}
    {row : SharedRowLayout.Program printer work} (p : Program row U)
    (ds : List P1TopDownPaidReusable.Datum) (fuel : Nat) (H H' : Fin U→Nat)
    (A A' : Fin U→List Bool) (h : Spec p ds fuel H H' A A') :
    Step (RefillCycle.machine (code p)) fuel H A H' A' :=
  RefillCycle.run (code p) ds fuel H H' A A' (projection p ds fuel H H' A A' h)

end
end CachedFamilyLoader

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open NativeRecipes
open FixedLivePackets
namespace PhysicalFamilyLoader
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-- The existing reusable family loader source; the descriptor is appended here. -/
noncomputable def sourcePort (a : WilliamsAlgorithm) : Fin (r_tapes a) :=
 ⟨P1TopDownPaidPayload.tapes a+1+2,by unfold r_tapes; omega⟩

noncomputable abbrev CachedSourceSpec (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
 (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (ci : Fin (2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits))
 (globalH globalHnext : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→Nat)
 (globalA globalAfter : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→List Bool)
 (b siteFuel : Nat) : Prop :=
 let pcpp := pcppAt sources k clock x oracle
 let coordinate := CappedCoordinates.coordinate sources k clock p den x oracle bits
 ∃ (order : List (CircuitMonomial (C10TotalDecode.Atom pcpp) 4)),
 ∃ (_horder : order.Perm (CloseoutFinalC10SupplierCalls.siteCalls ph pcpp coordinate C10TotalDecode.Atom.systematic ci).monomials),
 ∃ (L target : Nat),
∃ (a : WilliamsAlgorithm),
∃ (rowWork : Nat),
∃ (rowProgram : SharedRowLayout.Program a rowWork),
let rowTapes := SharedRowLayout.tapes a rowWork
let rowCode := SharedRowLayout.code rowProgram
∃ (prepT : Nat),
∃ (_hsize : scratch = r_tapes a+14+prepT),
∃ (dflt : P1TopDownPaidReusable.Datum),
∃ (ds : Nat → List P1TopDownPaidReusable.Datum),
∃ (xs : Nat → List Nat),
∃ (S : Nat → Nat),
∃ (R : Nat → Nat),
∃ (B : Nat → Nat),
∃ (rowWidth : Nat → Nat),
∃ (total : Nat → Nat),
∃ (denominator : Nat → Nat),
∃ (D : Nat → Nat),
∃ (cap : Nat → Nat),
∃ (logSize : Nat → Nat),
∃ (resetSize : Nat → Nat),
∃ (coefficient : Nat → CompetitorValidity.Estimate),
∃ (old : Nat → List Bool),
∃ (phasePrefix : List Stream.Entry),
∃ (entries : List Stream.Entry),
∃ (_hlen : entries.length=order.length),
∃ (_hxs : xs=fun j=>(ds j).map FixedLivePackets.datumValue),
∃ (_hcoeff : ∀ j<entries.length,coefficient j=CloseoutFinalC10SupplierCalls.coefficientEstimate
  ((order.map (fun m=>m.coefficient)).getD j 0)),
∃ (_hnative : ∀ j<entries.length,NativeRows selector compiler sources L target mode
  ((order.map (fun m=>m.factors)).getD j []) a (S j) (R j) (B j) (rowWidth j) (ds j) (total j) (denominator j)),
∃ (U : Nat),
∃ (slots : Fin (r_tapes a) → Fin U),
∃ (_hs : ∀ i,(slots i).val=(SelectedBranchPhases.offset sources p k r)+1155+i.val),
∃ (enc : Fin 11 → Fin U),
∃ (_he : ∀ i,(enc i).val=if i.val=5 then (SelectedBranchPhases.offset sources p k r)+1155+r_tapes a-5
   else (SelectedBranchPhases.offset sources p k r)+1155+r_tapes a+(if i.val<5 then i.val else i.val-1)),
∃ (app : Fin 6 → Fin U),
∃ (_ha : ∀ i,(app i).val=(![(SelectedBranchPhases.offset sources p k r)+1155+r_tapes a+5,(CloseoutFinalC10RetainedPhaseFold.wordSlots (SelectedBranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (SelectedBranchPhases.offset_ge sources p k r) (SelectedBranchPhases.fresh_lt sources p k r scratch) ph 81).val,
   (SelectedBranchPhases.offset sources p k r)+1155+r_tapes a+10,(CloseoutFinalC10RetainedPhaseFold.wordSlots (SelectedBranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (SelectedBranchPhases.offset_ge sources p k r) (SelectedBranchPhases.fresh_lt sources p k r scratch) ph 90).val,(SelectedBranchPhases.offset sources p k r)+1155+r_tapes a+11,(SelectedBranchPhases.offset sources p k r)+1155+r_tapes a+12] : Fin 6 → Nat) i),
∃ (H : Nat → Fin U → Nat),
∃ (A : Nat → Fin U → List Bool),
∃ (reserveSize : Nat),
∃ (_hw : ∀ j<entries.length,rowWidth j≤b),
∃ (_hfit : ∀ j<entries.length,total j<2^b),
∃ (_hH : ∀ j<entries.length,∀ i,H j (slots i)=r_inputH a (ds j) (S j) (R j) (B j) (xs j).length i),
∃ (_hA : ∀ j<entries.length,∀ i,A j (slots i)=r_inputT a (ds j) (S j) (R j) (B j)
   (rowWidth j) b (xs j).length i),
∃ (_hc : ∀ j<entries.length,4*b+5≤cap j),
∃ (_hold : ∀ j<entries.length,(old j).length≤D j),
∃ (_hl : ∀ j<entries.length,20*b+27≤logSize j),
∃ (_hr : ∀ j<entries.length,CloseoutFinalC10AppendPositioning.rawBudget b (phasePrefix++entries.take j).length≤resetSize j),
∃ (_heH : ∀ j<entries.length,∀ i,dockH slots (H j)
   (r_outputH a (ds j) (S j) (R j) (B j) (rowWidth j) (xs j)) (enc i)=0),
∃ (_haH : ∀ j<entries.length,∀ i,dockH slots (H j)
   (r_outputH a (ds j) (S j) (R j) (B j) (rowWidth j) (xs j)) (app i)=0),
∃ (_hfields : ∀ j<entries.length,∀ Z,
   Step (f_machine a) (f_budget a (S j) (rowWidth j) b (xs j).length)
    (r_inputH a (ds j) (S j) (R j) (B j) (xs j).length)
    (r_inputT a (ds j) (S j) (R j) (B j) (rowWidth j) b (xs j).length)
    (r_outputH a (ds j) (S j) (R j) (B j) (rowWidth j) (xs j))
    (r_outputT a (ds j) (S j) (R j) (B j) (rowWidth j) b (xs j) Z)  →
   r_outputT a (ds j) (S j) (R j) (B j) (rowWidth j) b (xs j) Z
    (P1TopDownPaidFamilySum.sumSlots (f_raw a) 5)=RepairOrdinary.frame (SignedSortKey.binary b (total j))  →
   let entry : Stream.Entry := ⟨coefficient j,total j,denominator j⟩
   let mid := install slots (A j)
    (r_outputT a (ds j) (S j) (R j) (B j) (rowWidth j) b (xs j) Z)
   (∀ i,mid (enc i)=e_bank b entry (D j) (cap j) (old j) i) ∧
   (∀ i,install enc mid (e_bank b entry (D j) (cap j)
     (ZeroPadding.pad (D j) (Stream.entryWord b entry))) (app i)=
     CloseoutFinalC10AppendPositioning.tapes b (D j) (logSize j) (resetSize j) entry (phasePrefix++entries.take j) i)),
∃ (familyCost : Nat),
∃ (refillCost : Nat),
∃ (firstCost : Nat),
∃ (refillCycle : CachedFamilyLoader.Program rowProgram U),
∃ (firstCycle : CachedFamilyLoader.Program rowProgram (U+1)),
∃ (_refillSource : refillCycle.rewindSlots 0=slots (sourcePort a)),
∃ (_firstSource : firstCycle.rewindSlots 0=(slots (sourcePort a)).castAdd 1),
let refill := RefillCycle.machine (CachedFamilyLoader.code refillCycle)
let first := RefillCycle.machine (CachedFamilyLoader.code firstCycle)
∃ (whole : Fin (U+1) → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)),
∃ (_hwhole : ∀ i,(whole i).val=i.val),
∃ (counterReserve : Nat),
let reserve := fun (i : Fin U) => if (SelectedBranchPhases.offset sources p k r + 1155) ≤ i.val then reserveSize else 0
 let queried := install (SelectedBranchPhases.cache sources p k r scratch mode) globalA
   (PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k clock x oracle) ((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle))) (req sources k clock x oracle).arity ci.val
     (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources) ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity))
     (natListWord [literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauses ci).left,
       literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauses ci).right]))
 let originalH := fun i=>globalH (whole i)
 let originalA := fun i=>queried (whole i)
 let counterCaps : Fin (U+1) → Nat := fun i=>if i.val=U then counterReserve else 0
 let family := Composition.machine (RecoveryFocus.machine slots (f_machine a))
  (Composition.machine (RecoveryFocus.machine enc e_machine)
    (RecoveryFocus.machine app CloseoutFinalC10SingleAppend.machine))
 let fuel := fun j=>f_budget a (S j) (rowWidth j) b (xs j).length+1+
   (2*D j+4+1+(2*e_emitCost b+2)+1+
    CloseoutFinalC10AppendPositioning.budget b (phasePrefix++entries.take j).length)
 let outH := fun j=>dockH slots (H j)
   (r_outputH a (ds j) (S j) (R j) (B j) (rowWidth j) (xs j))
 let outA := fun j Z=>
   let entry : Stream.Entry := ⟨coefficient j,total j,denominator j⟩
   install app
    (install enc (install slots (A j)
      (r_outputT a (ds j) (S j) (R j) (B j) (rowWidth j) b (xs j) Z))
     (e_bank b entry (D j) (cap j) (ZeroPadding.pad (D j) (Stream.entryWord b entry))))
    (CloseoutFinalC10AppendPositioning.tapes b (D j) (logSize j) (resetSize j)
      entry ((phasePrefix++entries.take j)++[entry]))
 let padded := fun j i=>ZeroPadding.pad (reserve i) (A j i)
 let body := Composition.machine family refill
 let state := fun j (_out : List Bool)=>(⟨body.start,H j,padded j⟩ : Configuration U _)

∃ (_hcost : (∀ j<entries.length,fuel j≤familyCost)),
∃ (_hrefill : (∀ j<entries.length,∀ Z,Step family (fuel j) (H j) (A j) (outH j) (outA j Z)  →
   CachedFamilyLoader.Spec refillCycle (ds (j+1)) refillCost
    (outH j) (H (j+1)) (fun i=>ZeroPadding.pad (reserve i) (outA j Z i)) (padded (j+1)))),
∃ (_hfirst : CachedFamilyLoader.Spec firstCycle (ds 0) firstCost originalH
   (RepeatMachine.cfg 0 (state 0 []) entries.length 1).heads originalA
   (fun i=>ZeroPadding.pad (counterCaps i) ((RepeatMachine.cfg 0 (state 0 []) entries.length 1).tapes i))),
∃ (_hfinalH : (dockH whole globalH (RepeatMachine.cfg 3 (state entries.length []) entries.length 1).heads=globalHnext)),
∃ (_hfinalA : (install whole queried (fun i=>ZeroPadding.pad (counterCaps i)
    ((RepeatMachine.cfg 3 (state entries.length []) entries.length 1).tapes i))=globalAfter)),
∃ (_hcode : (⟨_,RecoveryFocus.machine whole (Composition.machine first (CloseoutRowsDegreeLoop.machine body))⟩ : Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)=site mode ph),
firstCost+1+(entries.length*(familyCost+1+refillCost+3)+3) ≤ siteFuel

noncomputable def sourceProjection (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
 (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (ci : Fin (2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits))
 (globalH globalHnext : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→Nat)
 (globalA globalAfter : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→List Bool)
 (b siteFuel : Nat) (supplied : CachedSourceSpec selector compiler sources p k den r scratch clock n x oracle bits site mode ph ci globalH globalHnext globalA globalAfter b siteFuel) :
 FixedLivePackets.NativeSourceSpec selector compiler sources p k den r scratch clock n x oracle bits site mode ph ci globalH globalHnext globalA globalAfter b siteFuel := by
 rcases supplied with ⟨order,horder,L,target,a,rowWork,rowProgram,prepT,hsize,dflt,ds,xs,S,R,B,rowWidth,total,denominator,D,cap,logSize,resetSize,coefficient,old,phasePrefix,entries,hlen,hxs,hcoeff,hnative,U,slots,hs,enc,he,app,ha,H,A,reserveSize,hw,hfit,hH,hA,hc,hold,hl,hr,heH,haH,hfields,familyCost,refillCost,firstCost,refillCycle,firstCycle,refillSource,firstSource,whole,hwhole,counterReserve,hcost,hrefill,hfirst,hfinalH,hfinalA,hcode,hbound⟩
 have refills := fun j hj Z hrun =>
   CachedFamilyLoader.run refillCycle (ds (j+1)) refillCost _ _ _ _ (hrefill j hj Z hrun)
 have firstRun := CachedFamilyLoader.run firstCycle (ds 0) firstCost _ _ _ _ hfirst
 exact ⟨order,horder,L,target,a,prepT,hsize,dflt,ds,xs,S,R,B,rowWidth,total,denominator,D,cap,logSize,resetSize,coefficient,old,phasePrefix,entries,hlen,hxs,hcoeff,hnative,U,slots,hs,enc,he,app,ha,H,A,reserveSize,hw,hfit,hH,hA,hc,hold,hl,hr,heH,haH,hfields,familyCost,refillCost,firstCost,_,_,RefillCycle.machine (CachedFamilyLoader.code refillCycle),RefillCycle.machine (CachedFamilyLoader.code firstCycle),whole,hwhole,counterReserve,hcost,refills,firstRun,hfinalH,hfinalA,hcode,hbound⟩

end PhysicalFamilyLoader

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open NativeRecipes

open FixedLivePackets
namespace PhysicalFamilyLoader

noncomputable abbrev CachedPhase (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
   Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (hin : Fin (SelectedBranchPhases.tapes sources p k r scratch) → Nat)
 (tin : Fin (SelectedBranchPhases.tapes sources p k r scratch) → List Bool)
 (fuel width : Nat) : Prop :=
let pcpp := pcppAt sources k clock x oracle
 let Atom := C10TotalDecode.Atom pcpp
 let constants := NearCubicWires.RepairSource.CloseoutFinal.constantsOf sources
 let coordinate := CappedCoordinates.coordinate sources k clock p den x oracle bits
 let systematicAtom := C10TotalDecode.Atom.systematic (pcpp := pcpp)
 let evaluate := C10TotalDecode.evaluate (pcpp := pcpp)
 let mass : Real := ((CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).coefficientMass : Rat)
 let L := SelectedBranchPhases.offset sources p k r
 let B := ControllerSelectedContinuation.bodyTapes sources p k r scratch
 let hL := SelectedBranchPhases.offset_ge sources p k r
 let hFresh := SelectedBranchPhases.fresh_lt sources p k r scratch
 let t := SelectedBranchPhases.tapes sources p k r scratch
 let body := SelectedBranchPhases.body sources p k r scratch
 let driver := SelectedBranchPhases.driver sources p k r scratch
 ∃ (liveScale target : Nat)
   (limits : CanonicalWitnessCodec.LegalSumLimits) (denBits : Nat)
   (order : List (CircuitMonomial Atom 4)),
 let supplier := LiveRows.supplier sources liveScale target mode (pcpp := pcpp)
 let failure := failure target
 ∃ (b : Nat)
    (entries : List NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.Entry)
    (H : Nat → Fin B → Nat)
    (A : Nat → Fin B → List Bool)
    (entryFuel : Nat)
    (N : Nat)
    (cost : Nat)
    (middleH : Fin t → Nat)
    (middle : Fin t → List Bool)
    (_horder : (CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).monomials.Perm order)
    (_hmode : ∀ m ∈ order, ∀ atom ∈ m.factors, C10NaturalModeAtoms.ModeAtom mode atom)
    (_hrecords : List.Forall₂ (fun m e =>
      e.coefficient = CloseoutFinalC10SupplierCalls.coefficientEstimate m.coefficient ∧
      e.count = (LiveRows.fraction sources liveScale target mode m.factors).1 ∧
      e.denominator = (LiveRows.fraction sources liveScale target mode m.factors).2)
      order entries)
    (_hmass : (CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).coefficientMass ≤
      C10FamilyMass.siteMassBound limits.coefficientMassCap ph)
    (_hcoeff : CloseoutFinalC10SupplierCalls.CoefficientsFit b
      (CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom))
    (_htarget : C10SupplierAccuracyChain.accuracyTarget constants limits ph ≤ target)
    (_htargetpos : 0 < target)
    (_hden : ∀ m ∈ order,
      (LiveRows.fraction sources liveScale target mode m.factors).2 ≤ 2^denBits)
    (_hdenwidth : denBits+1 ≤ b)
    (_hHw : ∀ i, H N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i) = 0)
    (_hHf : ∀ i, H N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph i) = 0)
    (_hwidthDriver : A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph 218) = List.replicate b true)
    (_hcount : A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph 90) = NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word entries.length)
    (_hstream : A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph 81) = NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.words b entries)
    (_hblank : ∀ i : Fin 278, 2 ≤ i.val → i.val < 215 → i.val ≠ 81 → i.val ≠ 90 → A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i)=[])
    (_hfresh : ∀ i : Fin 278, 219 ≤ i.val → A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i)=[])
    (_hrecord : A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph 215)=[])
    (_hlog : A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph 218)=[])
    (_hentry : Step (RecoveryFocus.machine body (SelectedBranchPhases.phaseEntry sources p k r scratch mode ph).2)
      entryFuel hin tin middleH middle)
    (_hhead : ∀ i, middleH (body i)=H 0 i)
    (_htape : ∀ i, middle (body i)=A 0 i)
    (_hdriver : middleH driver=1)
    (_hword : middle driver=UnaryTemplate.tape N)
    (_hN : N=2^pcpp.clauseBits)
    (siteFuel : Nat)
    (_hcost : 4*N+PCPPQueryCachedBounds.callBudget (CloseoutLanguage.selectedPCPP sources)
       ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)+siteFuel+21≤cost)
    (s_after : Nat → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (_s_head : ∀ (j : Nat), j≤2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits → ∀ (i : Fin 19),H j (SelectedBranchPhases.cache sources p k r scratch mode i)=0)
    (_s_terminal_head : ∀ (j : Nat),j<2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits → H j (LiveClauseSites.Selected.terminal sources p k r scratch)=0)
    (_s_count : ∀ (j : Nat),j<2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits → A j (LiveClauseSites.Selected.terminal sources p k r scratch)=
   List.replicate (2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits) true)
    (_s_cached : ∀ (j : Nat),j<2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits → ∀ (i : Fin 19),A j (SelectedBranchPhases.cache sources p k r scratch mode i)=
   PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k clock x oracle) ((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle))) (req sources k clock x oracle).arity j
   (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources) ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)) [] i)
    (_s_source : ∀ ci : Fin (2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits),
      CachedSourceSpec selector compiler sources p k den r scratch clock n x oracle bits site mode ph ci
       (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel)
    (_s_restored : ∀ (j : Nat),j<2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits → ∀ (i : Fin 19),s_after j (SelectedBranchPhases.cache sources p k r scratch mode i)=
   PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k clock x oracle) ((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle))) (req sources k clock x oracle).arity j
   (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources) ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)) [] i)
    (_s_next : ∀ (j : Nat),j<2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits → A (j+1)=
   install (SelectedBranchPhases.cache sources p k r scratch mode) (s_after j)
    (PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k clock x oracle) ((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle))) (req sources k clock x oracle).arity (j+1)
     (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources) ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)) [])),
 fuel=entryFuel+1+(N*(cost+3)+3+1+CloseoutFinalC10RetainedPhaseFold.fuel b entries.length) ∧
 width=CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width b) entries

noncomputable def phaseProjection (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
   Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (hin : Fin (SelectedBranchPhases.tapes sources p k r scratch) → Nat)
 (tin : Fin (SelectedBranchPhases.tapes sources p k r scratch) → List Bool)
 (fuel width : Nat) (supplied : CachedPhase selector compiler sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width) : FixedLivePackets.PreparedPhase selector compiler sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width := by
 rcases supplied with ⟨liveScale,target,limits,denBits,order,b,entries,H,A,entryFuel,N,cost,middleH,middle,horder,hmode,hrecords,hmass,hcoeff,htarget,htargetpos,hden,hdenwidth,_hHw,_hHf,_hwidthDriver,_hcount,_hstream,_hblank,_hfresh,_hrecord,_hlog,_hentry,_hhead,_htape,_hdriver,_hword,_hN,siteFuel,_hcost,s_after,s_head,s_terminal_head,s_count,s_cached,s_source,s_restored,s_next,hfuel,hwidth⟩
 have sourcesReady := fun ci => sourceProjection selector compiler sources p k den r scratch clock n x oracle bits site mode ph ci
   (H ci.val) (H (ci.val+1)) (A ci.val) (s_after ci.val) b siteFuel (s_source ci)
 exact ⟨liveScale,target,limits,denBits,order,b,entries,H,A,entryFuel,N,cost,middleH,middle,horder,hmode,hrecords,hmass,hcoeff,htarget,htargetpos,hden,hdenwidth,_hHw,_hHf,_hwidthDriver,_hcount,_hstream,_hblank,_hfresh,_hrecord,_hlog,_hentry,_hhead,_htape,_hdriver,_hword,_hN,siteFuel,_hcost,s_after,s_head,s_terminal_head,s_count,s_cached,sourcesReady,s_restored,s_next,hfuel,hwidth⟩

noncomputable def cachedBuildPhase (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws) (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
   Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (hin : Fin (SelectedBranchPhases.tapes sources p k r scratch) → Nat)
 (tin : Fin (SelectedBranchPhases.tapes sources p k r scratch) → List Bool)
 (fuel width : Nat) (supplied : CachedPhase selector compiler sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width) :
 OrderedCallPhases.PhaseConstruction.Input sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width :=
 FixedLivePackets.preparedBuildPhase selector compiler tables semantics buildSource sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width
   (phaseProjection selector compiler sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width supplied)

end PhysicalFamilyLoader

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open NativeRecipes

open FixedLivePackets
namespace PhysicalFamilyLoader

noncomputable abbrev CachedSelected (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws) (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (den : Nat) (hden : 0<den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
 (hp : P1Independent.CappedLegalAdmission.passed sources p
  (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
  (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
 (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (remainingFuel : Nat) (width : Phase → Nat) : Prop :=
∃ (cost : Phase → Nat),
∃ (penaltySpec : CachedPhase selector compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .penalty (SelectedPhaseLayout.S.heads sources p k r scratch) (SelectedPhaseLayout.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty)),
let penalty := (cachedBuildPhase selector compiler tables semantics buildSource) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .penalty (SelectedPhaseLayout.S.heads sources p k r scratch) (SelectedPhaseLayout.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) penaltySpec
∃ (momentSpec : CachedPhase selector compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .moment penalty.realize.heads penalty.realize.exit (cost .moment) (width .moment)),
let moment := (cachedBuildPhase selector compiler tables semantics buildSource) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .moment penalty.realize.heads penalty.realize.exit (cost .moment) (width .moment) momentSpec
∃ (clauseSpec : CachedPhase selector compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .clause moment.realize.heads moment.realize.exit (cost .clause) (width .clause)),
let clause := (cachedBuildPhase selector compiler tables semantics buildSource) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .clause moment.realize.heads moment.realize.exit (cost .clause) (width .clause) clauseSpec
∃ (_penalty_kept : clause.realize.exit (SelectedPhaseLayout.S.ports sources p k r scratch .penalty)=
   CloseoutRowsEstimatorCoefficients.Stream.recordWord (width .penalty) penalty.realize.result 1 1),
∃ (_moment_kept : clause.realize.exit (SelectedPhaseLayout.S.ports sources p k r scratch .moment)=
   CloseoutRowsEstimatorCoefficients.Stream.recordWord (width .moment) moment.realize.result 1 1),
∃ (_threshold : ∀ ph,C10ThresholdWidths.thresholdWidth (constantsOf sources)≤width ph),
∃ (_head : ∀ i,clause.realize.heads (SelectedBranchPhases.body sources p k r scratch
   (CloseoutFinalC10RetainedPhaseFold.tailSlots (SelectedBranchPhases.offset sources p k r)
    (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (SelectedBranchPhases.offset_ge sources p k r) (SelectedBranchPhases.fresh_lt sources p k r scratch) i))=0),
∃ (_words : ∀ ph j,clause.realize.exit (SelectedBranchPhases.body sources p k r scratch
   (CloseoutFinalC10RetainedPhaseFold.tailSlots (SelectedBranchPhases.offset sources p k r)
    (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (SelectedBranchPhases.offset_ge sources p k r) (SelectedBranchPhases.fresh_lt sources p k r scratch)
    (C10TailSlotsUniform.widthSlotT ph j)))=C10BodyWidths.widthWord (width ph) j),
∃ (_blank : ∀ i : Fin 475, (15 ≤ i.val ∧ i.val < 102) ∨ 221 ≤ i.val →
   clause.realize.exit (SelectedBranchPhases.body sources p k r scratch
    (CloseoutFinalC10RetainedPhaseFold.tailSlots (SelectedBranchPhases.offset sources p k r)
     (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (SelectedBranchPhases.offset_ge sources p k r) (SelectedBranchPhases.fresh_lt sources p k r scratch) i))=[]),
SelectedPhaseLayout.branchFuel cost width+2≤remainingFuel

noncomputable def selectedProjection (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws) (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (den : Nat) (hden : 0<den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
 (hp : P1Independent.CappedLegalAdmission.passed sources p
  (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
  (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
 (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (remainingFuel : Nat) (width : Phase → Nat) (supplied : (CachedSelected selector compiler tables semantics buildSource) sources p den hden k r scratch n x bits hp site remainingFuel width) : (FixedLivePackets.PreparedSelected selector compiler tables semantics buildSource) sources p den hden k r scratch n x bits hp site remainingFuel width := by
 rcases supplied with ⟨cost,penaltySpec,momentSpec,clauseSpec,penalty_kept,moment_kept,threshold,head,words,blank,fits⟩
 let penalty := (cachedBuildPhase selector compiler tables semantics buildSource) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .penalty (SelectedPhaseLayout.S.heads sources p k r scratch) (SelectedPhaseLayout.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) penaltySpec
 let moment := (cachedBuildPhase selector compiler tables semantics buildSource) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .moment penalty.realize.heads penalty.realize.exit (cost .moment) (width .moment) momentSpec
 let clause := (cachedBuildPhase selector compiler tables semantics buildSource) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .clause moment.realize.heads moment.realize.exit (cost .clause) (width .clause) clauseSpec
 exact ⟨cost,((phaseProjection selector compiler) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .penalty (SelectedPhaseLayout.S.heads sources p k r scratch) (SelectedPhaseLayout.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) penaltySpec),((phaseProjection selector compiler) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .moment penalty.realize.heads penalty.realize.exit (cost .moment) (width .moment) momentSpec),((phaseProjection selector compiler) sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (SelectedPhaseLayout.S.mode sources p den hden k r scratch n x bits hp) .clause moment.realize.heads moment.realize.exit (cost .clause) (width .clause) clauseSpec),penalty_kept,moment_kept,threshold,head,words,blank,fits⟩

noncomputable abbrev CachedRecipe (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws) (tables : TableCertificate) (semantics : Certificate) : Prop :=
∀ (buildSource : SourceBuilder),
∃ (capIndex : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
∃ (remainingDegree : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
∃ (r : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
∃ (base : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
∃ (scratch : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
∃ (site : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Bool → NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule.Phase → Σ states,
 NearCubicWires.LocalBitMultitape.Machine
 (NearCubicWires.P1TopDown.ControllerSelectedContinuation.bodyTapes sources p
  (NearCubicWires.P1TopDown.ControllerCappedRuntime.hierarchyIndex sources p
   (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p))
  (r sources gamma hg hh p) (scratch sources gamma hg hh p)) states)),
∃ (remainingFuel : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat → Nat)),
∃ (widths : (open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.RepairSource.CloseoutFinal.C10GuardedMachineConsumer NearCubicWires.RepairSource.CloseoutFinal.C10GuardedStageConsumer NearCubicWires.RepairSource.CloseoutFinal.C10Fusion NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode NearCubicWires.P1TopDown in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) → Phase → Nat)),
∃ (phaseConstruction : (open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.RepairSource.CloseoutFinal.C10GuardedMachineConsumer NearCubicWires.RepairSource.CloseoutFinal.C10GuardedStageConsumer NearCubicWires.RepairSource.CloseoutFinal.C10Fusion NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode NearCubicWires.P1TopDown in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) → let C := NearCubicWires.P1TopDown.ControllerCappedRuntime.continuation sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p); (hn : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).onset ≤ n) → (hp : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).passed n x bits = true) → (CachedSelected selector compiler tables semantics buildSource) sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) C.k (r sources gamma hg hh p) (scratch sources gamma hg hh p) n x bits hp (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p n) (widths sources gamma hg hh p n x bits))),
∃ (remainingCoefficient : ((sources : NearCubicWires.RepairSource.EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : NearCubicWires.RepairSource.CloseoutFinal.Parameters sources gamma) → Nat)),
∃ (remainingOnset : ((sources : NearCubicWires.RepairSource.EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : NearCubicWires.RepairSource.CloseoutFinal.Parameters sources gamma) → Nat)),
∃ (tableCoefficient : ((sources : NearCubicWires.RepairSource.EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : NearCubicWires.RepairSource.CloseoutFinal.Parameters sources gamma) → Nat)),
∃ (tableDegree : ((sources : NearCubicWires.RepairSource.EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : NearCubicWires.RepairSource.CloseoutFinal.Parameters sources gamma) → Nat)),
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.P1TopDown in
∀ (sources : EightSources) (gamma : Real) (hg : 0<gamma) (hh : gamma<1/2) (p : Parameters sources gamma),
 let C := ControllerCappedRuntime.continuation sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p);
 ∀ n, remainingOnset sources gamma hg hh p≤n → remainingFuel sources gamma hg hh p n+3≤
 remainingCoefficient sources gamma hg hh p*(n+1)^(remainingDegree sources gamma hg hh p)+
 tableCoefficient sources gamma hg hh p*(2^(SelectedRuntime.width C n-(SelectedRuntime.sigma sources+tableDegree sources gamma hg hh p+2)*
 SelectedRuntime.logarithm C n)*(SelectedRuntime.width C n+1)^(tableDegree sources gamma hg hh p))

end PhysicalFamilyLoader

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open NativeRecipes

open FixedLivePackets
namespace PhysicalFamilyLoader

theorem parent (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws) (tables : TableCertificate) (semantics : Certificate) (physical : CachedRecipe selector compiler tables semantics) : FixedLivePackets.PreparedRecipe selector compiler tables semantics := by
 classical
 intro buildSource
 have chosen := physical buildSource
 rcases chosen with ⟨capIndex,remainingDegree,r,base,scratch,site,remainingFuel,widths,phaseConstruction,remainingCoefficient,remainingOnset,tableCoefficient,tableDegree,runtimeBound⟩
 refine ⟨capIndex,remainingDegree,r,base,scratch,site,remainingFuel,widths,?_,remainingCoefficient,remainingOnset,tableCoefficient,tableDegree,runtimeBound⟩
 intro sources gamma hg hh p n x bits C hn hp
 exact selectedProjection selector compiler tables semantics buildSource sources p
  (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p))
  C.k (r sources gamma hg hh p) (scratch sources gamma hg hh p) n x bits hp
  (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p n)
  (widths sources gamma hg hh p n x bits) (phaseConstruction sources gamma hg hh p n x bits hn hp)

end PhysicalFamilyLoader

end
