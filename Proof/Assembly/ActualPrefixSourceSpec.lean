import Proof.Assembly.Generator
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open NativeRecipes
open SemanticRecipes

namespace ActualPrefixRecipes
open NativeFamilyGenerator
noncomputable abbrev GeneratedSourceSpec (g : Data) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
 (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (ci : Fin (2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits))
 (globalH globalHnext : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→Nat)
 (globalA globalAfter : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→List Bool)
 (L target b siteFuel : Nat) : Prop :=
 let pcpp := pcppAt sources k clock x oracle
 let coordinate := CappedCoordinates.coordinate sources k clock p den x oracle bits
 ∃ (order : List (CircuitMonomial (C10TotalDecode.Atom pcpp) 4)),
 ∃ (_horder : order.Perm (CloseoutFinalC10SupplierCalls.siteCalls ph pcpp coordinate C10TotalDecode.Atom.systematic ci).monomials),
let a := g.printer
∃ (prepT : Nat),
∃ (_hsize : scratch = r_tapes a+14+prepT),
∃ (dflt : P1TopDownPaidReusable.Datum),
let genInput := fun j=>if j<order.length then
 inputOf ((order.map (fun m=>m.factors)).getD j []) L target b mode true
 else inputOf ([] : List (C10TotalDecode.Atom pcpp)) L target b mode false
let produced := fun j=>g.result (genInput j)
let ds := fun j=>(produced j).ds
∃ (xs : Nat → List Nat),
let S := fun j=>(produced j).S
let R := fun j=>(produced j).R
let B := fun j=>(produced j).B
let rowWidth := fun j=>(produced j).rowWidth
let total := fun j=>(produced j).total
let denominator := fun j=>(produced j).denominator
∃ (D : Nat → Nat),
∃ (cap : Nat → Nat),
∃ (logSize : Nat → Nat),
∃ (resetSize : Nat → Nat),
∃ (coefficient : Nat → CompetitorValidity.Estimate),
∃ (old : Nat → List Bool),
∃ (phasePrefix : List Stream.Entry),
∃ (entries : List Stream.Entry),
∃ (_hlen : entries.length=order.length),
∃ (_hxs : xs=fun j=>(ds j).map datumValue),
∃ (_hcoeff : ∀ j<entries.length,coefficient j=CloseoutFinalC10SupplierCalls.coefficientEstimate
  ((order.map (fun m=>m.coefficient)).getD j 0)),
/- Exact executions at every real call, including terminal preparation. -/
∃ (_hproduced : ∀ j≤entries.length,Produced g (genInput j)),
/- Exact prescribed rows at active calls; multiplicity is retained. -/
∃ (_hnative : ∀ j<entries.length,NativeRows sources L target mode
  ((order.map (fun m=>m.factors)).getD j []) a (S j) (R j) (B j)
  (rowWidth j) (ds j) (total j) (denominator j)),
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
∃ (initializeStates prepareStates prefixStates enterStates exitStates : Nat),
∃ (initialMachine : Machine (U+1) initializeStates),
∃ (prepareNext : Machine U prepareStates),
∃ (prefixMachine : Machine U prefixStates),
∃ (enterMachine : Machine U enterStates),
∃ (exitMachine : Machine U exitStates),
∃ (generatorSlots : Fin (tapes g.printer g.scratch) → Fin U),
∃ (_hgeneratorInjective : Function.Injective generatorSlots),
∃ (enterCost exitCost : Nat → Nat),
∃ (genH : Nat → Fin U → Nat),
∃ (genA : Nat → Fin U → List Bool),
∃ (genCaps : Nat → Fin (tapes g.printer g.scratch) → Nat),
let tailMachine := Composition.machine enterMachine
 (Composition.machine (RecoveryFocus.machine generatorSlots g.machine) exitMachine)
∃ (fetchSlots : Fin 31 → Fin U),
∃ (_hfetchSlots : ∀ i,(fetchSlots i).val=
  SelectedBranchPhases.offset sources p k r+1155+r_tapes a+13+i.val),
∃ (_hfetchInjective : Function.Injective fetchSlots),
let loadCurrent := Composition.machine prefixMachine
 (Composition.machine (RecoveryFocus.machine fetchSlots IndexFetchProgram.machine) tailMachine)
∃ (initializeCost prepareCost loadCost : Nat),
∃ (cursorH : Nat → Fin U → Nat),
∃ (cursorA : Nat → Fin U → List Bool),
let refill := Composition.machine prepareNext loadCurrent
let first := Composition.machine initialMachine (TapeEmbedding.machine 1 loadCurrent)
let refillCost := prepareCost+1+loadCost
let firstCost := initializeCost+1+loadCost
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

∃ (_hfamilyBound : ∀ j<entries.length,
 f_budget a (S j) (rowWidth j) b (xs j).length+1+
 (2*D j+4+1+(2*e_emitCost b+2)+1+
  CloseoutFinalC10AppendPositioning.budget b (phasePrefix++entries.take j).length)≤familyCost),
∃ (_hprepare : ∀ j<entries.length,∀ Z,
   Step family (fuel j) (H j) (A j) (outH j) (outA j Z) →
   Step prepareNext prepareCost (outH j)
     (fun i=>ZeroPadding.pad (reserve i) (outA j Z i))
     (cursorH (j+1)) (cursorA (j+1))),
∃ (ts : Nat → List CloseoutRowsTupleSeek.TermSlices),
∃ (indices : (j : Nat) → List (Fin (ts j).length)),
∃ (fetchC fetchD prefixCost tailCost : Nat → Nat),
∃ (fetchPos : Nat → Fin 3 → Nat),
∃ (fetchCaps : Nat → Fin 31 → Nat),
∃ (fetchH : Nat → Fin U → Nat),
∃ (fetchA : Nat → Fin U → List Bool),
∃ (_hfC : ∀ j≤entries.length,∀ t∈ts j,t.cost+1≤fetchC j),
∃ (_hfD : ∀ j≤entries.length,∀ i,(CloseoutRowsTupleSeek.familyWords (ts j) i).length≤fetchD j),
∃ (_hfour : ∀ j≤entries.length,(indices j).length≤4),
∃ (_hindex : ∀ j≤entries.length,(CloseoutRowsTupleSeek.tupleWord (indices j)).length≤fetchC j),
∃ (_hfPos : ∀ j≤entries.length,∀ i,fetchPos j i≤fetchD j),
∃ (_hterminalIndices : indices entries.length=[]),
∃ (_hselected : ∀ j<entries.length,∀ i : Fin 4,i.val≠2 →
 CloseoutRowsTupleSeek.tupleOutput (ts j) (indices j) (fun _=>[]) i =
 (((order.map (fun m=>m.factors)).getD j []).flatMap
  (fun atom=>IndexFetchProgram.atomWords mode atom i))),
∃ (_hprefix : ∀ j≤entries.length,
 Step prefixMachine (prefixCost j) (cursorH j) (cursorA j)
  (dockH fetchSlots (fetchH j) (IndexFetchProgram.entryH (fetchPos j)))
  (install fetchSlots (fetchA j) (fun i=>ZeroPadding.pad (fetchCaps j i)
   (IndexFetchProgram.entryT (ts j) (indices j) (fetchC j) (fetchD j) i)))),
∃ (_henter : ∀ j≤entries.length,
 Step enterMachine (enterCost j)
  (dockH fetchSlots (fetchH j) (IndexFetchProgram.exitH (ts j) (indices j)))
  (install fetchSlots (fetchA j) (fun i=>ZeroPadding.pad (fetchCaps j i)
   (IndexFetchProgram.exitT (ts j) (indices j) (fetchC j) (fetchD j) i)))
  (dockH generatorSlots (genH j) (fun _=>0))
  (install generatorSlots (genA j) (fun i=>ZeroPadding.pad (genCaps j i)
   (inputBank g.printer g.scratch (genInput j) i)))),
∃ (_hexit : ∀ j≤entries.length,
 Step exitMachine (exitCost j)
  (dockH generatorSlots (genH j) (produced j).H)
  (install generatorSlots (genA j) (fun i=>ZeroPadding.pad (genCaps j i) ((produced j).A i)))
  (H j) (padded j)),
∃ (_htailBound : ∀ j≤entries.length,
 enterCost j+1+((produced j).fuel+1+exitCost j)≤tailCost j),
∃ (_hloadBound : ∀ j≤entries.length,
 prefixCost j+1+(IndexFetchProgram.cost (ts j) (indices j) (fetchC j) (fetchD j)+1+tailCost j)≤loadCost),
∃ (_hinitialize : Step initialMachine initializeCost originalH originalA
   (Fin.addCases (cursorH 0) (fun _ : Fin 1=>1))
   (Fin.addCases (cursorA 0) (fun _ : Fin 1=>
     ZeroPadding.pad counterReserve (CompareMachine.word entries.length)))),
∃ (_hfirstHeads : Fin.addCases (H 0) (fun _ : Fin 1=>1)=
   (RepeatMachine.cfg 0 (state 0 []) entries.length 1).heads),
∃ (_hfirstTapes : Fin.addCases (padded 0) (fun _ : Fin 1=>
     ZeroPadding.pad counterReserve (CompareMachine.word entries.length))=
   (fun i=>ZeroPadding.pad (counterCaps i)
     ((RepeatMachine.cfg 0 (state 0 []) entries.length 1).tapes i))),
∃ (_hfinalH : (dockH whole globalH (RepeatMachine.cfg 3 (state entries.length []) entries.length 1).heads=globalHnext)),
∃ (_hfinalA : (install whole queried (fun i=>ZeroPadding.pad (counterCaps i)
    ((RepeatMachine.cfg 3 (state entries.length []) entries.length 1).tapes i))=globalAfter)),
∃ (_hcode : (⟨_,RecoveryFocus.machine whole (Composition.machine first (CloseoutRowsDegreeLoop.machine body))⟩ : Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)=site mode ph),
firstCost+1+(entries.length*(familyCost+1+refillCost+3)+3) ≤ siteFuel

end ActualPrefixRecipes
