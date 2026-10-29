import Proof.Assembly.NativeBase

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

namespace NativeRecipes

noncomputable abbrev SourceSpec (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k r scratch : Nat)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (pcpp_a : PointwisePCPPAlgorithm) (rq : PCPPRequest pcpp_a.minimumArity)
 (ci : Fin (2^(pcpp_a.output rq).clauseBits))
 (globalH globalHnext : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
 (globalA globalAfter : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (b siteFuel : Nat) : Prop :=
∃ (a : WilliamsAlgorithm),
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
∃ (_hv : ∀ j<entries.length,∀ k (hk : k<(ds j).length),
   P1TopDownPaidReusable.Valid a (B j) (R j) (S j) (ds j)[k]),
∃ (_hwords : ∀ j<entries.length,(ds j).map P1TopDownPaidReusable.Datum.emit=
   (xs j).map (SignedSortKey.binary (rowWidth j))),
∃ (_hw : ∀ j<entries.length,rowWidth j≤b),
∃ (_hx : ∀ j<entries.length,∀ x∈xs j,x<2^(rowWidth j)),
∃ (_hsum : ∀ j<entries.length,(xs j).sum=total j),
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
∃ (refillStates : Nat),
∃ (firstStates : Nat),
∃ (refill : Machine U refillStates),
∃ (first : Machine (U+1) firstStates),
∃ (whole : Fin (U+1) → Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)),
∃ (_hwhole : ∀ i,(whole i).val=i.val),
∃ (counterReserve : Nat),
let reserve := fun (i : Fin U) => if (SelectedBranchPhases.offset sources p k r + 1155) ≤ i.val then reserveSize else 0
 let queried := install (SelectedBranchPhases.cache sources p k r scratch mode) globalA
   (PCPPQueryIndexPadding.clauseData (pcppOutput rq (pcpp_a.output rq)) rq.arity ci.val
     (PCPPQueryCachedBounds.capacity pcpp_a (rq.circuit.size+rq.arity))
     (natListWord [literalIndex ((pcpp_a.output rq).clauses ci).left,
       literalIndex ((pcpp_a.output rq).clauses ci).right]))
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
   Step refill refillCost (outH j) (fun i=>ZeroPadding.pad (reserve i) (outA j Z i))
    (H (j+1)) (padded (j+1)))),
∃ (_hfirst : Step first firstCost originalH originalA
   (RepeatMachine.cfg 0 (state 0 []) entries.length 1).heads
   (fun i=>ZeroPadding.pad (counterCaps i) ((RepeatMachine.cfg 0 (state 0 []) entries.length 1).tapes i))),
∃ (_hfinalH : (dockH whole globalH (RepeatMachine.cfg 3 (state entries.length []) entries.length 1).heads=globalHnext)),
∃ (_hfinalA : (install whole queried (fun i=>ZeroPadding.pad (counterCaps i)
    ((RepeatMachine.cfg 3 (state entries.length []) entries.length 1).tapes i))=globalAfter)),
∃ (_hcode : (⟨_,RecoveryFocus.machine whole (Composition.machine first (CloseoutRowsDegreeLoop.machine body))⟩ : Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)=site mode ph),
firstCost+1+(entries.length*(familyCost+1+refillCost+3)+3) ≤ siteFuel

noncomputable abbrev SourceBuilder : Prop :=
∀ (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k r scratch : Nat)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (pcpp_a : PointwisePCPPAlgorithm) (rq : PCPPRequest pcpp_a.minimumArity)
 (ci : Fin (2^(pcpp_a.output rq).clauseBits))
 (globalH globalHnext : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
 (globalA globalAfter : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (b siteFuel : Nat) (supplied : SourceSpec sources p k r scratch site mode ph pcpp_a rq ci globalH globalHnext globalA globalAfter b siteFuel),
 Step (site mode ph).2 siteFuel globalH (install (SelectedBranchPhases.cache sources p k r scratch mode) globalA
   (PCPPQueryIndexPadding.clauseData (pcppOutput rq (pcpp_a.output rq)) rq.arity ci.val
     (PCPPQueryCachedBounds.capacity pcpp_a (rq.circuit.size+rq.arity))
     (natListWord [literalIndex ((pcpp_a.output rq).clauses ci).left,
       literalIndex ((pcpp_a.output rq).clauses ci).right]))) globalHnext globalAfter

end NativeRecipes
