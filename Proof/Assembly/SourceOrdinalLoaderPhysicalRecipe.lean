import Proof.Assembly.SourceSpec
import Proof.Assembly.LoadAssembly

set_option autoImplicit false
set_option pp.maxSteps 2000
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open NativeRecipes
open SemanticRecipes

namespace FetchRecipes
noncomputable def toLoaderSource (fetchCorrect : IndexFetchProgram.Correct) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
 (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (ci : Fin (2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits))
 (globalH globalHnext : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→Nat)
 (globalA globalAfter : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→List Bool)
 (b siteFuel : Nat)
 (supplied : FetchSourceSpec sources p k den r scratch clock n x oracle bits site mode ph ci globalH globalHnext globalA globalAfter b siteFuel) : LoaderRecipes.LoaderSourceSpec sources p k den r scratch clock n x oracle bits site mode ph ci globalH globalHnext globalA globalAfter b siteFuel := by
 refine supplied.elim (fun order remainder1 =>
  remainder1.elim (fun _horder remainder2 =>
  remainder2.elim (fun L remainder3 =>
  remainder3.elim (fun target remainder4 =>
  remainder4.elim (fun a remainder5 =>
  remainder5.elim (fun prepT remainder6 =>
  remainder6.elim (fun _hsize remainder7 =>
  remainder7.elim (fun dflt remainder8 =>
  remainder8.elim (fun ds remainder9 =>
  remainder9.elim (fun xs remainder10 =>
  remainder10.elim (fun S remainder11 =>
  remainder11.elim (fun R remainder12 =>
  remainder12.elim (fun B remainder13 =>
  remainder13.elim (fun rowWidth remainder14 =>
  remainder14.elim (fun total remainder15 =>
  remainder15.elim (fun denominator remainder16 =>
  remainder16.elim (fun D remainder17 =>
  remainder17.elim (fun cap remainder18 =>
  remainder18.elim (fun logSize remainder19 =>
  remainder19.elim (fun resetSize remainder20 =>
  remainder20.elim (fun coefficient remainder21 =>
  remainder21.elim (fun old remainder22 =>
  remainder22.elim (fun phasePrefix remainder23 =>
  remainder23.elim (fun entries remainder24 =>
  remainder24.elim (fun _hlen remainder25 =>
  remainder25.elim (fun _hxs remainder26 =>
  remainder26.elim (fun _hcoeff remainder27 =>
  remainder27.elim (fun _hnative remainder28 =>
  remainder28.elim (fun U remainder29 =>
  remainder29.elim (fun slots remainder30 =>
  remainder30.elim (fun _hs remainder31 =>
  remainder31.elim (fun enc remainder32 =>
  remainder32.elim (fun _he remainder33 =>
  remainder33.elim (fun app remainder34 =>
  remainder34.elim (fun _ha remainder35 =>
  remainder35.elim (fun H remainder36 =>
  remainder36.elim (fun A remainder37 =>
  remainder37.elim (fun reserveSize remainder38 =>
  remainder38.elim (fun _hw remainder39 =>
  remainder39.elim (fun _hfit remainder40 =>
  remainder40.elim (fun _hH remainder41 =>
  remainder41.elim (fun _hA remainder42 =>
  remainder42.elim (fun _hc remainder43 =>
  remainder43.elim (fun _hold remainder44 =>
  remainder44.elim (fun _hl remainder45 =>
  remainder45.elim (fun _hr remainder46 =>
  remainder46.elim (fun _heH remainder47 =>
  remainder47.elim (fun _haH remainder48 =>
  remainder48.elim (fun _hfields remainder49 =>
  remainder49.elim (fun familyCost remainder50 =>
  remainder50.elim (fun initializeStates remainder51 =>
  remainder51.elim (fun prepareStates remainder52 =>
  remainder52.elim (fun prefixStates remainder53 =>
  remainder53.elim (fun tailStates remainder54 =>
  remainder54.elim (fun initialMachine remainder55 =>
  remainder55.elim (fun prepareNext remainder56 =>
  remainder56.elim (fun prefixMachine remainder57 =>
  remainder57.elim (fun tailMachine remainder58 =>
  remainder58.elim (fun fetchSlots remainder59 =>
  remainder59.elim (fun _hfetchSlots remainder60 =>
  remainder60.elim (fun _hfetchInjective remainder61 =>
  remainder61.elim (fun initializeCost remainder62 =>
  remainder62.elim (fun prepareCost remainder63 =>
  remainder63.elim (fun loadCost remainder64 =>
  remainder64.elim (fun cursorH remainder65 =>
  remainder65.elim (fun cursorA remainder66 =>
  remainder66.elim (fun whole remainder67 =>
  remainder67.elim (fun _hwhole remainder68 =>
  remainder68.elim (fun counterReserve remainder69 =>
  remainder69.elim (fun _hcost remainder70 =>
  remainder70.elim (fun _hprepare remainder71 =>
  remainder71.elim (fun ts remainder72 =>
  remainder72.elim (fun indices remainder73 =>
  remainder73.elim (fun fetchC remainder74 =>
  remainder74.elim (fun fetchD remainder75 =>
  remainder75.elim (fun prefixCost remainder76 =>
  remainder76.elim (fun tailCost remainder77 =>
  remainder77.elim (fun fetchPos remainder78 =>
  remainder78.elim (fun fetchCaps remainder79 =>
  remainder79.elim (fun fetchH remainder80 =>
  remainder80.elim (fun fetchA remainder81 =>
  remainder81.elim (fun _hfC remainder82 =>
  remainder82.elim (fun _hfD remainder83 =>
  remainder83.elim (fun _hfour remainder84 =>
  remainder84.elim (fun _hindex remainder85 =>
  remainder85.elim (fun _hfPos remainder86 =>
  remainder86.elim (fun _hterminalIndices remainder87 =>
  remainder87.elim (fun _hselected remainder88 =>
  remainder88.elim (fun _hprefix remainder89 =>
  remainder89.elim (fun _htail remainder90 =>
  remainder90.elim (fun _hloadBound remainder91 =>
  remainder91.elim (fun _hinitialize remainder92 =>
  remainder92.elim (fun _hfirstHeads remainder93 =>
  remainder93.elim (fun _hfirstTapes remainder94 =>
  remainder94.elim (fun _hfinalH remainder95 =>
  remainder95.elim (fun _hfinalA remainder96 =>
  remainder96.elim (fun _hcode fits =>
  ?_)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 have loaded (j : Nat) (hj : j≤entries.length) :
   Step (Composition.machine prefixMachine
     (Composition.machine (RecoveryFocus.machine fetchSlots IndexFetchProgram.machine) tailMachine))
    loadCost (cursorH j) (cursorA j) (H j)
    (fun (i : Fin U) => ZeroPadding.pad
      (if (SelectedBranchPhases.offset sources p k r + 1155) ≤ i.val then reserveSize else 0)
      (A j i)) :=
  assembleLoad fetchCorrect prefixMachine tailMachine fetchSlots _hfetchInjective
   (ts j) (indices j) (fetchC j) (fetchD j) (_hfC j hj) (_hfD j hj)
   (_hfour j hj) (_hindex j hj) (fetchPos j) (_hfPos j hj) (fetchCaps j)
   (fetchH j) (fetchA j) (cursorH j) (H j) (cursorA j) _
   (prefixCost j) (tailCost j) loadCost (_hprefix j hj) (_htail j hj) (_hloadBound j hj)
 refine ⟨order,_horder,L,target,a,prepT,_hsize,dflt,ds,xs,S,R,B,rowWidth,total,denominator,D,cap,logSize,resetSize,coefficient,old,phasePrefix,entries,_hlen,_hxs,_hcoeff,_hnative,U,slots,_hs,enc,_he,app,_ha,H,A,reserveSize,_hw,_hfit,_hH,_hA,_hc,_hold,_hl,_hr,_heH,_haH,_hfields,familyCost,initializeStates,prepareStates,_,initialMachine,prepareNext,(Composition.machine prefixMachine (Composition.machine (RecoveryFocus.machine fetchSlots IndexFetchProgram.machine) tailMachine)),initializeCost,prepareCost,loadCost,cursorH,cursorA,whole,_hwhole,counterReserve,_hcost,_hprepare,loaded,_hinitialize,?_,_hfinalH,_hfinalA,_hcode,fits⟩

 exact ((loaded 0 (Nat.zero_le _)).embed
  (fun _ : Fin 1=>1) (fun _ : Fin 1=>ZeroPadding.pad counterReserve (CompareMachine.word entries.length))).congr
   _hfirstHeads _hfirstTapes

end FetchRecipes
