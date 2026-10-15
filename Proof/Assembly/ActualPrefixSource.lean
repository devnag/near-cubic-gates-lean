import Proof.Assembly.ActualPrefixSourceSpec
import Proof.Assembly.SourceSpec
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

namespace ActualPrefixRecipes
open NativeFamilyGenerator
noncomputable def toFetchSource (g : Data) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
 (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (ci : Fin (2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits))
 (globalH globalHnext : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→Nat)
 (globalA globalAfter : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→List Bool)
 (L target b siteFuel : Nat)
 (supplied : GeneratedSourceSpec g sources p k den r scratch clock n x oracle bits site mode ph ci globalH globalHnext globalA globalAfter L target b siteFuel) : FetchRecipes.FetchSourceSpec sources p k den r scratch clock n x oracle bits site mode ph ci globalH globalHnext globalA globalAfter b siteFuel := by
 refine supplied.elim (fun order remainder1 =>
  remainder1.elim (fun _horder remainder2 =>
  remainder2.elim (fun prepT remainder5 =>
  remainder5.elim (fun _hsize remainder6 =>
  remainder6.elim (fun dflt remainder7 =>
  remainder7.elim (fun xs remainder8 =>
  remainder8.elim (fun D remainder9 =>
  remainder9.elim (fun cap remainder10 =>
  remainder10.elim (fun logSize remainder11 =>
  remainder11.elim (fun resetSize remainder12 =>
  remainder12.elim (fun coefficient remainder13 =>
  remainder13.elim (fun old remainder14 =>
  remainder14.elim (fun phasePrefix remainder15 =>
  remainder15.elim (fun entries remainder16 =>
  remainder16.elim (fun _hlen remainder17 =>
  remainder17.elim (fun _hxs remainder18 =>
  remainder18.elim (fun _hcoeff remainder19 =>
  remainder19.elim (fun _hproduced remainder20 =>
  remainder20.elim (fun _hnative remainder21 =>
  remainder21.elim (fun U remainder22 =>
  remainder22.elim (fun slots remainder23 =>
  remainder23.elim (fun _hs remainder24 =>
  remainder24.elim (fun enc remainder25 =>
  remainder25.elim (fun _he remainder26 =>
  remainder26.elim (fun app remainder27 =>
  remainder27.elim (fun _ha remainder28 =>
  remainder28.elim (fun H remainder29 =>
  remainder29.elim (fun A remainder30 =>
  remainder30.elim (fun reserveSize remainder31 =>
  remainder31.elim (fun _hw remainder32 =>
  remainder32.elim (fun _hfit remainder33 =>
  remainder33.elim (fun _hH remainder34 =>
  remainder34.elim (fun _hA remainder35 =>
  remainder35.elim (fun _hc remainder36 =>
  remainder36.elim (fun _hold remainder37 =>
  remainder37.elim (fun _hl remainder38 =>
  remainder38.elim (fun _hr remainder39 =>
  remainder39.elim (fun _heH remainder40 =>
  remainder40.elim (fun _haH remainder41 =>
  remainder41.elim (fun _hfields remainder42 =>
  remainder42.elim (fun familyCost remainder43 =>
  remainder43.elim (fun initializeStates remainder44 =>
  remainder44.elim (fun prepareStates remainder45 =>
  remainder45.elim (fun prefixStates remainder46 =>
  remainder46.elim (fun enterStates remainder47 =>
  remainder47.elim (fun exitStates remainder48 =>
  remainder48.elim (fun initialMachine remainder49 =>
  remainder49.elim (fun prepareNext remainder50 =>
  remainder50.elim (fun prefixMachine remainder51 =>
  remainder51.elim (fun enterMachine remainder52 =>
  remainder52.elim (fun exitMachine remainder53 =>
  remainder53.elim (fun generatorSlots remainder54 =>
  remainder54.elim (fun _hgeneratorInjective remainder55 =>
  remainder55.elim (fun enterCost remainder56 =>
  remainder56.elim (fun exitCost remainder57 =>
  remainder57.elim (fun genH remainder58 =>
  remainder58.elim (fun genA remainder59 =>
  remainder59.elim (fun genCaps remainder60 =>
  remainder60.elim (fun fetchSlots remainder61 =>
  remainder61.elim (fun _hfetchSlots remainder62 =>
  remainder62.elim (fun _hfetchInjective remainder63 =>
  remainder63.elim (fun initializeCost remainder64 =>
  remainder64.elim (fun prepareCost remainder65 =>
  remainder65.elim (fun loadCost remainder66 =>
  remainder66.elim (fun cursorH remainder67 =>
  remainder67.elim (fun cursorA remainder68 =>
  remainder68.elim (fun whole remainder69 =>
  remainder69.elim (fun _hwhole remainder70 =>
  remainder70.elim (fun counterReserve remainder71 =>
  remainder71.elim (fun _hfamilyBound remainder72 =>
  remainder72.elim (fun _hprepare remainder73 =>
  remainder73.elim (fun ts remainder74 =>
  remainder74.elim (fun indices remainder75 =>
  remainder75.elim (fun fetchC remainder76 =>
  remainder76.elim (fun fetchD remainder77 =>
  remainder77.elim (fun prefixCost remainder78 =>
  remainder78.elim (fun tailCost remainder79 =>
  remainder79.elim (fun fetchPos remainder80 =>
  remainder80.elim (fun fetchCaps remainder81 =>
  remainder81.elim (fun fetchH remainder82 =>
  remainder82.elim (fun fetchA remainder83 =>
  remainder83.elim (fun _hfC remainder84 =>
  remainder84.elim (fun _hfD remainder85 =>
  remainder85.elim (fun _hfour remainder86 =>
  remainder86.elim (fun _hindex remainder87 =>
  remainder87.elim (fun _hfPos remainder88 =>
  remainder88.elim (fun _hterminalIndices remainder89 =>
  remainder89.elim (fun _hselected remainder90 =>
  remainder90.elim (fun _hprefix remainder91 =>
  remainder91.elim (fun _henter remainder92 =>
  remainder92.elim (fun _hexit remainder93 =>
  remainder93.elim (fun _htailBound remainder94 =>
  remainder94.elim (fun _hloadBound remainder95 =>
  remainder95.elim (fun _hinitialize remainder96 =>
  remainder96.elim (fun _hfirstHeads remainder97 =>
  remainder97.elim (fun _hfirstTapes remainder98 =>
  remainder98.elim (fun _hfinalH remainder99 =>
  remainder99.elim (fun _hfinalA remainder100 =>
  remainder100.elim (fun _hcode fits =>
  ?_)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 let a := g.printer
 let pcpp := pcppAt sources k clock x oracle
 let genInput := fun j=>if j<order.length then
  inputOf ((order.map (fun m=>m.factors)).getD j []) L target b mode true
  else inputOf ([] : List (C10TotalDecode.Atom pcpp)) L target b mode false
 let produced := fun j=>g.result (genInput j)
 let ds := fun j=>(produced j).ds
 let S := fun j=>(produced j).S
 let R := fun j=>(produced j).R
 let B := fun j=>(produced j).B
 let rowWidth := fun j=>(produced j).rowWidth
 let total := fun j=>(produced j).total
 let denominator := fun j=>(produced j).denominator
 let tailMachine := Composition.machine enterMachine
  (Composition.machine (RecoveryFocus.machine generatorSlots g.machine) exitMachine)
 have _htail (j : Nat) (hj : j≤entries.length) :
   Step tailMachine (tailCost j)
    (dockH fetchSlots (fetchH j) (IndexFetchProgram.exitH (ts j) (indices j)))
    (install fetchSlots (fetchA j) (fun i=>ZeroPadding.pad (fetchCaps j i)
      (IndexFetchProgram.exitT (ts j) (indices j) (fetchC j) (fetchD j) i)))
    (H j) (fun (i : Fin U)=>ZeroPadding.pad
      (if ((SelectedBranchPhases.offset sources p k r + 1155) ≤ i.val) then reserveSize else 0)
      (A j i)) := by
  have core : Step g.machine (produced j).fuel (fun _=>0)
    (inputBank g.printer g.scratch (genInput j)) (produced j).H (produced j).A :=
   (_hproduced j hj).1
  have focused := (core.pad (genCaps j)).focus generatorSlots _hgeneratorInjective (genH j) (genA j)
  exact ((_henter j hj).seq (focused.seq (_hexit j hj))).enlarge (_htailBound j hj)
 exact ⟨order,_horder,L,target,a,prepT,_hsize,dflt,ds,xs,S,R,B,rowWidth,total,denominator,D,cap,logSize,resetSize,coefficient,old,phasePrefix,entries,_hlen,_hxs,_hcoeff,_hnative,U,slots,_hs,enc,_he,app,_ha,H,A,reserveSize,_hw,_hfit,_hH,_hA,_hc,_hold,_hl,_hr,_heH,_haH,_hfields,familyCost,initializeStates,prepareStates,prefixStates,_,initialMachine,prepareNext,prefixMachine,tailMachine,fetchSlots,_hfetchSlots,_hfetchInjective,initializeCost,prepareCost,loadCost,cursorH,cursorA,whole,_hwhole,counterReserve,_hfamilyBound,_hprepare,ts,indices,fetchC,fetchD,prefixCost,tailCost,fetchPos,fetchCaps,fetchH,fetchA,_hfC,_hfD,_hfour,_hindex,_hfPos,_hterminalIndices,_hselected,_hprefix,_htail,_hloadBound,_hinitialize,_hfirstHeads,_hfirstTapes,_hfinalH,_hfinalA,_hcode,fits⟩

end ActualPrefixRecipes
