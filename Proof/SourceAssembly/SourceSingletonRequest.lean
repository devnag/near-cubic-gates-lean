import Proof.SourceAssembly.SourceSingletonNative

/- First actual complete Request native/support family: the carried systematic
singleton. Fixed L/target are paid finite-code words, q/circuit read from cache. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblySingletonRequest
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity SupplierPipeline SupplierEstimator
open CloseoutRowsOriginalClause (index negative)
open PacketProduction
noncomputable section

def request {q : Nat} (S : Finset (Fin q)) (L target : Nat) : Request:=
  .thr ⟨q,[normalizedThresholdParityCircuit S]⟩ (by simp) L target

theorem native_eq {q : Nat} (S : Finset (Fin q)) (L target : Nat) :
    SourceAssemblySingletonNative.native q L target
      (thrWord (normalizedThresholdParityCircuit S))=(request S L target).nativeWord := by
  simp only [SourceAssemblySingletonNative.native,
    SourceAssemblySingletonNative.prefixWord,SourceAssemblySingletonNative.tail,
    request,Request.nativeWord,List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

theorem support_eq {q : Nat} (S : Finset (Fin q)) (L target : Nat) (a : DecompositionAlgorithm) :
    CloseoutRowsTupleSeek.supportWord (SourceAssemblyThresholdPhysical.gates q S.card
      (SourceAssemblySymmetricMeaning.bitmap S))=(request S L target).supportWord a := by
  unfold Request.supportWord request Request.family FixedLivePackets.Packets.thrFamily
  simp only [thresholdFourfoldOccurrences,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change _=(List.ofFn (fun i : Fin (normalizedThresholdParityCircuit S).top.support.card=>
    (normalizedThresholdParityCircuit S).bottom (retainedTopIndex (normalizedThresholdParityCircuit S) i))).flatMap
      (fun g=>frame (SourceAssemblySymmetricMeaning.bitmap g.support))
  rw [show (List.ofFn (fun i : Fin (normalizedThresholdParityCircuit S).top.support.card=>
      (normalizedThresholdParityCircuit S).bottom (retainedTopIndex (normalizedThresholdParityCircuit S) i))).flatMap
        (fun g=>frame (SourceAssemblySymmetricMeaning.bitmap g.support))=
      (List.ofFn (fun _ : Fin (normalizedThresholdParityCircuit S).top.support.card=>
        frame (SourceAssemblySymmetricMeaning.bitmap S))).flatten by
    simp only [List.ofFn_eq_map,List.flatMap_map];rfl]
  rw [SourceAssemblyThresholdCanonical.ofFn_range _ (fun _=>frame (SourceAssemblySymmetricMeaning.bitmap S)),
    SourceAssemblyThresholdCanonical.card_eq]
  simp only [CloseoutRowsTupleSeek.supportWord,SourceAssemblyThresholdPhysical.gates,List.flatMap_map]
  rfl

def circuit (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits):=
  normalizedThresholdParityCircuit ((a.output r).systematicSupport ⟨index ((a.output r).clauses ci).left,hk⟩)
def slots : Fin 4→Fin 216:=![131,212,214,215]
def first:=TapeEmbedding.machine 2 SourceAssemblyCircuitFrame.machine
def last (L target : Nat):=RecoveryFocus.machine slots (SourceAssemblySingletonNative.machine L target)
def machine (L target : Nat):=Composition.machine first (last L target)
def input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat) : Fin 216→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (AppendOutputFrame.input (SourceAssemblyThresholdReady.input a r ci C)) (fun _ : Fin 2=>[])
def finalHeads (q L target : Nat) (bits : List Bool):=
  dockH slots (fun _=>0) (SourceAssemblySingletonNative.H (frame bits).length
    (SourceAssemblySingletonNative.native q L target bits))
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C L target : Nat)
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits):=
  2*SourceAssemblyThresholdPhysical.budget a r ci C hk+4*(thrWord (circuit a r ci hk)).length+7+1+
    SourceAssemblySingletonNative.budget r.arity L target (thrWord (circuit a r ci hk))

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C L target : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C)
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits)
    (d : DecompositionAlgorithm) :
    let req:=request ((a.output r).systematicSupport ⟨index ((a.output r).clauses ci).left,hk⟩) L target
    ∃ A,Step (machine L target) (budget a r ci C L target hk) (fun _=>0) (input a r ci C)
      (finalHeads r.arity L target (thrWord (circuit a r ci hk))) A ∧
      A 214=req.nativeWord ∧A 208=req.supportWord d := by
  dsimp only
  obtain ⟨A,ha,h212,h207,h208,h131⟩:=SourceAssemblyCircuitFrame.run a r ci C hc hk
  let bank : Fin 216→List Bool:=Fin.addCases (motive:=fun _=>List Bool) A (fun _ : Fin 2=>[])
  have firstStep:Step first _ (fun _=>0) (input a r ci C) (fun _=>0) bank:=
    (ha.embed (fun _ : Fin 2=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl |>.congr
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  have selected : ∀ i,bank (slots i)=SourceAssemblySingletonNative.A r.arity (thrWord (circuit a r ci hk)) [] [] i := by
    intro i;fin_cases i
    · exact h131
    · exact h212
    · rfl
    · rfl
  have lastStep:=(SourceAssemblySingletonNative.run r.arity L target (thrWord (circuit a r ci hk))).dock slots (by decide)
    (fun _=>0) bank (fun _=>rfl) selected
  refine ⟨_,firstStep.seq lastStep,?_,?_⟩
  · exact (install_slot slots (by decide) bank _ 2).trans (native_eq _ L target)
  · rw [install_other slots bank _ 208 (by decide)]
    change A 208=_
    rw [h208]
    have hb : SourceAssemblySymmetricQuery.bitmap a r ci=
      ZeroPadding.pad (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity))
        (SourceAssemblySymmetricMeaning.bitmap
          ((a.output r).systematicSupport ⟨index ((a.output r).clauses ci).left,hk⟩)) := by
      simp only [SourceAssemblySymmetricQuery.bitmap,
        SourceAssemblyLiteralSupport.value,dif_pos hk];rfl
    unfold SourceAssemblySymmetricHeaderQuery.count
    rw [hb,SourceAssemblySymmetricMeaning.count_eq]
    exact support_eq _ L target d

theorem native_head (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (L target : Nat)
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) :
    finalHeads r.arity L target (thrWord (circuit a r ci hk)) 214=
      (request ((a.output r).systematicSupport ⟨index ((a.output r).clauses ci).left,hk⟩) L target).nativeWord.length := by
  change finalHeads r.arity L target (thrWord (circuit a r ci hk)) (slots 2)=_
  rw [finalHeads,dockH_slot _ (by decide) _ _ 2]
  change (SourceAssemblySingletonNative.native r.arity L target (thrWord (circuit a r ci hk))).length=_
  unfold circuit
  rw [native_eq]

theorem actual_template (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) :
    CloseoutRowsOriginalTask.row (.penalty 0 0)
      (CloseoutRowsOriginalSourceTask.control (a.output r).systematicBits ((a.output r).clauses ci))=
      CloseoutRowsOriginalTemplates.carried 1 0 [] := by
  simp [CloseoutRowsOriginalTask.row,CloseoutRowsOriginalSourceTask.control,
    CloseoutRowsOriginalTemplates.penaltySlot,CloseoutRowsOriginalTemplates.slot,
    CloseoutRowsOriginalTemplates.systematic,Nat.not_le.mpr hk]

end
end SourceAssemblySingletonRequest
