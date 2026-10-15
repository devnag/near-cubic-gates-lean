import Proof.SourceAssembly.SourceSymmetricQuery

/- Identify the physical increasing bitmap scan with the SAME canonical parity
circuit's dependent support enumeration, including empty support. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblySymmetricMeaning
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open CloseoutRowsEstimatorParity RecoveryRootRound SupplierPipeline
open SourceAssemblySymmetricScan (outputs selected)
noncomputable section

def bitmap {q : Nat} (S : Finset (Fin q)):=List.ofFn (fun i=>decide (i∈S))

theorem read_bitmap {q : Nat} (S : Finset (Fin q)) (C j : Nat) (hj : j<q) :
    readTapeBit (ZeroPadding.pad C (bitmap S)) j=decide ((⟨j,hj⟩ : Fin q)∈S) := by
  rw [ZeroPadding.read_pad]
  change (List.ofFn (fun i : Fin q=>decide (i∈S))).getD j false=_
  rw [List.getD_eq_getElem _ _ (by simp;exact hj),List.getElem_ofFn]

theorem coordinates {q : Nat} (S : Finset (Fin q)) : List.ofFn (supportCoordinate S)=S.sort := by
  rw [List.ofFn_eq_map]
  have he : supportCoordinate S=(S.orderEmbOfFin rfl : Fin S.card→Fin q) := by
    funext i;exact S.coe_orderIsoOfFin_apply rfl i
  rw [he]
  exact S.listMap_orderEmbOfFin_finRange rfl

theorem selected_eq {q : Nat} (S : Finset (Fin q)) (C : Nat) :
    selected (ZeroPadding.pad C (bitmap S)) q=(List.ofFn (supportCoordinate S)).map Fin.val := by
  rw [coordinates]
  have left : (selected (ZeroPadding.pad C (bitmap S)) q).SortedLT :=
    ((List.sortedLT_range q).pairwise.filter _).sortedLT
  have right : (S.sort.map Fin.val).SortedLT :=
    (S.sortedLT_sort.pairwise.map Fin.val (fun _ _ h=>h)).sortedLT
  apply left.eq_of_mem_iff right
  intro j
  constructor
  · intro hj
    obtain ⟨hr,hb⟩:=List.mem_filter.mp hj
    have hlt : j<q:=List.mem_range.mp hr
    refine List.mem_map.mpr ⟨⟨j,hlt⟩,?_,rfl⟩
    simpa only [Finset.mem_sort,read_bitmap S C j hlt,decide_eq_true_eq] using hb
  · intro hj
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hj
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr i.isLt,?_⟩
    rw [read_bitmap S C i.val i.isLt]
    simpa only [decide_eq_true_eq,Finset.mem_sort] using hi

theorem count_eq {q : Nat} (S : Finset (Fin q)) (C : Nat) :
    (selected (ZeroPadding.pad C (bitmap S)) q).length=S.card := by
  rw [selected_eq,List.length_map,List.length_ofFn]

theorem native_eq {q : Nat} (S : Finset (Fin q)) (C : Nat) :
    outputs q (ZeroPadding.pad C (bitmap S)) q 0=
      (List.ofFn (normalizedParityCircuit S).bottom).flatMap (fun g=>frame (CloseoutRowsCircuitBottom.nativeWord g)) := by
  rw [outputs,selected_eq]
  simp only [List.ofFn_eq_map,List.flatMap_map,List.map_map,Function.comp_apply,normalizedParityCircuit]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i _
  rw [identity_native,Identity.identityMask_eq]
  rfl

theorem supports_eq {q : Nat} (S : Finset (Fin q)) (C : Nat) :
    outputs q (ZeroPadding.pad C (bitmap S)) q 1=
      CloseoutRowsSupportStream.supportWord (List.ofFn (normalizedParityCircuit S).bottom) := by
  rw [outputs,selected_eq]
  simp only [CloseoutRowsSupportStream.supportWord,List.ofFn_eq_map,List.flatMap_map,List.map_map,
    Function.comp_apply,normalizedParityCircuit]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i _
  rw [identity_support,Identity.identityMask_eq]
  rfl

end
end SourceAssemblySymmetricMeaning
