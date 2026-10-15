import Proof.MachineModel.ClosureBinaryPool

/-! Exact bytes for the nested physical hardwiring loops in A.12. The cache
includes its length prefix and false sentinel, then every original child
occurrence for each binary-order assignment. No permutation is performed.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinarySerialization
open RepairRepresentation RepairOrdinary SupplierPipeline SupplierEstimator
open RepairSource CloseoutFinal C10SupplierRowInput

theorem castGate_word {m n : Nat} (h : m=n) (g : ExactThresholdGate n) :
    exactWord (castGate h g)=exactWord g := by
  subst n
  rfl

variable {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : Nat)
  (harity : (s+1)/2+s/2 = liveᶜ.card)

theorem poolFn_block (yi : Fin (LiveEnumeration.binary live.card).length)
    (ci : Fin (childList a live occ).length) :
    BinaryPool.poolFn a live occ s harity (yi.val*(childList a live occ).length+ci.val) =
      castGate harity (hardwire live (childList a live occ)[ci.val]
        (LiveEnumeration.binary live.card)[yi.val]) := by
  have hpos : 0 < (childList a live occ).length := Nat.lt_of_le_of_lt (Nat.zero_le ci.val) ci.isLt
  unfold BinaryPool.poolFn BinaryPool.assignmentAt
  rw [Nat.mul_comm yi.val (childList a live occ).length,
    Nat.mul_add_mod,Nat.mod_eq_of_lt ci.isLt,Nat.mul_add_div hpos,Nat.div_eq_of_lt ci.isLt]
  simp only [Nat.add_zero,List.getD_eq_getElem _ _ ci.isLt,List.getD_eq_getElem _ _ yi.isLt]

theorem pool_eq : BinaryPool.pool a live occ s harity =
    falseGate ((s+1)/2+s/2) ::
      (LiveEnumeration.binary live.card).flatMap (fun y =>
        (childList a live occ).map (fun g => castGate harity (hardwire live g y))) := by
  have hlen := (LiveEnumeration.binary_perm live).length_eq
  rw [BinaryPool.pool,←hlen,List.ofFn_mul]
  simp_rw [poolFn_block]
  have inner (y : BitInput live.card) :
      List.ofFn (fun ci : Fin (childList a live occ).length =>
        castGate harity (hardwire live (childList a live occ)[ci.val] y)) =
      (childList a live occ).map (fun g => castGate harity (hardwire live g y)) :=
    List.ofFn_getElem_eq_map (childList a live occ) (fun g => castGate harity (hardwire live g y))
  simp_rw [inner]
  rw [List.ofFn_getElem_eq_map (LiveEnumeration.binary live.card)
    (fun y => (childList a live occ).map (fun g => castGate harity (hardwire live g y)))]
  rfl

theorem exactListWord_eq : exactListWord (BinaryPool.pool a live occ s harity) =
    natWord (2^live.card*(childList a live occ).length+1) ++
      exactWord (falseGate ((s+1)/2+s/2)) ++
      (LiveEnumeration.binary live.card).flatMap (fun y =>
        (childList a live occ).flatMap (fun g => exactWord (castGate harity (hardwire live g y)))) := by
  rw [exactListWord,BinaryPool.pool_length,C10SupplierRowInput.pool_length,liveList_length,pool_eq]
  simp only [List.flatMap_cons,List.flatMap_assoc,List.flatMap_map,List.append_assoc]

theorem exactListWord_eq_native : exactListWord (BinaryPool.pool a live occ s harity) =
    natWord (2^live.card*(childList a live occ).length+1) ++
      exactWord (falseGate ((s+1)/2+s/2)) ++
      (LiveEnumeration.binary live.card).flatMap (fun y =>
        (childList a live occ).flatMap (fun g => exactWord (hardwire live g y))) := by
  rw [exactListWord_eq]
  simp only [castGate_word]

end NearCubicWires.P1Closure.BinarySerialization
