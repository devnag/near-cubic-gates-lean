import Proof.MachineModel.ClosureLiveEnumeration
import Proof.MachineModel.ClosureCompactSharedInput
import Proof.CaseAnalysis.FinalSupplierTable

/-! A.12 enumerates every live assignment once; its column count is independent
of that enumeration order. This pool uses the physical binary order while
keeping the existing sentinel, offsets, raw bank and pool cardinality. The
exported equality is at the count consumer, not merely a list permutation.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryPool
open RepairRepresentation RepairOrdinary SupplierPipeline SupplierEstimator SupplierPrinter
open ThresholdCompiler CanonicalFourfoldRowProgram RepairSource CloseoutFinal
open C10SupplierRowInput
open scoped BigOperators

noncomputable section
variable {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : Nat)

def assignmentAt (k : Nat) : BitInput live.card :=
  (LiveEnumeration.binary live.card).getD k (fun _ => false)

def poolFn (harity : (s+1)/2+s/2 = liveᶜ.card) (k : Nat) :
    ExactThresholdGate ((s+1)/2+s/2) :=
  castGate harity (hardwire live
    ((childList a live occ).getD (k % (childList a live occ).length) falseChild)
    (assignmentAt live (k / (childList a live occ).length)))

def pool (harity : (s+1)/2+s/2 = liveᶜ.card) : List (ExactThresholdGate ((s+1)/2+s/2)) :=
  falseGate ((s+1)/2+s/2) ::
    List.ofFn (fun k : Fin ((liveList live).length * (childList a live occ).length) =>
      poolFn a live occ s harity k.val)

theorem pool_length (harity : (s+1)/2+s/2 = liveᶜ.card) :
    (pool a live occ s harity).length = (C10SupplierRowInput.pool a live occ s harity).length := by
  simp only [pool,C10SupplierRowInput.pool,List.length_cons,List.length_ofFn]

theorem raw_polynomial_value_of_length {l r B : Nat} (gs : List (ExactThresholdGate (l+r)))
    (h : B = gs.length) {R C : Type} (holds : RowBinLift.Equation l r → R → C → Bool)
    (ms : List (List (Fin B))) (row : R) (column : C) :
    exactPolynomialValue holds (CloseoutRowsCacheInput.polynomial gs (ExtIncidence.rawRows ms)) row column =
      exactPolynomialValue (fun i => holds (CloseoutRowsCacheInput.coordinates
        (RowCachedEquation.equation (gs.get (Fin.cast h i))))) ms row column := by
  subst B
  exact ExtIncidence.raw_polynomial_value gs holds ms row column

theorem sum_assignmentAt {M : Type} [AddCommMonoid M] (f : BitInput live.card → M) :
    (∑ yi : Fin (liveList live).length, f (assignmentAt live yi.val)) =
      ∑ y : BitInput live.card, f y := by
  have hlen := (LiveEnumeration.binary_perm live).length_eq
  have he : List.ofFn (fun yi : Fin (liveList live).length => assignmentAt live yi.val) =
      LiveEnumeration.binary live.card := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using hlen.symm
    · intro i hi hj
      simp only [List.getElem_ofFn,assignmentAt,List.getD_eq_getElem _ _ hj]
  rw [← List.sum_ofFn]
  change (List.ofFn (f ∘ fun yi : Fin (liveList live).length => assignmentAt live yi.val)).sum = _
  rw [← List.map_ofFn,he,LiveEnumeration.sum_binary]
  exact Finset.sum_map_toList _ _

theorem pool_index_eval (harity : (s+1)/2+s/2 = liveᶜ.card)
    (yi : Fin (liveList live).length) (c : Nat) (x : BitInput ((s+1)/2+s/2)) :
    ((pool a live occ s harity).get
      (Fin.cast (pool_length a live occ s harity).symm (poolIndex a live occ s harity yi c))).eval x =
      CloseoutRowsUniversal.assignment a live occ
        (joinInput live (assignmentAt live yi.val) (residualPoint live s harity x)) c := by
  rw [List.get_eq_getElem]
  simp only [Fin.val_cast]
  by_cases h : c < (childList a live occ).length
  · have hpos : 0 < (childList a live occ).length := Nat.lt_of_le_of_lt (Nat.zero_le c) h
    have hval : (poolIndex a live occ s harity yi c).val =
        (childList a live occ).length * yi.val + c + 1 := by
      unfold poolIndex
      rw [dif_pos h]
    have hmod : ((childList a live occ).length * yi.val + c) %
        (childList a live occ).length = c := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h]
    have hdiv : ((childList a live occ).length * yi.val + c) /
        (childList a live occ).length = yi.val := by
      rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt h]
      omega
    have h' : c < (ExtDecompositionBatch.GS a (CloseoutRowsUniversal.pool live occ)).length := h
    simp only [pool,hval,List.getElem_cons_succ,List.getElem_ofFn,poolFn,hmod,hdiv,
      List.getD_eq_getElem (childList a live occ) falseChild h,castGate_eval,hardwire_eval]
    unfold CloseoutRowsUniversal.assignment encodedFiniteBooleanAssignment residualPoint
    rw [dif_pos h']
    simp only [List.get_eq_getElem]
    rfl
  · have hval : (poolIndex a live occ s harity yi c).val = 0 := by
      unfold poolIndex
      rw [dif_neg h]
    have h' : ¬ c < (ExtDecompositionBatch.GS a (CloseoutRowsUniversal.pool live occ)).length := h
    simp only [pool,hval,List.getElem_cons_zero,falseGate_eval]
    unfold CloseoutRowsUniversal.assignment encodedFiniteBooleanAssignment
    rw [dif_neg h']

theorem bank_eval (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial)
    (yi : Fin (liveList live).length) (rowN colN : Nat) :
    CompetitorRowCountMeaning.occurrence
        (CloseoutRowsCacheInput.polynomial (pool a live occ s harity)
          (ExtIncidence.rawRows (indexRow a live occ s harity P yi))) rowN colN % 2 =
      (exactPolynomialValue
        (fun (code : Nat) (y : BitInput live.card) (z : BitInput liveᶜ.card) =>
          encodedFiniteBooleanAssignment
            (fun i : Fin occ.length =>
              residualVariable (occ.get i).gate live (joinInput live y z)) code)
        P (assignmentAt live yi.val)
        (residualPoint live s harity (halfPoint ((s+1)/2) (s/2) rowN colN))).toNat := by
  set x : BitInput ((s+1)/2+s/2) := halfPoint ((s+1)/2) (s/2) rowN colN with hx
  set z : BitInput liveᶜ.card := residualPoint live s harity x with hz
  set y : BitInput live.card := assignmentAt live yi.val with hy
  have hstep :
      CompetitorRowCountMeaning.occurrence
          (CloseoutRowsCacheInput.polynomial (pool a live occ s harity)
            (ExtIncidence.rawRows (indexRow a live occ s harity P yi))) rowN colN % 2 =
        (exactPolynomialValue
          (fun (e : RowBinLift.Equation ((s+1)/2) (s/2)) (_ : Unit) (_ : Unit) =>
            decide (e.Holds (RowBinLift.assignment rowN colN)))
          (CloseoutRowsCacheInput.polynomial (pool a live occ s harity)
            (ExtIncidence.rawRows (indexRow a live occ s harity P yi))) () ()).toNat :=
    (exactPolynomialValue_toNat _ _ () ()).symm
  rw [hstep,raw_polynomial_value_of_length (pool a live occ s harity)
    (pool_length a live occ s harity).symm]
  congr 1
  rw [indexRow,exactPolynomialValue_map]
  have hcoord : (fun (c : Nat) =>
      (fun (i : Fin (C10SupplierRowInput.pool a live occ s harity).length) (_ : Unit) (_ : Unit) =>
        decide ((CloseoutRowsCacheInput.coordinates
          (RowCachedEquation.equation ((pool a live occ s harity).get
            (Fin.cast (pool_length a live occ s harity).symm i)))).Holds
            (RowBinLift.assignment rowN colN)))
        (poolIndex a live occ s harity yi c)) =
      (fun (c : Nat) (_ : Unit) (_ : Unit) =>
        CloseoutRowsUniversal.assignment a live occ (joinInput live y z) c) := by
    funext c _ _
    dsimp only
    rw [coordinates_holds,hy,hz,hx]
    exact pool_index_eval a live occ s harity yi c _
  rw [hcoord]
  exact CloseoutRowsUniversal.lower_value a live occ P (joinInput live y z)

theorem count_eq_exactColumnCount (harity : (s+1)/2+s/2 = liveᶜ.card)
    (P : StructuralGF2Polynomial) (rowN colN : Nat) :
    CompetitorRowCountMeaning.count
      (CloseoutRowsCacheInput.family (pool a live occ s harity) (bank a live occ s harity P))
      rowN colN = exactColumnCount
        (fun (code : Nat) (y : BitInput live.card) (z : BitInput liveᶜ.card) =>
          encodedFiniteBooleanAssignment
            (fun i : Fin occ.length => residualVariable (occ.get i).gate live (joinInput live y z)) code)
        P (residualPoint live s harity (halfPoint ((s+1)/2) (s/2) rowN colN)) := by
  simp only [CompetitorRowCountMeaning.count,CloseoutRowsCacheInput.family,
    bank,ExtIncidence.NativeRowInput.bank,ps,List.map_ofFn,Function.comp_def,List.sum_ofFn]
  simp_rw [bank_eval]
  exact sum_assignmentAt live (M:=Nat) (fun y => (exactPolynomialValue
    (fun (code : Nat) (y' : BitInput live.card) (z : BitInput liveᶜ.card) =>
      encodedFiniteBooleanAssignment
        (fun i : Fin occ.length => residualVariable (occ.get i).gate live (joinInput live y' z)) code)
    P y (residualPoint live s harity (halfPoint ((s+1)/2) (s/2) rowN colN))).toNat)

theorem count_eq_table (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial)
    (w : Nat) (hs : 67 ≤ s)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w)
    (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)
    (i j : Fin (2^((s+1)/2))) :
    CompetitorRowCountMeaning.count
      (CloseoutRowsCacheInput.family (pool a live occ s harity) (bank a live occ s harity P))
      i.val j.val = C10SupplierTable.table a live occ s harity P w hs hmon hpos hload i j :=
  (count_eq_exactColumnCount a live occ s harity P i.val j.val).trans
    (C10SupplierTable.table_eq_exactColumnCount a live occ s harity P w hs hmon hpos hload i j).symm

end
end NearCubicWires.P1Closure.BinaryPool
