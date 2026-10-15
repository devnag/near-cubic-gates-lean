import Proof.CaseAnalysis.FinalSupplierRowInput
import Proof.Amplification.CanonicalRecoveryLanguage
import Proof.MachineModel.SharedNormalizedEstimatorProgram

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.LiveEnumeration
open RepairSource.CloseoutFinal.C10SupplierRowInput
open SharedNormalizedEstimatorProgram CanonicalRecoveryLanguage
open scoped BigOperators

def binary (K : Nat) : List (BitInput K) := List.ofFn (fourfoldInputFinEquiv K).symm

theorem binary_nodup (K : Nat) : (binary K).Nodup :=
  List.nodup_ofFn.mpr (fourfoldInputFinEquiv K).symm.injective

theorem binary_mem (K : Nat) (y : BitInput K) : y ∈ binary K := by
  apply List.mem_ofFn.mpr
  exact ⟨fourfoldInputFinEquiv K y,(fourfoldInputFinEquiv K).symm_apply_apply y⟩

theorem binary_perm {q : Nat} (live : Finset (Fin q)) :
    (binary live.card).Perm (liveList live) := by
  apply List.perm_ext_iff_of_nodup (binary_nodup live.card) (Finset.nodup_toList _ ) |>.mpr
  intro y
  simp only [binary_mem,Finset.mem_toList,Finset.mem_univ]

theorem binary_word_order (K : Nat) : binary K = allBitInputs K := by
  apply List.ext_getElem
  · simp only [binary,allBitInputs,List.length_ofFn,List.length_map,List.length_range]
  · intro i hi hj
    simp only [binary,allBitInputs,List.getElem_ofFn,List.getElem_map,List.getElem_range]
    rfl

theorem sum_binary {q : Nat} (live : Finset (Fin q)) {M : Type} [AddCommMonoid M]
    (f : BitInput live.card → M) :
    ((binary live.card).map f).sum = ((liveList live).map f).sum :=
  ((binary_perm live).map f).sum_eq

end NearCubicWires.P1Closure.LiveEnumeration
