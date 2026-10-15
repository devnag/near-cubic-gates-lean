import Proof.Amplification.RecoveryBoundedNativeFoldResult

/-! Original literal references fit the one enclosing compiler envelope. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prefixCount_bound {n : ℕ} (items : List (Item n)) : prefixCount items ≤ 2*items.length := by
  induction items with
  | nil=>simp [prefixCount]
  | cons item items ih=>
    have h : item.2.toNat ≤ 1 := by cases item.2 <;> decide
    simp only [prefixCount,literalCount,List.length_cons]
    omega

theorem references_bound {n : ℕ} (base : ℕ) (items : List (Item n)) :
    ∀ ref∈literalReferences base items,ref ≤ base+prefixCount items := by
  induction items generalizing base with
  | nil=>simp [literalReferences]
  | cons item items ih=>
    intro ref hr
    simp only [literalReferences,List.mem_cons] at hr
    rcases hr with rfl|hr
    · simp only [prefixCount,literalCount]
      omega
    · have h:=ih (base+literalCount item) ref hr
      simp only [prefixCount]
      omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedNative
