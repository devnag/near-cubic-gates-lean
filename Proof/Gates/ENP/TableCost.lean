import Proof.Gates.ENP.TableBlock

set_option autoImplicit false

namespace NearCubicGates.Close.ENP.TEmit

open NearCubicGates.Close.CheckedPCPP.NodeEmit

theorem argCost_mono2 {x x' k bz bz' : ℕ} (hx : x ≤ x') (hb : bz ≤ bz') : argCost x k bz ≤ argCost x' k bz' := by
  have h1 := argCost_mono (k := k) (bz := bz) hx
  have h2 : argCost x' k bz ≤ argCost x' k bz' := by
    unfold argCost
    omega
  omega

theorem groupCost_mono3 {ℓ a gs Wm P a' gs' Wm' P' : ℕ} (ha : a ≤ a') (hg : gs ≤ gs') (hw : Wm ≤ Wm') (hP : P ≤ P') :
    groupCost ℓ a gs Wm P ≤ groupCost ℓ a' gs' Wm' P' := by
  unfold groupCost
  have h1 := pairCost_mono (u := a) (w := Wm) (V := gs + 2 * ℓ + Wm + a + 4) (u' := a') (w' := Wm')
    (V' := gs' + 2 * ℓ + Wm' + a' + 4) ha hw (by omega)
  have h2 := nodeCost_mono (V := gs + 2 * ℓ + Wm + a + 4) (V' := gs' + 2 * ℓ + Wm' + a' + 4) (by omega)
  have h3 := Nat.mul_le_mul_left ℓ (Nat.add_le_add_right h1 8)
  omega

theorem groupsCost_mono3 {ℓ T np0 Wm P np0' Wm' P' : ℕ} (hn : np0 ≤ np0') (hw : Wm ≤ Wm') (hP : P ≤ P') :
    groupsCost ℓ T np0 Wm P ≤ groupsCost ℓ T np0' Wm' P' := by
  unfold groupsCost
  have := groupCost_mono3 (ℓ := ℓ) (a := T) (a' := T) (gs := np0 + T * (2 * ℓ + 1)) (gs' := np0' + T * (2 * ℓ + 1))
    le_rfl (by omega) hw hP
  have := Nat.mul_le_mul_left T (Nat.add_le_add_right this 8)
  omega

theorem oracleCost_mono {ℓ T np0 Xm kk bz np0' Xm' bz' : ℕ} (hn : np0 ≤ np0') (hx : Xm ≤ Xm') (hb : bz ≤ bz') :
    oracleCost ℓ T np0 Xm kk bz ≤ oracleCost ℓ T np0' Xm' kk bz' := by
  unfold oracleCost
  have hxk : Xm * kk ≤ Xm' * kk := Nat.mul_le_mul_right _ hx
  have h1 := Nat.mul_le_mul_left ℓ (Nat.add_le_add_right (argCost_mono2 (k := kk) hx hb) 8)
  have h2 : ℓ * (bz + Xm * kk + kk) ≤ ℓ * (bz' + Xm' * kk + kk) := Nat.mul_le_mul_left _ (by omega)
  have h3 := groupsCost_mono3 (ℓ := ℓ) (T := T) hn (show bz + Xm * kk + kk ≤ bz' + Xm' * kk + kk by omega) h2
  omega

end NearCubicGates.Close.ENP.TEmit
