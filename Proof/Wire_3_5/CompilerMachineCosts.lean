import Proof.Wire_3_5.CompilerMachineMasksAll
import Proof.Wire_3_5.CompilerMachineCancelEntry

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Cancel NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.CompilerMachine.Unions

theorem filterLoopCost_mono2 {n n' W W' : ℕ} (h1 : n ≤ n') (h2 : W ≤ W') : filterLoopCost n W ≤ filterLoopCost n' W' := by
  unfold filterLoopCost; gcongr

theorem copyLoopCost_mono2 {n n' W W' : ℕ} (h1 : n ≤ n') (h2 : W ≤ W') : copyLoopCost n W ≤ copyLoopCost n' W' := by
  unfold copyLoopCost; gcongr

theorem symCost_mono2 {n n' W W' : ℕ} (h1 : n ≤ n') (h2 : W ≤ W') : symCost n W ≤ symCost n' W' := by
  unfold symCost
  have := filterLoopCost_mono2 h1 h2
  have := copyLoopCost_mono2 (Nat.add_le_add_right h1 1) h2
  omega

theorem allCost_mono2 {n n' W W' : ℕ} (h1 : n ≤ n') (h2 : W ≤ W') : allCost n W ≤ allCost n' W' := by
  unfold allCost
  have := symCost_mono2 h1 h2
  omega

theorem insertAllCost_mono {m m' n n' W W' : ℕ} (h1 : m ≤ m') (h2 : n ≤ n') (h3 : W ≤ W') :
    insertAllCost m n W ≤ insertAllCost m' n' W' := by
  unfold insertAllCost
  have := allCost_mono2 (Nat.add_le_add h2 h1) h3
  gcongr

theorem expandLoopCost_mono2 {m m' K L : ℕ} (h : m ≤ m') : expandLoopCost m K L ≤ expandLoopCost m' K L := by
  unfold expandLoopCost; gcongr

theorem atomCost_mono {P K N N' L : ℕ} (h : N ≤ N') : atomCost P K N L ≤ atomCost P K N' L := by
  unfold atomCost
  have := expandLoopCost_mono2 (K := K) (L := L) h
  have := copyLoopCost_mono2 (W := L) (W' := L) h (le_refl L)
  omega

theorem atomsCost_mono {n n' P K L : ℕ} (hK : 1 ≤ K) (h : n ≤ n') : atomsCost n P K L ≤ atomsCost n' P K L := by
  unfold atomsCost
  have h1 : K ^ n ≤ K ^ n' := Nat.pow_le_pow_right hK h
  have h2 := atomCost_mono (P := P) (K := K) (L := L) h1
  gcongr

theorem monoCost_mono {n n' P Q W : ℕ} (h : n ≤ n') : monoCost n P Q W ≤ monoCost n' P Q W := by
  unfold monoCost
  have := atomsCost_mono (P := P) (L := Q + W + 1) (by omega : 1 ≤ W + 1) h
  omega

theorem unionsCost_mono {m m' N N' L : ℕ} (h1 : m ≤ m') (h2 : N ≤ N') : unionsCost m N L ≤ unionsCost m' N' L := by
  unfold unionsCost aCost
  have := liftCost_mono L h2
  gcongr

end NearCubicWires.WireExponent3_5.CompilerMachine
