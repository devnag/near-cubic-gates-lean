import SourceAdapters.Joins.AffineRouting
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.BitVec

/-!
The construction in `app:affine-embedding`: binary masks label the full Boolean span, and XOR of masks
is addition in the characteristic-two field. Independence is used only
for injectivity of bounded masks. No layout or landing claim is assumed.-/
set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.LayoutFacts
open scoped BigOperators
variable {F : Type} [Field F]

theorem cubeEval_xor [CharP F 2] (m : ℕ) (e : Fin m → F) (u v : Fin m → Bool) :
    cubeEval m e (fun i => u i ^^ v i) = cubeEval m e u + cubeEval m e v := by
  unfold cubeEval
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hu : u i <;> cases hv : v i <;> simp [hu, hv, CharTwo.add_self_eq_zero]

theorem maskEval_zero (m : ℕ) (e : Fin m → F) : maskEval m e 0 = 0 := by
  simp [maskEval]

theorem maskEval_xor [CharP F 2] (m : ℕ) (e : Fin m → F) (u v : ℕ) :
    maskEval m e (u ^^^ v) = maskEval m e u + maskEval m e v := by
  simpa only [cubeEval, maskEval, Nat.testBit_xor] using
    cubeEval_xor m e (fun i => u.testBit i.val) (fun i => v.testBit i.val)

theorem maskEval_mem (m : ℕ) (e : Fin m → F) (u : ℕ) : InH m e (maskEval m e u) :=
  ⟨fun i => u.testBit i.val, rfl⟩

theorem inH_add [CharP F 2] (m : ℕ) (e : Fin m → F) (x y : F) (hx : InH m e x) (hy : InH m e y) :
    InH m e (x+y) := by
  obtain ⟨u,rfl⟩ := hx
  obtain ⟨v,rfl⟩ := hy
  exact ⟨fun i => u i ^^ v i, cubeEval_xor m e u v⟩

theorem inH_translate [CharP F 2] (m : ℕ) (e : Fin m → F) (u : ℕ) (z : F) (hz : InH m e z) :
    InH m e (z + maskEval m e u) := inH_add m e z _ hz (maskEval_mem m e u)

theorem maskEval_injective (m : ℕ) (e : Fin m → F) (he : Independent m e)
    (u v : ℕ) (hu : u < 2^m) (hv : v < 2^m) (h : maskEval m e u = maskEval m e v) : u = v := by
  have hb := he h
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < m
  · exact congrFun hb ⟨i,hi⟩
  · have hp : 2^m ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (hu.trans_le hp), Nat.testBit_lt_two_pow (hv.trans_le hp)]

theorem maskEval_two_pow (m : ℕ) (e : Fin m → F) (i : Fin m) :
    maskEval m e (2^i.val) = e i := by
  simp [maskEval, Nat.testBit_two_pow, ← Fin.ext_iff]

/-- A Boolean cube vertex as an ordinary bounded natural mask. -/
def cubeMask {m : ℕ} (v : Fin m → Bool) : ℕ :=
  (BitVec.ofBoolListLE (List.ofFn v)).toNat

theorem cubeMask_lt {m : ℕ} (v : Fin m → Bool) : cubeMask v < 2^m := by
  simpa only [cubeMask, List.length_ofFn] using (BitVec.ofBoolListLE (List.ofFn v)).isLt

theorem cubeMask_testBit {m : ℕ} (v : Fin m → Bool) (i : Fin m) :
    (cubeMask v).testBit i.val = v i := by
  change (BitVec.ofBoolListLE (List.ofFn v)).getLsbD i.val = v i
  rw [BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD]

theorem maskEval_cubeMask {m : ℕ} (e : Fin m → F) (v : Fin m → Bool) :
    maskEval m e (cubeMask v) = cubeEval m e v := by
  simp only [maskEval, cubeEval, cubeMask_testBit]

end NearCubicGates.Adapters.Routing.LayoutFacts
