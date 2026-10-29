import Proof.Gates.Cells.Hs

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the source input tag preserves its
address, while the proof tag doubles it. Both branches execute paid operations. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.AddressRenaming

open NearCubicGates.Close.Cells
variable {V M : ℕ}

private theorem Rne (R : Fin 3 ↪ Fin V) {i j : Fin 3} (h : i ≠ j) : R i ≠ R j := R.injective.ne h

def renameProgram (R : Fin 3 ↪ Fin V) : St V M :=
  .ite (.eq (R 0) (R 1)) (.op (.zero (R 1))) (.op (.shl (R 2)))

theorem rename_program (C : Ctx) (R : Fin 3 ↪ Fin V) (a : DS V M) (proof : Bool) (address : ℕ)
    (hz : a.env (R 0) = 0) (htag : a.env (R 1) = proof.toNat) (ha : a.env (R 2) = address)
    (hW : 2 * address < 2 ^ C.Wd) :
    Hs C (renameProgram R) a 2 (fun b =>
      b.env (R 1) = proof.toNat ∧ b.env (R 2) = (if proof then 2 * address else address) ∧
      Same a b ∧ Fr a b [R 1, R 2]) := by
  cases proof
  · have e : Ex C (renameProgram R) a (a.set (R 1) 0) 2 :=
      Ex.iteT (c := Cnd.eq (R 0) (R 1)) (Rne R (by decide))
        (by simp [Cnd.eval, hz, htag]) (Ex.op (OpEx.zero (C := C) (R 1) a))
    exact ⟨_, _, e, le_rfl, by simp, by simp [DS.set, ha], Same.set a _ _, Fr.set a 0 (by simp)⟩
  · have e : Ex C (renameProgram R) a (a.set (R 2) (2 * address)) 2 := by
      have h := Ex.op (OpEx.shl (C := C) (R 2) a (by rw [ha]; exact hW))
      rw [ha] at h
      exact Ex.iteF (c := Cnd.eq (R 0) (R 1)) (Rne R (by decide)) (by simp [Cnd.eval, hz, htag]) h
    exact ⟨_, _, e, le_rfl, by simp [DS.set, htag], by simp, Same.set a _ _, Fr.set a _ (by simp)⟩

end NearCubicGates.Adapters.Proximity.AddressRenaming
