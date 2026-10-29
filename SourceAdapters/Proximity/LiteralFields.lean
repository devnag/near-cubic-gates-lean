import SourceAdapters.Proximity.LegacyOutput
import SourceAdapters.Proximity.OriginalAddress

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": literal polarity is converted to the
signed-query negation bit, then the exact tag/address/negation triple is emitted
using the trimming request's natWord fields. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.LiteralFields

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open SourceRequests (State Script)
open SourceResults (tagReg)
open OriginalAddress (kindReg addressReg)

def negatedReg : Fin VV := 31

def negatePositive : Script :=
  .ite (.eq tagReg vZ) (.op (.copy negatedReg v1)) (.op (.zero negatedReg))

theorem negate_positive (C : Ctx) (a : State) (hc : Cst a) (positive : Bool)
    (hpositive : a.env tagReg = positive.toNat) :
    Ex C negatePositive a (a.set negatedReg (!positive).toNat) 2 := by
  cases positive
  · have e := Ex.op (OpEx.copy (C := C) negatedReg v1 a (by decide))
    rw [hc.one] at e
    exact Ex.iteT (c := Cnd.eq tagReg vZ) (by decide : tagReg ≠ vZ)
      (by simp [Cnd.eval, hc.z, hpositive]) e
  · exact Ex.iteF (c := Cnd.eq tagReg vZ) (by decide : tagReg ≠ vZ)
      (by simp [Cnd.eval, hc.z, hpositive]) (Ex.op (OpEx.zero negatedReg a))

def scratch : List (Fin VV) := negatedReg :: LegacyOutput.scratch

def fields : Script :=
  .seq negatePositive (LegacyOutput.fieldsFrom [kindReg, addressReg, negatedReg])

def literalWord (proof : Bool) (address : ℕ) (positive : Bool) : List Bool :=
  natWord proof.toNat ++ natWord address ++ natWord (!positive).toNat

theorem bool_bitLength (b : Bool) : natBitLength b.toNat = 1 := by cases b <;> decide

theorem fields_run (C : Ctx) (a : State) (hc : Cst a) (proof positive : Bool) (address : ℕ)
    (hkind : a.env kindReg = proof.toNat) (haddress : a.env addressReg = address)
    (hpositive : a.env tagReg = positive.toNat) (hW : 2 ≤ C.Wd)
    (hvalue : natBitLength address + 2 < 2 ^ C.Wd) :
    Hs C fields a (40 * natBitLength address + 213) (fun b =>
      LegacyOutput.rest b = LegacyOutput.rest a ∧
      b.out = a.out ++ literalWord proof address positive ∧ Fr a b scratch) := by
  have e1 := negate_positive C a hc positive hpositive
  let b := a.set negatedReg (!positive).toNat
  have hbC : Cst b := Cst.of_fr hc (Fr.set a _ (T := [negatedReg]) (by simp)) (by decide)
  have hbk : b.env kindReg = proof.toNat := by
    rw [DS.set_env_ne _ _ (by decide : kindReg ≠ negatedReg)]; exact hkind
  have hba : b.env addressReg = address := by
    rw [DS.set_env_ne _ _ (by decide : addressReg ≠ negatedReg)]; exact haddress
  have hbn : b.env negatedReg = (!positive).toNat := by simp [b]
  have hthree : 3 < 2 ^ C.Wd := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hW
    norm_num at hp
    omega
  have e2 := LegacyOutput.fields_from C [kindReg, addressReg, negatedReg] b hbC hW (by decide) (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · simpa [hbk, bool_bitLength] using hthree
    · simpa [hba] using hvalue
    · simpa [hbn, bool_bitLength] using hthree)
  obtain ⟨d, cost, he, hcost, hd⟩ := e2
  refine ⟨d, 2 + cost + 1, Ex.seq e1 he, ?_, hd.rest_eq, ?_, ?_⟩
  · simp only [LegacyOutput.fieldsCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      hbk, hba, hbn, bool_bitLength] at hcost
    omega
  · have hbo : b.out = a.out := rfl
    rw [hd.out_eq, hbo]
    simp [LegacyOutput.fieldsWord, hbk, hba, hbn, literalWord, List.append_assoc]
  · exact (Fr.set a _ (List.mem_cons_self ..)).trans
      (hd.vars.weaken (fun _ h => List.mem_cons_of_mem negatedReg h))

end NearCubicGates.Adapters.Proximity.LiteralFields
