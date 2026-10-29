import SourceAdapters.Proximity.HeaderReading
import Proof.Gates.Cells.Kit

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": read and retain a target natural header, then
restore the cursor by its actual unary-length-prefixed field length. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.LegacyHeader

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Code.CountedParsing
open SourceHeader (arityReg State Script)

def scratch : List (Fin VV) := arityReg :: rdNatT

def readArity : Script := .seq rdNatI (.seq (.op (.copy arityReg t3))
  (.seq (.op (.shl t4)) (.seq (.op (.inc t4)) (rewindCount vZ v1 t4))))

theorem read_arity (C : Ctx) (a : State) (hc : Cst a) (n : ℕ) (pre tail : List Bool)
    (hin : C.inp = pre ++ natWord n ++ tail) (hip : a.ip = pre.length)
    (hW : natBitLength n + 2 ≤ C.Wd) (hrew : 2 * natBitLength n + 1 < 2 ^ C.Wd) :
    Hs C readArity a (40 * natBitLength n + 50)
      (fun b => b.env arityReg = n ∧ Same a b ∧ Fr a b scratch) := by
  have hdrop : C.inp.drop a.ip = natWord n ++ tail := by rw [hip, hin, List.append_assoc, List.drop_left]
  obtain ⟨b, cost, he, ht, hbn, hbL, hbip, hbo, hbf⟩ := rdNatI_spec a hc n tail hdrop hW
  have hbC := cst_fr hc hbf
  have e2 := Ex.op (OpEx.copy (C := C) arityReg t3 b (by decide))
  rw [hbn] at e2
  let d := b.set arityReg n
  have hdL : d.env t4 = natBitLength n := by simpa only [d, DS.set_env_ne _ _ (by decide : t4 ≠ arityReg)] using hbL
  have e3 := Ex.op (OpEx.shl (C := C) t4 d (by rw [hdL]; omega))
  rw [hdL] at e3
  let f := d.set t4 (2 * natBitLength n)
  have e4 := Ex.op (OpEx.inc (C := C) t4 f (by simpa only [f, DS.set_env_self] using hrew))
  let g := f.set t4 (2 * natBitLength n + 1)
  change Ex C (.op (.inc t4)) f g 1 at e4
  have e5 := rewind_count C vZ v1 t4 (by decide) (by decide) g
    (by simp only [g, f, d, DS.set_env_ne _ _ (by decide : vZ ≠ t4), DS.set_env_ne _ _ (by decide : vZ ≠ arityReg)]; exact hbC.z)
    (by simp only [g, f, d, DS.set_env_ne _ _ (by decide : v1 ≠ t4), DS.set_env_ne _ _ (by decide : v1 ≠ arityReg)]; exact hbC.one)
    pre.length (2 * natBitLength n + 1)
  have hg : rewindState t4 g (pre.length + (2 * natBitLength n + 1)) (2 * natBitLength n + 1) = g := by
    apply state_ext
    · simp [rewindState, g, f, d, DS.set]
    · change pre.length + (2 * natBitLength n + 1) = b.ip
      rw [hbip, hip, natWord_length]
    all_goals rfl
  rw [hg] at e5
  refine ⟨_, _, Ex.seq he (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 e5))), by omega, ?_, ?_, ?_⟩
  · simp only [rewindState, g, f, DS.set_env_ne _ _ (by decide : arityReg ≠ t4), d, DS.set_env_self]
  · simp only [Prod.mk.injEq] at hbo
    exact ⟨hip.symm, hbo.1, hbo.2.1, hbo.2.2.1, hbo.2.2.2.1, hbo.2.2.2.2.1, hbo.2.2.2.2.2⟩
  · intro i hi
    have hia : i ≠ arityReg := fun h => hi (by simp [scratch, h])
    have hit : i ≠ t4 := fun h => hi (by simp [scratch, rdNatT, h])
    simp only [rewindState, g, f, d, DS.set_env_ne _ _ hit, DS.set_env_ne _ _ hia]
    exact hbf i (fun h => hi (List.mem_cons_of_mem _ h))

end NearCubicGates.Adapters.Proximity.LegacyHeader
