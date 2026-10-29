import SourceAdapters.Proximity.HonestPreparedSkip
import SourceAdapters.Proximity.DescriptorParsing

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": physically parse total and source lengths, and
compute the exact remaining rewind distance from the legacy header width. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestPrepared

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open SourceRequests (State Script lengthReg)

def totalReg : Fin VV := 60
def prefixReg : Fin VV := 61

def header : Script := .seq (SourcePrinting.readInto totalReg) (.seq rdNatI
  (.seq (.op (.copy lengthReg t3)) (.seq (.op (.copy prefixReg t4))
    (.seq (.op (.shl prefixReg)) (.seq (.op (.inc prefixReg)) (.op (.sub totalReg prefixReg)))))))

def headerScratch : List (Fin VV) := [totalReg, prefixReg, lengthReg] ++ rdNatT

structure HeaderRead (a b : State) (total sourceLength : ℕ) : Prop where
  source_length : b.env lengthReg = sourceLength
  prefix_length : b.env prefixReg = (natWord sourceLength).length
  remaining : b.env totalReg = total - (natWord sourceLength).length
  cursor : b.ip = (natWord total).length + (natWord sourceLength).length
  other : (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) = (a.out, a.ram, a.rc, a.kin, a.kout, a.kc)
  vars : Fr a b headerScratch

theorem header_run (C : Ctx) (a : State) (hc : Cst a) (total sourceLength : ℕ) (tail : List Bool)
    (hin : C.inp = natWord total ++ natWord sourceLength ++ tail) (hip : a.ip = 0)
    (ht : natBitLength total + 2 ≤ C.Wd) (hs : natBitLength sourceLength + 2 ≤ C.Wd)
    (hp : (natWord sourceLength).length < 2 ^ C.Wd) (hle : (natWord sourceLength).length ≤ total) :
    Hs C header a (30 * natBitLength total + 30 * natBitLength sourceLength + 73)
      (fun b => HeaderRead a b total sourceLength) := by
  have hdrop : C.inp.drop a.ip = natWord total ++ (natWord sourceLength ++ tail) := by
    rw [hip, List.drop_zero, hin, List.append_assoc]
  obtain ⟨b, nb, eb, hb, rb⟩ := SourcePrinting.read_into (C := C) totalReg (by decide)
    a hc total _ hdrop ht
  have cb := rb.constants hc (by decide)
  obtain ⟨d, nd, ed, hd, dn, dbits, dip, dother, df⟩ := rdNatI_spec (C := C) b cb sourceLength tail (rb.tail _ hdrop) hs
  have dtotal : d.env totalReg = total := (df totalReg (by decide)).trans rb.value
  have e1 := Ex.op (OpEx.copy (C := C) lengthReg t3 d (by decide))
  rw [dn] at e1
  let f := d.set lengthReg sourceLength
  have fbits : f.env t4 = natBitLength sourceLength := by
    simpa only [f, DS.set_env_ne _ _ (by decide : t4 ≠ lengthReg)] using dbits
  have e2 := Ex.op (OpEx.copy (C := C) prefixReg t4 f (by decide))
  rw [fbits] at e2
  let g := f.set prefixReg (natBitLength sourceLength)
  have hplen : (natWord sourceLength).length = 2 * natBitLength sourceLength + 1 := natWord_length sourceLength
  have e3 := Ex.op (OpEx.shl (C := C) prefixReg g (by simp only [g, DS.set_env_self]; rw [hplen] at hp; omega))
  let h := g.set prefixReg (2 * natBitLength sourceLength)
  change Ex C (.op (.shl prefixReg)) g h 1 at e3
  have e4 := Ex.op (OpEx.inc (C := C) prefixReg h (by simp only [h, DS.set_env_self]; rw [hplen] at hp; exact hp))
  let j := h.set prefixReg (2 * natBitLength sourceLength + 1)
  change Ex C (.op (.inc prefixReg)) h j 1 at e4
  have jtotal : j.env totalReg = total := by
    simp only [j, h, g, f, DS.set_env_ne _ _ (by decide : totalReg ≠ prefixReg),
      DS.set_env_ne _ _ (by decide : totalReg ≠ lengthReg), dtotal]
  have jprefix : j.env prefixReg = (natWord sourceLength).length := by simp [j, hplen]
  have e5 := Ex.op (OpEx.sub (C := C) totalReg prefixReg j (by decide) (by rw [jtotal, jprefix]; exact hle))
  rw [jtotal, jprefix] at e5
  refine ⟨_, _, Ex.seq eb (Ex.seq ed (Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 e5))))), by omega, ?_⟩
  refine ⟨?_, ?_, by simp, ?_, dother.trans rb.other, ?_⟩
  · simp [j, h, g, f, DS.set, lengthReg, totalReg, prefixReg]
  · simp only [DS.set_env_ne _ _ (by decide : prefixReg ≠ totalReg), jprefix]
  · change d.ip = _
    rw [dip, rb.cursor, hip, Nat.zero_add]
  · intro i hi
    have hit : i ≠ totalReg := fun h => hi (by simp [headerScratch, h])
    have hipr : i ≠ prefixReg := fun h => hi (by simp [headerScratch, h])
    have hil : i ≠ lengthReg := fun h => hi (by simp [headerScratch, h])
    have hid : i ∉ rdNatT := fun h => hi (List.mem_append_right _ h)
    have hir : i ∉ totalReg :: rdNatT := by simp only [List.mem_cons, not_or]; exact ⟨hit, hid⟩
    simp only [j, h, g, f, DS.set_env_ne _ _ hit, DS.set_env_ne _ _ hipr, DS.set_env_ne _ _ hil]
    exact (df i hid).trans (rb.vars i hir)

end NearCubicGates.Adapters.Proximity.HonestPrepared
