import SourceAdapters.Proximity.RawFraming
import SourceAdapters.Proximity.SourcePrinting

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": retained-count raw field copying with exact state
preservation, including the physically emitted frame delimiter. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.RawFields

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Code.CellSending NearCubicGates.Adapters.Code.CountedParsing
abbrev State := DS VV MM
abbrev Script := St VV MM

def remaining : Fin VV := 45

def copyChunk (x : Fin VV) (framed : Bool) : Script :=
  .seq (.op (.copy remaining x)) (.seq (.op (.zero vJ))
    (RawFraming.sendChunk vZ v1 vJ remaining false framed))

structure Copied (a b : State) (count : ℕ) (word : List Bool) : Prop where
  cursor : b.ip = a.ip + count
  output : b.out = a.out ++ word
  ram : b.ram = a.ram
  rc : b.rc = a.rc
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  vars : Fr a b [vJ, remaining]

theorem Copied.constants {a b : State} {n : ℕ} {w : List Bool}
    (h : Copied a b n w) (hc : Cst a) : Cst b := Cst.of_fr hc h.vars (by decide)

theorem copy_chunk (C : Ctx) (x : Fin VV) (hx : x ≠ remaining) (framed : Bool)
    (a : State) (hc : Cst a) (bits pre suffix : List Bool)
    (hin : C.inp = pre ++ bits ++ suffix) (hip : a.ip = pre.length)
    (hxv : a.env x = bits.length) :
    Hs C (copyChunk x framed) a ((payloadCost framed + 8) * bits.length + 6)
      (fun b => Copied a b bits.length (bits.flatMap (payload framed))) := by
  have e1 := Ex.op (OpEx.copy (C := C) remaining x a hx.symm)
  rw [hxv] at e1
  let b := a.set remaining bits.length
  have e2 := Ex.op (OpEx.zero (C := C) vJ b)
  let d := b.set vJ 0
  have e3 := RawFraming.send_chunk C vZ v1 vJ remaining (by decide) (by decide)
    (by decide) (by decide) (by decide) false framed bits pre suffix d
    (by simp only [d, b, DS.set_env_ne _ _ (by decide : vZ ≠ vJ),
        DS.set_env_ne _ _ (by decide : vZ ≠ remaining)]; exact hc.z)
    (by simp only [d, b, DS.set_env_ne _ _ (by decide : v1 ≠ vJ),
        DS.set_env_ne _ _ (by decide : v1 ≠ remaining)]; exact hc.one)
    (by simp [d]) (by simp only [d, DS.set_env_ne _ _ (by decide : remaining ≠ vJ), b, DS.set_env_self]) hin hip (by simp)
  refine ⟨_, _, Ex.seq e1 (Ex.seq e2 e3), by omega, ?_⟩
  refine ⟨by simp [chunkResult, sent, hip], rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  have hij : i ≠ vJ := fun h => hi (by simp [h])
  have hir : i ≠ remaining := fun h => hi (by simp [h])
  simp [chunkResult, sent, d, b, DS.set, hij, hir]

def field (x : Fin VV) : Script := .seq (copyChunk x true) (.op (.emit false))

theorem field_run (C : Ctx) (x : Fin VV) (hx : x ≠ remaining)
    (a : State) (hc : Cst a) (bits pre suffix : List Bool)
    (hin : C.inp = pre ++ bits ++ suffix) (hip : a.ip = pre.length)
    (hxv : a.env x = bits.length) :
    Hs C (field x) a (12 * bits.length + 8)
      (fun b => Copied a b bits.length (frame bits)) := by
  obtain ⟨b, cost, he, ht, hb⟩ := copy_chunk C x hx true a hc bits pre suffix hin hip hxv
  refine ⟨_, _, Ex.seq he (Ex.op (OpEx.emit false b)), by simp only [payloadCost, if_true] at ht; omega, ?_⟩
  refine ⟨hb.cursor, ?_, hb.ram, hb.rc, hb.kin, hb.kout, hb.kc, hb.vars⟩
  change b.out ++ [false] = a.out ++ frame bits
  rw [hb.output, List.append_assoc]
  apply congrArg (a.out ++ ·)
  exact (NearCubicGates.Close.CounterMachine.CellTablesProg.frame_marks bits).symm

end NearCubicGates.Adapters.Proximity.RawFields
