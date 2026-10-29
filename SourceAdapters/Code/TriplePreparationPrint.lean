import SourceAdapters.Code.TriplePreparationBits
import SourceAdapters.Proximity.RawFields
import Proof.Gates.CheckedPCPP.NodeEmit

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": print the requested triple codec from two retained bit
stores and an exactly counted raw input suffix. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.TriplePreparation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Proximity

def total : Fin VV := 40
def xlen : Fin VV := 41
def ylen : Fin VV := 42
def zlen : Fin VV := 43
def temp : Fin VV := 44

def printScript : St VV MM := .seq (.op (.copy t3 xlen)) (.seq emitNatO
  (.seq (TriplePreparationBits.script 0 xlen)
    (.seq (RawFields.field zlen) (TriplePreparationBits.script 1 ylen))))

theorem print_runs (C : Ctx) (a : DS VV MM) (hc : Cst a) (x y z pre suffix : List Bool)
    (hin : C.inp = pre ++ z ++ suffix) (hip : a.ip = pre.length)
    (hx : a.ram 0 = x.map Bool.toNat) (hy : a.ram 1 = y.map Bool.toNat)
    (hxl : a.env xlen = x.length) (hyl : a.env ylen = y.length) (hzl : a.env zlen = z.length)
    (hxc : a.rc 0 ≤ x.length) (hyc : a.rc 1 ≤ y.length)
    (hW : 2 ≤ C.Wd) (hxb : natBitLength x.length + 2 < 2 ^ C.Wd)
    (hxw : x.length < 2 ^ C.Wd) (hyw : y.length < 2 ^ C.Wd) :
    Hs C printScript a (200 * (x.length + y.length + z.length + 1))
      (fun b => b.out = a.out ++ (natWord x.length ++ x ++ frame z ++ y)) := by
  have e0 := Ex.op (OpEx.copy (C := C) t3 xlen a (by decide))
  rw [hxl] at e0
  let a1 := a.set t3 x.length
  have c1 : Cst a1 := Cst.of_fr hc (Fr.set (T := [t3]) a _ (by simp)) (by decide)
  obtain ⟨b, nb, eb, hb, bout, brest, bc, bf⟩ := emitNatO_spec (C := C) a1 c1 hW
    (by simpa [a1] using hxb)
  simp only [Prod.mk.injEq] at brest
  obtain ⟨bi, bm, brc, _, _, _⟩ := brest
  have bxl : b.env xlen = x.length := (bf xlen (by decide)).trans
    ((DS.set_env_ne _ _ (by decide : xlen ≠ t3)).trans hxl)
  obtain ⟨c, nc, ec, hcc, cout, _, cc, ci, _, cm, _, cothers, _, _, cf⟩ :=
    TriplePreparationBits.runs C 0 xlen (by decide) (by decide) b bc x
      (by rw [bm]; exact hx) bxl (by exact hxw)
  obtain ⟨d, nd, ed, hdd, hd⟩ := RawFields.field_run C zlen (by decide) c cc z pre suffix hin
    (ci.trans bi |>.trans hip)
    ((cf zlen (by decide)).trans ((bf zlen (by decide)).trans
      ((DS.set_env_ne _ _ (by decide : zlen ≠ t3)).trans hzl)))
  have dyl : d.env ylen = y.length := (hd.vars ylen (by decide)).trans
    ((cf ylen (by decide)).trans ((bf ylen (by decide)).trans
      ((DS.set_env_ne _ _ (by decide : ylen ≠ t3)).trans hyl)))
  obtain ⟨e, ne, ee, hee, eout, _, _, _, _, _, _, _, _, _, _⟩ :=
    TriplePreparationBits.runs C 1 ylen (by decide) (by decide) d (hd.constants cc) y
      (by rw [hd.ram, cm, bm]; exact hy) dyl hyw
  refine ⟨e, _, Ex.seq e0 (Ex.seq eb (Ex.seq ec (Ex.seq ed ee))), ?_, ?_⟩
  · have hbits := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le x.length
    have bxc : b.rc 0 ≤ x.length := by rw [brc]; exact hxc
    have dyc : d.rc 1 ≤ y.length := by rw [hd.rc, cothers 1 (by decide), brc]; exact hyc
    simp only [a1, DS.set_env_self] at hb
    omega
  · change e.out = _
    rw [eout, hd.output, cout, bout]
    simp [a1, List.append_assoc]

end NearCubicGates.Adapters.Code.TriplePreparation
