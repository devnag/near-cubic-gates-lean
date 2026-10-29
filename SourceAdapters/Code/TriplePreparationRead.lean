import SourceAdapters.Code.TriplePreparationPrint
import SourceAdapters.Code.InputBitLoading
import Proof.Gates.Cells.Prelude

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": read a computed total-length header, load the two framed
fields, and derive the exact remaining raw length by paid arithmetic. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.TriplePreparation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

def inputWord (x y z : List Bool) : List Bool := frame x ++ frame y ++ z

def rawPrefix (x y z : List Bool) : List Bool := natWord (inputWord x y z).length ++ frame x ++ frame y

def arithmetic : St VV MM := .seq (.op (.copy zlen total)) (.seq (.op (.copy temp xlen))
  (.seq (.op (.add temp ylen)) (.seq (.op (.shl temp))
    (.seq (.op (.add temp v2)) (.op (.sub zlen temp))))))

theorem arithmetic_runs (C : Ctx) (a : DS VV MM) (hc : Cst a) (x y z : ℕ)
    (ht : a.env total = 2 * x + 2 * y + 2 + z) (hx : a.env xlen = x) (hy : a.env ylen = y)
    (hwidth : 2 * x + 2 * y + 2 + z < 2 ^ C.Wd) :
    Ex C arithmetic a ((a.set zlen z).set temp (2 * (x + y) + 2)) 11 := by
  have e1 := Ex.op (OpEx.copy (C := C) zlen total a (by decide))
  rw [ht] at e1
  let a1 := a.set zlen (2 * x + 2 * y + 2 + z)
  have e2 := Ex.op (OpEx.copy (C := C) temp xlen a1 (by decide))
  have h1x : a1.env xlen = x := by simpa [a1, xlen, zlen] using hx
  rw [h1x] at e2
  let a2 := a1.set temp x
  have h2y : a2.env ylen = y := by simpa [a2, a1, ylen, temp, zlen] using hy
  have e3 := Ex.op (OpEx.add (C := C) temp ylen a2 (by decide)
    (by simp [a2, h2y]; omega))
  simp only [a2, DS.set_env_self] at e3
  rw [show (a1.set temp x).env ylen = y from h2y] at e3
  let a3 := a2.set temp (x + y)
  have e4 := Ex.op (OpEx.shl (C := C) temp a3 (by simp [a3]; omega))
  simp only [a3, DS.set_env_self] at e4
  let a4 := a3.set temp (2 * (x + y))
  have h42 : a4.env v2 = 2 := by
    simp only [a4, a3, a2, a1, DS.set_env_ne _ _ (by decide : v2 ≠ temp),
      DS.set_env_ne _ _ (by decide : v2 ≠ zlen)]
    exact hc.two
  have e5 := Ex.op (OpEx.add (C := C) temp v2 a4 (by decide)
    (by rw [h42]; simp [a4]; omega))
  rw [h42] at e5
  simp only [a4, DS.set_env_self] at e5
  let a5 := a4.set temp (2 * (x + y) + 2)
  have h5z : a5.env zlen = 2 * x + 2 * y + 2 + z := by simp [a5, a4, a3, a2, a1, zlen, temp]
  have e6 := Ex.op (OpEx.sub (C := C) zlen temp a5 (by decide)
    (by rw [h5z]; simp [a5]; omega))
  rw [h5z] at e6
  simp only [a5, DS.set_env_self] at e6
  have hsub : 2 * x + 2 * y + 2 + z - (2 * (x + y) + 2) = z := by omega
  rw [hsub] at e6
  have hstate : a5.set zlen z = (a.set zlen z).set temp (2 * (x + y) + 2) := by
    apply CountedParsing.state_ext
    · funext i
      by_cases hz : i = zlen
      · subst i; simp [a5, DS.set, zlen, temp]
      · by_cases ht : i = temp
        · subst i; simp [a5, DS.set, zlen, temp]
        · simp [a5, a4, a3, a2, a1, DS.set, hz, ht]
    all_goals rfl
  rw [hstate] at e6
  exact Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 (Ex.seq e5 e6))))

def readScript : St VV MM := .seq initP (.seq rdNatI (.seq (.op (.copy total t3))
  (.seq (InputBitLoading.script 0 xlen) (.seq (InputBitLoading.script 1 ylen) arithmetic))))

structure Loaded (x y z : List Bool) (a : DS VV MM) : Prop where
  constants : Cst a
  xstore : a.ram 0 = x.map Bool.toNat
  ystore : a.ram 1 = y.map Bool.toNat
  xsize : a.env xlen = x.length
  ysize : a.env ylen = y.length
  zsize : a.env zlen = z.length
  xcursor : a.rc 0 = x.length
  ycursor : a.rc 1 = y.length
  input : a.ip = (rawPrefix x y z).length
  output : a.out = []

theorem read_runs (C : Ctx) (x y z : List Bool)
    (hin : C.inp = natWord (inputWord x y z).length ++ inputWord x y z)
    (hW : 16 * ((inputWord x y z).length + 1) ≤ C.Wd) :
    Hs C readScript (a0 : DS VV MM) (1000 * ((inputWord x y z).length + 1)) (Loaded x y z) := by
  let L := (inputWord x y z).length
  have hL : L = 2 * x.length + 2 * y.length + 2 + z.length := by
    simp only [L, inputWord, List.length_append, frame_length]
    omega
  have hbits := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le L
  have hwidth : L < 2 ^ C.Wd := lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
  obtain ⟨b, nb, eb, hb, bc, bm, brc, bi, bo, _, _, _, _⟩ :=
    initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl (by omega)
  obtain ⟨d, nd, ed, hd, dt, _, di, dr, df⟩ := rdNatI_spec (C := C) b bc L (inputWord x y z)
    (by rw [bi, hin]; rfl) (by omega)
  simp only [Prod.mk.injEq] at dr
  obtain ⟨do_, dm, drc, _, _, _⟩ := dr
  have dc := cst_fr bc df
  have e0 := Ex.op (OpEx.copy (C := C) total t3 d (by decide))
  rw [dt] at e0
  let d0 := d.set total L
  have dc0 : Cst d0 := Cst.of_fr dc (Fr.set (T := [total]) d _ (by simp)) (by decide)
  have hxw : x.length < 2 ^ C.Wd := by omega
  have hyw : y.length < 2 ^ C.Wd := by omega
  obtain ⟨e, ne, ee, he, ex, exl, exc, ei, ec, eo, _, _, _, eother, ef⟩ :=
    InputBitLoading.spec C 0 xlen (by decide) (by decide) d0 dc0 x (natWord L) (frame y ++ z)
      (by simpa [L, inputWord, List.append_assoc] using hin)
      (by simp [d0, di, bi, a0])
      (by change d.ram 0 = []; rw [dm, bm]; rfl)
      (by change d.rc 0 = 0; rw [drc, brc]; rfl) hxw
  obtain ⟨f, nf, eF, hf, fy, fyl, fyc, fi, fc, fo, _, _, _, fother, ff⟩ :=
    InputBitLoading.spec C 1 ylen (by decide) (by decide) e ec y (natWord L ++ frame x) z
      (by simpa [L, inputWord, List.append_assoc] using hin)
      (by simpa using ei)
      (by rw [(eother 1 (by decide)).1]; change d.ram 1 = []; rw [dm, bm]; rfl)
      (by rw [(eother 1 (by decide)).2]; change d.rc 1 = 0; rw [drc, brc]; rfl) hyw
  have ft : f.env total = 2 * x.length + 2 * y.length + 2 + z.length := by
    rw [ff total (by decide), ef total (by decide)]
    simpa [d0] using hL
  have fxl : f.env xlen = x.length := (ff xlen (by decide)).trans exl
  have ea := arithmetic_runs C f fc x.length y.length z.length ft fxl fyl (by omega)
  let g := (f.set zlen z.length).set temp (2 * (x.length + y.length) + 2)
  have gf : Fr f g [zlen, temp] :=
    (Fr.set f _ (by simp)).trans (Fr.set (f.set zlen z.length) _ (by simp))
  refine ⟨g, _, Ex.seq eb (Ex.seq ed (Ex.seq e0 (Ex.seq ee (Ex.seq eF ea)))), ?_, ?_⟩
  · change _ ≤ 1000 * (L + 1)
    omega
  · refine ⟨Cst.of_fr fc gf (by decide), ?_, fy, ?_, ?_, ?_, ?_, fyc, ?_, ?_⟩
    · exact (fother 0 (by decide)).1.trans ex
    · exact (gf xlen (by decide)).trans fxl
    · exact (gf ylen (by decide)).trans fyl
    · simp [g, zlen, temp]
    · exact (fother 0 (by decide)).2.trans exc
    · simpa [g, rawPrefix, L, Nat.add_assoc] using fi
    · exact fo.trans (eo.trans (do_.trans bo))

end NearCubicGates.Adapters.Code.TriplePreparation
