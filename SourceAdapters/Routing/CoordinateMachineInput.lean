import SourceAdapters.Routing.CoordinateMachineInputBounds
import SourceAdapters.ShortPCP.Machines.FLangParseMain
import SourceAdapters.ShortPCP.Machines.FLangComp

/-!
# The coordinate request parser

The construction in `lem:generator`: parse the three natural-number fields
and configure their actual field operations. The internal framed payload is
provided by a paid ordinary preprocessing stage, not a change to the public
raw request. Scratch is below 20; parameters occupy 20,21,22.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary
open NearCubicGates.Adapters.Joins
open NearCubicGates.Adapters.ShortPCP.Machines.FL

def storeNat (dst : Var) : S := .seq pNat (.set dst (.v 5))

theorem storeNat_spec (G : Glob) (s : FS) (dst : Var) (v pos Bd : ℕ)
    (hat : At (s.env 10) pos (RepairRepresentation.natWord v)) (hp : s.env 14 = pos)
    (hend : pos + (RepairRepresentation.natWord v).length ≤ Bd) (hB : BdOk G Bd)
    (hdst : dst ≠ 14) :
    let t := evalS G (storeNat dst) s
    t.env dst = v ∧ t.env 14 = pos + (RepairRepresentation.natWord v).length ∧
      Wr (dst :: pNatW) s t := by
  obtain ⟨hv, hp', hw⟩ := pNat_at G s v pos Bd hat hp hend hB
  have he : evalS G (storeNat dst) s = (evalS G pNat s).setv dst v := by
    simp only [storeNat, evalS_seq, evalS_set, evalE, hv]
  rw [he]
  refine ⟨by simp, ?_, ?_⟩
  · simpa only [FS.setv_env, Function.update_of_ne hdst.symm] using hp'
  · exact (hw.mono (fun _ hx => List.mem_cons_of_mem dst hx)).trans (Wr.setv _ (by simp) _)

def parseFields : S := .seq (storeNat 20) (.seq (storeNat 21) (storeNat 22))

def fieldsW : List Var := [5, 6, 8, 9, 14, 20, 21, 22]

theorem parseFields_spec (G : Glob) (s : FS) (p : CoordReq)
    (hat : At (s.env 10) 0 (coordInput p)) (hp : s.env 14 = 0)
    (hB : BdOk G (coordInput p).length) :
    let t := evalS G parseFields s
    t.env 20 = p.f ∧ t.env 21 = p.irr ∧ t.env 22 = p.m ∧ Wr fieldsW s t := by
  have ha := At.append (At.append hat).1
  have hb := (At.append hat).2
  have hlen : (coordInput p).length = (RepairRepresentation.natWord p.f).length +
      (RepairRepresentation.natWord p.irr).length + (RepairRepresentation.natWord p.m).length := by
    simp only [coordInput, List.length_append]
  obtain ⟨a20, a14, aW⟩ := storeNat_spec G s 20 p.f 0 (coordInput p).length ha.1 hp
    (by omega) hB (by decide)
  generalize ea : evalS G (storeNat 20) s = a at a20 a14 aW
  have a10 : a.env 10 = s.env 10 := aW.env 10 (by decide)
  obtain ⟨b21, b14, bW⟩ := storeNat_spec G a 21 p.irr (RepairRepresentation.natWord p.f).length
    (coordInput p).length (by simpa only [a10, zero_add] using ha.2) (by simpa using a14)
    (by omega) hB (by decide)
  generalize eb : evalS G (storeNat 21) a = b at b21 b14 bW
  have b10 : b.env 10 = s.env 10 := (bW.env 10 (by decide)).trans a10
  obtain ⟨c22, _, cW⟩ := storeNat_spec G b 22 p.m
    ((RepairRepresentation.natWord p.f).length + (RepairRepresentation.natWord p.irr).length)
    (coordInput p).length (by simpa only [b10, List.length_append, zero_add] using hb) b14
    (by omega) hB (by decide)
  generalize ec : evalS G (storeNat 22) b = c at c22 cW
  have he : evalS G parseFields s = c := by simp only [parseFields, evalS_seq, ea, eb, ec]
  rw [he]
  exact ⟨(cW.env 20 (by decide)).trans ((bW.env 20 (by decide)).trans a20),
    (cW.env 21 (by decide)).trans b21, c22,
    ((aW.mono (by decide)).trans (bW.mono (by decide))).trans (cW.mono (by decide))⟩

/-- The packed parser does not move the physical input cursor. -/
theorem parseFields_ip (G : Glob) (s : FS) : (evalS G parseFields s).ip = s.ip :=
  ip_rdFree G parseFields s (by decide)

def coordParse : S := .seq rdFrame (.seq (.set 10 (.v 0)) (.seq (.set 14 (.k 0))
  (.seq parseFields (.field (.v 20) (.v 21)))))

theorem coordParse_spec (G : Glob) (s : FS) (p : CoordReq) (h : CoordOk p) (rest : List Bool)
    (hin : G.inp.drop s.ip = frame (coordInput p) ++ rest)
    (hB : BdOk G (coordInput p).length) (hK : p.f + 2 ≤ G.K) :
    let t := evalS G coordParse s
    t.env 20 = p.f ∧ t.env 21 = p.irr ∧ t.env 22 = p.m ∧ t.fl = p.f ∧ t.fp = p.irr ∧
      t.out = s.out ∧ t.bad = s.bad ∧ t.ip = s.ip + 2 * (coordInput p).length + 1 ∧
      ∀ j : Var, 23 ≤ j.val → t.env j = s.env j := by
  obtain ⟨a0, _, aip, aW⟩ := rdFrame_spec G s (coordInput p) rest hin (by have := hB.1; omega) hB.2
  generalize ea : evalS G rdFrame s = a at a0 aip aW
  let b := (a.setv 10 (bitsValue (coordInput p))).setv 14 0
  obtain ⟨c20, c21, c22, cW⟩ := parseFields_spec G b p
    (by simpa [b] using At.self (coordInput p)) (by simp [b]) hB
  have cip := parseFields_ip G b
  generalize ec : evalS G parseFields b = c at c20 c21 c22 cW cip
  have he : evalS G coordParse s = { c with fl := p.f, fp := p.irr } := by
    simp only [coordParse, evalS_seq, ea, evalS_set, evalE, a0, Nat.zero_min]
    change evalS G (.field (.v 20) (.v 21)) (evalS G parseFields b) = _
    rw [ec]
    simp only [evalS, evalE, c20, c21, coordOk_fieldOk G p h hK, if_true]
  rw [he]
  refine ⟨c20, c21, c22, rfl, rfl, cW.out.trans aW.out, cW.bad.trans aW.bad, ?_, ?_⟩
  · exact cip.trans aip
  · intro j hj
    have hj0 : j ∉ fieldsW := by
      simp only [fieldsW, List.mem_cons, List.not_mem_nil, or_false, not_or]
      norm_num [Fin.ext_iff, NU]
      omega
    have hj10 : j ≠ 10 := by intro e; subst j; norm_num at hj
    have hj14 : j ≠ 14 := by intro e; subst j; norm_num at hj
    have hjrd : j ∉ rdFrameW := by
      intro hm
      simp only [rdFrameW, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl <;> norm_num at hj
    rw [cW.env j hj0]
    simpa only [b, FS.setv_env, Function.update_of_ne hj14, Function.update_of_ne hj10] using aW.env j hjrd

theorem coordParse_wf (d : ℕ) (hd : d ≤ 7) : wfS coordParse d = true := by
  simp [coordParse, parseFields, storeNat, pNat, pNatOnes, pNatBits, bitE, rdFrame, wfS, dE, okE]
  omega

end NearCubicGates.Adapters.Routing.CoordinateMachine
