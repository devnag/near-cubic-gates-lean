import SourceAdapters.Proximity.TrimChooseIndex

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": read, translate and sign one original literal. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins
variable {C : Ctx}

def renderValueTemps : List (Fin VV) := renderReadTemps ++ rankTemps
def renderValue : St VV MM := .seq renderRead (.seq chooseIndex signCode)

theorem render_value {n : ℕ} (q : SignedQuery n) (a : DS VV MM) (hc : Cst a)
    (records tail : List ℕ) (hread : (a.ram sN).drop (a.rc sN) = trimQueryFields q ++ tail)
    (hm : a.ram distinctStore = records) (hlen : a.env distinctCountReg = records.length)
    (hn : a.env arityReg = n) (hrc : a.rc distinctStore ≤ records.length)
    (hW : 2 * (n + records.length) + 1 < 2 ^ C.Wd) :
    Hs C renderValue a (10 * records.length + 25) (fun b =>
      b.env codeReg = 2 * queryIndex records q + q.negated.toNat ∧
      b.out = a.out ∧ b.rc sN = a.rc sN + 3 ∧
      b.rc distinctStore ≤ records.length ∧ (b.ram sN).drop (b.rc sN) = tail ∧
      RenderFrame renderValueTemps a b) := by
  obtain ⟨b, nb, eb, hb, btag, baddr, bsign, bq, bd, btail, bout, bf⟩ :=
    render_read (C := C) q a tail hread
  obtain ⟨d, nd, ed, hd, dval, dout, dq, dd, df⟩ :=
    choose_index (C := C) q b (bf.constants hc (by decide)) records
      (by rw [bf.ram]; exact hm) ((bf.env distinctCountReg (by decide)).trans hlen)
      ((bf.env arityReg (by decide)).trans hn) btag baddr (by omega) (by omega) (by omega)
  have hq := queryIndex_le records q
  have hs : q.negated.toNat ≤ 1 := by cases q.negated <;> decide
  have dsign : d.env signReg = q.negated.toNat :=
    (df.env signReg (by decide)).trans bsign
  have ee := sign_code (C := C) d (queryIndex records q) q.negated.toNat dval dsign (by omega)
  let e := d.set codeReg (2 * queryIndex records q + q.negated.toNat)
  refine ⟨e, nb + (nd + 3 + 1) + 1, Ex.seq eb (Ex.seq ed ee), by omega, ?_⟩
  refine ⟨by simp [e], dout.trans bout, dq.trans bq, dd, ?_, ?_⟩
  · change (d.ram sN).drop (d.rc sN) = tail
    rw [df.ram, dq]
    exact btail
  · exact (bf.weaken (fun _ hx => List.mem_append_left _ hx)).trans
      ((df.weaken (fun _ hx => List.mem_append_right _ hx)).trans
        (RenderFrame.set renderValueTemps d codeReg _ (by simp [renderValueTemps, rankTemps])))

end NearCubicGates.Adapters.Proximity.Trim
