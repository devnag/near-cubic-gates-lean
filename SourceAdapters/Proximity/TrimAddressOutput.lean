import SourceAdapters.Proximity.TrimPrepare
import SourceAdapters.Proximity.LegacyOutput
import SourceAdapters.Code.RecordPrinting

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the second trimming output is its sorted distinct address
schedule, with a paid natural-word count and every address bit printed. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
variable {C : Ctx}

def addressOutput : St VV MM := .seq (LegacyOutput.fieldFrom distinctCountReg)
  (RecordPrinting.script distinctStore distinctCountReg)

theorem address_output (a : DS VV MM) (hc : Cst a) (records : List ℕ) (Λ : ℕ)
    (hm : a.ram distinctStore = records) (hlen : a.env distinctCountReg = records.length)
    (hcursor : a.rc distinctStore ≤ records.length) (hwidth : records.length < 2 ^ C.Wd)
    (hW : 2 ≤ C.Wd) (hΛ : Λ + 2 < 2 ^ C.Wd)
    (hcount : natBitLength records.length ≤ Λ)
    (hfit : ∀ value ∈ records, natBitLength value ≤ Λ) :
    Hs C addressOutput a ((records.length + 1) * (40 * Λ + 50) + 10)
      (fun b => b.out = a.out ++ (natWord records.length ++ records.flatMap natWord)) := by
  obtain ⟨b, nb, eb, hb, bp⟩ := LegacyOutput.field_from C distinctCountReg (by decide) a hc hW
    (by rw [hlen]; omega)
  have br := bp.rest_eq
  simp only [LegacyOutput.rest, Prod.mk.injEq] at br
  obtain ⟨d, nd, ed, hd, dp⟩ := RecordPrinting.runs C distinctStore distinctCountReg (by decide)
    b (bp.constants hc) records Λ (by rw [br.2.1]; exact hm)
    ((bp.vars distinctCountReg (by decide)).trans hlen) hwidth hW hΛ hfit
  refine ⟨d, nb + nd + 1, Ex.seq eb ed, ?_, ?_⟩
  · rw [hlen] at hb
    rw [br.2.2.1] at hd
    nlinarith
  · change d.out = a.out ++ (natWord records.length ++ records.flatMap natWord)
    rw [dp.1, bp.out_eq, hlen, List.append_assoc]

end NearCubicGates.Adapters.Proximity.Trim
