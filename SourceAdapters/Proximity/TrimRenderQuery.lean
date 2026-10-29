import SourceAdapters.Proximity.TrimRenderValue
import SourceAdapters.Proximity.TrimRenderBounds
import SourceAdapters.Proximity.TrimPrintedFrame

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": an actual paid query-to-literal transducer, with exact
raw verifier framing and preservation of every remaining query. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins
variable {C : Ctx}

def renderQueryTemps : List (Fin VV) := renderValueTemps ++ SourcePrinting.scratch
def renderQuery : St VV MM := .seq renderValue (SourcePrinting.fieldFrom codeReg)

theorem render_query {n : ℕ} (V : ThreeQueryVerifier n) (q : SignedQuery n)
    (a : DS VV MM) (hc : Cst a) (tail : List ℕ)
    (hread : (a.ram sN).drop (a.rc sN) = trimQueryFields q ++ tail)
    (hm : a.ram distinctStore = trimSortedAddresses ⟨n, V⟩)
    (hlen : a.env distinctCountReg = (trimSortedAddresses ⟨n, V⟩).length)
    (hn : a.env arityReg = n) (hrc : a.rc distinctStore ≤ (trimSortedAddresses ⟨n, V⟩).length)
    (hW : inputSize V + 4 ≤ C.Wd) :
    Hs C renderQuery a (100 * (inputSize V + 1)) (fun b =>
      b.out = a.out ++ literalWord V q ∧ b.rc sN = a.rc sN + 3 ∧
      b.rc distinctStore ≤ (trimSortedAddresses ⟨n, V⟩).length ∧
      (b.ram sN).drop (b.rc sN) = tail ∧ RenderFrame renderQueryTemps a b) := by
  have hcap : 2 * (n + (trimSortedAddresses ⟨n, V⟩).length) + 1 < 2 ^ C.Wd :=
    (literal_cap V).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨b, nb, eb, hb, bval, bout, bq, bd, btail, bf⟩ :=
    render_value (C := C) q a hc (trimSortedAddresses ⟨n, V⟩) tail hread hm hlen hn hrc hcap
  have hv : b.env codeReg = literalValue V q := by simpa [literalValue_eq_index] using bval
  have hw4 : 4 ≤ 2 ^ C.Wd := (by decide : 4 ≤ 2 ^ 2).trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨d, nd, ed, hd, dp⟩ := SourcePrinting.field_from C codeReg (by decide) b
    (bf.constants hc (by decide)) hw4
  have dn := (schedule_bounds V).1
  have db := literal_bits_le V q
  rw [hv] at hd
  refine ⟨d, nb + nd + 1, Ex.seq eb ed, by omega, ?_⟩
  refine ⟨?_, (printed_cursor dp sN).trans bq, ?_, ?_, ?_⟩
  · rw [dp.out_eq, bout, hv]
    rfl
  · rw [printed_cursor dp distinctStore]
    exact bd
  · rw [(printed_frame dp).ram, printed_cursor dp sN]
    exact btail
  · exact (bf.weaken (fun _ hx => List.mem_append_left _ hx)).trans
      ((printed_frame dp).weaken (fun _ hx => List.mem_append_right _ hx))

end NearCubicGates.Adapters.Proximity.Trim
