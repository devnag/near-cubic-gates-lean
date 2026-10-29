import SourceAdapters.Proximity.TrimRenderWords

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": exact verifier output, including both raw headers and all
original-order literals. Every rank scan and output bit is paid. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins
variable {C : Ctx}

def verifierOutput : St VV MM := .seq
  (.seq (SourcePrinting.fieldFrom distinctCountReg) (SourcePrinting.fieldFrom randomReg)) renderWords

theorem verifier_prepared {n : ℕ} (V : ThreeQueryVerifier n) (a b : DS VV MM)
    (bp : Prepared a b V) (hW : inputSize V + 4 ≤ C.Wd) :
    Hs C verifierOutput b (1000 * (inputSize V + 1) ^ 2)
      (fun d => d.out = b.out ++ (trimVerifier V).word) := by
  have hw4 : 4 ≤ 2 ^ C.Wd := (by decide : 4 ≤ 2 ^ 2).trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨d, nd, ed, hd, dp⟩ := SourcePrinting.two_fields C distinctCountReg randomReg
    (by decide) (by decide) b bp.constants hw4
  have dr : RenderFrame SourcePrinting.scratch b d := printed_frame dp
  have hlen : (trimSortedAddresses ⟨n, V⟩).length = (usedProofAddresses V).card := by
    simp [trimSortedAddresses]
  have hf := fields_count_le V
  have hq : (queries V).length ≤ inputSize V := by
    rw [fields, flatFields_length] at hf
    omega
  have hfit : (fields V).length < 2 ^ C.Wd :=
    lt_of_lt_of_le (by omega : (fields V).length < C.Wd) (Nat.lt_two_pow_self).le
  obtain ⟨z, nz, ez, hz, zout⟩ := render_words (C := C) V (queries V) d (dp.constants bp.constants)
    (by rw [dr.ram]; exact bp.queryRAM)
    ((dp.vars fieldsReg (by decide)).trans bp.fieldsCount)
    (by rw [dr.ram]; exact bp.distinctRAM)
    (((dp.vars distinctCountReg (by decide)).trans bp.distinctCount).trans hlen.symm)
    ((dp.vars arityReg (by decide)).trans bp.arity)
    (by rw [printed_cursor dp distinctStore, bp.distinctCursor, hlen]) hW hfit
  have hc : (usedProofAddresses V).card ≤ inputSize V := by
    simpa only [hlen] using (schedule_bounds V).1
  have hcb : (usedProofAddresses V).card.bits.length ≤ inputSize V := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans hc
  have hrb : V.randomBits.bits.length ≤ inputSize V := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (randomness_le V).le
  have hcur : d.rc sN = (fields V).length := (printed_cursor dp sN).trans bp.queryCursor
  rw [bp.distinctCount, bp.randomness] at hd
  rw [hcur] at hz
  have hmul := Nat.mul_le_mul_left (100 * (inputSize V + 1) + 6) hq
  refine ⟨z, nd + nz + 1, Ex.seq ed ez, ?_, ?_⟩
  · nlinarith only [hd, hz, hmul, hf, hcb, hrb]
  · change z.out = b.out ++ (trimVerifier V).word
    rw [zout, dp.out_eq, bp.distinctCount, bp.randomness, trimmedWord_eq]
    simp only [List.append_assoc]

end NearCubicGates.Adapters.Proximity.Trim
