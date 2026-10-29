import SourceAdapters.Proximity.TrimLiteralArithmetic

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": actual sorted-address rank lookup and input-arity offset.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
variable {C : Ctx}

def rankTemps : List (Fin VV) := [c0, vJ, rankReg, codeReg]
def rankAddress : St VV MM :=
  .seq (RecordLookup.script distinctStore addressReg distinctCountReg rankReg) addRank

theorem rank_address (a : DS VV MM) (hc : Cst a) (records : List ℕ) (n : ℕ)
    (hm : a.ram distinctStore = records) (hlen : a.env distinctCountReg = records.length)
    (hn : a.env arityReg = n) (hwidth : records.length < 2 ^ C.Wd)
    (hsum : n + records.length < 2 ^ C.Wd) :
    Hs C rankAddress a (a.rc distinctStore + 9 * records.length + 12) (fun b =>
      b.env codeReg = n + records.idxOf (a.env addressReg) ∧ b.out = a.out ∧
      b.rc sN = a.rc sN ∧ b.rc distinctStore = records.length ∧ RenderFrame rankTemps a b) := by
  obtain ⟨b, nb, eb, hb, bval, _, _, _, bip, bout, bram, brc, bother, bkin, bkout, bkc, bvars⟩ :=
    RecordLookup.runs C distinctStore addressReg distinctCountReg rankReg
      (by decide) (by decide) (by decide) (by decide) (by decide) a hc records hm hlen hwidth
  have hidx : records.idxOf (a.env addressReg) ≤ records.length := List.idxOf_le_length
  have ec := add_rank (C := C) b n (records.idxOf (a.env addressReg))
    ((bvars arityReg (by decide)).trans hn) bval (by omega)
  have bf : RenderFrame rankTemps a b :=
    ⟨bram, fun m _ hd => bother m hd, bip, bkin, bkout, bkc, bvars.weaken (by simp [rankTemps])⟩
  refine ⟨b.set codeReg (n + records.idxOf (a.env addressReg)), nb + 3 + 1, Ex.seq eb ec, by omega, ?_⟩
  refine ⟨by simp, bout, bother sN (by decide), brc, ?_⟩
  exact bf.trans (RenderFrame.set rankTemps b codeReg _ (by simp [rankTemps]))

end NearCubicGates.Adapters.Proximity.Trim
