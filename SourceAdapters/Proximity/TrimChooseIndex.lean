import SourceAdapters.Proximity.TrimRankAddress
import SourceAdapters.Proximity.TrimRenderRead

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid input/proof dispatch for the dense literal index.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def queryIndex {n : ℕ} (records : List ℕ) (q : SignedQuery n) : ℕ :=
  match q.address with
  | .inl i => i.val
  | .inr v => n + records.idxOf v

def chooseIndex : St VV MM :=
  .ite (.eq tagReg v1) rankAddress (.op (.copy codeReg addressReg))

theorem queryIndex_le {n : ℕ} (records : List ℕ) (q : SignedQuery n) :
    queryIndex records q ≤ n + records.length := by
  cases h : q.address with
  | inl i => simp only [queryIndex, h]; omega
  | inr v => simp only [queryIndex, h]; exact Nat.add_le_add_left List.idxOf_le_length n

theorem choose_index {n : ℕ} (q : SignedQuery n) (a : DS VV MM) (hc : Cst a)
    (records : List ℕ) (hm : a.ram distinctStore = records)
    (hlen : a.env distinctCountReg = records.length) (hn : a.env arityReg = n)
    (htag : a.env tagReg = (queryIsProof q).toNat)
    (haddr : a.env addressReg = queryAddress q)
    (hrc : a.rc distinctStore ≤ records.length)
    (hwidth : records.length < 2 ^ C.Wd) (hsum : n + records.length < 2 ^ C.Wd) :
    Hs C chooseIndex a (10 * records.length + 13) (fun b =>
      b.env codeReg = queryIndex records q ∧ b.out = a.out ∧ b.rc sN = a.rc sN ∧
      b.rc distinctStore ≤ records.length ∧ RenderFrame rankTemps a b) := by
  cases h : q.address with
  | inl i =>
    have ht : a.env tagReg = 0 := by simpa [queryIsProof, h] using htag
    have ha : a.env addressReg = i.val := by simpa [queryAddress, h] using haddr
    refine Hs.mono (Hs.iteF (c := Cnd.eq tagReg v1) (show tagReg ≠ v1 by decide)
      (by simp [Cnd.eval, ht, hc.one]) (hs_copy C codeReg addressReg a (by decide)))
      (by omega) ?_
    rintro b rfl
    exact ⟨by simp [queryIndex, h, ha], rfl, rfl, hrc,
      RenderFrame.set rankTemps a codeReg _ (by simp [rankTemps])⟩
  | inr v =>
    have ht : a.env tagReg = 1 := by simpa [queryIsProof, h] using htag
    have ha : a.env addressReg = v := by simpa [queryAddress, h] using haddr
    refine Hs.mono (Hs.iteT (c := Cnd.eq tagReg v1) (show tagReg ≠ v1 by decide)
      (by simp [Cnd.eval, ht, hc.one]) (rank_address a hc records n hm hlen hn hwidth hsum))
      (by omega) ?_
    rintro b ⟨hb, ho, hq, hd, hf⟩
    exact ⟨by simpa [queryIndex, h, ha] using hb, ho, hq, hd.le, hf⟩

end NearCubicGates.Adapters.Proximity.Trim
