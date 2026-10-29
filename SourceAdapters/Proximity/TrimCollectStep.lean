import SourceAdapters.Proximity.TrimCollectAction

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": one complete paid collection iteration; the loop index
advances by three numeric fields, independently of their values. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins
variable {C : Ctx}

def bumpThree : St VV MM := .seq (.op (.add c0 v2)) (.op (.inc c0))

theorem bump_three (a : DS VV MM) (hc : Cst a) (hW : a.env c0 + 3 < 2 ^ C.Wd) :
    Ex C bumpThree a (a.set c0 (a.env c0 + 3)) 3 := by
  have e1 := Ex.op (OpEx.add (C := C) c0 v2 a (by decide) (by rw [hc.two]; omega))
  rw [hc.two] at e1
  have e2 := Ex.op (OpEx.inc (C := C) c0 (a.set c0 (a.env c0 + 2))
    (by simp only [DS.set_env_self]; omega))
  have he := Ex.seq e1 e2
  simpa [bumpThree, DS.set, Nat.add_assoc] using he

def collectStep : St VV MM := .seq collectAction bumpThree

def CollectStepPost (a : DS VV MM) (output tail : List ℕ) (b : DS VV MM) : Prop :=
  b.ram proofStore = output ∧ b.rc proofStore = output.length ∧
  b.env proofCountReg = output.length ∧ b.rc sN = a.rc sN + 3 ∧
  b.env c0 = a.env c0 + 3 ∧ (b.ram sN).drop (b.rc sN) = tail ∧ CollectFrame a b

theorem collect_step {n : ℕ} (q : SignedQuery n) (a : DS VV MM) (hc : Cst a)
    (output tail : List ℕ) (hread : (a.ram sN).drop (a.rc sN) = trimQueryFields q ++ tail)
    (hm : a.ram proofStore = output) (hrc : a.rc proofStore = output.length)
    (hn : a.env proofCountReg = output.length) (hW : output.length + 1 < 2 ^ C.Wd)
    (hindex : a.env c0 + 3 < 2 ^ C.Wd) :
    Hs C collectStep a 14 (CollectStepPost a (output ++ queryProofValues q) tail) := by
  obtain ⟨b, nb, eb, hb, bm, brc, bn, bs, bi, bt, bf⟩ :=
    collect_action (C := C) q a hc output tail hread hm hrc hn hW
  have ec := bump_three (C := C) b (bf.cst collectRegisters_valid hc) (by rw [bi]; exact hindex)
  refine ⟨b.set c0 (b.env c0 + 3), nb + 3 + 1, Ex.seq eb ec, by omega, ?_⟩
  refine ⟨bm, brc, ?_, bs, ?_, bt, ?_⟩
  · rw [DS.set_env_ne _ _ (by decide)]
    exact bn
  · simp [bi]
  · exact bf.trans (DistinctRecords.Frame.set collectRegisters sN proofStore b c0 _ (by decide))

end NearCubicGates.Adapters.Proximity.Trim
