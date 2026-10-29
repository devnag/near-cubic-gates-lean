import SourceAdapters.Proximity.TrimHonestAppendData

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": append the actual paired numeric labels of one row. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
variable {C : Ctx}

def appendKeys : St VV MM := PairKeys.script pairRegisters addressReg localBound keyStore

theorem append_keys (rows B : ℕ) (a : DS VV MM) (hc : Cst a)
    (hrow : a.env QueryStep.rowReg = rows) (hbound : a.env localBound = B)
    (hm : a.ram keyStore = auxKeys rows B) (hrc : a.rc keyStore = rows * B)
    (hB : B < 2 ^ C.Wd) (hkey : ∀ i < B, 2 * Nat.pair rows i + 1 < 2 ^ C.Wd) :
    Hs C appendKeys a (20 * B + 4) (fun b =>
      b.ram keyStore = auxKeys (rows + 1) B ∧ b.rc keyStore = (rows + 1) * B ∧
      b.ram auxiliaryStore = a.ram auxiliaryStore ∧ b.rc auxiliaryStore = a.rc auxiliaryStore ∧
      b.rc rowStore = a.rc rowStore ∧ AppendFrame keyTemps a b) := by
  have hr : a.env (pairRegisters 0) = rows := hrow
  have run := PairKeys.runs C pairRegisters addressReg localBound keyStore
    (by decide) (by decide) (by decide) a hc (auxKeys rows B) hm
    (by simpa only [auxKeys_length] using hrc) (by rw [hbound]; exact hB)
    (fun i hi => by rw [hr]; exact hkey i (by simpa only [hbound] using hi))
  refine run.mono (by rw [hbound]) ?_
  rintro b ⟨bk, br, _, _, _, _, bi, bo, bki, bko, bkc, bother, bf⟩
  refine ⟨?_, ?_, (bother auxiliaryStore (by decide)).1,
    (bother auxiliaryStore (by decide)).2, (bother rowStore (by decide)).2, ?_⟩
  · rw [auxKeys_succ]
    simpa only [hr, hbound, PairKeys.keys, rowKeys] using bk
  · rw [auxKeys_length, hbound] at br
    simpa only [Nat.add_mul, Nat.one_mul] using br
  · exact ⟨fun m hmk _ => (bother m hmk).1, fun m hmk _ _ => (bother m hmk).2,
      bi, bo, bki, bko, bkc, bf⟩

end NearCubicGates.Adapters.Proximity.TrimHonest
