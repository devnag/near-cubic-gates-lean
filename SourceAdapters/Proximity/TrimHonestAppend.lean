import SourceAdapters.Proximity.TrimHonestAppendKeys
import SourceAdapters.Proximity.TrimHonestAppendValues

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": actual construction of one complete auxiliary dictionary
row, including paired labels, shifted values and retained record count. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def appendRow : St VV MM := .seq appendKeys
  (.seq appendValues (.op (.add auxiliaryLength localBound)))

theorem append_row {n q N : ℕ} (V : NonadaptiveVerifier n q)
    (coins : Fin (2 ^ V.randomBits)) (input : BitInput n) (proof : BitInput N)
    (a : DS VV MM) (hc : Cst a) (ready : AuxiliaryReady V input (finiteProofOracle proof) coins.val a)
    (hrow : a.env QueryStep.rowReg = coins.val) (hbound : a.env localBound = blockVariableBound q)
    (hq : a.env QueryStep.boundReg = q)
    (htable : a.ram rowStore = (List.ofFn fun i : Fin (blockVariableBound q) =>
      canonicalBlockAssignment (rowPredicate V coins) (rowAnswers V coins input proof) i.val).map Bool.toNat)
    (hrc : a.rc rowStore ≤ blockVariableBound q) (hwidth : q + blockVariableBound q < 2 ^ C.Wd)
    (hkey : ∀ i < blockVariableBound q, 2 * Nat.pair coins.val i + 1 < 2 ^ C.Wd)
    (hcount : (coins.val + 1) * blockVariableBound q < 2 ^ C.Wd) :
    Hs C appendRow a
      (6 * (blockVariableBound q) ^ 2 + 40 * blockVariableBound q + 11) (fun b =>
        AuxiliaryReady V input (finiteProofOracle proof) (coins.val + 1) b ∧
        b.rc rowStore ≤ blockVariableBound q ∧ AppendFrame appendTemps a b) := by
  obtain ⟨b, nb, eb, hb, bk, bkc, ba, bac, brc, fb⟩ :=
    append_keys coins.val (blockVariableBound q) a hc hrow hbound ready.keys ready.key_cursor
      (by omega) hkey
  have btable := (fb.ram rowStore (by decide) (by decide)).trans htable
  obtain ⟨d, nd, ed, hd, da, dac, dk, dkc, drc, fd⟩ :=
    append_values V coins input proof b (fb.constants hc (by decide)) btable (ba.trans ready.values)
      ((fb.env localBound (by decide)).trans hbound) ((fb.env QueryStep.boundReg (by decide)).trans hq)
      (by rw [brc]; exact hrc) (bac.trans ready.value_cursor) hwidth
  have dlength : d.env auxiliaryLength = coins.val * blockVariableBound q :=
    (fd.env auxiliaryLength (by decide)).trans ((fb.env auxiliaryLength (by decide)).trans ready.length)
  have dbound : d.env localBound = blockVariableBound q :=
    (fd.env localBound (by decide)).trans ((fb.env localBound (by decide)).trans hbound)
  have hsum : coins.val * blockVariableBound q + blockVariableBound q =
      (coins.val + 1) * blockVariableBound q := by ring
  have e3 := Ex.op (OpEx.add (C := C) auxiliaryLength localBound d (by decide)
    (by rw [dlength, dbound, hsum]; exact hcount))
  rw [dlength, dbound, hsum] at e3
  let e := d.set auxiliaryLength ((coins.val + 1) * blockVariableBound q)
  refine ⟨e, nb + (nd + 1 + 1) + 1, Ex.seq eb (Ex.seq ed e3), ?_, ?_⟩
  · calc
      nb + (nd + 1 + 1) + 1 ≤ (20 * blockVariableBound q + 4) +
        (blockVariableBound q * (6 * blockVariableBound q + 20) + 4 + 1 + 1) + 1 := by omega
      _ = _ := by ring
  · refine ⟨⟨dk.trans bk, da, dkc.trans bkc, dac, by simp [e]⟩, drc, ?_⟩
    exact (fb.weaken (fun _ hx => List.mem_cons_of_mem _ (List.mem_append_left _ hx))).trans
      ((fd.weaken (fun _ hx => List.mem_cons_of_mem _ (List.mem_append_right _ hx))).trans
        (AppendFrame.set appendTemps d auxiliaryLength _ (by simp [appendTemps])))

end NearCubicGates.Adapters.Proximity.TrimHonest
