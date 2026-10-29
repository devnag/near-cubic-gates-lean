import SourceAdapters.Proximity.TrimHonestAppendData

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": append the exact q-shifted canonical auxiliary values
using the actual finite row table and guarded default-false reads. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def appendValues : St VV MM := ShiftedBits.script rowStore auxiliaryStore
  localBound QueryStep.boundReg localBound localIndex addressReg valueReg

theorem append_values {n q N : ℕ} (V : NonadaptiveVerifier n q)
    (coins : Fin (2 ^ V.randomBits)) (input : BitInput n) (proof : BitInput N)
    (a : DS VV MM) (hc : Cst a)
    (hrow : a.ram rowStore = (List.ofFn fun i : Fin (blockVariableBound q) =>
      canonicalBlockAssignment (rowPredicate V coins) (rowAnswers V coins input proof) i.val).map Bool.toNat)
    (hprevious : a.ram auxiliaryStore = (auxiliaryValues V input (finiteProofOracle proof) coins.val).map Bool.toNat)
    (hbound : a.env localBound = blockVariableBound q) (hq : a.env QueryStep.boundReg = q)
    (hrc : a.rc rowStore ≤ blockVariableBound q)
    (hac : a.rc auxiliaryStore = coins.val * blockVariableBound q)
    (hwidth : q + blockVariableBound q < 2 ^ C.Wd) :
    Hs C appendValues a (blockVariableBound q * (6 * blockVariableBound q + 20) + 4) (fun b =>
      b.ram auxiliaryStore = (auxiliaryValues V input (finiteProofOracle proof) (coins.val + 1)).map Bool.toNat ∧
      b.rc auxiliaryStore = (coins.val + 1) * blockVariableBound q ∧
      b.ram keyStore = a.ram keyStore ∧ b.rc keyStore = a.rc keyStore ∧
      b.rc rowStore ≤ blockVariableBound q ∧ AppendFrame valueTemps a b) := by
  let bits := List.ofFn fun i : Fin (blockVariableBound q) =>
    canonicalBlockAssignment (rowPredicate V coins) (rowAnswers V coins input proof) i.val
  have hb : bits.length = blockVariableBound q := List.length_ofFn
  have run := ShiftedBits.runs C rowStore auxiliaryStore (by decide)
    localBound QueryStep.boundReg localBound localIndex addressReg valueReg
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    a hc bits (auxiliaryValues V input (finiteProofOracle proof) coins.val) hrow hprevious
    (hbound.trans hb.symm) (by rw [hb]; exact hrc)
    (by simpa only [auxiliary_values_length] using hac) (by rw [hb]; omega)
    (by rw [hbound]; omega) (by rw [hq, hbound]; exact hwidth)
  refine run.mono (by rw [hbound, hb]) ?_
  rintro b ⟨bv, ba, br, bm, bc, _, _, _, _, _, bi, bo, bki, bko, bkc, bf⟩
  refine ⟨?_, ?_, bm keyStore (by decide), bc keyStore (by decide) (by decide),
    by simpa only [hb] using br, ?_⟩
  · rw [hq, hbound] at bv
    rw [auxiliary_values_succ, row_values_shifted]
    exact bv
  · rw [auxiliary_values_length, hbound] at ba
    simpa only [Nat.add_mul, Nat.one_mul] using ba
  · exact ⟨fun m _ hma => bm m hma, fun m _ hma hmr => bc m hmr hma,
      bi, bo, bki, bko, bkc, bf⟩

end NearCubicGates.Adapters.Proximity.TrimHonest
