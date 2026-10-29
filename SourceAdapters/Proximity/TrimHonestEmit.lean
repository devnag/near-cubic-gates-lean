import SourceAdapters.Proximity.TrimHonestLookup

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": emit precisely one retained canonical proof bit, raw. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def emitAddress : St VV MM := .seq lookupAddress (CellSending.sendReadBit vZ valueReg false)

theorem emit_address {n q N : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : BitInput N) (a : DS VV MM) (hc : Cst a)
    (ready : Ready C V input proof a) (hwidth : a.env addressReg < 2 ^ C.Wd) :
    Hs C emitAddress a
      (6 * N + 16 * (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length + 32)
      (fun b => b.out = a.out ++
          [canonicalClauseProof V input (finiteProofOracle proof) (a.env addressReg)] ∧
        Ready C V input proof b ∧ LookupFrame addressTemps a b) := by
  obtain ⟨b, cost, e1, hcost, bv, bo, rb, fb⟩ := lookup_address V input proof a hc ready hwidth
  let bit := canonicalClauseProof V input (finiteProofOracle proof) (a.env addressReg)
  have bc := fb.constants hc (by decide)
  have e2 := CellSending.send_read_bit C vZ valueReg (by decide) false b bit bc.z bv (by simp)
  let d := CellSending.sent false b [bit]
  have fd : LookupFrame addressTemps b d :=
    ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
  have rd := rb.frame fd (by decide) (by decide) rb.proof_cursor rb.aux_cursor rb.key_cursor
  refine ⟨d, cost + 2 + 1, Ex.seq e1 e2, by omega, ?_⟩
  exact ⟨by change b.out ++ [bit] = _; rw [bo], rd, fb.trans fd⟩

end NearCubicGates.Adapters.Proximity.TrimHonest
