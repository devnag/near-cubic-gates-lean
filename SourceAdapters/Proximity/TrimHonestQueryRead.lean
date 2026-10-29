import SourceAdapters.Proximity.TrimHonestQueryMemory

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": read the two actual words of a stored padded query. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def readPair : St VV MM := .seq (.op (.rdM queryStore queryTagReg)) (.op (.rdM queryStore addressReg))

theorem read_pair {n N : ℕ} (input : BitInput n) (proof : BitInput N)
    (p : Bool × ℕ) (a : DS VV MM) (ready : OracleReady C input proof a) (tail : List ℕ)
    (hread : (a.ram queryStore).drop (a.rc queryStore) = pairFields p ++ tail) :
    Hs C readPair a 3 (fun b =>
      b.env queryTagReg = p.1.toNat ∧ b.env addressReg = p.2 ∧
      b.ram = a.ram ∧ b.rc queryStore = a.rc queryStore + 2 ∧
      b.rc answerStore = a.rc answerStore ∧ OracleReady C input proof b ∧
      QueryFrame queryReadTemps a b) := by
  obtain ⟨e1, h1⟩ := read_query_head (C := C) a queryTagReg p.1.toNat (p.2 :: tail) hread
  let b := afterQueryRead a queryTagReg p.1.toNat
  obtain ⟨e2, _⟩ := read_query_head (C := C) b addressReg p.2 tail h1
  let d := afterQueryRead b addressReg p.2
  have rb : OracleReady C input proof b :=
    (ready.set queryTagReg _ (by decide) (by decide)).advance_query
  have rd : OracleReady C input proof d :=
    (rb.set addressReg _ (by decide) (by decide)).advance_query
  refine ⟨d, 3, Ex.seq e1 e2, le_rfl, ?_⟩
  refine ⟨?_, ?_, rfl, ?_, ?_, rd,
    (after_query_frame a queryTagReg _ (by decide)).trans
      (after_query_frame b addressReg _ (by decide))⟩
  · simp [d, b, afterQueryRead, DS.adv, DS.set, queryTagReg, addressReg]
  · simp [d, afterQueryRead, DS.adv]
  · simp [d, b, afterQueryRead, DS.adv, Nat.add_assoc]
  · simp [d, b, afterQueryRead, DS.adv, queryStore, answerStore]

end NearCubicGates.Adapters.Proximity.TrimHonest
