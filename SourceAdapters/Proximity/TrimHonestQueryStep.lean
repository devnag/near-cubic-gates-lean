import SourceAdapters.Proximity.TrimHonestQueryRead

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": read, evaluate and store one source-query answer, retaining
the exact remaining row and overwriting any old answer at this position. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def answerTemps : List (Fin VV) := queryReadTemps ++ lookupTemps
def answerStep : St VV MM := .seq readPair (.seq queryLookup (.op (.wrM answerStore valueReg)))

theorem answer_step {n N : ℕ} (input : BitInput n) (proof : BitInput N)
    (p : Bool × ℕ) (a : DS VV MM) (hc : Cst a) (ready : OracleReady C input proof a)
    (queryTail previous oldTail : List ℕ)
    (hread : (a.ram queryStore).drop (a.rc queryStore) = pairFields p ++ queryTail)
    (hanswer : a.ram answerStore = previous ++ oldTail) (hcursor : a.rc answerStore = previous.length) :
    Hs C answerStep a (6 * (n + N) + 17) (fun b =>
      b.ram answerStore = previous ++ (answerValue input proof p).toNat :: oldTail.drop 1 ∧
      b.rc answerStore = previous.length + 1 ∧ b.rc queryStore = a.rc queryStore + 2 ∧
      OracleReady C input proof b ∧ QueryFrame answerTemps a b) := by
  obtain ⟨b, nb, eb, hb, btag, baddr, bram, bquery, banswer, rb, fb⟩ :=
    read_pair input proof p a ready queryTail hread
  obtain ⟨d, nd, ed, hd, dval, dout, rd, dc, fd⟩ :=
    query_lookup input proof p b (fb.constants hc (by decide)) rb btag baddr
  have dm : d.ram answerStore = previous ++ oldTail := by rw [fd.ram, bram, hanswer]
  have da : d.rc answerStore = previous.length :=
    (dc answerStore (by decide) (by decide)).trans (banswer.trans hcursor)
  have eq := Ex.op (OpEx.wrM (C := C) answerStore valueReg d (by rw [dm, da]; simp))
  rw [dval] at eq
  let e := d.put answerStore (answerValue input proof p).toNat
  refine ⟨e, nb + (nd + 1 + 1) + 1, Ex.seq eb (Ex.seq ed eq), by omega, ?_⟩
  refine ⟨?_, ?_, ?_, rd.put_answer _, ?_⟩
  · change putAt (d.ram answerStore) (d.rc answerStore) _ = _
    rw [dm, da, putAt_split]
  · change d.rc answerStore + 1 = _
    rw [da]
  · change (Function.update d.rc answerStore (d.rc answerStore + 1)) queryStore = _
    rw [Function.update_of_ne (by decide : queryStore ≠ answerStore)]
    exact (dc queryStore (by decide) (by decide)).trans bquery
  · exact (fb.weaken (fun _ hx => List.mem_append_left _ hx)).trans
      (((QueryFrame.of_lookup fd dout dc).weaken (fun _ hx => List.mem_append_right _ hx)).trans
        (QueryFrame.put answerTemps d _))

end NearCubicGates.Adapters.Proximity.TrimHonest
