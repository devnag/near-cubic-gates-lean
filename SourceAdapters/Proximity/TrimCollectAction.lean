import SourceAdapters.Proximity.TrimCollectKeep

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": one exact signed-query record is read and its proof address
is conditionally appended. The original query store remains unchanged. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins
variable {C : Ctx}

def queryIsProof {n : ℕ} (q : SignedQuery n) : Bool :=
  match q.address with | .inl _ => false | .inr _ => true

def queryAddress {n : ℕ} (q : SignedQuery n) : ℕ :=
  match q.address with | .inl i => i.val | .inr a => a

theorem queryFields_split {n : ℕ} (q : SignedQuery n) :
    trimQueryFields q = [(queryIsProof q).toNat, queryAddress q, q.negated.toNat] := by
  cases h : q.address <;> simp [trimQueryFields, queryIsProof, queryAddress, h]

theorem queryProofValues_split {n : ℕ} (q : SignedQuery n) :
    queryProofValues q = if queryIsProof q then [queryAddress q] else [] := by
  cases h : q.address <;> simp [queryProofValues, queryIsProof, queryAddress, h]

def collectAction : St VV MM := .seq readThree chooseAddress

def ActionPost (a : DS VV MM) (output tail : List ℕ) (b : DS VV MM) : Prop :=
  b.ram proofStore = output ∧ b.rc proofStore = output.length ∧
  b.env proofCountReg = output.length ∧ b.rc sN = a.rc sN + 3 ∧
  b.env c0 = a.env c0 ∧ (b.ram sN).drop (b.rc sN) = tail ∧ CollectFrame a b

theorem collect_action {n : ℕ} (q : SignedQuery n) (a : DS VV MM) (hc : Cst a)
    (output tail : List ℕ) (hread : (a.ram sN).drop (a.rc sN) = trimQueryFields q ++ tail)
    (hm : a.ram proofStore = output) (hrc : a.rc proofStore = output.length)
    (hn : a.env proofCountReg = output.length) (hW : output.length + 1 < 2 ^ C.Wd) :
    Hs C collectAction a 10 (ActionPost a (output ++ queryProofValues q) tail) := by
  rw [queryFields_split] at hread
  obtain ⟨b, nb, eb, hb, btag, bvalue, bcursor, btail, bram, bdest, bvars, bframe⟩ :=
    read_three (C := C) a (queryIsProof q).toNat (queryAddress q) q.negated.toNat tail hread
  obtain ⟨d, nd, ed, hd, dm, drc, dn, dsrc, di, dframe⟩ :=
    choose_address (C := C) b (bframe.cst collectRegisters_valid hc) output (queryAddress q)
      (queryIsProof q) btag (by rw [bram]; exact hm) (by rw [bdest]; exact hrc)
      (by rw [bvars proofCountReg (by decide)]; exact hn) bvalue hW
  refine ⟨d, nb + nd + 1, Ex.seq eb ed, by omega, ?_⟩
  refine ⟨?_, ?_, ?_, dsrc.trans bcursor, ?_, ?_, bframe.trans dframe⟩
  · simpa only [queryProofValues_split] using dm
  · simpa only [queryProofValues_split] using drc
  · simpa only [queryProofValues_split] using dn
  · exact di.trans (bvars c0 (by decide))
  · rw [dframe.ramSource, dsrc]
    exact btail

end NearCubicGates.Adapters.Proximity.Trim
