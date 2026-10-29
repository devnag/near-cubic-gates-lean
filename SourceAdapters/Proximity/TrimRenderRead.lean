import SourceAdapters.Proximity.TrimRenderFrame

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": read an original query while retaining its sign in a
register disjoint from lookup scratch. No query occurrence is discarded. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins
variable {C : Ctx}

def renderReadTemps : List (Fin VV) := [tagReg, addressReg, signReg]
def renderRead : St VV MM := .seq (.op (.rdM sN tagReg))
  (.seq (.op (.rdM sN addressReg)) (.op (.rdM sN signReg)))

def RenderReadPost {n : ℕ} (a : DS VV MM) (q : SignedQuery n) (tail : List ℕ)
    (b : DS VV MM) : Prop :=
  b.env tagReg = (queryIsProof q).toNat ∧ b.env addressReg = queryAddress q ∧
  b.env signReg = q.negated.toNat ∧ b.rc sN = a.rc sN + 3 ∧
  b.rc distinctStore = a.rc distinctStore ∧ (b.ram sN).drop (b.rc sN) = tail ∧
  b.out = a.out ∧ RenderFrame renderReadTemps a b

theorem render_read {n : ℕ} (q : SignedQuery n) (a : DS VV MM) (tail : List ℕ)
    (h : (a.ram sN).drop (a.rc sN) = trimQueryFields q ++ tail) :
    Hs C renderRead a 5 (RenderReadPost a q tail) := by
  rw [queryFields_split] at h
  obtain ⟨e1, h1⟩ := read_head (C := C) a tagReg (queryIsProof q).toNat
    (queryAddress q :: q.negated.toNat :: tail) h
  let b := afterRead a tagReg (queryIsProof q).toNat
  obtain ⟨e2, h2⟩ := read_head (C := C) b addressReg (queryAddress q) (q.negated.toNat :: tail) h1
  let d := afterRead b addressReg (queryAddress q)
  obtain ⟨e3, h3⟩ := read_head (C := C) d signReg q.negated.toNat tail h2
  refine ⟨afterRead d signReg q.negated.toNat, 5, Ex.seq e1 (Ex.seq e2 e3), le_rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, h3, rfl, ?_⟩
  · vsimp [afterRead, d, b, DS.adv]
  · vsimp [afterRead, d, DS.adv]
  · simp [afterRead, DS.adv]
  · simp [afterRead, d, b, DS.adv]
  · vsimp [afterRead, d, b, DS.adv]
  · exact (RenderFrame.afterRead renderReadTemps a tagReg _ (by decide)).trans
      ((RenderFrame.afterRead renderReadTemps b addressReg _ (by decide)).trans
        (RenderFrame.afterRead renderReadTemps d signReg _ (by decide)))

end NearCubicGates.Adapters.Proximity.Trim
