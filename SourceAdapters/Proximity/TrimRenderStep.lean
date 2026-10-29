import SourceAdapters.Proximity.TrimRenderQuery

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": one complete serializer iteration with a retained index. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins
variable {C : Ctx}

def renderBump : St VV MM := .seq (.op (.add renderIndex v2)) (.op (.inc renderIndex))

theorem render_bump (a : DS VV MM) (hc : Cst a) (hW : a.env renderIndex + 3 < 2 ^ C.Wd) :
    Ex C renderBump a (a.set renderIndex (a.env renderIndex + 3)) 3 := by
  have e1 := Ex.op (OpEx.add (C := C) renderIndex v2 a (by decide) (by rw [hc.two]; omega))
  rw [hc.two] at e1
  have e2 := Ex.op (OpEx.inc (C := C) renderIndex (a.set renderIndex (a.env renderIndex + 2))
    (by simp only [DS.set_env_self]; omega))
  simpa [renderBump, DS.set, Nat.add_assoc] using Ex.seq e1 e2

def renderStepTemps : List (Fin VV) := renderIndex :: renderQueryTemps
def renderStep : St VV MM := .seq renderQuery renderBump

theorem render_step {n : ℕ} (V : ThreeQueryVerifier n) (q : SignedQuery n)
    (a : DS VV MM) (hc : Cst a) (tail : List ℕ)
    (hread : (a.ram sN).drop (a.rc sN) = trimQueryFields q ++ tail)
    (hm : a.ram distinctStore = trimSortedAddresses ⟨n, V⟩)
    (hlen : a.env distinctCountReg = (trimSortedAddresses ⟨n, V⟩).length)
    (hn : a.env arityReg = n) (hrc : a.rc distinctStore ≤ (trimSortedAddresses ⟨n, V⟩).length)
    (hW : inputSize V + 4 ≤ C.Wd) (hindex : a.env renderIndex + 3 < 2 ^ C.Wd) :
    Hs C renderStep a (100 * (inputSize V + 1) + 4) (fun b =>
      b.out = a.out ++ literalWord V q ∧ b.rc sN = a.rc sN + 3 ∧
      b.rc distinctStore ≤ (trimSortedAddresses ⟨n, V⟩).length ∧
      b.env renderIndex = a.env renderIndex + 3 ∧
      RenderFrame renderStepTemps a b) := by
  obtain ⟨b, nb, eb, hb, bout, bq, bd, _, bf⟩ :=
    render_query (C := C) V q a hc tail hread hm hlen hn hrc hW
  have bi : b.env renderIndex = a.env renderIndex := bf.env renderIndex (by decide)
  have ec := render_bump (C := C) b (bf.constants hc (by decide)) (by rw [bi]; exact hindex)
  refine ⟨b.set renderIndex (b.env renderIndex + 3), nb + 3 + 1, Ex.seq eb ec, by omega, ?_⟩
  refine ⟨bout, bq, bd, by simp [bi], ?_⟩
  exact (bf.weaken (fun _ hx => List.mem_cons_of_mem _ hx)).trans
    (RenderFrame.set renderStepTemps b renderIndex _ (by simp [renderStepTemps]))

end NearCubicGates.Adapters.Proximity.Trim
