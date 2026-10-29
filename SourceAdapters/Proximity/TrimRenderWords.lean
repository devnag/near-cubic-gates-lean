import SourceAdapters.Proximity.TrimRenderSetup

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": complete original-order literal serialization, including
rewind and setup charges. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins
variable {C : Ctx}

def renderWords : St VV MM := .seq renderSetup renderLoop

theorem render_words {n : ℕ} (V : ThreeQueryVerifier n) (qs : List (SignedQuery n))
    (a : DS VV MM) (hc : Cst a) (hsource : a.ram sN = qs.flatMap trimQueryFields)
    (hN : a.env fieldsReg = (qs.flatMap trimQueryFields).length)
    (hm : a.ram distinctStore = trimSortedAddresses ⟨n, V⟩)
    (hn : a.env distinctCountReg = (trimSortedAddresses ⟨n, V⟩).length)
    (harity : a.env arityReg = n) (hrc : a.rc distinctStore ≤ (trimSortedAddresses ⟨n, V⟩).length)
    (hW : inputSize V + 4 ≤ C.Wd) (hfit : (qs.flatMap trimQueryFields).length < 2 ^ C.Wd) :
    Hs C renderWords a (a.rc sN + (100 * (inputSize V + 1) + 6) * qs.length + 6)
      (fun b => b.out = a.out ++ qs.flatMap (literalWord V)) := by
  let b := renderInitial a
  have hf : RenderFrame renderStepTemps a b := render_initial_frame a
  have hbs : b.ram sN = [] ++ qs.flatMap trimQueryFields := by
    simpa [b, renderInitial, DS.rew] using hsource
  have hbc : b.rc sN = ([] : List ℕ).length := by simp [b, renderInitial, DS.rew]
  have hbi : b.env renderIndex = ([] : List ℕ).length := by simp [b, renderInitial]
  have hbl : b.env fieldsReg = ([] : List ℕ).length + 3 * qs.length := by
    rw [hf.env fieldsReg (by decide), hN, flatFields_length]
    simp
  have hbd : b.rc distinctStore ≤ (trimSortedAddresses ⟨n, V⟩).length := by
    simpa [b, renderInitial, DS.rew, distinctStore, sN] using hrc
  obtain ⟨d, nd, ed, hd, dout, _⟩ :=
    render_loop (C := C) V qs b [] (hf.constants hc (by decide)) hbs hbc hbi hbl
      (by rw [hf.ram]; exact hm) ((hf.env distinctCountReg (by decide)).trans hn)
      ((hf.env arityReg (by decide)).trans harity) hbd hW
      (by simpa only [List.length_nil, Nat.zero_add, flatFields_length] using hfit)
  exact ⟨d, a.rc sN + 3 + nd + 1, Ex.seq (render_setup a) ed, by omega, dout⟩

end NearCubicGates.Adapters.Proximity.Trim
