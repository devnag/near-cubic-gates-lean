import SourceAdapters.Proximity.RowState

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": fixed-q constructor registers are initialized by
actual constant-writing programs. Their costs depend on q before input size. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicGates.Close.Cells
open SourceRequests (State Script)
open QueryStep (boundReg)

def configure (q : ℕ) : Script :=
  .seq (setK boundReg q) (setK truthLengthReg (2 ^ q))

theorem configure_run (C : Ctx) (q : ℕ) (a : State) (hq : q < 2 ^ C.Wd) (ht : 2 ^ q < 2 ^ C.Wd) :
    Hs C (configure q) a (2 * q + 2 * 2 ^ q + 7) (fun b =>
      b.env boundReg = q ∧ b.env truthLengthReg = 2 ^ q ∧ Same a b ∧
      Fr a b [boundReg, truthLengthReg, vJ]) := by
  have e1 := setK_spec (C := C) boundReg (by decide) q a hq
  obtain ⟨b, cost1, he1, hc1, hbq, hbsh, hbfr⟩ := e1
  have e2 := setK_spec (C := C) truthLengthReg (by decide) (2 ^ q) b ht
  obtain ⟨d, cost2, he2, hc2, hdt, hdsh, hdfr⟩ := e2
  refine ⟨d, cost1 + cost2 + 1, Ex.seq he1 he2, by omega,
    (hdfr boundReg (by decide)).trans hbq, hdt, (Same.of_sh hbsh).trans (Same.of_sh hdsh), ?_⟩
  exact (hbfr.weaken (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp)).trans
    (hdfr.weaken (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp))

end NearCubicGates.Adapters.Proximity.SourceCallee
