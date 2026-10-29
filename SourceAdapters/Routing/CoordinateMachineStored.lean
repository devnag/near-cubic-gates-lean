import SourceAdapters.Routing.CoordinateMachineOps
import SourceAdapters.Routing.CoordinateMachineEval

/-!
# Calls to the stored linearized evaluator

The construction in `lem:generator`: each triangular stage evaluates its two stored coefficient vectors at the next basis element.
This program copies the actual packed vector, count and argument into the fixed evaluator's registers and copies its
answer back. All copies and the evaluator call are part of the same counted program.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open NearCubicGates.Adapters.ShortPCP.Machines.FL NearCubicWires.WireExponent3_5
open scoped BigOperators

/-- Evaluate the vector in `src`, with count in 35 and argument in 27, and store the answer in `dst`. -/
def evalStored (src dst : Var) : S :=
  .seq (.set 40 (.v src)) (.seq (.set 41 (.v 35)) (.seq (.set 42 (.v 27))
    (.seq CoordinateMachineEval.program (.set dst (.v 44)))))

theorem evalStored_spec (G : Glob) (s : FS) (src dst : Var) (cs : List ℕ) (n x : ℕ)
    (hcs : ∀ c ∈ cs, c < 2 ^ s.fl) (h20 : s.env 20 = s.fl) (hsrc : s.env src = packW s.fl cs)
    (h35 : s.env 35 = n) (h27 : s.env 27 = x) (hx : x < 2 ^ s.fl)
    (hok : fieldOk G s.fl s.fp = true) (hN : n ≤ G.N) (hcap : n * s.fl ≤ G.cap) :
    let t := evalS G (evalStored src dst) s
    t.env dst < 2 ^ s.fl ∧
      GF.rep s.fp (t.env dst) =
        ∑ r ∈ Finset.range n, GF.rep s.fp (cs.getD r 0) * (GF.rep s.fp x) ^ (2 ^ r) ∧
      Wr [dst, 40, 41, 42, 44, 45, 46] s t ∧ t.ip = s.ip := by
  intro t
  let s1 := ((s.setv 40 (packW s.fl cs)).setv 41 n).setv 42 x
  have hcall := CoordinateMachineEval.program_spec G s1 cs n x
    (by simpa only [s1, FS.setv_fl] using hcs)
    (by simpa [s1] using h20) (by simp [s1]) (by simp [s1]) (by simp [s1])
    (by simpa only [s1, FS.setv_fl] using hx)
    (by simpa only [s1, FS.setv_fl, FS.setv_fp] using hok) hN
    (by simpa only [s1, FS.setv_fl] using hcap)
  let u := evalS G CoordinateMachineEval.program s1
  have ht : t = u.setv dst (u.env 44) := by
    simp only [t, evalStored, evalS_seq, evalS_set, evalE]
    simp only [FS.setv_env, Function.update_of_ne (by decide : (35 : Var) ≠ 40),
      Function.update_of_ne (by decide : (27 : Var) ≠ 41),
      Function.update_of_ne (by decide : (27 : Var) ≠ 40), hsrc, h35, h27]
    rfl
  have hpre : Wr [dst, 40, 41, 42, 44, 45, 46] s s1 :=
    ((Wr.setv s (by simp) _).trans (Wr.setv _ (by simp) _)).trans (Wr.setv _ (by simp) _)
  rw [ht]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [FS.setv_env, Function.update_self, u, s1, FS.setv_fl] using hcall.1
  · simp only [FS.setv_env, Function.update_self]
    exact hcall.2.1
  · exact (hpre.trans (hcall.2.2.2.2.1.mono (by simp_all))).trans (Wr.setv _ (by simp) _)
  · exact hcall.2.2.2.2.2

end NearCubicGates.Adapters.Routing.CoordinateMachine
