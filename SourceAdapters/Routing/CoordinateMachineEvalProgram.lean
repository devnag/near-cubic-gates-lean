import SourceAdapters.ShortPCP.Machines.FLangPack
import SourceAdapters.ShortPCP.Machines.FLangComp

/-!
The construction in `lem:generator`: evaluate the packed coefficients
of a linearized polynomial with one product, sum, and squaring per coefficient.
The program reads width20/list40/count41/point42, writes result44, and uses45/46.
-/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachineEval

open ShortPCP.Machines.FL

/-- Coefficient at index45 of packed list40, with word width20. -/
def coefficient : E :=
  .md (.shr (.v 40) (.mul (.v 45) (.v 20))) (.shl (.k 1) (.v 20))

/-- Add the next term, then square the running power. -/
def step : S :=
  .seq (.set 44 (.fadd (.v 44) (.fmul coefficient (.v 46))))
    (.set 46 (.fmul (.v 46) (.v 46)))

/-- Evaluate the first count41 coefficients at point42. -/
def program : S :=
  .seq (.set 44 (.k 0)) (.seq (.set 46 (.v 42)) (.loop 45 (.v 41) step))

theorem coefficient_eval (G : Glob) (s : FS) (cs : List ℕ) (j : ℕ)
    (hcs : ∀ c ∈ cs, c < 2 ^ s.fl)
    (h20 : s.env 20 = s.fl) (h40 : s.env 40 = packW s.fl cs) (h45 : s.env 45 = j)
    (hok : fieldOk G s.fl s.fp = true) (hj : j * s.fl ≤ G.cap) :
    evalE G s coefficient = cs.getD j 0 := by
  have hf := tf_le hok
  have hp : 1 ≤ 2 ^ s.fl := Nat.one_le_two_pow
  have h1 : min 1 G.cap = 1 := min_eq_left (by omega)
  have hpow : min (2 ^ s.fl) G.cap = 2 ^ s.fl := min_eq_left (by omega)
  simp only [coefficient, evalE, h20, h40, h45, min_eq_left hj, h1, one_mul, hpow]
  exact packW_get s.fl cs hcs j

/-- Exact expression-count cost of the actual program. -/
theorem cost_eq (G : Glob) : costS G program = 38 + G.N * (7 * opc G + 57) := by
  simp only [program, step, coefficient, costS, costE]
  ring

theorem cost_le (G : Glob) :
    costS G program ≤ 6000 * (G.K + 1) ^ 3 * (G.N + 1) := by
  rw [cost_eq]
  have hp : 1 ≤ (G.K + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hb : 7 * opc G + 57 ≤ 6000 * (G.K + 1) ^ 3 := by
    unfold opc
    omega
  have hm := Nat.mul_le_mul_left G.N hb
  nlinarith

theorem wellFormed : wfS program 0 = true := by decide

theorem wellFormed_depth (d : ℕ) (hd : d ≤ 7) : wfS program d = true := by
  simp [program, step, coefficient, wfS, dE, show d < 8 by omega]

/-- The actual Cells implementation, with the compiler's explicit machine
context and state relation. No runtime or algorithm-existence premise. -/
theorem compiled {C : NearCubicGates.Close.Cells.Ctx} {G : Glob} (hg : GOk C G) :
    SOk C G program :=
  seq_ok (set_ok hg _ _) (seq_ok (set_ok hg _ _)
    (loop_ok hg _ _ (seq_ok (set_ok hg _ _) (set_ok hg _ _))))

end NearCubicGates.Adapters.Routing.CoordinateMachineEval
