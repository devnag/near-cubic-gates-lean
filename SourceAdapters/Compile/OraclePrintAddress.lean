import SourceAdapters.Compile.OraclePrintTemplate

/-!
# The query-address family as a template

proof of `thm:short-pcp-ours`, Step 4: "replace each read of a proof bit by an oracle gate on the ℓ address bits"; the address bits are
`queryAddressExpression width bit` read through `queryInputIndex` (the query tape's cells and its one-hot
length in the clock wires). `postR_queryAddress`: its postfix tokens are those of ONE template `addrT` read at run
time (`env = [width, cap, ell, |frame data|, bit]`), so a single cell program prints every address bit for every
width. Also `Tm.eval_append` (terms read only their own levels).
-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.FinitePredicateCircuit NearCubicWires.RepairSource
open NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicGates.Adapters.Compile (cellIndex windowBits anyExpression)

set_option autoImplicit false

/-- Terms reading only levels below `k`. -/
def Tm.lvOk (k : ℕ) : Tm → Prop
  | .v j => j < k
  | .k _ => True
  | .add a b | .sub a b | .mul a b | .div a b | .md a b | .lt a b | .eq a b => a.lvOk k ∧ b.lvOk k
  | .ite c a b => c.lvOk k ∧ a.lvOk k ∧ b.lvOk k

theorem Tm.eval_append (env e : List ℕ) : ∀ t : Tm, t.lvOk env.length → t.eval (env ++ e) = t.eval env
  | .v j, h => by simp only [Tm.eval]; exact List.getD_append _ _ _ _ h
  | .k _, _ => rfl
  | .add a b, h | .sub a b, h | .mul a b, h | .div a b, h | .md a b, h | .lt a b, h | .eq a b, h => by
      simp only [Tm.eval, Tm.eval_append env e a h.1, Tm.eval_append env e b h.2]
  | .ite c a b, h => by
      simp only [Tm.eval, Tm.eval_append env e c h.1, Tm.eval_append env e a h.2.1, Tm.eval_append env e b h.2.2]

theorem Tm.lvOk_mono {k k' : ℕ} (hk : k ≤ k') : ∀ t : Tm, t.lvOk k → t.lvOk k'
  | .v j, h => by simp only [Tm.lvOk] at *; omega
  | .k _, _ => trivial
  | .add a b, h | .sub a b, h | .mul a b, h | .div a b, h | .md a b, h | .lt a b, h | .eq a b, h =>
      ⟨Tm.lvOk_mono hk a h.1, Tm.lvOk_mono hk b h.2⟩
  | .ite c a b, h => ⟨Tm.lvOk_mono hk c h.1, Tm.lvOk_mono hk a h.2.1, Tm.lvOk_mono hk b h.2.2⟩

/-- The tokens of a frame-prefix test: the `c` cell reads, the final allocation-and-terminator test, `c` ANDs. -/
theorem postR_prefix {w : ℕ} (ρ : Fin w → ℕ) (read alloc : ℕ → BoolExpr w) (c : ℕ) : ∀ pos : ℕ,
    postR ρ (prefixExpression read alloc c pos) =
      (List.range c).flatMap (fun k => postR ρ (read (pos + 2 * k))) ++
        (postR ρ (alloc (pos + 2 * c)) ++ (postR ρ (read (pos + 2 * c)) ++ [.neg]) ++ [.conj]) ++
        List.replicate c .conj := by
  induction c with
  | zero => intro pos; simp [prefixExpression, postR]
  | succ c ih =>
      intro pos
      have e : (fun k => postR ρ (read (pos + 2 * (k + 1)))) = (fun k => postR ρ (read (pos + 2 + 2 * k))) :=
        funext fun k => by rw [show pos + 2 * (k + 1) = pos + 2 + 2 * k by ring]
      rw [prefixExpression, postR, ih (pos + 2), List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      simp only [e, show pos + 2 * (c + 1) = pos + 2 + 2 * c by ring, Nat.mul_zero,
        Nat.add_zero, List.replicate_succ', List.append_assoc]

/-- `s + (t·W + (x + W·q))`: the clock wire of query cell `x` (`W` at level `0`). -/
def cellT (t s q : ℕ) (x : Tm) : Tm := .add (.k s) (.add (.mul (.k t) (.v 0)) (.add x (.mul (.v 0) (.k q))))

/-- `(s + (t·W + t·W)) + (len + (W + 1)·q)`: the clock wire of query length `len`. -/
def lenT (t s q : ℕ) (len : Tm) : Tm :=
  .add (.add (.k s) (.add (.mul (.k t) (.v 0)) (.mul (.k t) (.v 0)))) (.add len (.mul (.add (.v 0) (.k 1)) (.k q)))

theorem queryInputIndex_val (p : OrdinaryOracleProgram) (width cap : ℕ) (i : Fin (queryWordBits width)) :
    (queryInputIndex p width cap i).val =
      if i.val < width then p.base.stateCount + (p.base.tapeCount * width + (i.val + width * p.queryTape.val))
      else (p.base.stateCount + (p.base.tapeCount * width + p.base.tapeCount * width)) +
        ((i.val - width) + (width + 1) * p.queryTape.val) := by
  rcases i with ⟨i, hi⟩
  show (queryInputIndex p width cap ⟨i, hi⟩).val = if i < width then _ else _
  unfold queryInputIndex
  split_ifs with h
  · have : (⟨i, hi⟩ : Fin (queryWordBits width)) = Fin.castAdd (width + 1) ⟨i, h⟩ := rfl
    rw [this, Fin.addCases_left]
    simp [clockViewIndex, cellIndex, finProdFinEquiv]
    omega
  · have : (⟨i, hi⟩ : Fin (queryWordBits width)) = Fin.natAdd width ⟨i - width, by unfold queryWordBits at hi; omega⟩ :=
      Fin.ext (by simp; omega)
    rw [this, Fin.addCases_right]
    simp [clockLengthIndex, windowBits, finProdFinEquiv]

/-! ## The templates -/

section Templates
variable (t s q : ℕ)

/-- Query cell `x` (`W` at level `0`). -/
def cellU (x : Tm) : U := .ite (.lt x (.v 0)) (.inp (cellT t s q x)) (.ofBool false)

/-- Query allocation at `x`, the length bound at level `ℓ`. -/
def allocU (ℓ : ℕ) (x : Tm) : U :=
  .bigOr (.add (.v 0) (.k 1)) (.ite (.lt x (.v ℓ)) (.inp (lenT t s q (.v ℓ))) (.ofBool false)) (.ofBool false)

/-- The frame prefix of `c` pairs from `pos` (members at level `ℓ`, the final allocation bound at `ℓ + 1`). -/
def prefixU (ℓ : ℕ) (c pos : Tm) : U :=
  .bigAnd c (cellU t s q (.add pos (.mul (.k 2) (.v ℓ))))
    (.and (allocU t s q (ℓ + 1) (.add pos (.mul (.k 2) c))) (.not (cellU t s q (.add pos (.mul (.k 2) c)))))

/-- **The address-bit template** (`bit` at level `4`, the frame count at level `5`). -/
def addrU : U :=
  .bigOr (.v 0) (.and (prefixU t s q 6 (.v 5) (.k 0))
    (.ite (.lt (.v 4) (.v 5)) (cellU t s q (.add (.mul (.k 2) (.v 4)) (.k 1))) (.ofBool false))) (.ofBool false)

end Templates

/-! ## The equalities -/

section Equalities
variable (p : OrdinaryOracleProgram) (width cap : ℕ) (D : List Bool)

/-- The clock-wire reading of the query inputs. -/
def qρ : Fin (queryWordBits width) → ℕ := fun i => (queryInputIndex p width cap i).val

theorem cell_eq (env : List ℕ) (hW : env.getD 0 0 = width) (x : ℕ) (xt : Tm) (hx : xt.eval env = x) :
    postR (qρ p width cap) (queryCellExpression width x) =
      (cellU p.base.tapeCount p.base.stateCount p.queryTape.val xt).toks D env := by
  unfold queryCellExpression
  simp only [cellU, U.toks, Tm.eval, cellT, hW, hx]
  by_cases h : x < width
  · simp [postR, h, qρ, queryInputIndex_val]
  · simp [postR, h, U.ofBool, Tm.ofBool, U.toks, Tm.eval]

theorem alloc_eq (env : List ℕ) (hW : env.getD 0 0 = width) (x : ℕ) (xt : Tm) (hx : xt.eval env = x)
    (hlv : xt.lvOk env.length) (hlen : 0 < env.length) :
    postR (qρ p width cap) (queryAllocatedExpression width x) =
      (allocU p.base.tapeCount p.base.stateCount p.queryTape.val env.length xt).toks D env := by
  unfold queryAllocatedExpression allocU
  refine postR_anyOfFn _ _ D env _ _ _ (by simp only [Tm.eval, hW]) (fun i => ?_) (by simp)
  have hx' : xt.eval (env ++ [i.val]) = x := by rw [Tm.eval_append env [i.val] xt hlv, hx]
  have hW' : (env ++ [i.val]).getD 0 0 = width := by
    rw [List.getD_append _ _ _ _ hlen]; exact hW
  have hi : (env ++ [i.val]).getD env.length 0 = i.val := by simp
  simp only [U.toks, Tm.eval, lenT, hx', hi, hW']
  by_cases h : x < i.val
  · simp [postR, h, qρ, queryInputIndex_val]
  · simp [postR, h, U.ofBool, Tm.ofBool, U.toks, Tm.eval]

theorem prefix_eq (env : List ℕ) (hW : env.getD 0 0 = width) (hlen : 0 < env.length) (c pos : ℕ) (ct pt : Tm)
    (hc : ct.eval env = c) (hp : pt.eval env = pos) (hlc : ct.lvOk env.length) (hlp : pt.lvOk env.length) :
    postR (qρ p width cap) (prefixExpression (queryCellExpression width) (queryAllocatedExpression width) c pos) =
      (prefixU p.base.tapeCount p.base.stateCount p.queryTape.val env.length ct pt).toks D env := by
  rw [postR_prefix]
  unfold prefixU
  simp only [U.toks, hc]
  have hWa : ∀ e, (env ++ e).getD 0 0 = width := fun e => by rw [List.getD_append _ _ _ _ hlen]; exact hW
  have hpa : ∀ e, pt.eval (env ++ e) = pos := fun e => by rw [Tm.eval_append env e pt hlp, hp]
  have hca : ∀ e, ct.eval (env ++ e) = c := fun e => by rw [Tm.eval_append env e ct hlc, hc]
  congr 2
  · refine List.flatMap_congr (fun k _ => ?_)
    exact cell_eq p width cap D (env ++ [k]) (hWa _) _ _ (by simp [Tm.eval, hpa])
  · have h1 := alloc_eq p width cap D (env ++ [c]) (hWa _) (pos + 2 * c) (.add pt (.mul (.k 2) ct))
      (by simp only [Tm.eval, hpa, hca]) ⟨Tm.lvOk_mono (by simp) pt hlp, trivial, Tm.lvOk_mono (by simp) ct hlc⟩
      (by simp)
    rw [List.length_append, List.length_singleton] at h1
    rw [h1, cell_eq p width cap D (env ++ [c]) (hWa _) _ (.add pt (.mul (.k 2) ct)) (by simp only [Tm.eval, hpa, hca])]

/-- **The address bits are one template** (`env = [width, cap, ell, |frame data|, bit]`). -/
theorem addr_eq (env : List ℕ) (hlen : env.length = 5) (hW : env.getD 0 0 = width) (bit : ℕ)
    (hb : env.getD 4 0 = bit) :
    postR (qρ p width cap) (queryAddressExpression width bit) =
      (addrU p.base.tapeCount p.base.stateCount p.queryTape.val).toks D env := by
  unfold queryAddressExpression addrU
  refine postR_anyOfFn _ _ D env _ _ _ (by simp only [Tm.eval, hW]) (fun cnt => ?_) (by simp)
  have hWa : (env ++ [cnt.val]).getD 0 0 = width := by rw [List.getD_append _ _ _ _ (by omega)]; exact hW
  have hba : (env ++ [cnt.val]).getD 4 0 = bit := by rw [List.getD_append _ _ _ _ (by omega)]; exact hb
  have hca : (env ++ [cnt.val]).getD 5 0 = cnt.val := by
    rw [show 5 = env.length by omega]; simp
  have hl6 : (env ++ [cnt.val]).length = 6 := by simp [hlen]
  simp only [postR, U.toks]
  have hp := prefix_eq p width cap D (env ++ [cnt.val]) hWa (by omega) cnt.val 0 (.v 5) (.k 0)
    (by simp only [Tm.eval, hca]) rfl (by simp only [Tm.lvOk, hl6]; omega) trivial
  rw [hl6] at hp
  rw [queryPrefixExpression, hp]
  congr 2
  by_cases h : bit < cnt.val
  · simp only [h, if_true, Tm.eval, hba, hca]
    simp only [show ¬ (1 = 0) from by omega, if_false]
    exact cell_eq p width cap D (env ++ [cnt.val]) hWa _ _ (by simp only [Tm.eval, hba])
  · simp only [h, Tm.eval, hba, hca, ↓reduceIte]
    simp [postR, U.ofBool, Tm.ofBool, U.toks, Tm.eval]

end Equalities

/-! ## The verdict as a template -/

theorem clockCell_val (p : OrdinaryOracleProgram) (width cap : ℕ) (tape : Fin p.base.tapeCount) (pos : Fin width) :
    (clockViewIndex (p := p) (cap := cap) (cellIndex tape pos)).val =
      p.base.stateCount + (p.base.tapeCount * width + (pos.val + width * tape.val)) := by
  simp [clockViewIndex, cellIndex, finProdFinEquiv]
  omega

theorem clockLength_val (p : OrdinaryOracleProgram) (width cap : ℕ) (tape : Fin p.base.tapeCount)
    (len : Fin (width + 1)) :
    (clockLengthIndex (p := p) (cap := cap) tape len).val =
      (p.base.stateCount + (p.base.tapeCount * width + p.base.tapeCount * width)) + (len.val + (width + 1) * tape.val) := by
  simp [clockLengthIndex, windowBits, finProdFinEquiv]

/-- **The verdict template** (proof of `thm:short-pcp-ours`: the negated literal output test). -/
def verdU (p : OrdinaryOracleProgram) : U :=
  let t := p.base.tapeCount
  let s := p.base.stateCount
  let o := p.base.outputTape.val
  .not (.and (U.orList (List.ofFn fun q : Fin s => .and (.inp (.k q.val)) (.ofBool (p.base.machine.halted q))))
    (.and (.inp (lenT t s o (.k 3))) (.and (.inp (cellT t s o (.k 0))) (.and (.inp (cellT t s o (.k 1)))
      (.not (.inp (cellT t s o (.k 2))))))))

theorem verd_eq (p : OrdinaryOracleProgram) (width cap : ℕ) (hw : 3 ≤ width) (D : List Bool) (env : List ℕ)
    (hW : env.getD 0 0 = width) :
    postR (fun i => i.val) (verdictExpression p width cap hw) = (verdU p).toks D env := by
  unfold verdictExpression outputWordExpression verdU clockControlSelection
  simp only [postR, U.toks, Tm.eval, lenT, cellT, hW]
  rw [postR_anyOfFn_list _ _ D env
    (fun q : Fin p.base.stateCount => (U.inp (.k q.val)).and (U.ofBool (p.base.machine.halted q))) (fun q => by
      simp [postR, U.toks, U.ofBool, Tm.ofBool, Tm.eval, controlIndex, clockViewIndex])]
  simp [clockCell_val, clockLength_val]

end NearCubicGates.Adapters.Compile.OraclePrint
