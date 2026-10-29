import SourceAdapters.ShortPCP.TimeVerifiers

/-!
# Single-run time, reference layer 7: the recursions of `V_{RS,=}` as iterations over levels

proof of `thm:short-pcp-ours`: "Its recursion roughly halves the dimension of the current affine subspace at each level and does
poly(f) field operations per level". `translateF` and `dEqFF` (`TimeRecursion.lean`) recurse on one level state
(basis, offset, remaining coins). A machine without recursion computes them by iterating the level map `Lvl.step`:
`dEqFF` is a tail recursion (`dEqFF_iter`: the base test at the last level), and `translateF` applies the level's
post-processing `Lvl.post` to the result of the next level (`translateF_iter`: a right fold over the levels, whose
level `j` is `step^[j]` of the first).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Time

open NearCubicGates.Published.BCGT13 NearCubicWires.CanonicalBinary

variable {F : Type} [Field F] [DecidableEq F]

/-- One level of the recursion of §12.3.1: the basis and offset of the current subspace, and the remaining coins. -/
structure Lvl (F : Type) where
  B : List F
  O : F
  r : List Bool

namespace Lvl

/-- The recursion stops at `κ ≤ κ0`. -/
def stop (x : Lvl F) : Bool := decide (x.B.length ≤ T0.κ0)

/-- The next level: the row domain `L_β` (coin `0`) or the column domain `Z_{L0}(L1)` (coin `1` or no coin). -/
def step (x : Lvl F) : Lvl F :=
  if x.r.head? = some false then
    ⟨if bitsValue ((x.r.drop 1).take (x.B.drop (x.B.length / 2)).length) < 2 then
        x.B.take (x.B.length / 2 + 1) ++ [x.B.getD (x.B.length / 2 + 1) 0]
      else x.B.take (x.B.length / 2 + 1) ++
        [sel (x.B.drop (x.B.length / 2)) (bitsValue ((x.r.drop 1).take (x.B.drop (x.B.length / 2)).length)) + x.O + x.O],
      x.O, x.r.drop (1 + (x.B.drop (x.B.length / 2)).length)⟩
  else ⟨zMulti (x.B.take (x.B.length / 2)) (x.B.drop (x.B.length / 2)), 0, x.r.drop (1 + (x.B.length / 2 + 1))⟩

/-- The post-processing of `Translate` at a level, given the next level's result (§12.3.1 (d) viii–xi, (e) vi–ix). -/
def post (x : Lvl F) (res : TrOut F) : TrOut F :=
  let κ := x.B.length
  let k := κ / 2
  let nL := 2 ^ κ
  let nLb := 2 ^ (k + 1 + 1)
  let nL1 := 2 ^ (x.B.drop k).length
  if x.r.head? = some false then
    let rv := bitsValue ((x.r.drop 1).take (x.B.drop k).length)
    let β' := zFast (x.B.take k) (sel (x.B.drop k) rv + x.O + x.O)
    match res with
    | .inp α ι => if zFast (x.B.take k) (α + x.O) = β' then .inp α (rowIdx k rv ι) else .prf (nL + nLb * rv + ι)
    | .prf ι => .prf ((ι - nLb + nL) + nLb * nL1 + rv * lengthEq T0 (k + 1 + 1))
  else
    let av := bitsValue ((x.r.drop 1).take (k + 1))
    let α := sel (x.B.take (k + 1)) av + x.O
    let α' := zFast (x.B.take k) (α + x.O)
    match res with
    | .inp β' ι => if α' = β' then .inp α (1 + av) else .prf (nL + nLb * (ι - 1) + (1 + av))
    | .prf ι => .prf ((ι - 2 ^ (x.B.drop k).length + nL) + nLb * nL1 + nL1 * lengthEq T0 (k + 1 + 1) +
        av * lengthEq T0 (x.B.drop k).length)

/-- The number of levels below `x` within fuel `n`. -/
def depth : ℕ → Lvl F → ℕ
  | 0, _ => 0
  | n + 1, x => if x.stop then 0 else depth n x.step + 1

end Lvl

omit [DecidableEq F] in
theorem zMulti_length : ∀ (B ys : List F), (zMulti B ys).length = ys.length
  | [], ys => rfl
  | a :: B, ys => by simp [zMulti, zMulti_length B]

theorem translateF_succ (n : ℕ) (x : Lvl F) (i : ℕ) :
    translateF (n + 1) x.B x.O x.r i =
      if x.stop then .inp (eltWithIndex x.B x.O i) i else x.post (translateF n x.step.B x.step.O x.step.r i) := by
  obtain ⟨B, O, r⟩ := x
  by_cases hs : B.length ≤ 4
  · simp [translateF, Lvl.stop, hs]
  · have hs' : (Lvl.stop ⟨B, O, r⟩ : Bool) = false := by simp [Lvl.stop, hs]
    rw [hs', if_neg (by simp)]
    by_cases hr : r.head? = some false
    · simp only [translateF, T0_κ0, T0_γ, T0_μ, hs, if_false, hr, if_true, Nat.sub_zero, Lvl.step, Lvl.post]
      cases translateF n _ O _ i <;> rfl
    · simp only [translateF, T0_κ0, T0_γ, T0_μ, hs, if_false, hr, Nat.sub_zero, Lvl.step, Lvl.post,
        zMulti_length]
      cases translateF n (zMulti (B.take (B.length / 2)) (B.drop (B.length / 2))) (0 : F)
        (r.drop (1 + (B.length / 2 + 1))) i <;> rfl

/-- **`Translate` as a right fold over the levels** (level `j` is `step^[j] x`). -/
theorem translateF_iter : ∀ (n : ℕ) (x : Lvl F) (i : ℕ),
    translateF n x.B x.O x.r i =
      (List.range (x.depth n)).foldr (fun j res => (Lvl.step^[j] x).post res)
        (.inp (eltWithIndex (Lvl.step^[x.depth n] x).B (Lvl.step^[x.depth n] x).O i) i)
  | 0, x, i => by simp [translateF, Lvl.depth]
  | n + 1, x, i => by
    rw [translateF_succ]
    by_cases hs : x.stop = true
    · simp [Lvl.depth, hs]
    · simp only [hs, Lvl.depth, if_false, Bool.false_eq_true]
      rw [translateF_iter n x.step i, List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
      simp only [Function.iterate_zero, id, Function.iterate_succ_apply]

omit [DecidableEq F] in
theorem dEqFF_succ (bt : List F → F → ℕ → (ℕ → F) → Bool) (n : ℕ) (x : Lvl F) (ans : ℕ → F) :
    dEqFF bt (n + 1) x.B x.O x.r ans =
      if x.stop then bt x.B x.O (dKE x.B.length T0.η) ans else dEqFF bt n x.step.B x.step.O x.step.r ans := by
  obtain ⟨B, O, r⟩ := x
  by_cases hs : B.length ≤ 4
  · simp [dEqFF, Lvl.stop, hs]
  · have hs' : (Lvl.stop ⟨B, O, r⟩ : Bool) = false := by simp [Lvl.stop, hs]
    rw [hs', if_neg (by simp)]
    by_cases hr : r.head? = some false
    · simp only [dEqFF, T0_κ0, T0_γ, T0_μ, hs, if_false, hr, if_true, Nat.sub_zero, Lvl.step]
    · simp only [dEqFF, T0_κ0, T0_γ, T0_μ, hs, if_false, hr, Nat.sub_zero, Lvl.step]

omit [DecidableEq F] in
/-- **`D_{RS,=}` as an iteration**: the base test at the last level. -/
theorem dEqFF_iter (bt : List F → F → ℕ → (ℕ → F) → Bool) : ∀ (n : ℕ) (x : Lvl F) (ans : ℕ → F),
    dEqFF bt n x.B x.O x.r ans =
      bt (Lvl.step^[x.depth n] x).B (Lvl.step^[x.depth n] x).O (dKE (Lvl.step^[x.depth n] x).B.length T0.η) ans
  | 0, x, ans => by simp [dEqFF, Lvl.depth]
  | n + 1, x, ans => by
    rw [dEqFF_succ]
    by_cases hs : x.stop = true
    · simp [Lvl.depth, hs]
    · simp only [hs, Lvl.depth, if_false, Bool.false_eq_true]
      rw [dEqFF_iter bt n x.step ans, Function.iterate_succ_apply]

end NearCubicGates.Adapters.ShortPCP.Time
