import SourceAdapters.RAMACSP.GenItemsHalt

/-!
# The coordinate rows `λ_j` in the input-record checks

Paper: `app:affine-embedding`, "Selectors" and "Input subspace", and the
proof of `lem:acsp-degree`. The input-address equation uses the lane coordinate
λ_j(X) for j < τ. Its linearized coefficient row is read from the coordinate
array printed for `lem:generator`.

`lamP`: the tokens of `λ_j` in postorder: for each `r < mH` the constant `c_{j,r}` (the mask at position `j·mH + r`
of the coordinate array in `vD`, `f` bits each), the read of `X`, `r` squarings and a product; then the constant
`0` and `mH` sums (`den_lamP`, `lamToks`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMTrace NearCubicGates.Adapters.Joins
open NearCubicWires NearCubicWires.RepairOrdinary

variable {G : Glob}

/-- The mask `c_{j,r}`: bits `(j·mH + r)·f … + f − 1` of the coordinate array (`mH` in 35, `f` in 36, `r` in `vR`). -/
def maskE : E := .md (.shr (.v vD) (.mul (.add (.mul jE (.v 35)) (.v vR)) (.v 36))) (pow1E (.v 36))

/-- The tokens of `λ_j`. -/
def lamP : P :=
  .seq (.loop vR (.v 35) (.seq (tokE 0 maskE) (.seq (tokE 1 k0) (.seq (.loop vS (.v vR) (tokE 4 k0)) (tokE 3 k0)))))
    (.seq (tokE 0 k0) (.loop vR (.v 35) (tokE 2 k0)))

/-- The numbers of `λ_j` with masks `c r`. -/
def lamNums (m : ℕ) (c : ℕ → ℕ) : List ℕ :=
  (List.range m).flatMap (fun r => [0, c r, 1, 0] ++ (List.range r).flatMap (fun _ => [4, 0]) ++ [3, 0]) ++ [0, 0] ++
    (List.range m).flatMap (fun _ => [2, 0])

theorem den_seq_eq (s : FS) (a b : P) : den G s (.seq a b) = den G s a ++ den G s b := rfl

theorem finRange_map_val (m : ℕ) : (List.finRange m).map Fin.val = List.range m := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem den_tokE_k {s : FS} (t v : ℕ) (ht : t ≤ G.cap) (hv : v ≤ G.cap) : den G s (tokE t (.k v)) = [t, v] := by
  simp [tokE, den, evalE, min_cap ht, min_cap hv]

/-- **The tokens of `λ_j`** from the coordinate array in `vD`. -/
theorem den_lamP {s : FS} (j m f D : ℕ) (c : ℕ → ℕ) (hj : s.env vJ = j) (hm : s.env 35 = m) (hf : s.env 36 = f)
    (hD : s.env vD = D) (hc : ∀ r < m, D / 2 ^ ((j * m + r) * f) % 2 ^ f = c r) (hjm : j < m)
    (hf1 : 1 ≤ f) (hcap1 : m * m * f + 8 ≤ G.cap) (hcap2 : 2 ^ f + 8 ≤ G.cap) (hN : m ≤ G.N) :
    den G s lamP = lamNums m c := by
  have hcap : m * m * f + 8 ≤ G.cap ∧ 2 ^ f + 8 ≤ G.cap := ⟨hcap1, hcap2⟩
  have hmmf : m * m ≤ m * m * f := Nat.le_mul_of_pos_right _ hf1
  have hp := Nat.two_pow_pos f
  have h8 : 8 ≤ G.cap := by omega
  have hmin : ∀ t : FS, t.env 35 = m → min (evalE G t (.v 35)) G.N = m := fun t ht => by
    show min (t.env 35) G.N = m; rw [ht]; omega
  simp only [lamP, den_seq_eq, lamNums, k0]
  rw [den_tokE_k 0 0 (by omega) (by omega)]
  have e2 : ∀ t : FS, t.env 35 = m → den G t (.loop vR (.v 35) (tokE 2 (.k 0))) =
      (List.range m).flatMap (fun _ => [2, 0]) := fun t ht => by
    rw [den_loop t vR _ _ m (hmin t ht) (fun _ => [2, 0])]
    intro r _
    exact den_tokE_k 2 0 (by omega) (by omega)
  rw [e2 s hm, List.append_assoc]
  refine congrArg₂ (· ++ ·) ?_ rfl
  rw [den_loop s vR _ _ m (hmin s hm) (fun r => [0, c r, 1, 0] ++ (List.range r).flatMap (fun _ => [4, 0]) ++ [3, 0])]
  intro r hr
  set t := s.setv vR r
  have tJ : t.env vJ = j := by
    show (s.setv vR r).env vJ = j; rw [FS.setv_env, Function.update_of_ne (show vJ ≠ vR by decide)]; exact hj
  have t35 : t.env 35 = m := by
    show (s.setv vR r).env 35 = m; rw [FS.setv_env, Function.update_of_ne (show (35 : Var) ≠ vR by decide)]; exact hm
  have t36 : t.env 36 = f := by
    show (s.setv vR r).env 36 = f; rw [FS.setv_env, Function.update_of_ne (show (36 : Var) ≠ vR by decide)]; exact hf
  have tD : t.env vD = D := by
    show (s.setv vR r).env vD = D; rw [FS.setv_env, Function.update_of_ne (show vD ≠ vR by decide)]; exact hD
  have tR : t.env vR = r := by simp [t]
  have hjm' : j * m + r < m * m := by
    have : (j + 1) * m ≤ m * m := Nat.mul_le_mul_right _ hjm
    nlinarith
  have hx : (j * m + r) * f ≤ m * m * f := Nat.mul_le_mul_right _ hjm'.le
  have hmask : evalE G t maskE = c r := by
    have a1 : evalE G t (.mul jE (.v 35)) = j * m := by
      show min (t.env vJ * t.env 35) G.cap = _; rw [tJ, t35]; exact min_cap (by omega)
    have a2 : evalE G t (.add (.mul jE (.v 35)) (.v vR)) = j * m + r := by
      show min (evalE G t (.mul jE (.v 35)) + t.env vR) G.cap = _; rw [a1, tR]; exact min_cap (by omega)
    have a3 : evalE G t (.mul (.add (.mul jE (.v 35)) (.v vR)) (.v 36)) = (j * m + r) * f := by
      show min (evalE G t (.add (.mul jE (.v 35)) (.v vR)) * t.env 36) G.cap = _; rw [a2, t36]
      exact min_cap (by omega)
    have a4 : evalE G t (pow1E (.v 36)) = 2 ^ f := eval_pow1 (show evalE G t (.v 36) = f from t36) (by omega)
    show evalE G t (.shr (.v vD) (.mul (.add (.mul jE (.v 35)) (.v vR)) (.v 36))) % evalE G t (pow1E (.v 36)) = _
    rw [a4]
    show t.env vD / 2 ^ evalE G t (.mul (.add (.mul jE (.v 35)) (.v vR)) (.v 36)) % 2 ^ f = _
    rw [a3, tD]
    exact hc r hr
  have hcr : c r ≤ G.cap := by
    rw [← hmask]; show _ % evalE G t (pow1E (.v 36)) ≤ _
    have a4 : evalE G t (pow1E (.v 36)) = 2 ^ f := eval_pow1 (show evalE G t (.v 36) = f from t36) (by omega)
    rw [a4]; have := Nat.mod_lt (t.env vD / 2 ^ evalE G t (.mul (.add (.mul jE (.v 35)) (.v vR)) (.v 36)))
      (Nat.two_pow_pos f)
    omega
  have hsq : den G t (.loop vS (.v vR) (tokE 4 (.k 0))) = (List.range r).flatMap (fun _ => [4, 0]) := by
    rw [den_loop t vS _ _ r (by show min (t.env vR) G.N = r; rw [tR]; omega) (fun _ => [4, 0])]
    intro i _
    exact den_tokE_k 4 0 (by omega) (by omega)
  simp only [den_seq_eq]
  rw [hsq]
  simp [tokE, den, evalE, hmask, k0, min_cap (show 0 ≤ G.cap by omega), min_cap (show 1 ≤ G.cap by omega),
    min_cap (show 3 ≤ G.cap by omega)]

/-! ## The tokens of `λ_j` -/

theorem exprToks_squares {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) :
    ∀ r : ℕ, (Joins.exprToks mk (squares r : Routing.Expr F)).flatMap tokNums =
      [1, 0] ++ (List.range r).flatMap (fun _ => [4, 0])
  | 0 => by simp [squares, Joins.exprToks, tokNums, Joins.varCode]
  | r + 1 => by
    simp only [squares, Joins.exprToks, List.flatMap_append, exprToks_squares mk r, List.range_succ]
    simp [tokNums]

theorem exprToks_foldr {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) {α : Type} (g : α → Routing.Expr F)
    (z : Routing.Expr F) :
    ∀ l : List α, (Joins.exprToks mk (l.foldr (fun r acc => .add (g r) acc) z)).flatMap tokNums =
      l.flatMap (fun r => (Joins.exprToks mk (g r)).flatMap tokNums) ++ (Joins.exprToks mk z).flatMap tokNums ++
        (List.range l.length).flatMap (fun _ => [2, 0])
  | [] => by simp
  | a :: l => by
    simp only [List.foldr_cons, Joins.exprToks, List.flatMap_append, exprToks_foldr mk g z l, List.flatMap_cons,
      List.length_cons, List.range_succ]
    simp [tokNums, List.append_assoc]

/-- **The numbers of `λ_j`** for a coefficient row `row` with masks `mk`. -/
theorem lamToks {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (hm0 : mk 0 = 0) {m : ℕ} (row : Fin m → F)
    (c : ℕ → ℕ) (hc : ∀ r : Fin m, mk (row r) = c r.val) :
    (Joins.exprToks mk (lamExpr row)).flatMap tokNums = lamNums m c := by
  unfold lamExpr lamNums
  rw [exprToks_foldr mk (fun r => .mul (.const (row r)) (squares r.val)) (.const 0) (List.finRange m)]
  simp only [List.length_finRange]
  have e1 : (List.finRange m).flatMap (fun r => (Joins.exprToks mk
      (Routing.Expr.mul (.const (row r)) (squares r.val) : Routing.Expr F)).flatMap tokNums) =
      (List.range m).flatMap (fun r => [0, c r, 1, 0] ++ (List.range r).flatMap (fun _ => [4, 0]) ++ [3, 0]) := by
    rw [← finRange_map_val, List.flatMap_map]
    apply List.flatMap_congr
    intro r _
    simp only [Joins.exprToks, List.flatMap_append, exprToks_squares, hc r]
    simp [tokNums]
  rw [e1]
  simp [Joins.exprToks, tokNums, hm0]

end NearCubicGates.Adapters.RAMACSP.Gen.Items
