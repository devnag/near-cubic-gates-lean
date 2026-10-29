import SourceAdapters.RAMACSP.CheckReads
import SourceAdapters.Routing.CircuitEvaluation

/-!
# Embedding theorem, part 4 (E1): the constraint at a point of `H` is the emitted sum

Paper: `thm:embedding` and `app:affine-embedding`, "Neighbors" and
"Selectors". The emitted polynomial is the sum of each selector times its
equation, with each assignment read made at a translation `X+b`. Its serialized
constants and bank offsets are reduced masks interpreted modulo irr.

The membership condition of `ACSP.Affine.Instance.Accepts` evaluates the instance's constraint polynomial `consPoly` at
`(α, A(N_1(α)), …, A(N_{c_N}(α)))`. `consPoly_eval` identifies this with `Routing.evaluate` of the emitted sum
`emit coords (termList (ownItems …))` at `α`, through the serialization (`fieldPoly_gateMask`), the circuit
evaluation theorem (`Routing.Circuit.Evaluation.eval_compileTerms`), the neighbor pairs (`nbrFn_eval`) and
the reading of a bank mask in `F₂[x]/(irr)` (`elt_toPoly_eq_maskEval`).
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.Joins
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Adapters.ShortPCP Polynomial

/-! ## A bank mask read in `F₂[x]/(irr)` -/

theorem toPoly_eq_cubePoly (m b : ℕ) (hb : b < 2 ^ m) :
    WireExponent3_5.GF.toPoly b = cubePoly m (fun i => b.testBit i.val) := by
  ext n
  rw [WireExponent3_5.GF.coeff_toPoly]
  by_cases hn : n < m
  · have h := cubePoly_coeff m (fun i => b.testBit i.val) ⟨n, hn⟩
    simp only at h
    rw [h]
    unfold WireExponent3_5.GF.bitF
    cases b.testBit n <;> simp
  · have hdeg : (cubePoly m (fun i => b.testBit i.val)).degree < n :=
      lt_of_lt_of_le (Polynomial.degree_sum_fin_lt _) (by exact_mod_cast not_lt.mp hn)
    rw [Polynomial.coeff_eq_zero_of_degree_lt hdeg,
      Nat.testBit_lt_two_pow (hb.trans_le (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hn)))]
    simp [WireExponent3_5.GF.bitF]

/-- A mask `b < 2^m` read modulo `irr` is the `H`-element `Σ_{b_i = 1} α^i` (`app:affine-embedding` `e_b = α^b`). -/
theorem elt_toPoly_eq_maskEval (irr : (ZMod 2)[X]) [Fact (Irreducible irr)] (m b : ℕ) (hb : b < 2 ^ m) :
    elt irr (WireExponent3_5.GF.toPoly b) = Routing.maskEval m (monoBasis irr m) b := by
  rw [toPoly_eq_cubePoly m b hb]
  exact (cubeEval_eq_mk irr m _).symm

/-! ## Changing the arity of a circuit evaluation -/

theorem eval_poly_cast {R : Type} [CommSemiring R] (c : ArithCircuit R) (n n' : ℕ) (h : n = n')
    (f : Fin (n + 1) → R) (g : Fin (n' + 1) → R) (hfg : ∀ i : Fin (n + 1), f i = g (Fin.cast (by omega) i)) :
    MvPolynomial.eval f (c.poly (n + 1)) = MvPolynomial.eval g (c.poly (n' + 1)) := by
  subst h
  have hfg' : f = g := funext fun i => (hfg i).trans rfl
  rw [hfg']

/-! ## The instance's coordinates and constraint terms -/

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X]) (r : ClockRequest)

/-- The instance's field. -/
abbrev OwnF : Type := Field2 (ownIrr V irrPoly (ownCons V irrPoly) r)

/-- The direct affine instance. -/
abbrev ownInstance : ACSP.Affine.Instance := ownInst V irrPoly (ownCons V irrPoly) r

theorem ownInstance_cN : (ownInstance V irrPoly r).cN = (Routing.globalBank (ownLayout V r.2)).length := by
  show (ownInst V irrPoly (ownCons V irrPoly) r).nbr.length = _
  rw [ownInst_nbr_list, List.length_map]

variable [Fact (Irreducible (ownIrr V irrPoly (ownCons V irrPoly) r))]

/-- The coordinate array printed by the generator (`Routing.explicitCoordinates`; `app:affine-embedding` Coordinate and row
selectors). -/
abbrev ownCoords (hI : Published.Shoup.IrreducibleChoice irrPoly) :
    Routing.Coordinates (ownLayout V r.2).m (ownBasis V irrPoly (ownCons V irrPoly) r) :=
  Routing.explicitCoordinates (ownBasis V irrPoly (ownCons V irrPoly) r)
    (ownBasis_independent V irrPoly (ownCons V irrPoly) r hI)

/-- The coordinate expressions `λ_j(X)` of the input-record address check (B5; `lamExpr`). -/
abbrev ownLam (hI : Published.Shoup.IrreducibleChoice irrPoly) : ℕ → Routing.Expr (OwnF V irrPoly r) := fun j =>
  if hj : j < (ownLayout V r.2).m then lamExpr ((ownCoords V irrPoly r hI).coeff ⟨j, hj⟩) else .const 0

/-- The emitted constraint sum of `lem:acsp-degree` (`P = Σ_t Sel_t·E_t`, routing items then machine items). -/
abbrev ownEmit (hI : Published.Shoup.IrreducibleChoice irrPoly) : Routing.MP (OwnF V irrPoly r) :=
  Routing.emit (ownCoords V irrPoly r hI) (Routing.Circuit.termList (ownItems V r (ownLam V irrPoly r hI)))

/-- The stored neighbor pair evaluates to translation by its bank mask. -/
theorem nbrFn_eval (i : Fin (ownInstance V irrPoly r).cN) (z : OwnF V irrPoly r) :
    (ownInstance V irrPoly r).nbrFn i z =
      z + Routing.maskEval (ownLayout V r.2).m (ownBasis V irrPoly (ownCons V irrPoly) r)
        ((Routing.globalBank (ownLayout V r.2)).getD i.val 0) := by
  have hi : i.val < (Routing.globalBank (ownLayout V r.2)).length :=
    lt_of_lt_of_eq i.isLt (ownInstance_cN V irrPoly r)
  have hb := Routing.LayoutFacts.globalBank_lt (ownLayout V r.2) _ (List.getElem_mem hi)
  unfold ACSP.Affine.Instance.nbrFn ACSP.Affine.Instance.slope ACSP.Affine.Instance.shift
    ACSP.Affine.Instance.elt
  rw [ownInst_nbr_list, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map]
  have h1 : elt (ownIrr V irrPoly (ownCons V irrPoly) r) (WireExponent3_5.GF.toPoly 1) = 1 := by simp [elt]
  rw [h1, one_mul, List.getD_eq_getElem _ _ hi]
  congr 1
  exact elt_toPoly_eq_maskEval _ _ _ hb

theorem ownCircuit_eq (hI : Published.Shoup.IrreducibleChoice irrPoly) (hG : ModulusGood V irrPoly r) :
    ownCircuit V irrPoly r hG = Routing.Circuit.compileTerms (ownLayout V r.2)
      (ownBasis V irrPoly (ownCons V irrPoly) r) (ownCoords V irrPoly r hI) (ownItems V r (ownLam V irrPoly r hI)) := by
  unfold ownCircuit
  rfl

theorem ownConsPoly_eq (hI : Published.Shoup.IrreducibleChoice irrPoly) :
    (ownInstance V irrPoly r).consPoly = (Routing.Circuit.compileTerms (ownLayout V r.2)
      (ownBasis V irrPoly (ownCons V irrPoly) r) (ownCoords V irrPoly r hI)
        (ownItems V r (ownLam V irrPoly r hI))).poly ((ownInstance V irrPoly r).cN + 1) := by
  have hG := modulusGood V irrPoly hI r
  have e1 : (ownInst V irrPoly (ownCons V irrPoly) r).cons = ownConsOf V irrPoly r hG := by
    rw [ownInst_cons]; unfold ownCons; exact dif_pos hG
  have e2 := fieldPoly_gateMask (baseIrr V irrPoly r) (modulus_monic hG.1) (fieldExp V r.2) hG.2
    (ownCircuit V irrPoly r hG).gates ((ownInstance V irrPoly r).cN + 1)
  rw [arithCircuit_mk_gates, ownCircuit_eq V irrPoly r hI hG] at e2
  refine Eq.trans ?_ e2
  rw [instance_consPoly, e1]
  rfl

/-- **E1: the evaluation bridge.** At every `α`, the constraint of `Accepts` evaluated at
`(α, A(N_1(α)), …, A(N_{c_N}(α)))` is `Routing.evaluate` of the emitted sum `P = Σ_t Sel_t·E_t` (`lem:acsp-degree`). -/
theorem consPoly_eval (hI : Published.Shoup.IrreducibleChoice irrPoly) (hn : 2 ≤ r.1.1) (hnt : r.1.1 ≤ r.2)
    (A : (OwnF V irrPoly r)[X]) (z : OwnF V irrPoly r) :
    MvPolynomial.eval (Fin.cons z fun i : Fin (ownInstance V irrPoly r).cN =>
        A.eval ((ownInstance V irrPoly r).nbrFn i z)) (ownInstance V irrPoly r).consPoly =
      Routing.evaluate (ownLayout V r.2) (ownBasis V irrPoly (ownCons V irrPoly) r) A.eval z (ownEmit V irrPoly r hI) := by
  have hr : ∀ item ∈ ownItems V r (ownLam V irrPoly r hI),
      Routing.Circuit.ReadsIn (Routing.globalBank (ownLayout V r.2)) item.2 :=
    itemsReadInBank V _ r hn hnt _ fun j => by
      show Routing.Circuit.ReadsIn _ (if hj : j < (ownLayout V r.2).m then _ else _)
      split
      · exact lamExpr_reads _ _
      · trivial
  have hE := Routing.Circuit.Evaluation.eval_compileTerms (ownLayout V r.2) (ownBasis V irrPoly (ownCons V irrPoly) r)
    (ownCoords V irrPoly r hI) (ownItems V r (ownLam V irrPoly r hI)) hr A.eval z
  refine Eq.trans ?_ hE
  rw [ownConsPoly_eq V irrPoly r hI]
  refine eval_poly_cast _ _ _ (ownInstance_cN V irrPoly r) _ _ fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Routing.Circuit.Evaluation.bankInputs, Fin.val_cast, Fin.val_zero, ↓reduceIte, Fin.cons_zero]
  · have hj : j.val < (Routing.globalBank (ownLayout V r.2)).length := lt_of_lt_of_eq j.isLt (ownInstance_cN V irrPoly r)
    rw [Fin.cons_succ, nbrFn_eval V irrPoly r j z]
    simp only [Routing.Circuit.Evaluation.bankInputs, Fin.val_cast, Fin.val_succ, Nat.add_one_ne_zero, ↓reduceIte,
      Nat.add_sub_cancel]

end NearCubicGates.Adapters.RAMACSP
