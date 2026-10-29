import NineInputs
import Mathlib.Algebra.Field.ZMod

/-!
# Vacuity examples for the STV leaf

* The hypotheses of `Theorem29` are satisfiable: `q = X` is monic, irreducible, of degree `1` (`𝔽₂[X]/(X) ≅ 𝔽₂`),
  and `c·√(0/2) < ε` for every `ε > 0` (`stv_hypotheses`).
* The identity decoder: the oracle machine `idMachine` (copy the point to the query tape, ask, copy the answer to
  the output tape) computes `P` from every oracle that agrees with `P` everywhere, within `2` transitions and with
  no coins; such an oracle has agreement `1` (`identity_computes`, `identity_halts`, `identity_agrees`).
* `Computes` is not trivially true: the machine that halts at once (output `0`) does not compute the constant
  polynomial `1` (`halt_not_computes`), so the model's success criterion depends on the output.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Vacuity.STV

open NearCubicWires.LocalBitMultitape Polynomial NearCubicGates.Published.STV

/-- The leaf's field hypotheses hold for `q = X`, `t = 1`. -/
theorem stv_hypotheses : (X : (ZMod 2)[X]).Monic ∧ Irreducible (X : (ZMod 2)[X]) ∧
    (X : (ZMod 2)[X]).natDegree = 1 ∧ ∀ c ε : ℝ, 0 < ε → c * Real.sqrt (((0 : ℕ) : ℝ) / 2 ^ 1) < ε := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨monic_X, irreducible_X, natDegree_X, fun c ε hε => ?_⟩
  simpa using hε

/-- The identity decoder's rule: state `0` copies the input bit to the query tape and enters the query state `1`;
state `1` copies the answer bit to the output tape and halts in state `2`. -/
def idRule : Fin 3 → (Fin 5 → Bool) → Option (Action 5 3) := fun s scanned =>
  if s.val = 0 then
    some ⟨1, fun i => if i.val = 2 then some (scanned 0) else none, fun _ => .stay⟩
  else if s.val = 1 then
    some ⟨2, fun i => if i.val = 4 then some (scanned 3) else none, fun _ => .stay⟩
  else none

/-- The identity decoder for `m = t = 1`, without coins. -/
def idMachine : OracleMachine where
  tapeCount := 5
  stateCount := 3
  fiveTapes := le_rfl
  machine := { descriptionBits := 0, start := 0, halted := fun s => decide (s.val = 2), rule := idRule }
  asks := fun s => decide (s.val = 1)
  randomBits := 0

/-- The single point word `[x 0 0]`. -/
theorem pointWord_one (x : Fin 1 → Fin 1 → Bool) : pointWord x = [x 0 0] := by
  simp [pointWord]

/-- The run of the identity decoder: after two transitions it halts with `f x` on the output tape. -/
theorem idMachine_run (f : (Fin 1 → Fin 1 → Bool) → Fin 1 → Bool) (x : Fin 1 → Fin 1 → Bool)
    (r : Fin idMachine.randomBits → Bool) : ∃ c, idMachine.oracleRun (fieldOracle f) 2 (idMachine.initial (pointWord x) (List.ofFn r)) =
      some c ∧ idMachine.outputWord 1 c = f x := by
  have hq : queryPoint 1 1 [x 0 0] = x := by
    funext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    rfl
  refine ⟨_, rfl, ?_⟩
  funext j
  rw [Subsingleton.elim j 0]
  simp [OracleMachine.outputWord, OracleMachine.initial, idMachine, applyAction, Configuration.scanned,
    pointWord_one, fieldOracle, OracleMachine.outputTape, OracleMachine.answerTape, OracleMachine.queryTape,
    Function.update_apply, readTapeBit, hq, HeadMove.apply, writeTapeBit]

/-- **The identity decoder computes `P`** from an oracle that agrees with `P` at every point. -/
theorem identity_computes (f : (Fin 1 → Fin 1 → Bool) → Fin 1 → Bool) (P : MvPolynomial (Fin 1) (AdjoinRoot X))
    (hfP : ∀ x, fieldElt X (f x) = evalAt X P x) : idMachine.Computes X f P := by
  intro x
  have hall : {r : Fin idMachine.randomBits → Bool | idMachine.OutputsValue X f x r (evalAt X P x)} = Set.univ := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨c, hc, hout⟩ := idMachine_run f x r
    exact ⟨2, c, hc, by rw [hout, hfP]⟩
  rw [hall, Set.ncard_univ]
  simp [idMachine]

/-- The identity decoder halts within two transitions. -/
theorem identity_halts (f : (Fin 1 → Fin 1 → Bool) → Fin 1 → Bool) : idMachine.HaltsWithin f 2 := by
  intro x r
  obtain ⟨c, hc, _⟩ := idMachine_run f x r
  exact ⟨2, by norm_num, by rw [hc]; rfl⟩

/-- An oracle that agrees with `P` everywhere has agreement `1`. -/
theorem identity_agrees (f : (Fin 1 → Fin 1 → Bool) → Fin 1 → Bool) (P : MvPolynomial (Fin 1) (AdjoinRoot X))
    (hfP : ∀ x, fieldElt X (f x) = evalAt X P x) : Agrees X f P 1 := by
  have hall : {x : Fin 1 → Fin 1 → Bool | fieldElt X (f x) = evalAt X P x} = Set.univ := by
    ext x; simp [hfP x]
  unfold Agrees
  rw [hall, Set.ncard_univ, Nat.card_eq_fintype_card]
  simp

/-- The machine that halts at once. -/
def haltMachine : OracleMachine where
  tapeCount := 5
  stateCount := 1
  fiveTapes := le_rfl
  machine := { descriptionBits := 0, start := 0, halted := fun _ => true, rule := fun _ _ => none }
  asks := fun _ => false
  randomBits := 0

/-- **`Computes` depends on the output**: the immediately halting machine (output word `0`) does not compute the
constant polynomial `1`, whatever the oracle. -/
theorem halt_not_computes (f : (Fin 1 → Fin 1 → Bool) → Fin 1 → Bool) :
    ¬ haltMachine.Computes X f (MvPolynomial.C 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial (AdjoinRoot (X : (ZMod 2)[X])) := AdjoinRoot.nontrivial (f := X) (by simp)
  intro h
  let x0 : Fin 1 → Fin 1 → Bool := fun _ _ => false
  let P : MvPolynomial (Fin 1) (AdjoinRoot (X : (ZMod 2)[X])) := MvPolynomial.C 1
  have h0 := h x0
  have hempty : {r : Fin haltMachine.randomBits → Bool | haltMachine.OutputsValue X f x0 r (evalAt X P x0)} = ∅ := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨fuel, c, hc, hv⟩
    have hc' : c = haltMachine.initial (pointWord x0) (List.ofFn r) := by
      cases fuel <;> simp [OracleMachine.oracleRun, haltMachine] at hc <;> exact hc.symm
    subst hc'
    have hw : haltMachine.outputWord 1 (haltMachine.initial (pointWord x0) (List.ofFn r)) = fun _ => false := by
      funext j
      simp [OracleMachine.outputWord, OracleMachine.initial, OracleMachine.outputTape, readTapeBit]
    rw [hw] at hv
    simp [fieldElt, wordPoly, evalAt, P] at hv
  rw [hempty, Set.ncard_empty] at h0
  simp [haltMachine] at h0

end NearCubicGates.Adapters.Vacuity.STV
