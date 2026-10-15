import Proof.Gates.EveryLengthPadding
import Proof.Gates.GadgetTableTransfer

/-! The name-selected functions really are literal restrictions of one actual
    weighted circuit. Address encoding is an explicit finite equivalence. -/

set_option autoImplicit false

namespace NearCubicGates.CircuitTableCofactors

open scoped BigOperators
open NearCubicWires Target FiniteAverages FiveCycle

variable {G Name : Type*} [Fintype G] [Nonempty G] {n k P : ℕ}

noncomputable def candidate (C : WeightedSymmetricCircuit (n + k))
    (encode : G × Fin P ≃ BitInput k) (a : G × Fin P) : BoolFunction n :=
  (C.restrictSuffix (encode a)).eval

noncomputable def honestTable (name : G → Fin 5 → Name)
    (honest : Name → BoolFunction n) (encode : G × Fin P ≃ BitInput k) :
    BoolFunction (n + k) := fun x =>
  let split := splitInputEquiv n k x
  let a := encode.symm split.2
  honest (name a.1 (slot a.2)) split.1

omit [Nonempty G] in
theorem table_error_eq (C : WeightedSymmetricCircuit (n + k))
    (name : G → Fin 5 → Name) (honest : Name → BoolFunction n)
    (encode : G × Fin P ≃ BitInput k) :
    error (honestTable name honest encode) C.eval =
      mean (fun a : G × Fin P =>
        error (GadgetTableTransfer.table name honest a) (candidate C encode a)) := by
  have hm := mean_equiv (splitInputEquiv n k).symm
    (fun x => mismatch (honestTable name honest encode x) (C.eval x))
  unfold error at hm ⊢
  rw [← hm, mean_prod]
  have he := mean_equiv encode (fun suffix : BitInput k =>
    mean (fun x : BitInput n => mismatch
      (honestTable name honest encode (Fin.append x suffix)) (C.eval (Fin.append x suffix))))
  change (mean (fun suffix : BitInput k => mean (fun x : BitInput n => mismatch
    (honestTable name honest encode (Fin.append x suffix)) (C.eval (Fin.append x suffix))))) = _
  rw [← he]
  congr 1
  funext a
  simp [honestTable, splitInputEquiv, GadgetTableTransfer.table, candidate]

noncomputable def selectedCircuit (hP : 0 < P) (C : WeightedSymmetricCircuit (n + k))
    (name : G → Fin 5 → Name) (honest : Name → BoolFunction n)
    (encode : G × Fin P ≃ BitInput k) (X : Name) : WeightedSymmetricCircuit n := by
  letI : Nonempty (Fin P) := ⟨⟨0, hP⟩⟩
  let addressName := fun a : G × Fin P => name a.1 (slot a.2)
  exact C.restrictSuffix (encode (NameCofactors.chosenAddress addressName
    (NameCofactors.addressError addressName honest (candidate C encode)) X))

@[simp] theorem selectedCircuit_topWeight (hP : 0 < P) (C : WeightedSymmetricCircuit (n + k))
    (name : G → Fin 5 → Name) (honest : Name → BoolFunction n)
    (encode : G × Fin P ≃ BitInput k) (X : Name) :
    (selectedCircuit hP C name honest encode X).topWeight = C.topWeight := rfl

theorem selectedCircuit_eval (hP : 0 < P) (C : WeightedSymmetricCircuit (n + k))
    (name : G → Fin 5 → Name) (honest : Name → BoolFunction n)
    (encode : G × Fin P ≃ BitInput k) (X : Name) (x : BitInput n) :
    (selectedCircuit hP C name honest encode X).eval x =
      GadgetTableTransfer.cofactors hP name honest (candidate C encode) X x := rfl

end NearCubicGates.CircuitTableCofactors
