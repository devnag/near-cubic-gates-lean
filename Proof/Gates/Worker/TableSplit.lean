import Proof.Gates.Worker.Normalize
import Proof.Gates.Worker.Meaning
import Proof.Gates.Interfaces.Transfer
import Proof.Gates.Gadget.ThreeQuery
import Proof.Gates.CircuitTableCofactors
import Proof.Gates.FreshHelperTable

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicGates NearCubicGates.FiniteAverages NearCubicGates.Close.Interfaces
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.FreshHelperTable NearCubicGates.GadgetTableTransfer NearCubicGates.FiveCycle
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311

/-! ## Binary addresses -/

/-- Bits ↔ numbers, least significant first (`natOfBits`). -/
def bitsEquiv (m : ℕ) : BitInput m ≃ Fin (2 ^ m) :=
  (Equiv.arrowCongr (Equiv.refl (Fin m)) finTwoEquiv.symm).trans finFunctionFinEquiv

theorem natOfBits_eq (m : ℕ) (f : BitInput m) : natOfBits f = (bitsEquiv m f).val := by
  unfold natOfBits bitsEquiv
  rw [Equiv.trans_apply, finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  cases h : f i <;> simp [finTwoEquiv, h]

/-- The address bits of number `a`. -/
def addressBits (m : ℕ) (a : Fin (2 ^ m)) : BitInput m := (bitsEquiv m).symm a

theorem natOfBits_addressBits (m : ℕ) (a : Fin (2 ^ m)) : natOfBits (addressBits m a) = a.val := by
  rw [natOfBits_eq, addressBits, Equiv.apply_symm_apply]

/-! ## Names and clauses of the checked verifier's PCPP -/

theorem literal_eval_eq {k : ℕ} (l : Literal k) (y : BitInput k) :
    l.eval y = literal (literalNeg l) (y (literalVar l)) := by
  cases l <;> rfl

/-- The underlying coordinate names: the checked circuit's input (systematic) and the PCPP proof. -/
abbrev Name (P : ThreeQueryPCPP) (D : Circuit) : Type :=
  Fin ((checkedCircuit P.code D).n + (P.output (checkedCircuit P.code D)).proofBits)

/-- Clause `a mod 2^{rb}` of the repeated list, as unsigned names and signs. -/
noncomputable def clausesOf (P : ThreeQueryPCPP) (D : Circuit) (cl : ℕ) (a : Fin (2 ^ cl)) : Clause (Name P D) where
  name i := literalVar ((P.output (checkedCircuit P.code D)).clause
    ⟨a.val % 2 ^ (P.output (checkedCircuit P.code D)).randomBits, Nat.mod_lt _ (by positivity)⟩ i)
  negative i := literalNeg ((P.output (checkedCircuit P.code D)).clause
    ⟨a.val % 2 ^ (P.output (checkedCircuit P.code D)).randomBits, Nat.mod_lt _ (by positivity)⟩ i)

/-- The honest coordinate functions: the systematic encoding and the honest proof. -/
noncomputable def originalOf (P : ThreeQueryPCPP) (D : Circuit) (hD : ∀ x, D.D.eval x = true) (X : Name P D)
    (x : BitInput D.n) : Bool :=
  (Fin.addCases (sysEnc P.code D.n x) (P.honest (acceptedInput P.code D x (hD x))) :
    BitInput ((checkedCircuit P.code D).n + (P.output (checkedCircuit P.code D)).proofBits)) X

theorem all_ofFn_three (f : Fin 3 → Bool) : (List.ofFn f).all id = (f 0 && f 1 && f 2) := by
  simp [List.ofFn_succ, Bool.and_assoc]

theorem clausesOf_true (P : ThreeQueryPCPP) (D : Circuit) (hD : ∀ x, D.D.eval x = true) (cl : ℕ)
    (a : Fin (2 ^ cl)) (x : BitInput D.n) :
    (clausesOf P D cl a).eval (fun X => originalOf P D hD X x) = true := by
  have h := P.complete D x (hD x)
    ⟨a.val % 2 ^ (P.output (checkedCircuit P.code D)).randomBits, Nat.mod_lt _ (by positivity)⟩
  unfold RawThreeQueryPCPP.accepts at h
  unfold Clause.eval clausesOf originalOf
  simp only [literal_eval_eq] at h
  simp only [List.ofFn_succ, List.ofFn_zero, List.any_cons, List.any_nil, id, Bool.or_false] at h
  simpa [Gadget.originalClause, Bool.or_assoc] using h

theorem names_lt {G N : Type*} (clauses : G → Clause N) (a : G) (t : Fin 5) (h : t.val < 3) :
    names clauses a t = Sum.inl ((clauses a).name ⟨t.val, h⟩) := by
  fin_cases t <;> first | rfl | (simp at h)

theorem names_ge {G N : Type*} (clauses : G → Clause N) (a : G) (t : Fin 5) (h : 3 ≤ t.val) :
    names clauses a t = Sum.inr a := by
  fin_cases t <;> first | rfl | (simp at h)

theorem hardTable_at (P : ThreeQueryPCPP) (D : Circuit) (hD : ∀ x, D.D.eval x = true) (cl pl : ℕ)
    (x : BitInput D.n) (a : Fin (2 ^ cl)) (j : Fin (2 ^ pl)) :
    hardTable P D hD cl pl (Fin.append (Fin.append x (addressBits cl a)) (addressBits pl j)) =
      honestAssignment (clausesOf P D cl) (originalOf P D hD) (names (clausesOf P D cl) a (slot j)) x := by
  have hx : (fun i : Fin D.n => Fin.append (Fin.append x (addressBits cl a)) (addressBits pl j)
      (Fin.castAdd pl (Fin.castAdd cl i))) = x := by
    funext i; simp
  have ha : natOfBits (fun i : Fin cl => Fin.append (Fin.append x (addressBits cl a)) (addressBits pl j)
      (Fin.castAdd pl (Fin.natAdd D.n i))) = a.val := by
    rw [← natOfBits_addressBits cl a]; congr 1; funext i; simp
  have hj : natOfBits (fun i : Fin pl => Fin.append (Fin.append x (addressBits cl a)) (addressBits pl j)
      (Fin.natAdd (D.n + cl) i)) = j.val := by
    rw [← natOfBits_addressBits pl j]; congr 1; funext i; simp
  unfold hardTable
  dsimp only
  generalize hx' : (fun i : Fin D.n => Fin.append (Fin.append x (addressBits cl a)) (addressBits pl j)
      (Fin.castAdd pl (Fin.castAdd cl i))) = x'
  obtain rfl : x' = x := hx'.symm.trans hx
  simp only [ha, hj]
  by_cases h3 : j.val % 5 < 3
  · rw [dif_pos h3, names_lt (clausesOf P D cl) a (slot j) h3]
    rfl
  · rw [dif_neg h3, names_ge (clausesOf P D cl) a (slot j) (Nat.le_of_not_lt h3), all_ofFn_three]
    simp only [literal_eval_eq]
    rfl

/-! ## The table error as an average of address-cofactor errors -/

/-- The cofactor of a target circuit at address `(a, j)`. -/
noncomputable def addressCofactor {n cl pl : ℕ} (C : Target.WeightedSymmetricCircuit (n + cl + pl))
    (aj : Fin (2 ^ cl) × Fin (2 ^ pl)) : Target.WeightedSymmetricCircuit n :=
  (C.restrictSuffix (addressBits pl aj.2)).restrictSuffix (addressBits cl aj.1)

@[simp] theorem addressCofactor_topWeight {n cl pl : ℕ} (C : Target.WeightedSymmetricCircuit (n + cl + pl))
    (aj : Fin (2 ^ cl) × Fin (2 ^ pl)) : (addressCofactor C aj).topWeight = C.topWeight := rfl

theorem addressCofactor_eval {n cl pl : ℕ} (C : Target.WeightedSymmetricCircuit (n + cl + pl))
    (aj : Fin (2 ^ cl) × Fin (2 ^ pl)) (x : BitInput n) :
    (addressCofactor C aj).eval x = C.eval (Fin.append (Fin.append x (addressBits cl aj.1)) (addressBits pl aj.2)) := by
  simp [addressCofactor]

theorem error_split {n cl pl : ℕ} (T : BoolFunction (n + cl + pl)) (C : Target.WeightedSymmetricCircuit (n + cl + pl)) :
    error T C.eval = mean (fun aj : Fin (2 ^ cl) × Fin (2 ^ pl) =>
      error (fun x => T (Fin.append (Fin.append x (addressBits cl aj.1)) (addressBits pl aj.2)))
        (addressCofactor C aj).eval) := by
  unfold error
  conv_lhs => rw [← mean_equiv (Target.splitInputEquiv (n + cl) pl).symm, mean_prod,
    ← mean_equiv (bitsEquiv pl).symm]
  conv_rhs => rw [mean_prod]
  congr 1
  funext j
  conv_lhs => rw [← mean_equiv (Target.splitInputEquiv n cl).symm, mean_prod, ← mean_equiv (bitsEquiv cl).symm]
  congr 1
  funext a
  congr 1
  funext x
  rw [addressCofactor_eval]
  rfl

end NearCubicGates.Close.Worker
