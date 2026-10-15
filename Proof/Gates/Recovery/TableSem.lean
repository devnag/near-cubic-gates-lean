import Proof.Gates.Transfer.CaseTwo
import Proof.Gates.CheckedPCPP.LitDecode

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.TableSem

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.CheckedPCPP.LitDecode
open NearCubicWires.RepairOrdinary.RadixSemantics (value value_append value_lt)

/-! ## Numbers -/

theorem natOfBits_eq_value : ∀ {m : ℕ} (f : Fin m → Bool), natOfBits f = value (List.ofFn f)
  | 0, f => by simp [natOfBits, value]
  | m + 1, f => by
    rw [List.ofFn_succ, value, ← natOfBits_eq_value (fun i : Fin m => f i.succ)]
    unfold natOfBits
    rw [Fin.sum_univ_succ, Finset.mul_sum]
    congr 1
    · cases f 0 <;> simp
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [Fin.val_succ, pow_succ]
      split_ifs <;> ring

theorem clog_eq_size (v : ℕ) : Nat.clog 2 v = (v - 1).size := by
  apply le_antisymm
  · apply Nat.clog_le_of_le_pow
    have := Nat.lt_size_self (v - 1)
    omega
  · rw [Nat.size_le]
    rcases Nat.eq_zero_or_pos v with h | h
    · subst h; simp
    · have := Nat.le_pow_clog (b := 2) (by decide) v
      omega

/-! ## The table bit -/

/-- The five-entry honest value at clause index `a` and position `j`, read from the clause list `raw` and the
assignment `asg` (a bit list, `false` past its end). -/
def tableBit {m : ℕ} (raw : RawThreeQueryPCPP m) (asg : List Bool) (a j : ℕ) : Bool :=
  let clause := raw.clause ⟨a % 2 ^ raw.randomBits, Nat.mod_lt _ (by positivity)⟩
  let bit : Fin 3 → Bool := fun t => asg.getD (litVar (clause t)) false
  let ev : Fin 3 → Bool := fun t => xor (bit t) (decide (litNeg (clause t) = 1))
  if h : j % 5 < 3 then bit ⟨j % 5, h⟩ else (ev 0 && ev 1) && ev 2

theorem getD_ofFn {k : ℕ} (y : BitInput k) (l : Literal k) :
    (List.ofFn y).getD (litVar l) false = y (literalVar l) := by
  cases l with
  | positive i => simp [litVar, literalVar, List.getD_eq_getElem?_getD]
  | negative i => simp [litVar, literalVar, List.getD_eq_getElem?_getD]

theorem eval_eq {k : ℕ} (y : BitInput k) (l : Literal k) :
    l.eval y = xor ((List.ofFn y).getD (litVar l) false) (decide (litNeg l = 1)) := by
  rw [getD_ofFn]
  cases l <;> simp [Literal.eval, litNeg, literalVar]

theorem hardTable_eq (P : ThreeQueryPCPP) (D : Circuit) (hD : ∀ x, D.D.eval x = true) (cl pl : ℕ)
    (address : BitInput (D.n + cl + pl)) :
    hardTable P D hD cl pl address =
      let x : BitInput D.n := fun i => address (Fin.castAdd pl (Fin.castAdd cl i))
      tableBit (P.output (checkedCircuit P.code D))
        (List.ofFn (Fin.addCases (sysEnc P.code D.n x) (P.honest (acceptedInput P.code D x (hD x))) :
          BitInput ((checkedCircuit P.code D).n + (P.output (checkedCircuit P.code D)).proofBits)))
        (natOfBits (fun i : Fin cl => address (Fin.castAdd pl (Fin.natAdd D.n i))))
        (natOfBits (fun i : Fin pl => address (Fin.natAdd (D.n + cl) i))) := by
  unfold hardTable tableBit
  dsimp only
  split_ifs with h
  · rw [getD_ofFn]
  · simp only [List.ofFn_succ, List.ofFn_zero, List.all_cons, List.all_nil, id, Bool.and_true, eval_eq,
      Bool.and_assoc]
    rfl

end NearCubicGates.Close.Recovery.TableSem
