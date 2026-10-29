import SourceAdapters.Proximity.SourceQueryRows
import SourceAdapters.Proximity.StoredCall

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the stored, actually computed source
truth table is passed to the checked finite ordinary block compiler. Its exact
raw literal stream is retained for sequential parsing. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

variable {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)

def blockRequest (table : BitInput (2 ^ q)) : ProofCall V := .inl (.inr (.inr (.inr (.inr table))))
def blockTag : List Bool := [false, true, true, true, true]

theorem block_input (table : BitInput (2 ^ q)) :
    proofCallInput V (blockRequest V table) = blockTag ++ List.ofFn table := rfl

variable (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofLength honest) budget)

theorem source_block_call (predicate : BitInput q → Bool) (Wd Lk Bk : ℕ) (input : List Bool)
    (m : Fin MM) (len : Fin VV) (hl0 : len ≠ c0) (hlj : len ≠ vJ) (hlt : len ≠ t0)
    (a : DS VV MM) (hc : Cst a)
    (hstore : a.ram m = (List.ofFn (predicateTable predicate)).map Bool.toNat)
    (hlen : a.env len = 2 ^ q) (hwidth : 2 ^ q < 2 ^ Wd) (hempty : a.kin = [])
    (hroom : 5 + 2 ^ q ≤ Lk) (hbudget : budget (blockRequest V (predicateTable predicate)) ≤ Bk) :
    let C := context V proofLength honest budget P Wd input Lk Bk
    Hs C (StoredCall.callStored m len blockTag) a
      (a.rc m + 8 * 2 ^ q + Lk + Bk + 20) (fun b =>
      b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc m = 2 ^ q ∧
      (∀ s, s ≠ m → b.rc s = a.rc s) ∧ b.kin = [] ∧ b.kout = blockWord predicate ∧ b.kc = 0 ∧
      Cst b ∧ Fr a b [t0, c0, vJ]) := by
  dsimp only
  let C := context V proofLength honest budget P Wd input Lk Bk
  have e := StoredCall.call_stored C m len blockTag (List.ofFn (predicateTable predicate))
    (blockWord predicate) hl0 hlj hlt a hc (blockRequest V (predicateTable predicate)) hstore
    (by simpa using hlen) (by simpa only [List.length_ofFn, C, context] using hwidth) hempty (block_input V _)
    (by simpa only [C, context, callee, block_input, List.length_append, List.length_ofFn,
      blockTag, List.length_cons, List.length_nil] using hroom)
    hbudget (blockTableWord_predicate predicate)
  simp only [List.length_ofFn] at e
  convert e using 1
  simp only [blockTag, List.length_cons, List.length_nil, C, context]
  omega

end NearCubicGates.Adapters.Proximity.SourceCallee
