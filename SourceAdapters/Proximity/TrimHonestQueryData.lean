import SourceAdapters.Proximity.TrimHonestOriginal

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": exact input and source-proof oracles for each padded
source query. The source query tag is true precisely for proof addresses. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

def queryStore : Fin MM := 1
def queryTagReg : Fin VV := 62
def pairFields (p : Bool × ℕ) : List ℕ := [p.1.toNat, p.2]
def answerValue {n N : ℕ} (input : BitInput n) (proof : BitInput N) (p : Bool × ℕ) : Bool :=
  if p.1 then finiteProofOracle proof p.2 else finiteProofOracle input p.2

theorem answer_value_address {n N : ℕ} (input : BitInput n) (proof : BitInput N)
    (address : QueryAddress n) :
    answerValue input proof (SourceCallee.addressPair address) =
      oracleValue input (finiteProofOracle proof) address := by
  cases address with
  | inl i => simp [answerValue, SourceCallee.addressPair, oracleValue, finiteProofOracle, i.isLt]
  | inr i => rfl

structure OracleReady {n N : ℕ} (C : Ctx) (input : BitInput n) (proof : BitInput N)
    (a : DS VV MM) : Prop where
  input_ram : a.ram inputStore = (List.ofFn input).map Bool.toNat
  input_len : a.env inputLength = n
  input_cursor : a.rc inputStore ≤ n
  input_width : n < 2 ^ C.Wd
  proof_ram : a.ram proofStore = (List.ofFn proof).map Bool.toNat
  proof_len : a.env proofLength = N
  proof_cursor : a.rc proofStore ≤ N
  proof_width : N < 2 ^ C.Wd

namespace OracleReady
variable {n N : ℕ} {C : Ctx} {input : BitInput n} {proof : BitInput N} {a b : DS VV MM}
theorem frame (h : OracleReady C input proof a) {T : List (Fin VV)}
    (f : LookupFrame T a b) (hi : inputLength ∉ T) (hp : proofLength ∉ T)
    (bi : b.rc inputStore ≤ n) (bp : b.rc proofStore ≤ N) : OracleReady C input proof b := by
  exact ⟨by rw [f.ram]; exact h.input_ram, (f.env _ hi).trans h.input_len, bi, h.input_width,
    by rw [f.ram]; exact h.proof_ram, (f.env _ hp).trans h.proof_len, bp, h.proof_width⟩
theorem set (h : OracleReady C input proof a) (reg : Fin VV) (value : ℕ)
    (hi : inputLength ≠ reg) (hp : proofLength ≠ reg) : OracleReady C input proof (a.set reg value) := by
  refine ⟨h.input_ram, ?_, h.input_cursor, h.input_width, h.proof_ram, ?_, h.proof_cursor, h.proof_width⟩
  · simpa [DS.set, hi] using h.input_len
  · simpa [DS.set, hp] using h.proof_len
end OracleReady

end NearCubicGates.Adapters.Proximity.TrimHonest
