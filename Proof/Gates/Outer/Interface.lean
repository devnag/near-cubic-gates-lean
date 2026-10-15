import Proof.Gates.Outer.Source
import Proof.PCP.PCPPNativeRequestSchema
import Proof.Foundations.SourceCore

set_option autoImplicit false

namespace NearCubicGates.Close.Outer

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape

/-- `L_ν = ν^{G+2}`: the length of the padded instance `⟨B_src⟩_ν` (paper §11.4: "Put L_ν = ν^{G′}", here with
`G′ = G + 2`). -/
def instLength (G ν : ℕ) : ℕ := ν ^ (G + 2)

def srcDescriptor {m : ℕ} (B : BooleanCircuit m) : List Bool := PCPPNative.descriptor B

/-- The description of `B` fits in `L_ν` bits. -/
def SrcFits (G ν : ℕ) {m : ℕ} (B : BooleanCircuit m) : Prop := (srcDescriptor B).length ≤ instLength G ν

/-- `⟨B⟩_ν`: the description padded with zeros to length `L_ν` (when it fits). -/
def srcWord (G ν : ℕ) {m : ℕ} (B : BooleanCircuit m) : List Bool :=
  srcDescriptor B ++ List.replicate (instLength G ν - (srcDescriptor B).length) false

/-- `⟨B⟩_ν` as an input of length exactly `L_ν`. -/
def srcBits (G ν : ℕ) {m : ℕ} (B : BooleanCircuit m) : BitInput (instLength G ν) :=
  fun i => (srcWord G ν B).getD i.val false

/-- `⟨B⟩_ν` as a request of the imported constructor. -/
def srcInput (G ν : ℕ) {m : ℕ} (B : BooleanCircuit m) : InputRequest := ⟨instLength G ν, srcBits G ν B⟩

theorem srcWord_length (G ν : ℕ) {m : ℕ} (B : BooleanCircuit m) (h : SrcFits G ν B) :
    (srcWord G ν B).length = instLength G ν := by
  unfold srcWord SrcFits at *
  simp only [List.length_append, List.length_replicate]
  omega

theorem ofFn_srcBits (G ν : ℕ) {m : ℕ} (B : BooleanCircuit m) (h : SrcFits G ν B) :
    List.ofFn (srcBits G ν B) = srcWord G ν B := by
  apply List.ext_getElem
  · rw [List.length_ofFn, srcWord_length G ν B h]
  · intro i h1 h2
    simp only [List.getElem_ofFn, srcBits, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
      Option.getD_some]

/-- The point `(bin_ν(i), 0^{m−ν})` on `m` inputs: bit `j < ν` is bit `j` of `i`, every other bit is `0` (paper §11.4,
eq:source-check). -/
def pointOf (ν m i : ℕ) : BitInput m := fun j => if j.val < ν then i.testBit j.val else false

/-- `tt_N(B)`, `N = 2^ν`: the table of `B` at the points `(bin_ν(i), 0^{m−ν})`, `i < N`. -/
def ttN (ν : ℕ) {m : ℕ} (B : BooleanCircuit m) : BitInput (2 ^ ν) := fun i => B.eval (pointOf ν m i.val)

/-- CHECK (paper §11.4, eq:source-check): `B_src(bin_ν(i) 0^{q−ν}) = z_i` for every `i < N`. -/
def Check (ν : ℕ) (z : BitInput (2 ^ ν)) {m : ℕ} (B : BooleanCircuit m) : Prop := ttN ν B = z

/-- CHECK at a source length `N` (the weak machine's form; equal to `Check` when `N = 2^ν`). -/
def CheckAt (ν : ℕ) {N : ℕ} (z : BitInput N) {m : ℕ} (B : BooleanCircuit m) : Prop :=
  ∀ i : Fin N, B.eval (pointOf ν m i.val) = z i

theorem check_iff_checkAt (ν : ℕ) (z : BitInput (2 ^ ν)) {m : ℕ} (B : BooleanCircuit m) :
    Check ν z B ↔ CheckAt ν z B := by
  unfold Check CheckAt ttN
  constructor
  · intro h i
    exact congrFun h i
  · intro h
    funext i
    exact h i

instance (ν : ℕ) (z : BitInput (2 ^ ν)) {m : ℕ} (B : BooleanCircuit m) : Decidable (Check ν z B) := by
  unfold Check
  infer_instance

/-- **lem:succinct-verifier** (paper v2 app:multitape, lem:succinct-verifier (i)–(iii)): the verifier `𝒱_G` of
`L′ = {⟨B⟩_ν : tt_N(B) ∈ L_Tclk}` for the hierarchy `H` at clock `n^{k+2}`. It halts within `T(n)` on every input and
witness (`RunsInTime`, the hypothesis of input 6), accepts `⟨B⟩_ν` with some witness of length `T(L_ν)` exactly when the
hierarchy verifier accepts `tt_N(B)` (from the onset `onset` on), `T_G(L_ν) ≤ c_G N^{C_clk}`, and `T_G(L_ν)` is computable
from `1^ν` in time polynomial in `ν`. -/
structure SuccinctVerifier {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (G : ℕ) where
  V : OrdinaryVerifier
  T : ℕ → ℕ
  atLeast : ∀ n, n ≤ T n
  runs : Bindings.MW20.RunsInTime V T
  onset : ℕ
  language : ∀ (ν m : ℕ) (B : BooleanCircuit m), onset ≤ ν → 1 ≤ ν → ν ≤ m → SrcFits G ν B →
    (V.language T (instLength G ν) (srcBits G ν B) ↔ H.verifier.language H.time (2 ^ ν) (ttN ν B))
  timeCoefficient : ℕ
  timeBound : ∀ ν, onset ≤ ν → T (instLength G ν) ≤ timeCoefficient * (2 ^ ν) ^ (k + 2)
  /-- The weak machine hands `T_G(L_ν)` in binary to the imported constructor (input 6 reads `T(n)` in binary), so it
  must compute it: from `1^ν`, in time polynomial in `ν`. -/
  timeExp : ℕ
  timeWord : OrdinaryWordFunction ℕ (fun ν => List.replicate ν true) (fun ν => (T (instLength G ν)).bits)
    (fun ν => timeCoefficient * (ν + 1) ^ timeExp)

/-- The guessed pair `B = (B_src, B_pf)` on the native width `q` (paper §11.4: "Write B = (B_src, B_pf)"; `B_pf` has
`q` inputs and answers the oracle query `a` as `B_pf(a 0^{q−ℓ_out})`). -/
@[ext] structure OuterGuess (q : ℕ) where
  src : BooleanCircuit q
  pf : BooleanCircuit q

end NearCubicGates.Close.Outer
