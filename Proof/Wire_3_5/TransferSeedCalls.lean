import Proof.Wire_3_5.TransferPropagation
import Proof.Wire_3_5.TransferSeedMasks

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Shared (uMean bitR)

section SeedCalls
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)

/-- One primitive call on a tuple of four atoms of mode `m`, naming the carriers `cs` at the translation. -/
def tupleRequest {α : Type} (m : Mode) (q : ℕ) (circ : α → m.Circuit q) (t : Fin 4 → α)
    (cs : List (Stars.Carrier q)) (translation : List ℕ) : PrimRequest :=
  ⟨q, m, 4, le_rfl, fun k => circ (t k), cs, translation⟩

/-- The primitive's truth of one call is the tuple truth under the call's mask. -/
theorem truth_tupleRequest {α : Type} (m : Mode) (q : ℕ) (circ : α → m.Circuit q) (t : Fin 4 → α)
    (cs : List (Stars.Carrier q)) (translation : List ℕ) :
    I.truth (tupleRequest m q circ t cs translation) =
      tupleTruth (fun a x => m.eval (circ a) x)
        (fun (e : I.Seed m q) x => I.mask (tupleRequest m q circ t cs translation) e x) t := by
  unfold PrimitiveInputs.truth maskedMean tupleTruth uMean
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  have hcard : (Fintype.card (BitInput q) : ℝ) = 2 ^ q := by
    simp [BitInput, Fintype.card_pi]
  rw [Nat.cast_mul, hcard]
  rfl

/-- A `V`/`Q` call naming the one carrier of `X` is estimated at the mask `G_X`. -/
theorem tupleTruth_single {α : Type} (m : Mode) {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H)
    (carrier : PcppVar pcpp → Stars.Carrier q) (translation : List ℕ) (circ : α → m.Circuit q) (X : PcppVar pcpp)
    (t : Fin 4 → α) :
    I.truth (tupleRequest m q circ t [carrier X] translation) =
      tupleTruth (fun a x => m.eval (circ a) x) (carrierFilter I m pcpp carrier translation X) t := by
  rw [truth_tupleRequest]
  rfl

/-- A `μ` call naming the carriers of `X(i,1)`, `X(i,2)` is estimated at the clause mask `M_i`. -/
theorem tupleTruth_pair {α : Type} (m : Mode) {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H)
    (carrier : PcppVar pcpp → Stars.Carrier q) (translation : List ℕ) (circ : α → m.Circuit q)
    (i : Fin (2 ^ pcpp.clauseBits)) (t : Fin 4 → α) :
    I.truth (tupleRequest m q circ t [carrier (posVar pcpp i 0), carrier (posVar pcpp i 1)] translation) =
      tupleTruth (fun a x => m.eval (circ a) x) (clauseMask pcpp (carrierFilter I m pcpp carrier translation) i) t := by
  rw [truth_tupleRequest]
  unfold tupleTruth
  congr 1; funext p
  rw [clauseMask_carrierFilter I m pcpp carrier translation i p.1 p.2 4 le_rfl]
  rfl

variable {α : Type} [Fintype α] {m : Mode} {q : ℕ} {H : BooleanCircuit q} {pcpp : PointwisePCPP H}
variable {circ : α → m.Circuit q}

/-- **`|V̂ − V| ≤ (1+Λ̄)⁴ q^{−D}`** at the seed's primitive: `V̂` formed from `P.value` on the one-carrier calls. -/
theorem seed_propagated_V (P : FusedPrimitive I) {Λbar : ℝ} (hL : 0 ≤ Λbar)
    (f : AtomForms pcpp (fun a x => m.eval (circ a) x) Λbar) (carrier : PcppVar pcpp → Stars.Carrier q)
    (translation : List ℕ)
    (hcall : ∀ (pos : Fin (2 ^ pcpp.clauseBits) × Fin 2) j t,
      (polyV (f.sys (posVar pcpp pos.1 pos.2)) (f.wS (posVar pcpp pos.1 pos.2)) f.wOne
        (f.wE (posVar pcpp pos.1 pos.2))).coeff j t ≠ 0 →
      I.Call (tupleRequest m q circ t [carrier (posVar pcpp pos.1 pos.2)] translation)) :
    |f.Vhat (fun pos _ t => (P.value (tupleRequest m q circ t [carrier (posVar pcpp pos.1 pos.2)] translation) : ℝ)) -
        testV pcpp f.guess (carrierFilter I m pcpp carrier translation)| ≤
      (1 + Λbar) ^ 4 * (q : ℝ) ^ (-(I.D : ℝ)) := by
  refine propagated_V hL f _ _ _ (by positivity) fun pos j t hc => ?_
  have h := P.error _ (hcall pos j t hc)
  rw [tupleTruth_single] at h
  exact h

/-- **`|Q̂ − Q| ≤ (1+Λ̄)⁴ q^{−D}`** at the seed's primitive. -/
theorem seed_propagated_Q (P : FusedPrimitive I) {Λbar : ℝ} (hL : 0 ≤ Λbar)
    (f : AtomForms pcpp (fun a x => m.eval (circ a) x) Λbar) (carrier : PcppVar pcpp → Stars.Carrier q)
    (translation : List ℕ)
    (hcall : ∀ (pos : Fin (2 ^ pcpp.clauseBits) × Fin 2) j t,
      (polyQ (f.wS (posVar pcpp pos.1 pos.2)) f.wOne).coeff j t ≠ 0 →
      I.Call (tupleRequest m q circ t [carrier (posVar pcpp pos.1 pos.2)] translation)) :
    |f.Qhat (fun pos _ t => (P.value (tupleRequest m q circ t [carrier (posVar pcpp pos.1 pos.2)] translation) : ℝ)) -
        testQ pcpp f.guess (carrierFilter I m pcpp carrier translation)| ≤
      (1 + Λbar) ^ 4 * (q : ℝ) ^ (-(I.D : ℝ)) := by
  refine propagated_Q hL f _ _ _ (by positivity) fun pos j t hc => ?_
  have h := P.error _ (hcall pos j t hc)
  rw [tupleTruth_single] at h
  exact h

/-- **`|μ̂ − μ| ≤ (1+Λ̄)⁴ q^{−D}`** at the seed's primitive: `μ̂` formed from `P.value` on the two-carrier calls. -/
theorem seed_propagated_Mu (P : FusedPrimitive I) {Λbar : ℝ} (hL : 0 ≤ Λbar)
    (f : AtomForms pcpp (fun a x => m.eval (circ a) x) Λbar) (carrier : PcppVar pcpp → Stars.Carrier q)
    (translation : List ℕ)
    (hcall : ∀ (i : Fin (2 ^ pcpp.clauseBits)) j t,
      (polyMu (posNeg pcpp i 0) (posNeg pcpp i 1) (f.wS (posVar pcpp i 0)) (f.wS (posVar pcpp i 1))
        f.wOne).coeff j t ≠ 0 →
      I.Call (tupleRequest m q circ t [carrier (posVar pcpp i 0), carrier (posVar pcpp i 1)] translation)) :
    |f.μhat (fun i _ t =>
        (P.value (tupleRequest m q circ t [carrier (posVar pcpp i 0), carrier (posVar pcpp i 1)] translation) : ℝ)) -
        testMu pcpp f.guess (carrierFilter I m pcpp carrier translation)| ≤
      (1 + Λbar) ^ 4 * (q : ℝ) ^ (-(I.D : ℝ)) := by
  refine propagated_Mu hL f _ _ _ (by positivity) fun i j t hc => ?_
  have h := P.error _ (hcall i j t hc)
  rw [tupleTruth_pair] at h
  exact h

end SeedCalls

end NearCubicWires.WireExponent3_5.Transfer
