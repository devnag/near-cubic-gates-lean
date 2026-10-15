import Proof.Wire_3_5.TransferTests
import Proof.Wire_3_5.Skeleton

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost

section SeedMasks
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)

/-- A request in mode `m` at length `q` naming the given carriers at the given translation, with no circuits (the
mask of a request depends only on its mode, length, carriers and translation). -/
def maskRequest (m : Mode) (q : ℕ) (carriers : List (Stars.Carrier q)) (translation : List ℕ) : PrimRequest :=
  ⟨q, m, 0, Nat.zero_le 4, Fin.elim0, carriers, translation⟩

/-- `G_X(e,x)` in mode `m`: the seed's regular filter of the carrier of `X` at the common translation and seed. -/
noncomputable def carrierFilter (m : Mode) {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H)
    (carrier : PcppVar pcpp → Stars.Carrier q) (translation : List ℕ) :
    PcppVar pcpp → I.Seed m q → BitInput q → Bool :=
  fun X e x => I.mask (maskRequest m q [carrier X] translation) e x

/-- A call in mode `m` naming one carrier, with any circuits, has the mask of that carrier. -/
theorem mask_single {q : ℕ} (m : Mode) (a : ℕ) (ha : a ≤ 4) (circuits : Fin a → m.Circuit q)
    (c : Stars.Carrier q) (translation : List ℕ) (e : I.Seed m q) (x : BitInput q) :
    I.mask ⟨q, m, a, ha, circuits, [c], translation⟩ e x = I.mask (maskRequest m q [c] translation) e x := rfl

theorem mask_pair {q : ℕ} (m : Mode) (a : ℕ) (ha : a ≤ 4) (circuits : Fin a → m.Circuit q)
    (c c' : Stars.Carrier q) (translation : List ℕ) (e : I.Seed m q) (x : BitInput q) :
    I.mask ⟨q, m, a, ha, circuits, [c, c'], translation⟩ e x =
      (I.mask (maskRequest m q [c] translation) e x && I.mask (maskRequest m q [c'] translation) e x) := by
  unfold PrimitiveInputs.mask maskRequest
  by_cases h : I.StarAt q
  · simp only [dif_pos h, List.all_cons, List.all_nil, Bool.and_true]
  · simp only [dif_neg h, Bool.and_self]

/-- The clause mask of the tests at the seed's filters is the mask of the clause's two-carrier call. -/
theorem clauseMask_carrierFilter (m : Mode) {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H)
    (carrier : PcppVar pcpp → Stars.Carrier q) (translation : List ℕ) (i : Fin (2 ^ pcpp.clauseBits))
    (e : I.Seed m q) (x : BitInput q) (a : ℕ) (ha : a ≤ 4) (circuits : Fin a → m.Circuit q) :
    clauseMask pcpp (carrierFilter I m pcpp carrier translation) i e x =
      I.mask ⟨q, m, a, ha, circuits, [carrier (posVar pcpp i 0), carrier (posVar pcpp i 1)], translation⟩ e x := by
  rw [mask_pair]
  rfl

/-- `tr:soundness` at the seed's seed space in mode `m`. -/
theorem seedMaskedVerifierTrace_empty (m : Mode) {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H) {cp sp : ℝ}
    (params : MaskedSoundnessParameters cp sp)
    (hsound : ∀ x, ¬ H.eval x → ∀ aux, pcpp.satisfiedFraction x aux ≤ sp)
    (houter : Shared.uMean (fun x : BitInput q => Shared.bitR (H.eval x)) ≤ params.outerError) :
    IsEmpty (MaskedVerifierTrace pcpp params (I.Seed m q)) :=
  maskedVerifierTrace_empty pcpp params hsound houter

end SeedMasks

end NearCubicWires.WireExponent3_5.Transfer
