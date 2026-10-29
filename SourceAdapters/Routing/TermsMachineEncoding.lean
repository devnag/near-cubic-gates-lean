import SourceAdapters.Joins.TermsCircuit
import SourceAdapters.Routing.TermsMachinePrefixData
import SourceAdapters.Routing.CoordinateMachineOutput
import SourceAdapters.ShortPCP.TimeAddr
import Proof.Wire_3_5.UnionCodec

/-!
# Reduced constants and packed coordinate input

The construction in `lem:generator`: the circuit printer copies the actual reduced masks.
The constant-zero and constant-one gates and the row-major coefficient pack
agree with the field circuit's serialization.
-/

set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.TermsMachine

open NearCubicWires NearCubicWires.CanonicalBinary
open NearCubicWires.WireExponent3_5
open Joins ACSP RAMACSP Polynomial
open ShortPCP.Machines.FL

theorem termsMask_zero (p : TermsReq) (h : TermsOk p) : termsMask p h 0 = 0 := by
  unfold termsMask
  rw [map_zero]
  apply GF.toPoly_injective
  rw [GF.toPoly_ofPoly _ _ (by simp), GF.toPoly_zero]

theorem termsMask_one (p : TermsReq) (h : TermsOk p) : termsMask p h 1 = 1 := by
  have hf : 0 < p.f := by have := h.2.2.1; have := h.2.2.2; omega
  have hd : (1 : (ZMod 2)[X]).degree < p.irr.degree := by
    rw [degree_eq_natDegree h.1.ne_zero, h.2.1, degree_one]
    exact_mod_cast hf
  have hm : AdjoinRoot.modByMonicHom (modulus_monic h.1) (1 : Field2 p.irr) = 1 := by
    have hh := AdjoinRoot.modByMonicHom_mk (modulus_monic h.1) (1 : (ZMod 2)[X])
    have hmod : (1 : (ZMod 2)[X]) %ₘ p.irr = 1 :=
      (Polynomial.modByMonic_eq_self_iff (modulus_monic h.1)).mpr hd
    simpa only [map_one, hmod] using hh
  unfold termsMask
  rw [hm]
  apply GF.toPoly_injective
  rw [GF.toPoly_ofPoly _ _ (by simpa only [degree_one] using (show (0 : WithBot ℕ) < p.f by exact_mod_cast hf)),
    GF.toPoly_one]

theorem codeGate_termsMask (p : TermsReq) (h : TermsOk p) (g : ArithGate (Field2 p.irr)) :
    codeGate (termsMask p h) g = gateMask p.irr (modulus_monic h.1) p.f g := by
  cases g <;> rfl

def coordMasks (p : TermsReq) (h : TermsOk p) : List ℕ :=
  (List.finRange p.l.m).flatMap fun a =>
    (List.finRange p.l.m).map fun r => termsMask p h (termsCoeff p h a r)

theorem coordMasks_length (p : TermsReq) (h : TermsOk p) :
    (coordMasks p h).length = p.l.m * p.l.m := by
  simp [coordMasks, List.length_flatMap]

theorem coordMasks_lt (p : TermsReq) (h : TermsOk p) :
    ∀ c ∈ coordMasks p h, c < 2 ^ p.f := by
  intro c hc
  obtain ⟨a, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hc
  exact GF.ofPoly_lt _ _

theorem coordWord_eq (p : TermsReq) (h : TermsOk p) :
    termsCoordWord p h = (coordMasks p h).flatMap (WilliamsLoaderForms.fixedWidthNatBits p.f) := by
  simp only [termsCoordWord, coordMasks, List.flatMap_assoc, List.flatMap_map]

theorem bitsValue_fixedWidth_words (f : ℕ) (cs : List ℕ) (hc : ∀ c ∈ cs, c < 2 ^ f) :
    bitsValue (cs.flatMap (WilliamsLoaderForms.fixedWidthNatBits f)) = packW f cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      rw [List.flatMap_cons, ShortPCP.Time.bv_append,
        ih (fun d hd => hc d (by simp [hd]))]
      have hv : bitsValue (WilliamsLoaderForms.fixedWidthNatBits f c) = c := by
        change bitsValue (WilliamsPublishedForm.fixedWidthNatBits f c) = c
        rw [Transfer.bitsValue_fixedWidth, Nat.mod_eq_of_lt (hc c (by simp))]
      rw [hv]
      simp only [WilliamsLoaderForms.fixedWidthNatBits, List.length_ofFn, packW]

theorem packed_coordinates (p : TermsReq) (h : TermsOk p) :
    bitsValue (termsCoordWord p h) = packW p.f (coordMasks p h) := by
  rw [coordWord_eq]
  exact bitsValue_fixedWidth_words p.f (coordMasks p h) (coordMasks_lt p h)

end NearCubicGates.Adapters.Routing.TermsMachine
