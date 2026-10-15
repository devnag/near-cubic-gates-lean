import Proof.Gates.Setup.Entry

set_option autoImplicit false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Worker (width gadgets)

/-- **Split point (half 1, `compU`).** The composite with one exponent for every parameter choice `g` (its cost is
polynomial in its input, the word of `C_{⟨B_src⟩_ν}` and the descriptor of `B_pf`, with an exponent fixed by `P`'s and the
substitution's exponents only). -/
def CompU (s : GateSources) (P : ThreeQueryPCPP) : Prop :=
  ∃ E : ℕ, ∀ g : GateParams, ∃ cf : CompFull s P g, cf.e ≤ E

def SetupU (s : GateSources) (P : ThreeQueryPCPP) : Prop :=
  ∃ E0 : ℕ, ∀ (g : GateParams) (tc N1 : ℕ), ∃ D : SetupData s P g, (∃ prog : WMX (nsW D) nrW, SetupSpec D prog) ∧
    D.tc = tc ∧ N1 ≤ D.N0 ∧
    (∃ Ca : ℕ, ∀ (N : ℕ) (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N)),
      D.N0 ≤ N → N / 16 + 1 ≤ pad →
      Worker.Decodes (width s g N) (guessWord N bits pad) B →
      auxN s P g x B + gadgets s g N ≤ Ca * (N + 1) ^ E0) ∧
    ∀ (padF : ℕ → ℕ) (Cp ep : ℕ), (∀ N, N / 16 + 1 ≤ padF N) → (∀ N, padF N ≤ Cp * (N + 1) ^ ep) →
      ∃ Fs : ℕ → ℕ,
        (∀ (N : ℕ) (x : BitInput N) (bits : List Bool), rejectCost D x bits (padF N) ≤ Fs N) ∧
        (∀ (N : ℕ) (x : BitInput N) (bits : List Bool) (B : Outer.OuterGuess (width s g N)), D.N0 ≤ N →
          Worker.Decodes (width s g N) (guessWord N bits (padF N)) B →
          setupCost D x bits (padF N) B ≤ Fs N) ∧
        ∃ C onset : ℕ, ∀ N, onset ≤ N → Fs N ≤ C * (N + 1) ^ (E0 * (ep + 1))

/-- **The set-up's deliverable**: the set-up (its program with `SetupSpec`, and the uniform cost exponent) for every
source bundle and PCPP. -/
def SetupSupply : Prop := ∀ (s : GateSources) (P : ThreeQueryPCPP), SetupU s P

end NearCubicGates.Close.Setup
