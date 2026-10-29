import Proof.Gates.Main.Amplifier
import Proof.Gates.Outer.Source
import Proof.Gates.Outer.Supply
import Bindings.CLW20_Lemma3_10_Wrapper
import Bindings.CLW20_Lemma3_8

/-!
# The source bundle of the gate chain

The gate chain is parametrized by `GateSources`, built here field by field from `NineInputs` by proved adapters. The
broader bundle `NearCubicWires.RepairSource.EightSources`, which also contains the expander bound (HLW06), the prime
θ bound (RS62), CW19 Proposition 18(2) and the two-query PCPP (CLW20 Lemma 3.11), is never instantiated: none of
those is an input of the main theorem. The XOR lemma is proved (`CLW20Lemma38.clw20_xor_source`) and costs no input.
-/

set_option autoImplicit false

namespace NearCubicGates.Close

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.SourceInterfaces
open NearCubicWires.RepairRepresentation

/-- The internal source objects the gate chain consumes, one per published input. -/
structure GateSources : Prop where
  normalization : ThresholdNormalizationContract
  williams : WilliamsSource
  /-- Input 6 (Murray–Williams' short PCP as an oracle circuit), in the ordinary model (`imp:short-pcp`). -/
  mw : NearCubicGates.Close.Outer.MWSource

  succinct : NearCubicGates.Close.Outer.SuccinctSupply
  hierarchyRefuter : HierarchyRefuterSource
  xor : XorSource
  amplifier : Nonempty SourceAmplifierFactory
  restriction : NearCubicGates.PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction
  bernstein : NearCubicGates.PublishedSources.Witness.Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0}
  primes : NearCubicGates.PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem
  threeQueryPCPP : NearCubicGates.PublishedSources.PCPP.ThreeQuerySourceGroup

theorem gateSources_of_inputs (h : NineInputs) (hs : NearCubicGates.Close.Outer.SuccinctSupply) : GateSources where
  normalization := NearCubicWires.Bindings.CTW26.ctw26_to_import h.normalization
  williams := NearCubicWires.Bindings.Williams14.williams14_to_import h.rectangularProduct
  mw := NearCubicGates.Close.Outer.mwSource_of_ordinary h.shortPCP
  succinct := hs
  hierarchyRefuter := NearCubicWires.Bindings.CLW20Theorem113.clw20_theorem1_13_to_import h.refuter
  xor := NearCubicWires.Bindings.CLW20Lemma38.clw20_xor_source
  amplifier := Amplifier.amplifier_of_multitape h.amplification
  restriction := h.restriction
  bernstein := h.bernstein
  primes := h.primes
  threeQueryPCPP := h.threeQueryPCPP

end NearCubicGates.Close
