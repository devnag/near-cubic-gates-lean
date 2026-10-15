import StatementSupport

set_option autoImplicit false

namespace NearCubicGates.PublishedSources.PCPP

open NearCubicWires
open NearCubicWires.SourceInterfaces
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource
open NearCubicWires.Bindings.CLW20Lemma311

/-- Literal projection short-PCP input. Ordinary addressed-table conversion
and uniform choice of the hierarchy machine remain local obligations. -/
abbrev ProjectionShortPCPLiteral : Prop :=
  NearCubicWires.Bindings.CLW20Lemma310TM2.CLW20_Lemma3_10_TM2

/-- Separate periodic addition. CLW3.11 already states pointwise semantics
and a power-of-two number of clauses. Rational gap reduction and ordinary
execution remain local. This input is not part of the nine main inputs. -/
abbrev PeriodicTwoQueryAdditionLiteral : Prop :=
  NearCubicWires.Bindings.CLW20Lemma311TM2.CLW20_Lemma3_11_explicitEnc_TM2

end NearCubicGates.PublishedSources.PCPP
