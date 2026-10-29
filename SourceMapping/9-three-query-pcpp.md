# 9. Three-query proximity and an efficient linear encoder

[Mapping index](README.md) · derived field `threeQueryPCPP` · two published premises

[`Assembly.field9Encoder`](../SourceAdapters/Assembly/Field9Encoder.lean) proves
`PerfectThreeQueryProximityLiteral ∧ EfficientLinearEncoder`. Its premises are exactly
`NearCubicGates.Published.CW19Proximity.Lemma22Half` and `NearCubicGates.Published.CW19Code.Lemma26` in
[Statement.lean](../Statement.lean). Lemmas 24 and 27 describe derived constructions; they are not the retained
source leaves.

Source: L. Chen and R. R. Williams, *Stronger Connections Between Circuit Analysis and Circuit Lower Bounds, via
PCPs of Proximity*, CCC 2019, LIPIcs 137, article 19,
[doi:10.4230/LIPIcs.CCC.2019.19](https://doi.org/10.4230/LIPIcs.CCC.2019.19). Definition 20 and Lemma 22 are on
printed p.19:15, Lemma 26 on p.19:16, and the nonadaptive address/decision construction is in Appendix A,
pp.19:38–19:39. Pinned PDF SHA-256:
`c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533`.

## Source proximity and its conversion

At each fixed rational proximity η in (0,1), `Lemma22Half` supplies a constant query bound, logarithmic
randomness, perfect completeness, soundness at most 1/2 and a uniform polynomial-time honest-proof algorithm.
Input coordinates and proof addresses are distinct. Addresses and the decision predicate depend on the circuit
and coins, not on answers. The source's far condition is **strict**: distance from every accepted input exceeds
η. The source statement does not assume a table of three-literal clauses or the final dense proof-address codec.

[`Proximity.perfect_three_query_proximity`](../SourceAdapters/Proximity/Perfect.lean) proves the target
three-query interface. Clause conversion, enumeration of the bounded random strings, sorting and removing unused
proof addresses, restriction of the honest proof, output serialization and the required machine conversions are
proved. The target's non-strict distance boundary is handled by choosing a smaller source proximity; equality at
the target threshold is not silently attributed to the source. The polynomial proof-length bound follows from
the constructed finite schedule of queried addresses, not an extra assumed proof-length guarantee.

## Source code and its conversion

`Lemma26` supplies one constant-rate binary linear code family beyond an onset, a fixed positive minimum
relative distance, an efficient encoder and a promised decoder. The ordinary encoder reads the message; the
decoder reads unary message length, a separator and the received word. Both algorithms and their polynomial
constants are fixed before all messages. The decoder's termination and correctness are required only near a
codeword. A source decoding radius may be decreased to obtain the closed promised radius in the formal
statement; no total behavior outside that promise is assumed.

[`Code.efficientLinearCode_of_lemma26`](../SourceAdapters/Code/Source.lean) proves the stronger
`EfficientLinearCodeLiteral`: the three-block construction, parity supports of size at most half the message
length, constant rate, positive distance, a closed target decoding radius, total decoding, finite-length patches
and both polynomial-time machine witnesses. Totalization uses a paid bounded run with a default output. It does
not replace the promised source decoder by an unproved total-decoder hypothesis.

The main theorem needs only the encoder part of that result. `Assembly.encoder_of_code` projects it to
`EfficientLinearEncoder`; `field9Encoder` combines it with the three-query proximity theorem. In the
[gadget reduction](../Proof/Gates/Gadget/ThreeQuery.lean), the verifier tests the relation y = (x,Enc(x)) with
D(x)=1. For a rejected x, any accepted pair has a different prefix, so code distance gives proximity soundness.
For an accepted x, perfect completeness and the honest proof apply. This systematic relation never calls the
decoder. The current [paper](../paper/paper.tex) labels are `imp:three-pcpp` and `sec:gadget-transfer`.

Check separately the strict source proximity, the target distance boundary, uniform honest-proof construction,
the promised source decoder, the proved total decoder and the final encoder-only consumer. Conflating these
interfaces would hide precisely the conversions the adapters establish.
