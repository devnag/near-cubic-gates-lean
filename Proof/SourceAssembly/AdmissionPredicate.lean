import Proof.CaseAnalysis.RawRowsDescriptions
import Proof.CaseAnalysis.FinalNaturalModeAtoms
import Proof.CaseAnalysis.FinalSiteWireEnvelope

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode
open NearCubicWires.RepairSource.CloseoutFinal.C10NaturalModeAtoms
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity

noncomputable section

/-- The carried per-atom wire cap at reciprocal coefficient `den` and log exponent `e`: exactly the
capped decoder's `wireCap` (`CappedDecode.symLimits` passes `⌊wireScale (1/den) 5 w⌋₊`, `thrLimits`
`⌊wireScale (1/den) 9 w⌋₊`) at arity `q = w`. -/
abbrev carriedWireCap (den e q : ℕ) : ℕ := ⌊wireScale (1 / (den : ℝ)) e q⌋₊

/-- The capped decoder's SYM description cap (`CloseoutSampledWitness.symmetricLimits` at
`r = clauseWidth degree q`), which is `CloseoutRawRows.symmetricDescription` at the carried cap. -/
abbrev carriedSymDescription (den degree q : ℕ) : ℕ :=
  RepairSource.CloseoutRawRows.symmetricDescription q
    (q + RepairSource.CloseoutLanguage.clauseWidth degree q + 1) (carriedWireCap den 5 q)

/-- The capped decoder's THR description cap (`CloseoutSampledWitness.thresholdLimits`). -/
abbrev carriedThrDescription (den degree q : ℕ) : ℕ :=
  RepairSource.CloseoutRawRows.thresholdDescription q
    (q + RepairSource.CloseoutLanguage.clauseWidth degree q + 1) (carriedWireCap den 9 q)

/-- **Per-atom admission** (`paper.tex:4292-4305`): a guessed atom passed the capped decoder's
wire and description envelope; a systematic atom is source-explicit and carries no premise. -/
def AtomAdmitted (den degree : ℕ) {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} : Atom pcpp → Prop
  | .systematic _ => True
  | .symmetric c => c.wireCount ≤ carriedWireCap den 5 q ∧
      c.descriptionBits ≤ carriedSymDescription den degree q
  | .threshold c => c.wireCount ≤ carriedWireCap den 9 q ∧
      c.descriptionBits ≤ carriedThrDescription den degree q

/-- **The admitted supplier request** (`paper.tex:721-733`, `:1368-1377`, `:3520-3527`,
`:4292-4305`): at most four atoms, each inside the capped decoder's per-atom envelope at carried
coefficient `1/den` and clause degree `degree`.  The request the source actually makes is
`Packets.request sources L target mode atoms` (either mode). -/
structure Admitted (den degree : ℕ) {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} (atoms : List (Atom pcpp)) : Prop where
  four : atoms.length ≤ 4
  envelope : ∀ atom ∈ atoms, AtomAdmitted den degree atom

/-! ## Non-vacuity: the source's own singleton systematic requests are admitted -/

/-- Every list of at most four systematic atoms is admitted, at every `den` (the carried
singleton `SourceAssemblySingletonRequest.request` is of this shape). -/
theorem admitted_systematic (den degree : ℕ) {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} (indices : List (Fin pcpp.systematicBits))
    (hfour : indices.length ≤ 4) :
    Admitted den degree (indices.map (Atom.systematic (pcpp := pcpp))) := by
  refine ⟨by simpa using hfour, ?_⟩
  · intro atom hatom
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hatom
    trivial

/-! ## The native circuits the request carries -/

/-- The SYM native parity circuit on any support has at most `q*(q+1)` wires. -/
theorem parity_sym_wires {q : ℕ} (S : Finset (Fin q)) :
    (normalizedParityCircuit S).wireCount ≤ q * (q + 1) := by
  rw [C10SiteWireEnvelope.normalizedParityCircuit_wireCount S]
  have hcard : S.card ≤ q := by simpa using Finset.card_le_univ S
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    omega
  · nlinarith

/-- SYM mode: every native circuit of the request is under `max (q*(q+1)) (carried cap)`
(parity, including the wrong-mode `normalizedParityCircuit ∅`: `2|S| ≤ q*(q+1)`,
`C10SiteWireEnvelope.normalizedParityCircuit_wireCount`). -/
theorem Admitted.sym_wires {den degree : ℕ} {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} {atoms : List (Atom pcpp)}
    (h : Admitted den degree atoms) :
    ∀ c ∈ atoms.map nativeSymmetricAtom,
      c.wireCount ≤ max (q * (q + 1)) (carriedWireCap den 5 q) := by
  intro c hc
  obtain ⟨atom, hatom, rfl⟩ := List.mem_map.mp hc
  have he := h.envelope atom hatom
  cases atom with
  | systematic index => exact (parity_sym_wires (pcpp.systematicSupport index)).trans (le_max_left _ _)
  | symmetric c => exact he.1.trans (le_max_right _ _)
  | threshold c => exact (parity_sym_wires ∅).trans (le_max_left _ _)

/-- THR mode: every native circuit of the request is under `max (q*(q+1)) (carried cap)`
(parity, including the wrong-mode `normalizedThresholdParityCircuit ∅`: `|S|(|S|+1) ≤ q*(q+1)`,
`C10NaturalModeAtoms.nativeThresholdParity_wires_le`). -/
theorem Admitted.thr_wires {den degree : ℕ} {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} {atoms : List (Atom pcpp)}
    (h : Admitted den degree atoms) :
    ∀ c ∈ atoms.map nativeThresholdAtom,
      c.wireCount ≤ max (q * (q + 1)) (carriedWireCap den 9 q) := by
  intro c hc
  obtain ⟨atom, hatom, rfl⟩ := List.mem_map.mp hc
  have he := h.envelope atom hatom
  cases atom with
  | systematic index =>
    exact (nativeThresholdParity_wires_le (pcpp.systematicSupport index)).trans (le_max_left _ _)
  | threshold c => exact he.1.trans (le_max_right _ _)
  | symmetric c => exact (nativeThresholdParity_wires_le ∅).trans (le_max_left _ _)

/-- The native request has at most four circuits in either mode. -/
theorem Admitted.four_sym {den degree : ℕ} {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} {atoms : List (Atom pcpp)}
    (h : Admitted den degree atoms) : (atoms.map nativeSymmetricAtom).length ≤ 4 := by
  simpa using h.four

theorem Admitted.four_thr {den degree : ℕ} {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} {atoms : List (Atom pcpp)}
    (h : Admitted den degree atoms) : (atoms.map nativeThresholdAtom).length ≤ 4 := by
  simpa using h.four

end
end NearCubicWires.Admission
