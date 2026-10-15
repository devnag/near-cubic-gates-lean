import Proof.Amplification.RecoveryFrontBound

/-! Choose the bounded flat certificate with its outer rows also in the first
table. The physical checker can always use that first table. This changes
only the existential completeness witness, not any input-code semantics,
parser, serialized layout, or arbitrary-accepting-run soundness premise. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate
open CanonicalBinary BalancedCNFSATEncoding BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selectedInner (formula : EncodedCNF) (inner outer : List Row) : List Row :=
  match formula with
  | [[],[(true,_)]] => outer
  | [[],[(true,_)],[(false,_),(true,_)]] => outer
  | _ => inner

def selected (c : Certificate) : Certificate :=
  { c with inner := selectedInner (RawSyntaxCertificate.project c.view) c.inner c.outer }

theorem selectedInner_cases (formula : EncodedCNF) (inner outer : List Row) :
    selectedInner formula inner outer=inner ∨ selectedInner formula inner outer=outer := by
  unfold selectedInner
  split <;> simp

theorem markerCheck_selectedInner (formula : EncodedCNF) (table : FiniteValuation.Table)
    (inner outer : List Row) :
    markerCheck formula table (selectedInner formula inner outer) outer=
      markerCheck formula table inner outer := by
  unfold markerCheck
  split <;> simp_all [selectedInner]

theorem formulaCheck_selectedInner (code : Nat) (formula : EncodedCNF)
    (table : FiniteValuation.Table) (inner outer : List Row) :
    formulaCheck code formula table (selectedInner formula inner outer) outer=
      formulaCheck code formula table inner outer := by
  unfold formulaCheck
  split
  · rfl
  · exact markerCheck_selectedInner formula table inner outer

theorem check_selected (code : Nat) (c : Certificate) :
    check code (selected c)=check code c := by
  simp only [check,selected,formulaCheck_selectedInner]

theorem Fits.selected {code : Nat} {c : Certificate} (h : Fits code c) :
    Fits code (selected c) := by
  refine ⟨h.1,?_⟩
  change DataFits code c.table
    (selectedInner (RawSyntaxCertificate.project c.view) c.inner c.outer) c.outer
  rcases selectedInner_cases (RawSyntaxCertificate.project c.view) c.inner c.outer with hi|ho
  · rw [hi]; exact h.2
  · rw [ho]
    refine ⟨h.2.1,h.2.2.1,?_,h.2.2.2.2.1,?_⟩
    · have hn : 1≤natBitLength code := by unfold natBitLength; omega
      have hl := h.2.2.2.2.1
      omega
    · intro row hm
      have hm' : row∈c.outer := by simpa using hm
      exact h.2.2.2.2.2 row (List.mem_append_right _ hm')

theorem selected_idempotent (c : Certificate) : selected (selected c)=selected c := by
  unfold selected
  congr 1
  unfold selectedInner
  split <;> simp_all

theorem bounded_selected_certificate (code : Nat) :
    correctedSat code=true ↔ ∃ c : Certificate,
      check code c=true ∧ Fits code c ∧ selected c=c := by
  constructor
  · intro hs
    obtain ⟨c,hc,hf⟩ := (bounded_certificate code).mp hs
    exact ⟨selected c,(check_selected code c).trans hc,hf.selected,selected_idempotent c⟩
  · rintro ⟨c,hc,_,_⟩
    exact check_sound code c hc

theorem selected_flat_rows (c : Certificate) (hs : selected c=c) (payload : Nat)
    (hf : RawSyntaxCertificate.project c.view=[[],[(true,payload)]]) : c.inner=c.outer := by
  have hi := congrArg Certificate.inner hs
  simpa only [selected,hf,selectedInner] using hi.symm

theorem selected_flat_prefix_rows (c : Certificate) (hs : selected c=c)
    (payload committed count : Nat)
    (hf : RawSyntaxCertificate.project c.view=
      [[],[(true,payload)],[(false,committed),(true,count)]]) : c.inner=c.outer := by
  have hi := congrArg Certificate.inner hs
  simpa only [selected,hf,selectedInner] using hi.symm

theorem bounded_selected_word (code : Nat) (hs : correctedSat code=true) :
    ∃ c : Certificate, Fits code c ∧ selected c=c ∧
      (TableFirst.pack (Serialization.width code) c).length≤128*(natBitLength code+1)^3 ∧
      TableFirst.checkWord code (TableFirst.pack (Serialization.width code) c)=true := by
  obtain ⟨c,hc,hf,hsel⟩ := (bounded_selected_certificate code).mp hs
  exact ⟨c,hf,hsel,TableFirst.pack_bound code c hf,
    (TableFirst.checkWord_pack code c hf).trans hc⟩

end NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate
