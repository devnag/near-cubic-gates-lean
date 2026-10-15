import Proof.CaseAnalysis.WitnessSumGuard

/-! The executed sum-header flag is exactly the original canonical code
shape with the same actual arity and a bounded ordered list of term codes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumGuard
open LocalBitMultitape RadixSemantics CanonicalBinary CompetitorWitnessTriple
open PCPPNativeCanonicalTree
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem passes_code (bits arityBits : List Bool) (cap : ℕ) : Passes bits arityBits cap ↔
    ∃ codes,value bits=encodeTaggedList [encodeNat (value arityBits),encodeBalancedList codes] ∧
      codes.length ≤ cap:=by
  have ha:value (SumFields.arityCode bits)=field bits 1:=rfl
  have hl:value (SumFields.listCode bits)=field bits 3:=rfl
  constructor
  · rintro ⟨hh,hn,⟨codes,hcodes⟩,hc⟩
    have hshape: value bits=encodeTaggedList
        [value (SumFields.arityCode bits),value (SumFields.listCode bits)]:=
      (PairHeader.valid_iff bits).mp hh
    rw [←encodeNat_of_decode hn,←hcodes] at hshape
    refine ⟨codes,hshape,?_⟩
    simpa only [SumFields.count,SumFields.atoms,←hcodes,tree_atoms] using hc
  · rintro ⟨codes,hcode,hcount⟩
    obtain ⟨hshape,hq,hs⟩:=PairHeader.extracted_values bits _ _ hcode
    rw [←ha] at hq
    rw [←hl] at hs
    refine ⟨hshape,?_,⟨codes,hs.symm⟩,?_⟩
    · rw [hq,decodeNat_encode]
    · simpa only [SumFields.count,SumFields.atoms,hs,tree_atoms] using hcount

theorem accepted_atoms (bits arityBits : List Bool) (cap : ℕ) (h : Passes bits arityBits cap) :
    value bits=encodeTaggedList
      [encodeNat (value arityBits),encodeBalancedList (SumFields.atoms bits)] ∧
      (SumFields.atoms bits).length ≤ cap:=by
  obtain ⟨codes,hc,hn⟩:=(passes_code bits arityBits cap).mp h
  have hs:SumFields.atoms bits=codes:=by
    obtain ⟨_,_,hlist⟩:=PairHeader.extracted_values bits _ _ hc
    change value (SumFields.listCode bits)=encodeBalancedList codes at hlist
    simp only [SumFields.atoms,hlist,tree_atoms]
  rw [hs]
  exact ⟨hc,hn⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumGuard
