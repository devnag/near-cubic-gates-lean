import Proof.Amplification.XorResources

/-! The tested sharper consumer of the unchanged XOR source. The numeric
coefficient cap is polynomial in the actual base arity for fixed delta/k;
the source's term count and constant coefficient mass remain unchanged. -/
namespace NearCubicWires.RepairSource.CloseoutXor
open SourceInterfaces ExecutableInterfaces RepairRepresentation RepairXor
open ValidatorLeafWidthCore
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cap (delta : ℚ) (n k : ℕ) : ℕ :=
  32*(n+1)*delta.den^(3*k+2)

theorem sampleForm_magnitudes (delta : ℚ) (hd : 0 < delta) (hh : delta < 1/2)
    {n k : ℕ} (terms : List (ℚ × BoolFunction n)) (form : SampleForm delta n k terms) :
    ∀ term ∈ terms, term.1.num.natAbs ≤ cap delta n k ∧ term.1.den ≤ cap delta n k := by
  cases form with
  | direct atom =>
    intro term hterm
    have he : term=(1,atom) := List.mem_singleton.mp hterm
    subst term
    have hp : 0 < cap delta n k := by unfold cap; positivity
    have hb : 1 ≤ cap delta n k := hp
    simpa using And.intro hb hb
  | affine j hj hjk atoms hcount one _hone =>
    have hb:=affine_coefficient_magnitudes delta hd hh n j hj
    have hmono : 32*(n+1)*delta.den^(3*j+2) ≤ cap delta n k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right delta.pos (by omega))
    intro term hterm
    rcases List.mem_append.mp hterm with hsample | hconstant
    · obtain ⟨atom,_hatom,rfl⟩:=List.mem_map.mp hsample
      simpa only [hcount] using And.intro (hb.1.1.trans hmono) (hb.1.2.trans hmono)
    · have he : term=((1-alphaQ delta j)/2,one) := List.mem_singleton.mp hconstant
      subst term
      exact ⟨hb.2.1.trans hmono,hb.2.2.trans hmono⟩

theorem xor_consumer_sharp (source : XorSource)
    (delta : ℚ) (hd : 0 < delta) (hh : delta < 1/2)
    (family : SizedFunctionFamily) (hprojection : LiteralProjectionClosed family)
    (hnegation : NegationClosedFamily family) {n : ℕ} (f : BoolFunction n)
    (hn : 1 ≤ n) (k size : ℕ) (hk : 1 ≤ k)
    (hfar : FarFromCircuitSums family f size (xorTermBound delta n k)
      (natBitLength (cap delta n k)) (1/xorEpsilon (delta : ℝ) k) (delta : ℝ))
    (candidate : BoolFunction (k*n)) (hcandidate : family (k*n) candidate size) :
    agreement candidate (xorPower f k) ≤ 1/2+xorEpsilon (delta : ℝ) k := by
  by_contra h
  obtain ⟨w⟩:=source delta hd hh family hprojection hnegation f hn k size hk
    candidate hcandidate (lt_of_not_ge h)
  obtain ⟨hterms,_hbits,hmass⟩:=sampleForm_resources delta hd hh hn w.sum.terms w.form
  have hsharp : w.sum.coefficientsWithinBitBound (natBitLength (cap delta n k)) := by
    intro term hterm
    obtain ⟨ha,hb⟩:=sampleForm_magnitudes delta hd hh w.sum.terms w.form term hterm
    exact ⟨natBitLength_mono ha,natBitLength_mono hb⟩
  exact (not_lt_of_ge w.close) (hfar w.sum hterms hsharp hmass)

end NearCubicWires.RepairSource.CloseoutXor
