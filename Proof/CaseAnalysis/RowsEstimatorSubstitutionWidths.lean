import Proof.CaseAnalysis.RowsEstimatorSubstitutionMeaning

/-! Logical word bounds preserve one expansion-count factor throughout the fold. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionBounds
open CanonicalFourfoldRowProgram CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Width (p : StructuralGF2Polynomial) (L : ℕ) : Prop:=∀ l∈p,(l.flatMap ExtIncidence.block).length ≤ L

theorem word_length (p : StructuralGF2Polynomial) (L : ℕ) (h : Width p L) :
    (ExtIncidence.stream p).length ≤ p.length*(L+2)+1 := by
  induction p with
  | nil=>simp [ExtIncidence.stream]
  | cons l p ih=>
    have hl:=h l (by simp)
    have ht:=ih (fun m hm=>h m (by simp [hm]))
    rw [ExtIncidence.stream_cons,List.length_append,ExtIncidence.monomialWord_length,List.length_cons]
    nlinarith

theorem width_mul (a b : StructuralGF2Polynomial) (L W : ℕ) (ha : Width a L) (hb : Width b W) :
    Width (structuralGF2Mul a b) (L+W) := by
  intro l hl
  obtain ⟨x,hx,hxy⟩:=List.mem_flatMap.mp hl
  obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hxy
  simpa only [List.flatMap_append,List.length_append] using Nat.add_le_add (ha x hx) (hb y hy)

theorem width_of_stream (p : StructuralGF2Polynomial) (W : ℕ) (h : (ExtIncidence.stream p).length ≤ W) :
    Width p W := by
  intro l hl
  have hm:=CloseoutRowsRawProductBudget.monomial_le p l hl
  omega

theorem pair_word (cs : List Pair) (p : Pair) (hp : p∈cs) : (word p).length ≤ (cacheWord cs).length := by
  induction cs with
  | nil=>simp at hp
  | cons c cs ih=>
    rcases List.mem_cons.mp hp with rfl|hp
    · simp only [cacheWord,List.flatMap_cons,List.length_append];omega
    · have ht:=ih hp
      simp only [cacheWord,List.flatMap_cons,List.length_append] at ht ⊢;omega

theorem atom_word (cs : List Pair) (i : ℕ) (hi : i<cs.length) :
    (ExtIncidence.stream (cs[i].1++cs[i].2)).length ≤ (cacheWord cs).length := by
  have hw:=pair_word cs cs[i] (List.getElem_mem hi)
  simp only [word,ExtIncidence.stream,List.flatMap_append,List.length_append,List.length_singleton] at hw ⊢
  omega

structure Shape (B W k : ℕ) (p : StructuralGF2Polynomial) : Prop where
  count : p.length ≤ B^k
  width : Width p (k*W)

theorem unit_shape (B W : ℕ) : Shape B W 0 [[]] := by
  constructor
  · simp
  · intro l hl;simp at hl;subst l;simp

theorem shape_mul (B W k : ℕ) (acc atom : StructuralGF2Polynomial)
    (h : Shape B W k acc) (hc : atom.length ≤ B) (hw : Width atom W) :
    Shape B W (k+1) (structuralGF2Mul acc atom) := by
  constructor
  · rw [CloseoutRowsRawOccurrenceBound.mul_length,pow_succ]
    exact Nat.mul_le_mul h.count hc
  · simpa only [Nat.add_mul,Nat.one_mul] using width_mul acc atom (k*W) W h.width hw

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionBounds
