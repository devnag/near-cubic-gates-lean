import Proof.CaseAnalysis.RowsOriginalMonomialRun
import Proof.CaseAnalysis.RowsOriginalTerms
import Proof.CaseAnalysis.RowsOriginalTemplates

/-! Real arithmetic, rather than GF2 cancellation, interprets the actual
ordered original-term expansion. Coefficients stay attached to their atoms. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalMonomial
open CloseoutRowsEstimator CloseoutRowsRawProductLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def evaluate (atom : ℕ → ℝ) (p : List (List ℕ)) : ℝ :=
  (p.map (fun m=>(m.map atom).prod)).sum

theorem evaluate_product (atom : ℕ → ℝ) (a b : List (List ℕ)) :
    evaluate atom (product a b)=evaluate atom a*evaluate atom b := by
  induction a with
  | nil=>simp [product,evaluate]
  | cons m a ih=>
    simp only [product,List.flatMap_cons,evaluate,List.map_append,List.sum_append] at ih ⊢
    rw [ih]
    simp only [List.map_map,Function.comp_def,List.map_append,List.prod_append,List.sum_map_mul_left]
    simp only [List.map_cons,List.sum_cons]
    ring

def atom (cs : List (List (List ℕ))) (i : ℕ) := cs[i]?.getD []

theorem atom_eq (cs : List (List (List ℕ))) (i : ℕ) (hi : i < cs.length) : atom cs i=cs[i] := by
  simp [atom,List.getElem?_eq_getElem hi]

theorem evaluate_value (a : ℕ → ℝ) (cs : List (List (List ℕ))) (m : List ℕ) (valid : Valid cs m)
    (acc : List (List ℕ)) : evaluate a (value cs m valid acc)=
      evaluate a acc*(m.map (fun i=>evaluate a (atom cs i))).prod := by
  induction m generalizing acc with
  | nil=>simp [value]
  | cons i m ih=>
    have hi : i < cs.length:=valid i (by simp)
    rw [value,ih]
    change evaluate a (product acc cs[i])*_= _
    rw [evaluate_product]
    simp only [List.map_cons,List.prod_cons,atom_eq cs i (valid i (by simp))]
    ring

theorem value_degree (cs : List (List (List ℕ)))
    (hc : ∀ p∈cs,∀ l∈p,l.length=1) (m : List ℕ) (valid : Valid cs m)
    (acc : List (List ℕ)) (k : ℕ) (ha : ∀ l∈acc,l.length=k) :
    ∀ l∈value cs m valid acc,l.length=k+m.length := by
  induction m generalizing acc k with
  | nil=>simpa [value] using ha
  | cons i m ih=>
    have hi : i < cs.length:=valid i (by simp)
    have hp : ∀ l∈CloseoutRowsOriginalFactor.value cs i (valid i (by simp)) acc,l.length=k+1 := by
      intro l hl
      obtain ⟨x,hx,hxy⟩:=List.mem_flatMap.mp hl
      obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hxy
      rw [List.length_append,ha x hx,hc cs[i] (List.getElem_mem _) y hy]
    simpa only [value,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (fun j hj=>valid j (by simp [hj])) _ (k+1) hp

theorem cache_singletons (offset : ℕ) (ns : List ℕ) :
    ∀ p∈CloseoutRowsRawAtomCache.cache offset ns,∀ l∈p,l.length=1 := by
  induction ns generalizing offset with
  | nil=>simp [CloseoutRowsRawAtomCache.cache]
  | cons n ns ih=>
    intro p hp l hl
    rcases List.mem_cons.mp hp with rfl|hp
    · obtain ⟨j,_,rfl⟩:=List.mem_map.mp hl
      rfl
    · exact ih (offset+n) p hp l hl

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalMonomial
