import Proof.MachineModel.ClosureCompactFamily
import Proof.MachineModel.ClosureCompactMetadataCost
import Proof.MachineModel.ClosureCompactPreparationCost
import Proof.MachineModel.ClosureCompactNativeBudget

/-! A.12 preparation costs are additive. This bounds the exact budget consumed
by `CompactColdFamily.family_run`, including metadata construction and fanout.
The only exponential factor is the existing digit enumeration; there is no
residual-table factor and the bank capacity occurs only to the first power.
The common source envelope X remains an explicit premise. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactColdCost
open RepairOrdinary RepairRepresentation ExtIncidence

/-- The seven source quantities are n, child count, encoded cache length,
radix, compact field width, Q and w. Raw-word length and family cardinality
are separate source-envelope premises, not free physical input producers. -/
theorem budget_bound {l r : Nat} (gs : List (ExactThresholdGate (l+r))) [P1Radix gs]
    (Q w X : Nat) (ps : List (List (List (Fin gs.length))))
    (hn : l+r≤X) (hN : gs.length≤X) (hcache : (exactListWord gs).length≤X)
    (hb : P1Radix.bits gs≤X) (hp : P1CompactNativeWidth.width gs Q≤X)
    (hQ : Q≤X) (hw : w≤X) (hQpos : 1≤Q)
    (hrows : ∀ ms∈ps,ms.length≤2^w)
    (hraw : ∀ ms∈ps,(P1CompactNativeFamily.rawWord ms).length≤X)
    (hps : ps.length≤X) :
    CompactColdFamily.budget gs Q w ps ≤ 2^119*(X+1)^22*2^(w*(Q+1)) := by
  let E := 2^(w*(Q+1))
  let Z := (X+1)^22
  have hE : 1≤E := Nat.one_le_two_pow
  have hZ : 1≤Z := Nat.one_le_pow _ _ (by omega)
  have h2 : (X+1)^2≤Z := Nat.pow_le_pow_right (by omega) (by decide)
  have h3 : (X+1)^3≤Z := Nat.pow_le_pow_right (by omega) (by decide)
  have h16 : (X+1)^16≤Z := Nat.pow_le_pow_right (by omega) (by decide)
  have h18 : (X+1)^18≤Z := Nat.pow_le_pow_right (by omega) (by decide)
  have hD : P1Radix.effectiveDegree gs≤X := (Nat.min_le_right _ _).trans hN
  have hm := CompactMetadata.budget_bound (exactListWord gs).length (l+r) gs.length
    (P1Radix.bits gs) (P1Radix.effectiveDegree gs) Q w X hcache hn hN hb hD hQ hw
  have hc := CompactPreparationCost.capacity_bound gs Q w X hn hN hcache hb hp hQ hw
  have hcZ : P1CompactNativeMeasured.capacity gs Q w≤2^84*Z*E := by
    exact hc.trans (by gcongr)
  have hf := P1CompactNativeFamilyBudget.family_bound gs Q w X ps hQpos hrows hraw
  have enlarge (C : Nat) :
      X*((X+2)*X+(40*X+13)*C+103*X+40)+3 ≤
        (X+1)*((2*(X+1))*(X+1)+(53*(X+1))*C+143*(X+1))+3 := by
    nlinarith
  have family : P1CompactNativeFamily.budget gs Q w ps≤2^92*Z*E := by
    calc
      _ ≤ X*((X+2)*X+(40*X+13)*(2^84*(X+1)^16*E)+103*X+40)+3 :=
        hf.trans (by gcongr)
      _ ≤ (X+1)*((2*(X+1))*(X+1)+(53*(X+1))*(2^84*(X+1)^16*E)+143*(X+1))+3 := by
        exact enlarge _
      _ = 2*(X+1)^3+53*2^84*(X+1)^18*E+143*(X+1)^2+3 := by ring
      _ ≤ 2*Z*E+53*2^84*Z*E+143*Z*E+3*Z*E := by
        have hZE : Z≤Z*E := Nat.le_mul_of_pos_right _ (by omega)
        nlinarith
      _ ≤ 2^92*Z*E := by nlinarith
  change _ ≤ 2^119*Z*E
  unfold CompactColdFamily.budget CompactNativeInitialize.budget
  change CompactMetadata.budget (exactListWord gs).length (l+r) gs.length (P1Radix.bits gs)
    (P1Radix.effectiveDegree gs) Q w≤2^118*Z*E at hm
  nlinarith

/-- Shifted unary indices pay at most B+1 bits per index, plus the literal
monomial and stream delimiters. This includes duplicate occurrences. -/
theorem raw_word_bound {B : Nat} (ms : List (List (Fin B))) (D : Nat)
    (hd : ∀ m∈ms,m.length≤D) :
    (P1CompactNativeFamily.rawWord ms).length ≤ ms.length*(D*(B+1)+2)+1 := by
  have blocks (m : List (Fin B)) :
      ((m.map Fin.val).flatMap block).length ≤ m.length*(B+1) := by
    induction m with
    | nil => simp
    | cons i m ih =>
      simp only [List.map_cons,List.flatMap_cons,List.length_append,block_length,List.length_cons]
      nlinarith [i.isLt]
  have rows : ((rawIndices ms).flatMap monomialWord).length ≤ ms.length*(D*(B+1)+2) := by
    induction ms with
    | nil => simp [rawIndices]
    | cons m ms ih =>
      have hm := (blocks m).trans (Nat.mul_le_mul_right (B+1) (hd m (by simp)))
      have ht := ih (fun m hm=>hd m (by simp [hm]))
      simp only [rawIndices,List.map_cons,List.flatMap_cons,List.length_append,
        monomialWord_length,List.length_cons]
      change ((List.map Fin.val m).flatMap block).length+2+
        ((rawIndices ms).flatMap monomialWord).length ≤ _
      nlinarith
  simpa only [P1CompactNativeFamily.rawWord,stream,List.length_append,List.length_singleton]
    using Nat.add_le_add_right rows 1

open SupplierPipeline SupplierEstimator ThresholdCompiler CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal C10SupplierRowInput

/-- Exactly the paper's 2^K assignments, not a forecast or an additional input. -/
theorem actual_family_length {q : Nat} (a : DecompositionAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2=liveᶜ.card) (P : StructuralGF2Polynomial) :
    (ps a live occ s harity P).length=2^live.card := by
  rw [ps,List.length_ofFn,liveList_length]

/-- The raw input envelope follows from the original polynomial degree and
its existing lowering; there is no incidence-cache-size degree assumption. -/
theorem actual_raw_word_bound {q : Nat} (a : DecompositionAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2=liveᶜ.card) (P : StructuralGF2Polynomial) (D : Nat)
    (hd : CloseoutRawRows.RawMonomialDegreeAtMost D P) :
    ∀ ms∈ps a live occ s harity P, (P1CompactNativeFamily.rawWord ms).length ≤
      (CloseoutRowsUniversal.lower a live occ P).length*
        (D*((pool a live occ s harity).length+1)+2)+1 := by
  intro ms hm
  obtain ⟨yi,rfl⟩ := List.mem_ofFn.mp hm
  have hdegree := CloseoutRowsUniversal.lower_degree a live occ P D hd
  have bound := raw_word_bound (indexRow a live occ s harity P yi) D (by
    intro m hm
    change m∈(CloseoutRowsUniversal.lower a live occ P).map
      (fun m=>m.map (poolIndex a live occ s harity yi)) at hm
    obtain ⟨m0,hm0,rfl⟩ := List.mem_map.mp hm
    simpa only [List.length_map] using hdegree m0 hm0)
  simpa only [indexRow,List.length_map] using bound

end NearCubicWires.P1Closure.CompactColdCost
