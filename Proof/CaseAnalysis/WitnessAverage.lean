import Proof.CaseAnalysis.WitnessFamily
import Proof.Circuits.ComponentwiseCircuitRestriction
import Proof.Amplification.XorResourcesBits

/-! The paper's unsigned occurrence average as an actual legal term list.
Term count grows by the fibre size; coefficient mass retains its original cap. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Average
open CanonicalWitnessCodec ExecutableInterfaces
open RepairXor ValidatorLeafWidthCore
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem occurrence_division (c : ℚ) (B d : ℕ) (hd : 0 < d)
    (hn : c.num.natAbs  ≤  B) (hden : c.den  ≤  B) :
    (c / (d : ℚ)).num.natAbs  ≤  B ∧ (c / (d : ℚ)).den  ≤  B*d := by
  have he : c/(d:ℚ)=(c.num:ℚ)/((c.den*d:ℕ):ℚ) := by
    rw [Nat.cast_mul,←div_div,Rat.num_div_den]
  have h:=fraction_reduction_bounds c.num (c.den*d) (Nat.mul_pos c.pos hd)
  rw [←he] at h
  exact ⟨h.1.trans hn,h.2.trans (Nat.mul_le_mul_right d hden)⟩

theorem occurrence_guard_bits (c : ℚ) (B d D : ℕ) (hd : 0 < d) (hD : d  ≤  D)
    (hn : c.num.natAbs  ≤  B) (hden : c.den  ≤  B) :
    natBitLength (c/(d:ℚ)).num.natAbs  ≤  natBitLength (B*D) ∧
    natBitLength (c/(d:ℚ)).den  ≤  natBitLength (B*D) := by
  obtain ⟨ha,hb⟩:=occurrence_division c B d hd hn hden
  have hpos:0<D:=hd.trans_le hD
  exact ⟨natBitLength_mono (ha.trans (Nat.le_mul_of_pos_right B hpos)),
    natBitLength_mono (hb.trans (Nat.mul_le_mul_left B hD))⟩

variable {Circuit : CanonicalWitnessCodec.CircuitFamily} {n : ℕ}
def scaled (d : ℕ) (ts : List (LegalCircuitTerm Circuit n)) :=
  ts.map fun t=>({coefficient:=t.coefficient/(d:ℚ),circuit:=t.circuit} : LegalCircuitTerm Circuit n)
def terms (slices : List (List (LegalCircuitTerm Circuit n))) := slices.flatMap (scaled slices.length)
def mass (ts : List (LegalCircuitTerm Circuit n)) := (ts.map fun t=>|t.coefficient|).sum
theorem mass_fold (ts : List (LegalCircuitTerm Circuit n)) :
    ts.foldl (fun total t=>total+|t.coefficient|) 0=mass ts := by
  simp only [mass,List.sum_eq_foldl,List.foldl_map]
noncomputable def value (evaluate : Circuit n→BitInput n→Bool)
    (ts : List (LegalCircuitTerm Circuit n)) (u : BitInput n) : ℝ :=
  (ts.map fun t=>(t.coefficient:ℝ)*bitAsReal (evaluate t.circuit u)).sum

theorem scaled_mass (d : ℕ) (ts : List (LegalCircuitTerm Circuit n)) : mass (scaled d ts)=mass ts/(d:ℚ) := by
  induction ts with
  | nil=>simp [mass,scaled]
  | cons t ts ih=>
    simpa [mass,scaled,abs_div,abs_of_nonneg (Nat.cast_nonneg d : (0:ℚ)  ≤  (d:ℚ)),add_div] using
      congrArg (fun x=>|t.coefficient|/(d:ℚ)+x) ih

theorem flat_mass (d : ℕ) (slices : List (List (LegalCircuitTerm Circuit n))) :
    mass (slices.flatMap (scaled d))=(slices.map mass).sum/(d:ℚ) := by
  induction slices with
  | nil=>simp [mass]
  | cons ts slices ih=>
    simp only [List.flatMap_cons,mass,List.map_append,List.sum_append] at ⊢
    change mass (scaled d ts)+mass (slices.flatMap (scaled d))=_
    rw [scaled_mass,ih]
    simp [add_div]

theorem terms_mass (slices : List (List (LegalCircuitTerm Circuit n))) :
    mass (terms slices)=(slices.map mass).sum/(slices.length:ℚ) := flat_mass _ _

theorem scaled_value (d : ℕ) (evaluate : Circuit n→BitInput n→Bool)
    (ts : List (LegalCircuitTerm Circuit n)) (u : BitInput n) :
    value evaluate (scaled d ts) u=value evaluate ts u/(d:ℝ) := by
  induction ts with
  | nil=>simp [value,scaled]
  | cons t ts ih=>
    change (((t.coefficient/(d:ℚ)):ℚ):ℝ)*bitAsReal (evaluate t.circuit u)+
      value evaluate (scaled d ts) u=
      ((t.coefficient:ℝ)*bitAsReal (evaluate t.circuit u)+value evaluate ts u)/(d:ℝ)
    rw [ih,Rat.cast_div,Rat.cast_natCast]
    ring

theorem flat_value (d : ℕ) (evaluate : Circuit n→BitInput n→Bool)
    (slices : List (List (LegalCircuitTerm Circuit n))) (u : BitInput n) :
    value evaluate (slices.flatMap (scaled d)) u=
      (slices.map fun ts=>value evaluate ts u).sum/(d:ℝ) := by
  induction slices with
  | nil=>simp [value]
  | cons ts slices ih=>
    simp only [List.flatMap_cons,value,List.map_append,List.sum_append] at ⊢
    change value evaluate (scaled d ts) u+value evaluate (slices.flatMap (scaled d)) u=_
    rw [scaled_value,ih]
    simp [add_div,value]

theorem terms_value (evaluate : Circuit n→BitInput n→Bool)
    (slices : List (List (LegalCircuitTerm Circuit n))) (u : BitInput n) :
    value evaluate (terms slices) u=(slices.map fun ts=>value evaluate ts u).sum/(slices.length:ℝ) :=
  flat_value _ _ _ _

theorem mass_bound (slices : List (List (LegalCircuitTerm Circuit n))) (A : ℚ)
    (hA : 0  ≤  A) (h : ∀ ts∈slices,mass ts ≤ A) : mass (terms slices) ≤ A := by
  have hs:(slices.map mass).sum ≤ (slices.length:ℚ)*A:=by
    induction slices with
    | nil=>simp
    | cons ts slices ih=>
      have ht:=h ts (by simp)
      have hr:=ih (by intro t hm;exact h t (by simp [hm]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith
  rw [terms_mass]
  by_cases hz:slices.length=0
  · simpa [hz] using hA
  · apply (div_le_iff₀ (by exact_mod_cast (Nat.pos_of_ne_zero hz) : (0:ℚ)<slices.length)).mpr
    simpa only [mul_comm] using hs

theorem terms_length (slices : List (List (LegalCircuitTerm Circuit n))) :
    (terms slices).length=(slices.map List.length).sum := by
  simp [terms,scaled,List.length_flatMap]

theorem length_bound (slices : List (List (LegalCircuitTerm Circuit n))) (J : ℕ)
    (h : ∀ ts∈slices,ts.length ≤ J) : (terms slices).length ≤ slices.length*J := by
  rw [terms_length]
  induction slices with
  | nil=>simp
  | cons ts slices ih=>
    have ht:=h ts (by simp)
    have hr:=ih (by intro t hm;exact h t (by simp [hm]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

theorem mem_terms (slices : List (List (LegalCircuitTerm Circuit n))) (t : LegalCircuitTerm Circuit n)
    (h : t∈terms slices) : ∃ ts∈slices,∃ a∈ts,
      t=({coefficient:=a.coefficient/(slices.length:ℚ),circuit:=a.circuit} : LegalCircuitTerm Circuit n) := by
  obtain ⟨ts,hts,ht⟩:=List.mem_flatMap.mp h
  obtain ⟨a,ha,he⟩:=List.mem_map.mp ht
  exact ⟨ts,hts,a,ha,he.symm⟩

def limits (n J B D : ℕ) (A : ℚ) (W L : ℕ) : LegalSumLimits where
  expectedArity:=n
  termCap:=D*J
  coefficientBitCap:=natBitLength (B*max 1 D)
  coefficientMassCap:=A
  wireCap:=W
  descriptionCap:=L

def checked (wires description : {n : ℕ}→Circuit n→ℕ)
    (slices : List (List (LegalCircuitTerm Circuit n))) (J B D : ℕ) (A : ℚ) (W L : ℕ)
    (hD : slices.length ≤ D) (hA : 0  ≤  A)
    (hj : ∀ ts∈slices,ts.length ≤ J) (hm : ∀ ts∈slices,mass ts ≤ A)
    (hc : ∀ ts∈slices,∀ t∈ts,t.coefficient.num.natAbs ≤ B ∧ t.coefficient.den ≤ B)
    (hw : ∀ ts∈slices,∀ t∈ts,wires t.circuit ≤ W)
    (hl : ∀ ts∈slices,∀ t∈ts,description t.circuit ≤ L) :
    CheckedLegalCircuitSum Circuit wires description (limits n J B D A W L) where
  value:=⟨n,terms slices⟩
  arity_eq:=rfl
  terms_le:=(length_bound slices J hj).trans (Nat.mul_le_mul_right J hD)
  coefficient_bits_le:=by
    intro t ht
    obtain ⟨ts,hts,a,ha,rfl⟩:=mem_terms slices t ht
    have hd:0<slices.length:=List.length_pos_of_mem hts
    exact occurrence_guard_bits a.coefficient B slices.length (max 1 D) hd
      (hD.trans (Nat.le_max_right _ _)) (hc ts hts a ha).1 (hc ts hts a ha).2
  mass_le:=by
    change (terms slices).foldl (fun total t=>total+|t.coefficient|) 0 ≤ A
    rw [mass_fold]
    exact mass_bound slices A hA hm
  wires_le:=by
    intro t ht
    obtain ⟨ts,hts,a,ha,rfl⟩:=mem_terms slices t ht
    exact hw ts hts a ha
  description_le:=by
    intro t ht
    obtain ⟨ts,hts,a,ha,rfl⟩:=mem_terms slices t ht
    exact hl ts hts a ha

end NearCubicWires.RepairOrdinary.CloseoutWitness.Average
