import Proof.Hierarchy.CompetitorCountProducer
import Proof.MachineModel.ClockFields

/-! Execute the exact paper normalization denominator. The first count is
the prime-list cardinality for THR and one for SYM; it never counts child
tuples. The binary power of two is physically printed from the unary q word,
then two short multiplications produce P * E * 2^q. All work starts blank. -/
namespace NearCubicWires.RepairOrdinary.CompetitorDenominator
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (b w q p e : ℕ) : Fin 37 → List Bool := fun i => match i.val with
  | 0 => frame (binary b e)
  | 1 => frame (binary w p)
  | 2 => List.replicate w true
  | 3 => List.replicate q true
  | _ => []
def powerBits (q : ℕ) := List.replicate q false++[true]
def powerSlots : Fin 6 → Fin 37 := ![3,4,5,6,7,8]
def firstSlots (j : Fin 14) : Fin 37 :=
  if j.val=0 then 0 else if j.val=8 then 1 else if j.val=9 then 2
  else ⟨9+j.val,by omega⟩
def secondSlots (j : Fin 14) : Fin 37 :=
  if j.val=0 then 4 else if j.val=8 then 12 else if j.val=9 then 2
  else ⟨23+j.val,by omega⟩
noncomputable def powerProgram := RecoveryFocus.machine powerSlots ClockFields.machine
noncomputable def firstProgram := RecoveryFocus.machine firstSlots HierarchyMultiplyEntry.machine
noncomputable def secondProgram := RecoveryFocus.machine secondSlots HierarchyMultiplyEntry.machine
noncomputable def machine := Composition.machine powerProgram (Composition.machine firstProgram secondProgram)
def budget (b w q : ℕ) := 4*q+24+128*(w+1)*(b+q+3)

theorem power_value (q : ℕ) : value (powerBits q)=2^q := by
  simp [powerBits,value_append,ClockScalarFields.zeros_value,value]

structure Powered (b w q p e : ℕ) (tapes : Fin 37 → List Bool) : Prop where
  retained : ∀ i : Fin 4,tapes ⟨i.val,by omega⟩=input b w q p e ⟨i.val,by omega⟩
  power : tapes 4=frame (powerBits q)
  fresh : ∀ i : Fin 37, 9 ≤ i.val → tapes i=[]

theorem power_ready (b w q p e : ℕ) :
    ∃ out,ClockJoin.ReadyRun powerProgram (4*q+22) (input b w q p e) out ∧
      Powered b w q p e out := by
  obtain ⟨base,hr,h0,h1,_,_,_,_,hh,hs⟩ := ClockFields.fields_run q
  have ready : ClockJoin.ReadyRun ClockFields.machine (4*q+22)
      (Fin.addCases (motive := fun _ : Fin (5+1) => List Bool)
        ![List.replicate q true,[],[],[],[]] (fun _ : Fin 1 => [])) base.final.tapes :=
    ⟨base,hr,rfl,hh,hs.le⟩
  have hfocus := CompetitorRationalProducts.bounded_focus powerSlots (by decide) _ _ _ ready
    (input b w q p e) (by intro i; fin_cases i <;> rfl)
  refine ⟨install powerSlots (input b w q p e) base.final.tapes,hfocus,?_,?_,?_⟩
  · intro i; fin_cases i
    · exact install_other powerSlots _ _ _ (by decide)
    · exact install_other powerSlots _ _ _ (by decide)
    · exact install_other powerSlots _ _ _ (by decide)
    · exact (install_slot powerSlots (by decide) _ _ 0).trans h0
  · exact (install_slot powerSlots (by decide) _ _ 1).trans h1
  · intro i hi
    have hn : ¬∃ j,powerSlots j=i := by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      fin_cases j <;> simp [powerSlots] at hv <;> omega
    rw [install_other powerSlots _ _ i (fun j hj => hn ⟨j,hj⟩)]
    match i with
    | ⟨0,_⟩ | ⟨1,_⟩ | ⟨2,_⟩ | ⟨3,_⟩ => simp only at hi; omega
    | ⟨_+4,_⟩ => rfl

structure Multiplied (w q p e : ℕ) (tapes : Fin 37 → List Bool) : Prop where
  product : tapes 12=frame (binary w (p*e))
  power : tapes 4=frame (powerBits q)
  width : tapes 2=List.replicate w true
  fresh : ∀ i : Fin 37, 23 ≤ i.val → tapes i=[]

theorem first_ready (b w q p e : ℕ) (ambient : Fin 37 → List Bool)
    (ha : Powered b w q p e ambient) (he : e<2^b) (hfit : p*2^b<2^w) :
    ∃ out,ClockJoin.ReadyRun firstProgram (128*(w+1)*(b+1)) ambient out ∧
      Multiplied w q p e out := by
  obtain ⟨base,hr,h3,_,_,h9,_,hh,hs⟩ := HierarchyMultiplyEntry.multiply_run w p (binary b e)
    (by simpa using hfit)
  have ready : ClockJoin.ReadyRun HierarchyMultiplyEntry.machine (128*(w+1)*(b+1))
      (HierarchyMultiplyEntry.input14 w p (binary b e)) base.final.tapes :=
    ⟨base,by simpa [HierarchyMultiplyEntry.budget] using hr,rfl,hh,
      by simpa [HierarchyMultiplyEntry.budget] using hs⟩
  have hin : ∀ j,ambient (firstSlots j)=HierarchyMultiplyEntry.input14 w p (binary b e) j := by
    intro j
    rw [CompetitorRationalProducts.input14_cases]
    by_cases h0 : j.val=0
    · have hj : j=0 := Fin.ext h0
      subst j
      exact ha.retained 0
    · by_cases h8 : j.val=8
      · have hj : j=8 := Fin.ext h8
        subst j
        exact ha.retained 1
      · by_cases h9 : j.val=9
        · have hj : j=9 := Fin.ext h9
          subst j
          exact ha.retained 2
        · simp only [firstSlots,h0,h8,h9,if_false]
          exact ha.fresh _ (by simp)
  have hfocus := CompetitorRationalProducts.bounded_focus firstSlots (by decide) _ _ _ ready ambient hin
  refine ⟨install firstSlots ambient base.final.tapes,hfocus,?_,?_,?_,?_⟩
  · simpa [firstSlots,binary_value b e he] using (install_slot firstSlots (by decide) ambient base.final.tapes 3).trans h3
  · exact (install_other firstSlots _ _ 4 (by decide)).trans ha.power
  · exact (install_slot firstSlots (by decide) _ _ 9).trans h9
  · intro i hi
    have hn : ¬∃ j,firstSlots j=i := by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      simp only [firstSlots] at hv
      split at hv <;> try omega
      split at hv <;> try omega
      split at hv <;> simp at hv <;> omega
    exact (install_other firstSlots _ _ i (fun j hj => hn ⟨j,hj⟩)).trans (ha.fresh i (by omega))

theorem second_ready (w q p e : ℕ) (ambient : Fin 37 → List Bool)
    (ha : Multiplied w q p e ambient) (hfit : p*e*2^(q+1)<2^w) :
    ∃ out,ClockJoin.ReadyRun secondProgram (128*(w+1)*(q+2)) ambient out ∧
      out 26=frame (binary w (p*e*2^q)) := by
  obtain ⟨base,hr,h3,_,_,_,_,hh,hs⟩ := HierarchyMultiplyEntry.multiply_run w (p*e) (powerBits q)
    (by simpa [powerBits] using hfit)
  have ready : ClockJoin.ReadyRun HierarchyMultiplyEntry.machine (128*(w+1)*(q+2))
      (HierarchyMultiplyEntry.input14 w (p*e) (powerBits q)) base.final.tapes :=
    ⟨base,by simpa [HierarchyMultiplyEntry.budget,powerBits] using hr,rfl,hh,
      by simpa [HierarchyMultiplyEntry.budget,powerBits] using hs⟩
  have hin : ∀ j,ambient (secondSlots j)=HierarchyMultiplyEntry.input14 w (p*e) (powerBits q) j := by
    intro j
    rw [CompetitorRationalProducts.input14_cases]
    by_cases h0 : j.val=0
    · have hj : j=0 := Fin.ext h0
      subst j
      exact ha.power
    · by_cases h8 : j.val=8
      · have hj : j=8 := Fin.ext h8
        subst j
        exact ha.product
      · by_cases h9 : j.val=9
        · have hj : j=9 := Fin.ext h9
          subst j
          exact ha.width
        · simp only [secondSlots,h0,h8,h9,if_false]
          exact ha.fresh _ (by simp)
  have hfocus := CompetitorRationalProducts.bounded_focus secondSlots (by decide) _ _ _ ready ambient hin
  refine ⟨install secondSlots ambient base.final.tapes,hfocus,?_⟩
  simpa [secondSlots,power_value] using (install_slot secondSlots (by decide) ambient base.final.tapes 3).trans h3

theorem denominator_run (b w q p e : ℕ) (he : e<2^b)
    (hfirst : p*2^b<2^w) (hsecond : p*e*2^(q+1)<2^w) :
    ∃ out,ClockJoin.ReadyRun machine (budget b w q) (input b w q p e) out ∧
      out 26=frame (binary w (p*e*2^q)) := by
  obtain ⟨powered,hp,hpowered⟩ := power_ready b w q p e
  obtain ⟨multiplied,hm,hmultiplied⟩ := first_ready b w q p e powered hpowered he hfirst
  obtain ⟨out,ho,hout⟩ := second_ready w q p e multiplied hmultiplied hsecond
  have htail := ClockJoin.join firstProgram secondProgram _ _ _ _ _ hm ho
  have hjoin := ClockJoin.join powerProgram (Composition.machine firstProgram secondProgram)
    _ _ _ _ _ hp htail
  have ht : (4*q+22)+1+(128*(w+1)*(b+1)+1+128*(w+1)*(q+2))=budget b w q := by
    unfold budget
    ring
  rw [ht] at hjoin
  exact ⟨out,hjoin,hout⟩

end NearCubicWires.RepairOrdinary.CompetitorDenominator
