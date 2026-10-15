import Proof.MachineModel.OrdinaryMatrixNativeDimension

/-! The three canonical dimensions share one paid width and use disjoint
physically blank local work banks. Every native word is actually printed. -/
namespace NearCubicWires.RepairOrdinary.MatrixNativeDimensions
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def dimension (j : Fin 3) : Fin 52 := ⟨j.val+1,by omega⟩
def output (j : Fin 3) : Fin 52 := ⟨17+16*j.val,by omega⟩
def slots (j : Fin 3) (i : Fin 18) : Fin 52 := if i=0 then 0 else if i=1 then dimension j
  else ⟨4+16*j.val+(i.val-2),by omega⟩
theorem slots_injective (j : Fin 3) : Function.Injective (slots j) := by
  fin_cases j <;> decide
theorem slot_zero (j : Fin 3) : slots j 0=0 := rfl
theorem slot_one (j : Fin 3) : slots j 1=dimension j := rfl
theorem slot_output (j : Fin 3) : slots j 15=output j := by
  apply Fin.ext
  simp [slots,output]
  omega
theorem slot_cases (j : Fin 3) (i : Fin 18) :
    slots j i=0 ∨ slots j i=dimension j ∨
      (4+16*j.val ≤ (slots j i).val ∧ (slots j i).val<4+16*(j.val+1)) := by
  unfold slots
  split
  · exact Or.inl rfl
  split
  · exact Or.inr (Or.inl rfl)
  · right; right; dsimp only; constructor <;> omega

noncomputable def call (j : Fin 3) := RecoveryFocus.machine (slots j) MatrixNativeDimension.machine
noncomputable def tail := Composition.machine (call 1) (call 2)
noncomputable def machine := Composition.machine (call 0) tail
def input (M : ℕ) (ns : Fin 3 → ℕ) : Fin 52 → List Bool := fun i =>
  if i=0 then List.replicate M true else if hi : i.val≤3 then UnaryTemplate.tape (ns ⟨i.val-1,by omega⟩) else []
def budget (M : ℕ) (ns : Fin 3 → ℕ) := MatrixNativeDimension.budget M (ns 0)+1+
  (MatrixNativeDimension.budget M (ns 1)+1+MatrixNativeDimension.budget M (ns 2))
structure Store (M : ℕ) (ns : Fin 3 → ℕ) (done : ℕ) (tapes : Fin 52 → List Bool) : Prop where
  width : tapes 0=List.replicate M true
  dimension : ∀ j,tapes (MatrixNativeDimensions.dimension j)=UnaryTemplate.tape (ns j)
  completed : ∀ j,j.val<done → tapes (output j)=frame (binary M (ns j))
  fresh : ∀ i : Fin 52,4+16*done ≤ i.val → tapes i=[]

theorem cold (M : ℕ) (ns : Fin 3 → ℕ) : Store M ns 0 (input M ns) := by
  constructor
  · rfl
  · intro j
    fin_cases j <;> rfl
  · intro j h; omega
  · intro i hi
    have h0 : i≠0 := by intro h; subst i; omega
    simp [input,h0,show ¬i.val≤3 by omega]

theorem step_run (M : ℕ) (ns : Fin 3 → ℕ) (positive : ∀ j,0<ns j) (fits : ∀ j,ns j<2^M)
    (j : Fin 3) (ambient : Fin 52 → List Bool) (store : Store M ns j.val ambient) :
    ∃ out,ClockJoin.ReadyRun (call j) (MatrixNativeDimension.budget M (ns j)) ambient out ∧
      Store M ns (j.val+1) out := by
  obtain ⟨base,ready,b0,b1,b15⟩ := MatrixNativeDimension.dimension_run M (ns j) (positive j) (fits j)
  have hi : ∀ i,ambient (slots j i)=MatrixNativeDimension.input M (ns j) i := by
    intro i
    by_cases h0 : i=0
    · subst i; exact store.width
    by_cases h1 : i=1
    · subst i; exact store.dimension j
    have hs : 4+16*j.val ≤ (slots j i).val := by simp only [slots,h0,h1,ite_false]; omega
    exact (store.fresh _ hs).trans (by simp [MatrixNativeDimension.input,h0,h1])
  let out := install (slots j) ambient base
  have run := bounded_focus (slots j) (slots_injective j) _ _ _ ready ambient hi
  have old (i : Fin 52) (h : ∀ k,slots j k≠i) : out i=ambient i := install_other (slots j) _ _ i h
  refine ⟨out,run,?_,?_,?_,?_⟩
  · exact (install_slot (slots j) (slots_injective j) _ _ 0).trans b0
  · intro k
    by_cases hk : k=j
    · subst k; exact (install_slot (slots j) (slots_injective j) _ _ 1).trans b1
    apply (old (dimension k) ?_).trans (store.dimension k)
    intro i h
    have hv := congrArg Fin.val h
    rcases slot_cases j i with hz | hd | ⟨lo,_⟩
    · rw [hz] at h
      have he := congrArg Fin.val h
      dsimp [dimension] at he
      omega
    · rw [hd] at h
      apply hk
      exact Fin.ext (by have he := congrArg Fin.val h; dsimp [dimension] at he; omega)
    · dsimp [dimension] at hv
      omega
  · intro k hk
    by_cases heq : k=j
    · subst k
      rw [←slot_output]
      exact (install_slot (slots j) (slots_injective j) _ _ 15).trans b15
    have hk' : k.val<j.val := by
      have hn : k.val≠j.val := fun h => heq (Fin.ext h)
      omega
    apply (old (output k) ?_).trans (store.completed k hk')
    intro i h
    have hv := congrArg Fin.val h
    rcases slot_cases j i with hz | hd | ⟨lo,_⟩
    · rw [hz] at h
      have he := congrArg Fin.val h
      dsimp [output] at he
      omega
    · rw [hd] at h
      have he := congrArg Fin.val h
      dsimp [dimension,output] at he
      omega
    · dsimp [output] at hv
      omega
  · intro i hi
    apply (old i ?_).trans (store.fresh i (by omega))
    intro k h
    have hv := congrArg Fin.val h
    rcases slot_cases j k with hz | hd | ⟨_,up⟩
    · rw [hz] at h
      have he := congrArg Fin.val h
      simp only [Fin.val_zero] at he
      omega
    · rw [hd] at h
      have he := congrArg Fin.val h
      dsimp [dimension] at he
      omega
    · omega

theorem dimensions_run (M : ℕ) (ns : Fin 3 → ℕ) (positive : ∀ j,0<ns j) (fits : ∀ j,ns j<2^M) :
    ∃ out,ClockJoin.ReadyRun machine (budget M ns) (input M ns) out ∧
      out 0=List.replicate M true ∧
      (∀ j,out (dimension j)=UnaryTemplate.tape (ns j)) ∧
      (∀ j,out (output j)=frame (binary M (ns j))) := by
  obtain ⟨s0,h0,f0⟩ := step_run M ns positive fits 0 (input M ns) (cold M ns)
  obtain ⟨s1,h1,f1⟩ := step_run M ns positive fits 1 s0 f0
  obtain ⟨s2,h2,f2⟩ := step_run M ns positive fits 2 s1 f1
  have ht := ClockJoin.join (call 1) (call 2) _ _ _ _ _ h1 h2
  have whole := ClockJoin.join (call 0) tail _ _ _ _ _ h0 ht
  exact ⟨s2,whole,f2.width,f2.dimension,fun j => f2.completed j (by omega)⟩

end NearCubicWires.RepairOrdinary.MatrixNativeDimensions
