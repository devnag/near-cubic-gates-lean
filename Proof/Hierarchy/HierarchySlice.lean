import Proof.Hierarchy.HierarchySliceKernel

/-! Exact ordinary production of the selected dyadic length slice from a
paid linear unary allocation. Both source and output are retained at head 0. -/
namespace NearCubicWires.RepairOrdinary.HierarchySlice
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem loop_prefix (p q : ℕ) (hp : 0<p) (A i remaining : ℕ) (he : i+remaining=A) :
    Timed (raw p q hp) remaining (config (loopState p q hp i) A i i)
      (config (loopState p q hp A) A A A) := by
  induction remaining generalizing i with
  | zero =>
    have hi : i=A := by omega
    subst i
    exact Timed.refl _ _
  | succ remaining ih =>
    have h := (Timed.single (by
        have hm := Nat.mod_lt i hp
        simp [raw,loopState,config]
        omega) (loop_step p q hp A i (by omega))).trans (ih (i+1) (by omega))
    simpa only [Nat.add_comm 1 remaining] using h

theorem finish_prefix (p q : ℕ) (hp : 0<p) (r remaining : ℕ) (he : r+remaining=p+q)
    (A out : ℕ) :
    Timed (raw p q hp) remaining (config (finishState p q r (by omega)) A A out)
      (config (finishState p q (p+q) (by omega)) A A (out+remaining)) := by
  induction remaining generalizing r out with
  | zero =>
    have hr : r=p+q := by omega
    subst r
    exact Timed.refl _ _
  | succ remaining ih =>
    have h := (Timed.single (by simp [raw,finishState,config]; omega)
      (finish_step p q hp r (by omega) A out)).trans (ih (r+1) (by omega) (out+1))
    simpa only [Nat.add_comm 1 remaining,Nat.add_assoc] using h

def length (p q A : ℕ) := p*(A/p+1)+q
theorem finish_length (p q A : ℕ) (hp : 0<p) : A+(p+q-A%p)=length p q A := by
  have hm := Nat.mod_lt A hp
  have he := Nat.mod_add_div A p
  dsimp [length]
  rw [Nat.mul_add,Nat.mul_one]
  omega

theorem raw_run (p q : ℕ) (hp : 0<p) (A : ℕ) :
    ∃ r,run (raw p q hp) (length p q A+1) ![List.replicate A true,[]]=some r ∧
      r.final=config (finishState p q (p+q) (by omega)) A A (length p q A) ∧
      r.steps=length p q A+1 := by
  have h1 := loop_prefix p q hp A 0 A (by omega)
  have h2 := Timed.single (by
    have hm := Nat.mod_lt A hp
    simp [raw,loopState,config]
    omega) (loop_stop p q hp A)
  have h3 := finish_prefix p q hp (A%p) (p+q-A%p)
    (by have := Nat.mod_lt A hp; omega) A A
  have h := (h1.trans h2).trans h3
  have hn := finish_length p q A hp
  have ht : A+1+(p+q-A%p)=length p q A+1 := by omega
  rw [hn,ht] at h
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [raw,finishState,config]; omega)
  have hi : config (loopState p q hp 0) A 0 0=
      initialConfiguration (raw p q hp) ![List.replicate A true,[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at hr
  exact ⟨r,hr,hf,hs⟩

def machine (k : ℕ) := Rewind.machine (raw (2^(k+1)) (2^k) (by positivity))
theorem slice_run (k A : ℕ) :
    ∃ r,run (machine k) (2*PowerSlice.length k A+4)
        ![List.replicate A true,[],[]]=some r ∧
      r.final.tapes 0=List.replicate A true ∧
      r.final.tapes 1=List.replicate (PowerSlice.length k A) true ∧
      r.final.tapes 2=List.replicate (PowerSlice.length k A+1) false ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=2*PowerSlice.length k A+4 := by
  obtain ⟨base,hb,hf,hs⟩ := raw_run (2^(k+1)) (2^k) (by positivity) A
  obtain ⟨r,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace
    (raw (2^(k+1)) (2^k) (by positivity)) _ _ base hb 0
  have hi : (Fin.addCases (motive := fun _ : Fin (2+1) => List Bool)
      ![List.replicate A true,[]] (fun _ : Fin 1 => []))=![List.replicate A true,[],[]] := by
    funext i; fin_cases i <;> rfl
  have hlen : length (2^(k+1)) (2^k) A=PowerSlice.length k A := rfl
  have he : 2*base.steps+2=2*PowerSlice.length k A+4 := by rw [hlen] at hs; omega
  change run (machine k) (2*base.steps+2)
    (Fin.addCases (motive := fun _ : Fin (2+1) => List Bool)
      ![List.replicate A true,[]] (fun _ : Fin 1 => []))=some r at hr
  rw [hi,he] at hr
  refine ⟨r,hr,?_,?_,?_,hh,by omega⟩
  · simpa [hf,config] using ht 0
  · simpa [hf,config,hlen] using ht 1
  · simpa [hs,hlen] using hcounter

end NearCubicWires.RepairOrdinary.HierarchySlice
