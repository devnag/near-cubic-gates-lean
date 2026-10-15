import Proof.Hierarchy.HierarchyHeaderCopy

/-! The complete paid header-and-zero-padding consumer. It retains all three
source fields and the total-length driver and restores every physical head. -/
namespace NearCubicWires.RepairOrdinary.HierarchyHeader
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def header (a b c : List Bool) := frame a++frame b++frame c
def padded (N : ℕ) (a b c : List Bool) := header a b c++List.replicate (N-(header a b c).length) false
def rawInput (N : ℕ) (a b c : List Bool) : Fin 5 → List Bool :=
  ![frame a,frame b,frame c,List.replicate N true,[]]
def source (a b c : List Bool) : Fin 3 → List Bool := ![frame a,frame b,frame c]
def pos0 : Fin 3 → ℕ := fun _ => 0
def pos1 (a : List Bool) := Function.update pos0 0 (2*a.length+1)
def pos2 (a b : List Bool) := Function.update (pos1 a) 1 (2*b.length+1)
def pos3 (a b c : List Bool) := Function.update (pos2 a b) 2 (2*c.length+1)

theorem raw_run (N : ℕ) (a b c : List Bool) (hfit : (header a b c).length≤N) :
    ∃ r,run raw (N+1) (rawInput N a b c)=some r ∧
      r.final=config 7 N (source a b c) (pos3 a b c) (padded N a b c) ∧ r.steps=N+1 := by
  have h0 := copy_prefix N (source a b c) pos0 [] [] a 0 rfl rfl
  have h1 := copy_prefix N (source a b c) (pos1 a) (frame a) [] b 1 rfl (by simp [pos1,pos0,Function.update])
  have h2 := copy_prefix N (source a b c) (pos2 a b) (frame a++frame b) [] c 2 rfl
    (by simp [pos2,pos1,pos0,Function.update])
  simp only [List.length_nil,Nat.zero_add,List.nil_append] at h0 h1 h2
  have hp := padding_prefix N (N-(header a b c).length) (source a b c) (pos3 a b c) (header a b c)
    (Nat.add_sub_of_le hfit)
  have h := ((h0.trans h1).trans h2).trans hp
  have ht : (2*a.length+1+(2*b.length+1)+(2*c.length+1))+(N-(header a b c).length+1)=N+1 := by
    have hl : (header a b c).length=2*a.length+1+(2*b.length+1)+(2*c.length+1) := by
      simp only [header,List.length_append,frame_length]
    omega
  rw [ht] at h
  obtain ⟨r,hr,hf,hs⟩ := h.run (by rfl)
  have hi : config (marker 0) N (source a b c) pos0 []=initialConfiguration raw (rawInput N a b c) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at hr
  exact ⟨r,hr,hf,hs⟩

def machine := Rewind.machine raw
def input (N : ℕ) (a b c : List Bool) : Fin 6 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (5+1) => List Bool) (rawInput N a b c) (fun _ : Fin 1 => [])
theorem header_run (N : ℕ) (a b c : List Bool) (hfit : (header a b c).length≤N) :
    ∃ r,run machine (2*N+4) (input N a b c)=some r ∧
      r.final.tapes 0=frame a ∧ r.final.tapes 1=frame b ∧ r.final.tapes 2=frame c ∧
      r.final.tapes 3=List.replicate N true ∧ r.final.tapes 4=padded N a b c ∧
      r.final.tapes 5=List.replicate (N+1) false ∧ (∀ i,r.final.heads i=0) ∧ r.steps=2*N+4 := by
  obtain ⟨base,hb,hf,hs⟩ := raw_run N a b c hfit
  obtain ⟨r,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw
    (N+1) (rawInput N a b c) base hb 0
  have he : 2*base.steps+2=2*N+4 := by omega
  rw [he] at hr
  refine ⟨r,hr,?_,?_,?_,?_,?_,?_,hh,by omega⟩
  · simpa [hf,config,source] using ht 0
  · simpa [hf,config,source] using ht 1
  · simpa [hf,config,source] using ht 2
  · simpa [hf,config] using ht 3
  · simpa [hf,config] using ht 4
  · simpa [hs] using hcounter

end NearCubicWires.RepairOrdinary.HierarchyHeader
