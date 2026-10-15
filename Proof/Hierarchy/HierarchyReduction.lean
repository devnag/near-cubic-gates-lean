import Proof.Hierarchy.HierarchyReductionPadding

/-! Complete ordinary padding producer from the retained framed source x.
All arithmetic, unary allocation, slice rounding, constant printing, header
copying, zero padding, physical returns, and head restoration are paid. -/
namespace NearCubicWires.RepairOrdinary.HierarchyReduction
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (k C Cpad : ℕ) (code : List Bool) := Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (boundProgram k C)
    (allocationProgram k C Cpad code)) (sliceProgram k)) (codeProgram k code)) (headerProgram k)
def budget (k C Cpad : ℕ) (code x : List Bool) := HierarchyFromInput.budget (k+2) C x+1+
  HierarchyAllocation.budget (coefficient Cpad) (constant C Cpad code) x+1+
  (2*length k C Cpad code x+4)+1+codeCost code+1+(2*length k C Cpad code x+4)

theorem reduction_run (k C Cpad : ℕ) (code x : List Bool) (hpad : k+3≤Cpad) :
    ∃ r,run (machine k C Cpad code) (budget k C Cpad code x) (input k x)=some r ∧
      r.final.tapes (extra k 13)=HierarchyPadding.rawInput k C Cpad code x ∧
      r.final.tapes (xTape k)=frame x ∧ (∀ i,r.final.heads i=0) ∧
      r.steps ≤ budget k C Cpad code x := by
  obtain ⟨a,ha,haf,hab⟩ := bound_ready k C x
  obtain ⟨b,hb,hbf,hba,hbb⟩ := allocation_ready k C Cpad code x a haf hab
  obtain ⟨c,hc,hcf,hcn,hcb⟩ := slice_ready k C Cpad code x b hbf hba hbb
  obtain ⟨d,hd,hdf,hdn,hdc,hdb⟩ := code_ready k C Cpad code x c hcf hcn hcb
  obtain ⟨e,he,heo,hex⟩ := header_ready k C Cpad code x hpad d hdf hdn hdc hdb
  have h1 := ClockJoin.join _ _ _ _ _ _ _ ha hb
  have h2 := ClockJoin.join _ _ _ _ _ _ _ h1 hc
  have h3 := ClockJoin.join _ _ _ _ _ _ _ h2 hd
  obtain ⟨r,hr,ht,hh,hs⟩ := ClockJoin.join _ _ _ _ _ _ _ h3 he
  exact ⟨r,hr,by rw [ht]; exact heo,by rw [ht]; exact hex,hh,hs⟩

theorem reduction_guards (k C Cpad : ℕ) (code x : List Bool)
    (hC : 0<C) (hcoeff : C≤Cpad) (hpad : k+3≤Cpad) :
    let y := HierarchyPadding.rawInput k C Cpad code x
    code.length≤Nat.log 2 y.length ∧
    (binary (HierarchyBinary.width C (k+2) x.length) (C*(x.length^(k+2)+1))).length≤ClockDyadicLedger.width y.length ∧
    x.length≤C*(x.length^(k+2)+1) ∧ C*(x.length^(k+2)+1)≤ClockDyadicLedger.limit y.length ∧
    PowerSlice.degree y.length=k+2 :=
  HierarchyPadding.entry_guards k C Cpad code x hC hcoeff hpad

end NearCubicWires.RepairOrdinary.HierarchyReduction
