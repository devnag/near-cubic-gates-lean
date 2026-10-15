import Proof.PCP.PCPPQuerySupportRetained
import Proof.PCP.PCPSerializerTapeSupport

/-! Paid restoration of the cached support reader's source and scratch heads.
The result is the exact raw mask at head zero; both real unary drivers survive. -/
namespace NearCubicWires.RepairOrdinary.PCPPQuerySupportReset
open LocalBitMultitape RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 6) := decide (i≠3 ∧ i≠5)
def caps (C : ℕ) (i : Fin 7) := if i=1 ∨ i=2 ∨ i=6 then C else 0
noncomputable def machine := MaskedReset.machine PCPPQuerySupport.machine selected
noncomputable def entry (source : List Bool) (arity index C : ℕ) :=
  ZeroPadding.config (caps C) (Rewind.recording (PCPPQuerySupport.ready source arity index) 0)
def cost {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) (i : Fin p.systematicBits) :=
  PCPPQuerySupport.budget p.systematicBits p.auxiliaryBits p.clauseBits r.arity i.val

theorem initial_head (source : List Bool) (arity index : ℕ) (j : Fin 6)
    (hj : selected j=true) : (PCPPQuerySupport.ready source arity index).heads j=0 := by
  fin_cases j <;> first | rfl | simp [selected] at hj

theorem lookup_run {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (i : Fin p.systematicBits) (C : ℕ) (hC : cost r p i+1 ≤ C) :
    ∃ receipt,runFrom machine (2*cost r p i+2)
      (entry (pcppOutput r p) r.arity i.val C)=some receipt ∧
      receipt.steps=2*cost r p i+2 ∧
      receipt.final.tapes 0=pcppOutput r p ∧
      receipt.final.tapes 3=UnaryTemplate.tape r.arity ∧
      receipt.final.tapes 5=UnaryTemplate.tape i.val ∧
      receipt.final.tapes 4=PCPPQuerySupport.mask r p i ∧
      (∀ j,receipt.final.heads j=if j=3 ∨ j=5 then 1 else 0) ∧
      (∀ j : Fin 7,j=1 ∨ j=2 ∨ j=6 → (receipt.final.tapes j).length ≤ C) := by
  obtain ⟨raw,hr,rs,ho,_,hsource,harity,hh3,hindex,hh5⟩ :=
    PCPPQuerySupport.lookup_retained_run r p i
  have hp := (prefix_of_run PCPPQuerySupport.machine _ _ raw hr).1
  have hhead : ∀ j,selected j=true → raw.final.heads j ≤ raw.steps := by
    intro j hj
    have h := SelectiveReset.prefix_head hp j
    rw [initial_head _ _ _ j hj,Nat.zero_add] at h
    exact h
  have hsmall (j : Fin 6) (hj : j=1 ∨ j=2) : (raw.final.tapes j).length ≤ C := by
    have hz : (PCPPQuerySupport.ready (pcppOutput r p) r.arity i.val).heads j=0 ∧
        (PCPPQuerySupport.ready (pcppOutput r p) r.arity i.val).tapes j=[] := by
      rcases hj with rfl|rfl <;> exact ⟨rfl,rfl⟩
    have h := PCPSerializerReuse.tape_support PCPPQuerySupport.machine _ _ raw hr j 0 0
      (by rw [hz.1]) (by rw [hz.2]; simp)
    simp only [Nat.zero_add,max_eq_right (Nat.zero_le _),rs] at h
    exact h.trans hC
  obtain ⟨reset,hreset,rf,rsteps,_⟩ :=
    MaskedReset.reset_run PCPPQuerySupport.machine selected _ _ raw hr hhead
  obtain ⟨result,hresult,ff,fs,_⟩ := ZeroPadding.run_config machine (caps C) _ _ reset hreset
  have he : 2*raw.steps+2=2*cost r p i+2 := by rw [rs]; rfl
  rw [he] at hresult
  refine ⟨result,hresult,fs.trans (rsteps.trans he),?_,?_,?_,?_,?_,?_⟩
  · rw [ff,rf]
    change ZeroPadding.pad 0 (raw.final.tapes 0)=pcppOutput r p
    simpa only [ZeroPadding.pad_zero] using hsource
  · rw [ff,rf]
    change ZeroPadding.pad 0 (raw.final.tapes 3)=UnaryTemplate.tape r.arity
    simpa only [ZeroPadding.pad_zero] using harity
  · rw [ff,rf]
    change ZeroPadding.pad 0 (raw.final.tapes 5)=UnaryTemplate.tape i.val
    simpa only [ZeroPadding.pad_zero] using hindex
  · rw [ff,rf]
    change ZeroPadding.pad 0 (raw.final.tapes 4)=PCPPQuerySupport.mask r p i
    simpa only [ZeroPadding.pad_zero] using ho
  · intro j
    rw [ff,rf]
    fin_cases j <;> simp [ZeroPadding.config,SelectiveReset.finished,Rewind.config,
      Fin.addCases,selected,hh3,hh5]
  · intro j hj
    rw [ff,rf]
    rcases hj with rfl|rfl|rfl
    · change (ZeroPadding.pad C (raw.final.tapes 1)).length ≤ C
      rw [ZeroPadding.pad_length]
      exact max_le le_rfl (hsmall 1 (Or.inl rfl))
    · change (ZeroPadding.pad C (raw.final.tapes 2)).length ≤ C
      rw [ZeroPadding.pad_length]
      exact max_le le_rfl (hsmall 2 (Or.inr rfl))
    · change (ZeroPadding.pad C (List.replicate raw.steps false)).length ≤ C
      rw [ZeroPadding.pad_length,List.length_replicate,rs]
      exact max_le le_rfl (by change cost r p i ≤ C; omega)

end NearCubicWires.RepairOrdinary.PCPPQuerySupportReset
