import Proof.PCP.PCPPQuerySupportErase
import Proof.Amplification.RecoveryFocusDock

/-! A complete cached support call with paid rewind and scratch erasure.
The raw mask occupies its first arity cells; allocated zero padding is kept
explicit so repeated callers never assume that erasure shrinks a tape. -/
namespace NearCubicWires.RepairOrdinary.PCPPQuerySupportReuse
open LocalBitMultitape RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def resultCaps (C : ℕ) (j : Fin 7) := if j=4 then C else 0
def extra (C : ℕ) : Fin 2 → List Bool := ![List.replicate C true,List.replicate (C+1) false]
noncomputable def first := TapeEmbedding.machine 2 PCPPQuerySupportReset.machine
noncomputable def machine := Composition.machine first eraseMachine
noncomputable def entry (source : List Bool) (arity index C : ℕ) :=
  Composition.leftConfig 4 (TapeEmbedding.config (fun _ => 0) (extra C)
    (ZeroPadding.config (resultCaps C) (PCPPQuerySupportReset.entry source arity index C)))
def data (source : List Bool) (arity index C : ℕ) (mask : List Bool) : Fin 9 → List Bool :=
  ![source,List.replicate C false,List.replicate C false,UnaryTemplate.tape arity,
    ZeroPadding.pad C mask,UnaryTemplate.tape index,List.replicate C false,
    List.replicate C true,List.replicate (C+1) false]
def heads (j : Fin 9) := if j=3 ∨ j=5 then 1 else 0
def budget {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (i : Fin p.systematicBits) (C : ℕ) := 2*PCPPQuerySupportReset.cost r p i+2*C+7

theorem lookup_run {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (i : Fin p.systematicBits) (C : ℕ) (hC : PCPPQuerySupportReset.cost r p i+1 ≤ C) :
    ∃ receipt,runFrom machine (budget r p i C) (entry (pcppOutput r p) r.arity i.val C)=some receipt ∧
      receipt.final.tapes=data (pcppOutput r p) r.arity i.val C (PCPPQuerySupport.mask r p i) ∧
      receipt.final.heads=heads ∧ receipt.steps=budget r p i C := by
  obtain ⟨raw,hr,rs,hsource,harity,hindex,hmask,hh,hsmall⟩ :=
    PCPPQuerySupportReset.lookup_run r p i C hC
  obtain ⟨padded,hp,pf,ps,_⟩ := ZeroPadding.run_config PCPPQuerySupportReset.machine
    (resultCaps C) _ _ raw hr
  let firstRun := TapeEmbedding.receipt (fun _ : Fin 2 => 0) (extra C) padded
  have firstCall := TapeEmbedding.run_embed PCPPQuerySupportReset.machine
    (fun _ : Fin 2 => 0) (extra C) _ _ padded hp
  have pt (j : Fin 7) : firstRun.final.tapes (j.castAdd 2)=
      ZeroPadding.pad (resultCaps C j) (raw.final.tapes j) := by
    exact (TapeEmbedding.receipt_tapes_old (fun _ : Fin 2 => 0) (extra C) padded j).trans
      (by rw [pf]; rfl)
  have ph (j : Fin 7) : firstRun.final.heads (j.castAdd 2)=raw.final.heads j := by
    exact (TapeEmbedding.receipt_heads_old (fun _ : Fin 2 => 0) (extra C) padded j).trans
      (by rw [pf]; rfl)
  have hb : ∀ j,(firstRun.final.tapes (scratchSlots j)).length ≤ C := by
    intro j
    fin_cases j
    · change (firstRun.final.tapes ((1 : Fin 7).castAdd 2)).length ≤ C
      rw [pt]
      simpa only [resultCaps,show (1 : Fin 7)≠4 by decide,if_false,ZeroPadding.pad_zero]
        using hsmall 1 (Or.inl rfl)
    · change (firstRun.final.tapes ((2 : Fin 7).castAdd 2)).length ≤ C
      rw [pt]
      simpa only [resultCaps,show (2 : Fin 7)≠4 by decide,if_false,ZeroPadding.pad_zero]
        using hsmall 2 (Or.inr (Or.inl rfl))
    · change (firstRun.final.tapes ((6 : Fin 7).castAdd 2)).length ≤ C
      rw [pt]
      simpa only [resultCaps,show (6 : Fin 7)≠4 by decide,if_false,ZeroPadding.pad_zero]
        using hsmall 6 (Or.inr (Or.inr rfl))
  have hheads : firstRun.final.heads=heads := by
    funext j
    refine Fin.addCases (m:=7) (n:=2) (motive:=fun j => firstRun.final.heads j=heads j)
      (fun k => ?_) (fun k => ?_) j
    · rw [ph,hh]
      fin_cases k <;> rfl
    · have h := TapeEmbedding.receipt_heads_new (fun _ : Fin 2 => 0) (extra C) padded k
      exact h.trans (by fin_cases k <;> rfl)
  obtain ⟨lastRun,lastCall,lh,lt,ls⟩ := erase_run C firstRun.final.heads firstRun.final.tapes hb
    rfl rfl (by intro j; rw [hheads]; fin_cases j <;> rfl) rfl rfl
  have joined := Composition.run_join first eraseMachine _ _ _ firstRun lastRun firstCall lastCall
  have hbudget : (2*PCPPQuerySupportReset.cost r p i+2)+1+(2*C+4)=budget r p i C := by
    unfold budget
    omega
  rw [hbudget] at joined
  refine ⟨Composition.joinedReceipt firstRun lastRun,joined,?_,lh.trans hheads,?_⟩
  · change lastRun.final.tapes=_
    rw [lt]
    funext j
    fin_cases j
    · change erased C firstRun.final.tapes (0 : Fin 9)=pcppOutput r p
      rw [erased_live C _ 0 (Or.inl rfl)]
      change firstRun.final.tapes ((0 : Fin 7).castAdd 2)=_
      rw [pt]
      change ZeroPadding.pad 0 (raw.final.tapes 0)=pcppOutput r p
      rw [ZeroPadding.pad_zero,hsource]
    · exact erased_slot C _ 0
    · exact erased_slot C _ 1
    · change erased C firstRun.final.tapes (3 : Fin 9)=UnaryTemplate.tape r.arity
      rw [erased_live C _ 3 (Or.inr (Or.inl rfl))]
      change firstRun.final.tapes ((3 : Fin 7).castAdd 2)=_
      rw [pt]
      change ZeroPadding.pad 0 (raw.final.tapes 3)=UnaryTemplate.tape r.arity
      rw [ZeroPadding.pad_zero,harity]
    · change erased C firstRun.final.tapes (4 : Fin 9)=ZeroPadding.pad C (PCPPQuerySupport.mask r p i)
      rw [erased_live C _ 4 (Or.inr (Or.inr (Or.inl rfl)))]
      change firstRun.final.tapes ((4 : Fin 7).castAdd 2)=_
      rw [pt]
      change ZeroPadding.pad C (raw.final.tapes 4)=ZeroPadding.pad C (PCPPQuerySupport.mask r p i)
      rw [hmask]
    · change erased C firstRun.final.tapes (5 : Fin 9)=UnaryTemplate.tape i.val
      rw [erased_live C _ 5 (Or.inr (Or.inr (Or.inr rfl)))]
      change firstRun.final.tapes ((5 : Fin 7).castAdd 2)=_
      rw [pt]
      change ZeroPadding.pad 0 (raw.final.tapes 5)=UnaryTemplate.tape i.val
      rw [ZeroPadding.pad_zero,hindex]
    · exact erased_slot C _ 2
    · exact erased_driver C _
    · exact erased_log C _
  · change padded.steps+1+lastRun.steps=budget r p i C
    rw [ps,rs,ls,hbudget]

end NearCubicWires.RepairOrdinary.PCPPQuerySupportReuse
