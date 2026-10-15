import Proof.CaseAnalysis.WitnessSourceCounts
import Proof.CaseAnalysis.WitnessCorePolicy

/-! One source metadata pass and one coefficient policy. The original
PCPP output and the public cache domain at head one are used directly;
the exact V, actual clause bits, q0 and coefficient bit cap are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (D : ℕ):=CorePolicy.tapes D+43
def countSlots (D : ℕ) (i : Fin 42) : Fin (tapes D):=⟨i.val,by dsimp only [tapes];omega⟩
def coreSlot (D : ℕ) : Fin (tapes D):=⟨42,by dsimp [tapes,CorePolicy.tapes];omega⟩
def policySlots (D : ℕ) (i : Fin (CorePolicy.tapes D)) : Fin (tapes D):=
  ⟨if i.val=0 then 42 else if i.val=5 then 38 else 43+i.val,by
    dsimp only [tapes];split_ifs <;> omega⟩
def q0Slot (D : ℕ):=policySlots D (CorePolicy.q0Slot D)
def capSlot (D : ℕ):=policySlots D (CorePolicy.capSlot D)
def heads (D : ℕ) (i : Fin (tapes D)) : ℕ:=if i.val=42 then 1 else 0
def input (D core : ℕ) (source : List Bool) (i : Fin (tapes D)) : List Bool:=
  if i.val=0 then source else if i.val=42 then UnaryTemplate.tape core else []
def count (D : ℕ):=RecoveryFocus.machine (countSlots D) SourceCounts.machine
def policy (D copies : ℕ) (delta : ℚ):=
  RecoveryFocus.machine (policySlots D) (CorePolicy.machine D copies delta)
def machine (D copies : ℕ) (delta : ℚ):=Composition.machine (count D) (policy D copies delta)
def entry (D copies core : ℕ) (delta : ℚ) (source : List Bool):=
  (⟨(machine D copies delta).start,heads D,input D core source⟩ : Configuration (tapes D) _)
def budget (D copies core a b cb : ℕ) (delta : ℚ):=
  SourceCounts.budget a b cb+1+CorePolicy.budget D copies core cb delta

theorem count_injective (D : ℕ) : Function.Injective (countSlots D):=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin (tapes D)=>k.val) h)
theorem policy_injective (D : ℕ) : Function.Injective (policySlots D):=by
  intro i j h
  have hv:=congrArg (fun k : Fin (tapes D)=>k.val) h
  dsimp only [policySlots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem count_outside (D : ℕ) (i : Fin (tapes D)) (hi : 42 ≤ i.val) :
    ∀ j,countSlots D j≠i:=by
  intro j h
  have hv:=congrArg (fun k : Fin (tapes D)=>k.val) h
  change j.val=i.val at hv
  omega
theorem policy_outside (D : ℕ) (i : Fin (tapes D)) (hi : i.val=0 ∨ i.val=40) :
    ∀ j,policySlots D j≠i:=by
  intro j h
  have hv:=congrArg (fun k : Fin (tapes D)=>k.val) h
  dsimp only [policySlots] at hv
  split_ifs at hv <;> rcases hi with hi|hi <;> omega
theorem policy_heads (D : ℕ) (i : Fin (CorePolicy.tapes D)) :
    heads D (policySlots D i)=CorePolicy.heads D i:=by
  dsimp only [heads,policySlots,CorePolicy.heads]
  split_ifs <;> omega

theorem policy_run (D copies core a b cb : ℕ) (delta : ℚ) (tail : List Bool) (hD : 1 ≤ D) : ∃ result,
    runFrom (machine D copies delta) (budget D copies core a b cb delta)
      (entry D copies core delta (SourceFields.word a b cb tail))=some result ∧
      result.steps ≤ budget D copies core a b cb delta ∧ result.final.heads=heads D ∧
      result.final.tapes (countSlots D 0)=SourceFields.word a b cb tail ∧
      result.final.tapes (countSlots D 40)=List.replicate (a+b) true ∧
      result.final.tapes (countSlots D 38)=List.replicate cb true ∧
      result.final.tapes (coreSlot D)=UnaryTemplate.tape core ∧
      result.final.tapes (q0Slot D)=List.replicate (CorePolicy.q0 D core) true ∧
      result.final.tapes (capSlot D)=List.replicate
        (natBitLength (CloseoutXor.cap delta (CorePolicy.q0 D core) copies*max 1 (2*2^cb))) true:=by
  let source:=SourceFields.word a b cb tail
  obtain ⟨co,hc,c0,cV,ccb⟩:=SourceCounts.counts_run a b cb tail
  obtain ⟨c,cr,ch,ct,cs⟩:=hc.focus_at (countSlots D) (count_injective D) (heads D)
    (input D core source) (by
      intro i
      simp only [input,countSlots,SourceCounts.input,if_neg (show i.val≠42 by omega)]
      rfl)
    (by intro i;simp only [heads,countSlots,if_neg (show i.val≠42 by omega)])
  have ccore:c.final.tapes (coreSlot D)=UnaryTemplate.tape core:=by
    rw [ct,install_other _ _ _ _ (count_outside D _ (by rfl))]
    rfl
  have cblank (i : Fin (tapes D)) (hi : 43 ≤ i.val) : c.final.tapes i=[]:=by
    rw [ct,install_other _ _ _ _ (count_outside D i (by omega))]
    simp only [input,if_neg (show i.val≠0 by omega),if_neg (show i.val≠42 by omega)]
  have cin:∀ i,c.final.tapes (policySlots D i)=CorePolicy.input D core cb i:=by
    intro i
    by_cases h0:i.val=0
    · simpa only [policySlots,if_pos h0,CorePolicy.input,coreSlot] using ccore
    by_cases h5:i.val=5
    · have he:policySlots D i=countSlots D 38:=by
        apply Fin.ext
        simp only [policySlots,if_neg h0,if_pos h5,countSlots]
        rfl
      rw [he,ct,install_slot _ (count_injective D),ccb]
      simp only [CorePolicy.input,if_neg h0,if_pos h5]
    rw [CorePolicy.input,if_neg h0,if_neg h5]
    exact cblank _ (by simp only [policySlots,if_neg h0,if_neg h5];omega)
  obtain ⟨p,pr,ps,ph,p0,pq,pcb,pb⟩:=CorePolicy.policy_run D copies core cb delta hD
  obtain ⟨last,lr,_,ls,lh,lt,la⟩:=RecoveryFocus.dock (policySlots D) (policy_injective D)
    (CorePolicy.machine D copies delta) _ c.final.heads c.final.tapes
    (CorePolicy.entry D copies core cb delta)
    (by intro i;rw [ch];exact policy_heads D i) cin p pr
  have joined:=Composition.run_join (count D) (policy D copies delta) _ _ _ c last cr lr
  refine ⟨Composition.joinedReceipt c last,joined,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change c.steps+1+last.steps ≤ budget D copies core a b cb delta
    rw [ls]
    unfold budget
    omega
  · change last.final.heads=heads D
    funext i
    by_cases hi:∃ j,policySlots D j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [lh,ph]
      exact (policy_heads D j).symm
    · rw [(la i (by simpa only [not_exists] using hi)).1,ch]
  · change last.final.tapes (countSlots D 0)=_
    rw [(la _ (policy_outside D _ (Or.inl rfl))).2,ct,install_slot _ (count_injective D)]
    exact c0
  · change last.final.tapes (countSlots D 40)=_
    rw [(la _ (policy_outside D _ (Or.inr rfl))).2,ct,install_slot _ (count_injective D)]
    exact cV
  · change last.final.tapes (policySlots D (CorePolicy.clauseSlot D))=_
    exact (lt _).trans pcb
  · change last.final.tapes (policySlots D (CorePolicy.templateSlots D 0))=_
    exact (lt _).trans p0
  · exact (lt _).trans pq
  · exact (lt _).trans pb

theorem actual_word {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) :
    pcppOutput r p=SourceFields.word p.systematicBits p.auxiliaryBits p.clauseBits
      ((PCPPQuerySupport.supportRows r p).flatten++PCPPQuerySupport.clauseTail r p):=by
  rw [PCPPQuerySupport.output_word]
  simp only [PCPPQuerySupport.headerBits,PCPPQueryField.fourBits,PCPPQueryField.pairBits,
    PCPPQueryField.fieldBits,SourceFields.word,PCPPNativeNodeRead.source,List.append_assoc]

theorem actual_run {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (D copies : ℕ) (delta : ℚ) (hD : 1 ≤ D) : ∃ result,
    runFrom (machine D copies delta) (budget D copies r.arity p.systematicBits p.auxiliaryBits p.clauseBits delta)
      (entry D copies r.arity delta (pcppOutput r p))=some result ∧
      result.steps ≤ budget D copies r.arity p.systematicBits p.auxiliaryBits p.clauseBits delta ∧
      result.final.heads=heads D ∧ result.final.tapes (countSlots D 0)=pcppOutput r p ∧
      result.final.tapes (countSlots D 40)=List.replicate (p.systematicBits+p.auxiliaryBits) true ∧
      result.final.tapes (countSlots D 38)=List.replicate p.clauseBits true ∧
      result.final.tapes (coreSlot D)=UnaryTemplate.tape r.arity ∧
      result.final.tapes (q0Slot D)=List.replicate (CorePolicy.q0 D r.arity) true ∧
      result.final.tapes (capSlot D)=List.replicate
        (natBitLength (CloseoutXor.cap delta (CorePolicy.q0 D r.arity) copies*max 1 (2*2^p.clauseBits))) true:=by
  rw [actual_word r p]
  exact policy_run D copies r.arity p.systematicBits p.auxiliaryBits p.clauseBits delta _ hD

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy
