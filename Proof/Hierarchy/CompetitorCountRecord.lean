import Proof.Hierarchy.CompetitorCountRecordPrepare
import Proof.Hierarchy.CompetitorCountProducerTemplate
import Proof.Amplification.RecoveryFocusDock

/-! The exact six-field monomial record is physically assembled from a native
count table and its count sentinel. The scalar width supplies the zero field
and reusable append counter. Coefficient and normalization fields are retained
at their actual caller tapes; the count field is the executed exact SUM. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountRecord
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts CompetitorRationalDecision
open CompetitorMonomialProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def prepareSlots (i : Fin 23) : Fin 38 := i.castAdd 15
def sumSlots : Fin 11 → Fin 38 := ![23,24,0,25,26,27,28,29,30,31,32]
def fields : List (Fin 38) := [33,34,35,20,36,27]
noncomputable def prepare := RecoveryFocus.machine prepareSlots CompetitorCountRecordPrepare.machine
noncomputable def sum := RecoveryFocus.machine sumSlots CompetitorCountProducer.machine
noncomputable def prefixMachine := Composition.machine prepare sum
noncomputable def emit := CompetitorRawFieldEmit.listProgram (37 : Fin 38) 22 fields
noncomputable def machine := Composition.machine prefixMachine emit

def input (Q b : ℕ) (q : ℚ) (denominator : ℕ) (xs : List ℕ) : Fin 38 → List Bool :=
  fun i => match i.val with
    | 0 => List.replicate b true
    | 23 => CompetitorCountFold.raw Q xs
    | 24 => List.replicate Q true
    | 30 => UnaryTemplate.tape xs.length
    | 33 => frame (binary (width b) (positive q))
    | 34 => frame (binary (width b) (negative q))
    | 35 => frame (binary (width b) q.den)
    | 36 => frame (binary b denominator)
    | _ => []
def scalarFields (b : ℕ) (q : ℚ) (denominator count : ℕ) : Fin 38 → List Bool :=
  fun i => match i.val with
    | 33 => binary (width b) (positive q)
    | 34 => binary (width b) (negative q)
    | 35 => binary (width b) q.den
    | 20 => binary (width b) 0
    | 36 => binary b denominator
    | 27 => binary b count
    | _ => []
def heads (Q n : ℕ) (i : Fin 38) := if i.val=23 then Q*n else if i.val=30 then 1 else 0
def prefixBudget (b n : ℕ) := CompetitorCountRecordPrepare.budget b+1+CompetitorCountProducer.budget b n
def budget (b n : ℕ) := prefixBudget b n+1+(40*b+56)

theorem prepare_injective : Function.Injective prepareSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 38 => k.val) h)

theorem stream_eq (b : ℕ) (q : ℚ) (denominator count : ℕ) :
    CompetitorRawFieldEmit.stream (scalarFields b q denominator count) fields=
      CompetitorMonomialStream.recordWord b q count denominator := by
  rfl

theorem emit_cost (b : ℕ) (q : ℚ) (denominator count : ℕ) :
    CompetitorRawFieldEmit.listCost (scalarFields b q denominator count) fields=40*b+56 := by
  simp [CompetitorRawFieldEmit.listCost,scalarFields,fields,width]
  omega

theorem prefix_run (Q b : ℕ) (q : ℚ) (denominator : ℕ) (xs : List ℕ)
    (hQ : Q≤b) (hx : ∀ x∈xs,x<2^Q) (hfit : xs.sum<2^b) :
    ∃ r,run prefixMachine (prefixBudget b xs.length) (input Q b q denominator xs)=some r ∧
      r.steps≤prefixBudget b xs.length ∧ r.final.heads=heads Q xs.length ∧
      (∀ j∈fields,r.final.tapes j=frame (scalarFields b q denominator xs.sum j)) ∧
      r.final.tapes 22=List.replicate (2*width b+1) false ∧ r.final.tapes 37=[] ∧
      r.final.tapes 23=CompetitorCountFold.raw Q xs ∧ r.final.tapes 0=List.replicate b true := by
  obtain ⟨p,hp,p0,p20,p22⟩ := CompetitorCountRecordPrepare.prepare_run b
  have hprep := bounded_focus prepareSlots prepare_injective _ _ _ hp (input Q b q denominator xs)
    (by intro i; fin_cases i <;> rfl)
  let middle := install prepareSlots (input Q b q denominator xs) p
  obtain ⟨first,hfirst,hft,hfh,hfs⟩ := hprep
  have fresh (i : Fin 38) (hi : 23 ≤ i.val) : middle i=input Q b q denominator xs i := by
    apply install_other
    intro j hj
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    omega
  have m0 : middle 0=List.replicate b true :=
    (install_slot prepareSlots prepare_injective _ _ 0).trans p0
  obtain ⟨base,hbase,b5,b0,bs,bh,b1,b2⟩ := CompetitorCountProducer.template_run Q b xs hQ hx hfit
  have hin : ∀ j,middle (sumSlots j)=CompetitorCountProducer.templateInput Q b xs j := by
    intro j
    fin_cases j
    · exact fresh _ (by decide)
    · exact fresh _ (by decide)
    · exact m0
    all_goals exact fresh _ (by decide)
  obtain ⟨last,hlast,_,hls,hlh,hlt,keep⟩ := RecoveryFocus.dock sumSlots (by decide)
    CompetitorCountProducer.machine _ (fun _ => 0) middle _ (by intro j; rfl) hin base hbase
  have he : Composition.restart first.final sum.start=
      (⟨CompetitorCountProducer.machine.start,fun _ => 0,middle⟩ : Configuration 38 _) := by
    apply configuration_ext
    · rfl
    · exact funext hfh
    · exact hft
  have hl' : runFrom sum (CompetitorCountProducer.budget b xs.length)
      (Composition.restart first.final sum.start)=some last := by rw [he]; exact hlast
  have hall := Composition.run_join prepare sum _ _ _ first last hfirst hl'
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,?_,?_,?_,?_,?_⟩
  · change first.steps+1+last.steps≤prefixBudget b xs.length
    rw [hls]
    unfold prefixBudget
    omega
  · change last.final.heads=_
    funext i
    by_cases hi : ∃ j,sumSlots j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [hlh,bh]
      fin_cases j <;> rfl
    · have k := (keep i (fun j hj => hi ⟨j,hj⟩)).1
      rw [k]
      have h23 : i.val≠23 := by intro hv; exact hi ⟨0,Fin.ext hv.symm⟩
      have h30 : i.val≠30 := by intro hv; exact hi ⟨8,Fin.ext hv.symm⟩
      simp [heads,h23,h30]
  · intro j hj
    change last.final.tapes j=_
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ((keep 33 (by decide)).2).trans (fresh _ (by decide))
    · exact ((keep 34 (by decide)).2).trans (fresh _ (by decide))
    · exact ((keep 35 (by decide)).2).trans (fresh _ (by decide))
    · exact ((keep 20 (by decide)).2).trans ((install_slot prepareSlots prepare_injective _ _ 20).trans p20)
    · exact ((keep 36 (by decide)).2).trans (fresh _ (by decide))
    · exact (hlt 5).trans b5
  · exact ((keep 22 (by decide)).2).trans ((install_slot prepareSlots prepare_injective _ _ 22).trans p22)
  · exact ((keep 37 (by decide)).2).trans (fresh _ (by decide))
  · exact (hlt 0).trans b0
  · exact (hlt 2).trans b2

theorem record_run (Q b : ℕ) (q : ℚ) (denominator : ℕ) (xs : List ℕ)
    (hQ : Q≤b) (hx : ∀ x∈xs,x<2^Q) (hfit : xs.sum<2^b) :
    ∃ r,run machine (budget b xs.length) (input Q b q denominator xs)=some r ∧
      r.steps≤budget b xs.length ∧
      r.final.tapes 37=CompetitorMonomialStream.recordWord b q xs.sum denominator ∧
      r.final.heads=Function.update (heads Q xs.length) 37
        (CompetitorMonomialStream.recordWord b q xs.sum denominator).length ∧
      r.final.tapes 23=CompetitorCountFold.raw Q xs ∧ r.final.tapes 0=List.replicate b true := by
  obtain ⟨first,hfirst,hfs,hfh,hfields,hcounter,hout,hsource,hwidth⟩ := prefix_run Q b q denominator xs hQ hx hfit
  have hs : ∀ j∈fields,heads Q xs.length j=0 := by
    intro j hj
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  have hc : ∀ j∈fields,2*(scalarFields b q denominator xs.sum j).length+1≤2*width b+1 := by
    intro j hj
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [scalarFields,width] <;> omega
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := CompetitorRawFieldEmit.list_run (37 : Fin 38) 22 fields
    (scalarFields b q denominator xs.sum) (by decide) (by decide) (by decide)
    [] (2*width b+1) (heads Q xs.length) first.final.tapes hs rfl rfl hfields hout hcounter hc
  rw [emit_cost] at hlast hls
  have he : Composition.restart first.final emit.start=
      RecoveryCalls.restarted emit (heads Q xs.length) first.final.tapes := by
    apply configuration_ext
    · rfl
    · exact hfh
    · rfl
  have hl' : runFrom emit (40*b+56) (Composition.restart first.final emit.start)=some last := by
    rw [he]
    exact hlast
  have hall := Composition.run_join prefixMachine emit _ _ _ first last hfirst hl'
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,?_,?_,?_⟩
  · change first.steps+1+last.steps≤budget b xs.length
    unfold budget
    omega
  · change last.final.tapes 37=_
    rw [hlt,Function.update_self,List.nil_append,stream_eq]
  · change last.final.heads=_
    simpa only [List.nil_append,stream_eq] using hlh
  · change last.final.tapes 23=_
    rw [hlt,Function.update_of_ne (by decide)]
    exact hsource
  · change last.final.tapes 0=_
    rw [hlt,Function.update_of_ne (by decide)]
    exact hwidth

end NearCubicWires.RepairOrdinary.CompetitorCountRecord
