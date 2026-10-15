import Proof.Hierarchy.CompetitorSameBucketGroupColdEntry

/-! Whole cold sorted-key-to-dense-bank execution: all dimensions, padding,
zero scalars and drivers are produced, then the SAME grouping controller
runs and a single paid outer rewind restores every head. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupCold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorSameBucketGroup
open CompetitorSameBucketGroupColdDimensions (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 24) : Fin 52 := i.castAdd 28
theorem slots_injective : Function.Injective slots := by
  intro i j h
  have hv := congrArg (fun x : Fin 52 => x.val) h
  exact Fin.ext hv
noncomputable def scan := RecoveryFocus.machine slots CompetitorSameBucketGroupMachine.machine
noncomputable def raw := Composition.machine CompetitorSameBucketGroupColdEntry.machine scan
noncomputable def machine := Rewind.machine raw
def rawBudget (w p m : ℕ) (es : List Entry) := CompetitorSameBucketGroupColdEntry.budget w p m+1+
  CompetitorSameBucketGroupMachine.streamBudget (capacity w p m) w p m es
def budget (w p m : ℕ) (es : List Entry) := 2*rawBudget w p m es+2
def input (w p m : ℕ) (source : List Bool) : Fin 53 → List Bool :=
  Fin.addCases (m := 52) (n := 1) (motive := fun _ => List Bool)
    (CompetitorSameBucketGroupColdDrivers.input w p m source) (fun _ => [])
def retained (w p m : ℕ) (source : List Bool) : Fin 4 → List Bool :=
  ![source,List.replicate w true,List.replicate p true,List.replicate m true]

theorem raw_run (w u p m : ℕ) (es : List Entry)
    (hpw : p ≤ w) (hd : ∀ e∈es,Domain u e) (hm : 2*u ≤ 2^m)
    (hs : es.Pairwise (fun a b => value (word (a.record p m)) ≤ value (word (b.record p m))))
    (coverage : ∀ row col : Fin u,∃ e∈es,e.row=row.val ∧ e.rightTaggedID=u+col.val)
    (hbits : ∀ e∈es,e.coefficient.natAbs<2^p)
    (hf : ∀ row col : Fin u,positive (atCell row.val (u+col.val) es)<2^w ∧
      negative (atCell row.val (u+col.val) es)<2^w) :
    ∃ r,run raw (rawBudget w p m es) (CompetitorSameBucketGroupColdDrivers.input w p m (stream p m es))=some r ∧
      r.final.tapes 4=dense w u es ∧
      (∀ i : Fin 4,r.final.tapes (i.castAdd 48)=retained w p m (stream p m es) i) ∧
      r.steps ≤ rawBudget w p m es := by
  obtain ⟨prepared,hp,ph,pt,ps⟩ := CompetitorSameBucketGroupColdEntry.prepare_run w p m (stream p m es)
  obtain ⟨hc,hw,_⟩ := CompetitorSameBucketGroupColdDimensions.capacity_bounds w p m
  obtain ⟨group,hg,_,gt,gs⟩ := CompetitorSameBucketGroupMachine.dense_run (capacity w p m) w u p m es
    hpw hc hw hd hm hs coverage hbits hf
  obtain ⟨actual,ha,_,ast,_,atapes,_⟩ := RecoveryFocus.dock slots slots_injective
    CompetitorSameBucketGroupMachine.machine _ prepared.final.heads prepared.final.tapes _
    (by intro i;rw [ph];fin_cases i <;> rfl) (by intro i;exact pt i) group hg
  change runFrom scan (CompetitorSameBucketGroupMachine.streamBudget (capacity w p m) w p m es)
    (Composition.restart prepared.final scan.start)=some actual at ha
  have hjoined := Composition.run_join CompetitorSameBucketGroupColdEntry.machine scan _ _ _ prepared actual hp ha
  refine ⟨Composition.joinedReceipt prepared actual,hjoined,?_,?_,?_⟩
  · exact (atapes 4).trans (by rw [gt];rfl)
  · intro i
    fin_cases i
    · exact (atapes 0).trans (by rw [gt];rfl)
    · exact (atapes 1).trans (by rw [gt];rfl)
    · exact (atapes 2).trans (by rw [gt];rfl)
    · exact (atapes 3).trans (by rw [gt];rfl)
  · change prepared.steps+1+actual.steps ≤ rawBudget w p m es
    rw [ast]
    unfold rawBudget
    omega

theorem cold_run (w u p m : ℕ) (es : List Entry)
    (hpw : p ≤ w) (hd : ∀ e∈es,Domain u e) (hm : 2*u ≤ 2^m)
    (hs : es.Pairwise (fun a b => value (word (a.record p m)) ≤ value (word (b.record p m))))
    (coverage : ∀ row col : Fin u,∃ e∈es,e.row=row.val ∧ e.rightTaggedID=u+col.val)
    (hbits : ∀ e∈es,e.coefficient.natAbs<2^p)
    (hf : ∀ row col : Fin u,positive (atCell row.val (u+col.val) es)<2^w ∧
      negative (atCell row.val (u+col.val) es)<2^w) :
    ∃ r,run machine (budget w p m es) (input w p m (stream p m es))=some r ∧
      r.final.tapes 4=dense w u es ∧
      (∀ i : Fin 4,r.final.tapes (i.castAdd 49)=retained w p m (stream p m es) i) ∧
      (∀ i,r.final.heads i=0) ∧ r.steps ≤ budget w p m es := by
  obtain ⟨base,hb,bt,br,bs⟩ := raw_run w u p m es hpw hd hm hs coverage hbits hf
  obtain ⟨r,hr,rt,rh,rs,_⟩ := Rewind.reset_run raw _ _ base hb
  have hbound : 2*base.steps+2 ≤ budget w p m es := by unfold budget;omega
  have hmore := run_moreFuel machine (2*base.steps+2) (budget w p m es-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hbound] at hmore
  refine ⟨r,hmore,(rt 4).trans bt,?_,rh,rs.trans_le hbound⟩
  intro i
  have h := (rt (i.castAdd 48)).trans (br i)
  exact h

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupCold
