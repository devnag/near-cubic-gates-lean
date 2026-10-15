import Proof.Amplification.RecoveryRowLookupSemantics

/-! Whole bounded prior-row lookup with the physical found flag and retained
binary count exposed to the balanced-row checker. Membership completeness
uses uniqueness of counts among the already checked rows. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowLookupTable
open LocalBitMultitape RecoveryRowLookupStream RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem iterate_inv (width total : Nat) (x : Cursor) (hx : Inv width x)
    (ha : (RepeatMachine.iterate next total x).1=true) :
    Inv width (RepeatMachine.iterate next total x).2 := by
  induction total generalizing x with
  | zero => exact hx
  | succ total ih =>
    cases hh : (next x).1 with
    | false => simp [RepeatMachine.iterate,hh] at ha
    | true =>
      simp only [RepeatMachine.iterate,hh,↓reduceIte] at ha ⊢
      exact ih (next x).2 (next_inv width x hx hh) ha

private theorem reject_ne_success (s : Nat) : RepeatMachine.phaseCode s 4≠RepeatMachine.phaseCode s 3 := by
  intro h
  have he := (RepeatMachine.code s).injective h
  cases he

noncomputable abbrev bodyStates := Fintype.card (RecoveryCalls.Control RecoveryRowLookupStream.sizes)

theorem result_acceptance (total : Nat) (x : Cursor)
    (final : Configuration 15 (Fintype.card (RepeatMachine.Control bodyStates)))
    (h : RepeatMachine.Result source total (RepeatMachine.iterate next total x) final) :
    final.control=RepeatMachine.phaseCode bodyStates 3 ↔
      (readMany (readRow x.data.row.width) total x.rest).isSome=true := by
  rw [←iterate_accepts]
  cases ha : (RepeatMachine.iterate next total x).1 with
  | false =>
    simp only [RepeatMachine.Result,ha,Bool.false_eq_true,↓reduceIte] at h
    rw [h]
    simp only [Bool.false_eq_true,iff_false]
    exact reject_ne_success _
  | true =>
    simp only [RepeatMachine.Result,ha,↓reduceIte] at h
    rw [h]
    exact iff_of_true rfl rfl

theorem result_lookup (width total : Nat) (x : Cursor) (hx : Inv width x)
    (rows : List Row) (rest : List Bool)
    (hparse : readMany (readRow x.data.row.width) total x.rest=some (rows,rest))
    (hfound : x.data.found=false)
    (final : Configuration 15 (Fintype.card (RepeatMachine.Control bodyStates)))
    (h : RepeatMachine.Result source total (RepeatMachine.iterate next total x) final) :
    ∃ word : List Bool,word.length≤width ∧ final.tapes 8=frame word ∧ final.heads 8=0 ∧
      final.tapes 9=[rows.any (fun row=>decide (value x.data.key=row.code))] ∧ final.heads 9=0 ∧
      value word=lookupOr rows (value x.data.key) (value x.data.saved) := by
  have ha : (RepeatMachine.iterate next total x).1=true := by rw [iterate_accepts,hparse]; rfl
  have hi := iterate_inv width total x hx ha
  have hv := congrArg Prod.snd (iterate_accumulator total x rows rest hparse)
  rw [fold_selected] at hv
  simp only [accumulator,hfound,Bool.false_eq_true,↓reduceIte] at hv
  have hf := congrArg Prod.fst (iterate_accumulator total x rows rest hparse)
  rw [fold_found] at hf
  simp only [accumulator,hfound,Bool.false_or] at hf
  simp only [RepeatMachine.Result,ha,↓reduceIte] at h
  rw [h]
  refine ⟨(RepeatMachine.iterate next total x).2.data.saved,?_,rfl,rfl,?_,rfl,hv⟩
  · exact hi.1.2.2.1.trans hi.2.1.le
  · exact congrArg List.singleton hf

theorem lookup_run (width total : Nat) (x : Cursor) (hx : Inv width x) (hfound : x.data.found=false) :
    ∃ r,runFrom machine (total*(budget width+3)+3)
        (RepeatMachine.cfg 0 (source x) total 1)=some r ∧
      r.steps≤total*(budget width+3)+3 ∧
      RepeatMachine.Result source total (RepeatMachine.iterate next total x) r.final ∧
      (r.final.control=RepeatMachine.phaseCode bodyStates 3 ↔
        (readMany (readRow x.data.row.width) total x.rest).isSome=true) ∧
      ∀ rows rest,readMany (readRow x.data.row.width) total x.rest=some (rows,rest) →
        ∃ word : List Bool,word.length≤width ∧ r.final.tapes 8=frame word ∧ r.final.heads 8=0 ∧
          r.final.tapes 9=[rows.any (fun row=>decide (value x.data.key=row.code))] ∧ r.final.heads 9=0 ∧
          value word=lookupOr rows (value x.data.key) (value x.data.saved) := by
  obtain ⟨r,hr,ht,hf⟩ := table_run width total x hx
  exact ⟨r,hr,ht,hf,result_acceptance total x r.final hf,
    fun rows rest hp=>result_lookup width total x hx rows rest hp hfound r.final hf⟩

theorem lookupCount_sound (rows : List Row) (key count : Nat) (h : lookupCount rows key=some count) :
    ∃ row∈rows,row.code=key ∧ row.count=count := by
  induction rows with
  | nil => simp [lookupCount] at h
  | cons row rest ih =>
    by_cases he : key=row.code
    · simp only [lookupCount,if_pos he,Option.some.injEq] at h
      exact ⟨row,List.mem_cons_self,he.symm,h⟩
    · simp only [lookupCount,if_neg he] at h
      obtain ⟨found,hf,hk,hc⟩ := ih h
      exact ⟨found,List.mem_cons_of_mem _ hf,hk,hc⟩

theorem lookupCount_of_member (rows : List Row) (key : Nat)
    (hp : ∀ row∈rows,Meaning row) (selected : Row) (hs : selected∈rows) (hk : selected.code=key) :
    lookupCount rows key=some selected.count := by
  induction rows with
  | nil => simp at hs
  | cons row rest ih =>
    by_cases he : key=row.code
    · have hn := meaning_count_unique row selected (hp row List.mem_cons_self) (hp selected hs)
        (he.symm.trans hk.symm)
      simp [lookupCount,he,hn]
    · have hrest : selected∈rest := by
        rcases List.mem_cons.mp hs with hh|hh
        · subst selected; exact False.elim (he hk.symm)
        · exact hh
      have h := ih (fun item hi=>hp item (List.mem_cons_of_mem _ hi)) hrest
      simpa only [lookupCount,if_neg he] using h

theorem checked_lookup_iff (rows : List Row) (hrows : checkFrom [] rows=true) (key count : Nat) :
    lookupCount rows key=some count ↔ ∃ row∈rows,row.code=key ∧ row.count=count := by
  constructor
  · exact lookupCount_sound rows key count
  · rintro ⟨row,hr,hk,hc⟩
    have hp := check_sound [] rows (by simp) hrows
    simpa only [hc] using lookupCount_of_member rows key (by simpa using hp) row hr hk

end NearCubicWires.RepairOrdinary.RecoveryRowLookupTable
