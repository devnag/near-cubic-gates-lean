import Proof.MachineModel.OrdinaryMatrixNativeDimensions

/-! Three native dimension words produced from the original request, using
the actual retained common width and canonical unary dimensions. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchNativeDimensions
open LocalBitMultitape SignedSortKey MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def dimensions (r : Request) : Fin 3 → ℕ :=
  ![MatrixBucketDimensions.capacity r.U,MatrixBucketDimensions.width r.U r.Gates,MatrixBucketDimensions.buckets r.U r.Gates]
theorem dimensions_positive (r : Request) (j : Fin 3) : 0<dimensions r j := by
  have hU : 1≤r.U := Nat.one_le_two_pow
  fin_cases j
  · exact MatrixBucketDimensions.capacity_positive r.U hU
  · exact MatrixBucketDimensions.width_positive r.U r.Gates
  · exact MatrixBucketDimensions.buckets_positive r.U r.Gates
theorem dimensions_fit (r : Request) (j : Fin 3) : dimensions r j<2^r.M := by
  have hp : 2^r.M=8*r.U := by
    rw [common_width,Request.U,Nat.pow_add]
    norm_num
    omega
  have hu : 1≤r.U := Nat.one_le_two_pow
  have hc := MatrixBucketDimensions.capacity_le r.U
  have hw := MatrixBucketDimensions.width_le r.U r.Gates
  have hb := MatrixBucketDimensions.buckets_le r.U r.Gates
  rw [hp]
  fin_cases j
  · change MatrixBucketDimensions.capacity r.U<8*r.U
    omega
  · change MatrixBucketDimensions.width r.U r.Gates<8*r.U
    omega
  · change MatrixBucketDimensions.buckets r.U r.Gates<8*r.U
    omega

theorem source_fields (r : Request) :
    ∃ actual,run MatrixBatchNativeWidth.machine (MatrixBatchNativeWidth.budget r) (MatrixBatchNativeWidth.input r)=some actual ∧
      actual.final.tapes 225=List.replicate r.M true ∧ actual.final.heads 225=0 ∧
      actual.final.tapes 166=UnaryTemplate.tape (dimensions r 0) ∧ actual.final.heads 166=0 ∧
      actual.final.tapes 216=UnaryTemplate.tape (dimensions r 1) ∧ actual.final.heads 216=0 ∧
      actual.final.tapes 222=UnaryTemplate.tape (dimensions r 2) ∧ actual.final.heads 222=0 ∧
      actual.steps≤MatrixBatchNativeWidth.budget r := by
  obtain ⟨base,actual,hb,ha,atapes,ah,a225,h225,_,_,_,_,as⟩ := MatrixBatchNativeWidth.raw_run r
  obtain ⟨same,hs,_,_,_,_,s166,h166,_,_,_,_,_,_,s216,h216,s222,h222,_⟩ := MatrixBatchBucketSizes.raw_run r
  have heq : same=base := Option.some.inj (hs.symm.trans hb)
  subst same
  exact ⟨actual,ha,a225,h225,(atapes 166).trans s166,(ah 166).trans h166,
    (atapes 216).trans s216,(ah 216).trans h216,(atapes 222).trans s222,(ah 222).trans h222,as⟩

def slots (i : Fin 52) : Fin 277 := if i=0 then 225 else if i=1 then 166 else if i=2 then 216
  else if i=3 then 222 else ⟨229+(i.val-4),by omega⟩
theorem slots_injective : Function.Injective slots := by decide
theorem pick_old (i : Fin 229) (h225 : i≠225) (h166 : i≠166) (h216 : i≠216) (h222 : i≠222) :
    RecoveryFocus.pick slots (i.castAdd 48)=none := by
  fin_cases i <;> first | contradiction | decide
noncomputable def first := TapeEmbedding.machine 48 MatrixBatchNativeWidth.machine
noncomputable def last := RecoveryFocus.machine slots MatrixNativeDimensions.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 277 → List Bool := fun i => if i=0 then physicalInput r else []
def budget (r : Request) := MatrixBatchNativeWidth.budget r+1+MatrixNativeDimensions.budget r.M (dimensions r)

theorem native_run (r : Request) (base : ExecutionReceipt 229 _)
    (hb : run MatrixBatchNativeWidth.machine (MatrixBatchNativeWidth.budget r) (MatrixBatchNativeWidth.input r)=some base)
    (b225 : base.final.tapes 225=List.replicate r.M true) (h225 : base.final.heads 225=0)
    (b166 : base.final.tapes 166=UnaryTemplate.tape (dimensions r 0)) (h166 : base.final.heads 166=0)
    (b216 : base.final.tapes 216=UnaryTemplate.tape (dimensions r 1)) (h216 : base.final.heads 216=0)
    (b222 : base.final.tapes 222=UnaryTemplate.tape (dimensions r 2)) (h222 : base.final.heads 222=0)
    (bs : base.steps≤MatrixBatchNativeWidth.budget r) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      (∀ i : Fin 229,actual.final.tapes (i.castAdd 48)=base.final.tapes i) ∧
      (∀ i : Fin 229,actual.final.heads (i.castAdd 48)=base.final.heads i) ∧
      actual.final.tapes 242=frame (binary r.M (dimensions r 0)) ∧ actual.final.heads 242=0 ∧
      actual.final.tapes 258=frame (binary r.M (dimensions r 1)) ∧ actual.final.heads 258=0 ∧
      actual.final.tapes 274=frame (binary r.M (dimensions r 2)) ∧ actual.final.heads 274=0 ∧
      actual.steps≤budget r := by
  have he := TapeEmbedding.run_embed MatrixBatchNativeWidth.machine (fun _ : Fin 48 => 0) (fun _ : Fin 48 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 48 => 0) (fun _ : Fin 48 => []) base
  obtain ⟨out,ready,o0,odim,oresult⟩ := MatrixNativeDimensions.dimensions_run r.M (dimensions r)
    (dimensions_positive r) (dimensions_fit r)
  obtain ⟨body,hbody,bt,bh,bsteps⟩ := ready
  let entry := initialConfiguration MatrixNativeDimensions.machine (MatrixNativeDimensions.input r.M (dimensions r))
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i
      · exact h225
      · exact h166
      · exact h216
      · exact h222
      all_goals rfl
    · intro i; fin_cases i
      · exact b225
      · exact b166
      · exact b216
      · exact b222
      all_goals rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots slots_injective MatrixNativeDimensions.machine
    prepared.final.heads prepared.final.tapes _ entry body hbody
  rw [hi] at hf
  have joined := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 48 => 0) (fun _ : Fin 48 => [])
      (initialConfiguration MatrixBatchNativeWidth.machine (MatrixBatchNativeWidth.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have localT (i : Fin 52) : focused.final.tapes (slots i)=out i := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bt]
  have localH (i : Fin 52) : focused.final.heads (slots i)=0 := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bh]
  refine ⟨Composition.joinedReceipt prepared focused,joined,?_,?_,(localT 17).trans (oresult 0),localH 17,
    (localT 33).trans (oresult 1),localH 33,(localT 49).trans (oresult 2),localH 49,?_⟩
  · intro i
    change focused.final.tapes (i.castAdd 48)=_
    by_cases hi225 : i=225
    · subst i; exact (localT 0).trans (o0.trans b225.symm)
    by_cases hi166 : i=166
    · subst i; exact (localT 1).trans ((odim 0).trans b166.symm)
    by_cases hi216 : i=216
    · subst i; exact (localT 2).trans ((odim 1).trans b216.symm)
    by_cases hi222 : i=222
    · subst i; exact (localT 3).trans ((odim 2).trans b222.symm)
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi225 hi166 hi216 hi222]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · intro i
    change focused.final.heads (i.castAdd 48)=_
    by_cases hi225 : i=225
    · subst i; exact (localH 0).trans h225.symm
    by_cases hi166 : i=166
    · subst i; exact (localH 1).trans h166.symm
    by_cases hi216 : i=216
    · subst i; exact (localH 2).trans h216.symm
    by_cases hi222 : i=222
    · subst i; exact (localH 3).trans h222.symm
    rw [hff]
    simp only [RecoveryFocus.config,pick_old i hi225 hi166 hi216 hi222]
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  · change prepared.steps+1+focused.steps≤budget r
    rw [hfs]
    change base.steps+1+body.steps≤budget r
    unfold budget
    omega

theorem raw_run (r : Request) :
    ∃ base : ExecutionReceipt 229 _,∃ actual,
      run MatrixBatchNativeWidth.machine (MatrixBatchNativeWidth.budget r) (MatrixBatchNativeWidth.input r)=some base ∧
      run machine (budget r) (input r)=some actual ∧
      (∀ i : Fin 229,actual.final.tapes (i.castAdd 48)=base.final.tapes i) ∧
      (∀ i : Fin 229,actual.final.heads (i.castAdd 48)=base.final.heads i) ∧
      actual.final.tapes 242=frame (binary r.M (dimensions r 0)) ∧ actual.final.heads 242=0 ∧
      actual.final.tapes 258=frame (binary r.M (dimensions r 1)) ∧ actual.final.heads 258=0 ∧
      actual.final.tapes 274=frame (binary r.M (dimensions r 2)) ∧ actual.final.heads 274=0 ∧
      actual.steps≤budget r := by
  obtain ⟨base,hb,b225,h225,b166,h166,b216,h216,b222,h222,bs⟩ := source_fields r
  obtain ⟨actual,ha,atapes,ah,a242,h242,a258,h258,a274,h274,as⟩ :=
    native_run r base hb b225 h225 b166 h166 b216 h216 b222 h222 bs
  exact ⟨base,actual,hb,ha,atapes,ah,a242,h242,a258,h258,a274,h274,as⟩

end NearCubicWires.RepairOrdinary.MatrixBatchNativeDimensions
