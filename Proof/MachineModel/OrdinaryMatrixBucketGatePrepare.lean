import Proof.MachineModel.OrdinaryMatrixBucketNativeReturn

/-! Actual reusable gate entry. Only the old local packet and boundary are
erased; bounded record/clone state, inner coordinate, global source and
append cursors are retained. The new zero boundary is physically copied. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketGatePrepare
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch MatrixBatchBucketEndpoints MatrixScoreWeight
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (r : Request) (unused : Fin 3 → List Bool) (source : List Bool) : Fin 12 → List Bool :=
  ![List.replicate (MatrixScoreReusableRanks.D r) true,frame (SignedSortKey.binary (H r) 0),
    frame (SignedSortKey.binary (H r) (r.bucketSize+1)),frame (SignedSortKey.binary r.M 0),
    UnaryTemplate.tape r.Buckets,unused 0,unused 1,unused 2,zeros (MatrixScoreReusableRanks.D r),
    zeros (MatrixScoreReusableRanks.D r),zeros (MatrixScoreReusableRanks.D r+1),source]
def core (r : Request) (inner boundary rank : ℕ) (upper record clone packet out : List Bool) : Fin 23 → List Bool :=
  ![frame (SignedSortKey.binary (H r) boundary),frame (SignedSortKey.binary (H r) (r.bucketSize+1)),
    upper,zeros (2*H r+1),frame (SignedSortKey.binary (H r) rank),[false],[true],zeros (6*H r+6),
    out,record,clone,zeros (4*H r+1),zeros (8*H r+3),zeros (2*H r+1),zeros (24*H r+14),packet,
    frame (SignedSortKey.binary r.M 0),frame (SignedSortKey.binary r.M inner),frame (SignedSortKey.binary r.M 0),
    zeros (MatrixScoreReusableRanks.D r),zeros (MatrixScoreReusableRanks.D r),zeros (4*H r+3),
    UnaryTemplate.tape r.Buckets]
theorem native_core {s : ℕ} (r : Request) (q : Fin s) (inner boundary rank : ℕ)
    (upper record clone packet out : List Bool) :
    (MatrixBucketNativeCall.cfg r q inner boundary rank upper record clone packet out 1).tapes=
      fun i => ZeroPadding.pad (MatrixScoreReusableRanks.D r) (core r inner boundary rank upper record clone packet out i) := by
  funext i
  fin_cases i <;> rfl

def data (r : Request) (inner boundary rank : ℕ) (upper record clone packet out : List Bool)
    (unused : Fin 3 → List Bool) (source : List Bool) : Fin 35 → List Bool :=
  Fin.addCases (m := 23) (n := 12) (motive := fun _ => List Bool)
    (MatrixBucketNativeCall.cfg r (0 : Fin 1) inner boundary rank upper record clone packet out 1).tapes
    (extra r unused source)
def heads (outLen pos : ℕ) (i : Fin 35) := if i=8 then outLen else if i=22 then 1 else if i=34 then pos else 0

def clearSlots : Fin 4 → Fin 35 := ![0,15,23,33]
def copySlots : Fin 4 → Fin 35 := ![24,0,31,32]
noncomputable def first := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 2)
noncomputable def last := RecoveryFocus.machine copySlots copyMachine
noncomputable def machine := Composition.machine first last
noncomputable def cfg (r : Request) (inner boundary rank : ℕ) (upper record clone packet out : List Bool)
    (unused : Fin 3 → List Bool) (source : List Bool) (pos : ℕ) : Configuration 35 10 :=
  ⟨machine.start,heads out.length pos,data r inner boundary rank upper record clone packet out unused source⟩
def budget (r : Request) := (2*MatrixScoreReusableRanks.D r+4)+1+(8*H r+8)

theorem data_same (r : Request) (inner boundary rank : ℕ) (upper record clone packet out : List Bool)
    (unused : Fin 3 → List Bool) (source : List Bool) (i : Fin 35) (h0 : i≠0) (h15 : i≠15) :
    data r inner boundary rank upper record clone packet out unused source i=
      data r inner 0 rank upper record clone [] out unused source i := by
  revert h0 h15
  refine Fin.addCases (m := 23) (n := 12)
    (motive := fun j => j≠0 → j≠15 →
      data r inner boundary rank upper record clone packet out unused source j=
        data r inner 0 rank upper record clone [] out unused source j)
    (fun j => ?_) (fun j => ?_) i
  · intro h0 h15
    by_cases hj0 : j=0
    · subst j
      exact (h0 rfl).elim
    by_cases hj15 : j=15
    · subst j
      exact (h15 rfl).elim
    simp only [data,Fin.addCases_left,native_core]
    apply congrArg (ZeroPadding.pad (MatrixScoreReusableRanks.D r))
    fin_cases j <;> first | exact (hj0 rfl).elim | exact (hj15 rfl).elim | simp only [core,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · intro _ _
    simp only [data,Fin.addCases_right]

theorem prepare_run (r : Request) (inner boundary rank : ℕ) (upper record clone packet out : List Bool)
    (unused : Fin 3 → List Bool) (source : List Bool) (pos : ℕ)
    (hpacket : packet.length ≤ MatrixScoreReusableRanks.D r) :
    ∃ actual,runFrom machine (budget r) (cfg r inner boundary rank upper record clone packet out unused source pos)=some actual ∧
      actual.final.heads=heads out.length pos ∧
      actual.final.tapes=data r inner 0 rank upper record clone [] out unused source ∧ actual.steps=budget r := by
  let D := MatrixScoreReusableRanks.D r
  let initial := data r inner boundary rank upper record clone packet out unused source
  have hH := MatrixBucketCallBounds.workspace_fit r
  have hwidth : 2*H r+1 ≤ D := by dsimp [D]; omega
  have hx : (scalar D (H r) boundary).length ≤ D := by simp [scalar,ZeroPadding.pad_length]; exact hwidth
  have hp : (ZeroPadding.pad D packet).length ≤ D := by
    rw [ZeroPadding.pad_length]
    exact max_le (Nat.le_refl _) hpacket
  have clearReady := RecoveryScratchErase.erase_ready D (D+1)
    (![scalar D (H r) boundary,ZeroPadding.pad D packet] : Fin 2 → List Bool)
    (by intro i; fin_cases i <;> assumption)
  obtain ⟨clear,hclear,ct,ch,cs⟩ := clearReady
  let clearEntry := initialConfiguration (RecoveryScratchErase.resetMachine 2)
    (Fin.addCases (m := 3) (n := 1) (motive := fun _ => List Bool)
      (Fin.addCases (m := 2) (n := 1) (motive := fun _ => List Bool)
        (![scalar D (H r) boundary,ZeroPadding.pad D packet]) (fun _ => List.replicate D true))
      (fun _ => zeros (D+1)))
  obtain ⟨prepared,hprep,pf,ps⟩ := RecoveryFocus.run_config clearSlots (by decide)
    (RecoveryScratchErase.resetMachine 2) (heads out.length pos) initial _ clearEntry clear hclear
  have hi : RecoveryFocus.config clearSlots (heads out.length pos) initial clearEntry=
      ⟨first.start,heads out.length pos,initial⟩ := by
    apply WilliamsSourceCrop.focus_same clearSlots
      (⟨first.start,heads out.length pos,initial⟩ : Configuration 35 4) clearEntry
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
  rw [hi] at hprep
  have pslot (i : Fin 4) : prepared.final.tapes (clearSlots i)=
      (![zeros D,zeros D,List.replicate D true,zeros (D+1)] : Fin 4 → List Bool) i := by
    rw [pf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot clearSlots (by decide),ct,Nat.max_self]
    fin_cases i <;> rfl
  have pold (i : Fin 35) (hi : ∀ j,clearSlots j≠i) : prepared.final.tapes i=initial i := by
    rw [pf]
    simp [RecoveryFocus.config,RecoveryFocus.pick,not_exists.mpr hi]
  have ph : prepared.final.heads=heads out.length pos := by
    rw [pf]
    funext i
    cases hi : RecoveryFocus.pick clearSlots i with
    | none => simp only [RecoveryFocus.config,hi]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick clearSlots hi
      subst i
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot clearSlots (by decide),ch]
      fin_cases j <;> rfl
  obtain ⟨copy,hcopy,copied,copyH,copyS⟩ := MatrixScoreInitialize.native_copy D (H r) 0 (by dsimp [D]; omega)
  let copyEntry := initialConfiguration copyMachine
    ![frame (SignedSortKey.binary (H r) 0),zeros D,zeros D,zeros D]
  have hcopyIn : RecoveryFocus.config copySlots prepared.final.heads prepared.final.tapes copyEntry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; rw [ph]; fin_cases i <;> rfl
    · intro i; fin_cases i
      · exact pold 24 (by decide)
      · exact pslot 0
      · exact pold 31 (by decide)
      · exact pold 32 (by decide)
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config copySlots (by decide) copyMachine
    prepared.final.heads prepared.final.tapes _ copyEntry copy hcopy
  rw [hcopyIn] at hf
  have joined := Composition.run_join first last _ _ _ prepared focused hprep hf
  have fslot (i : Fin 4) : focused.final.tapes (copySlots i)=
      (![frame (SignedSortKey.binary (H r) 0),scalar D (H r) 0,zeros D,zeros D] : Fin 4 → List Bool) i := by
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot copySlots (by decide),copied]
  have fold (i : Fin 35) (hi : ∀ j,copySlots j≠i) : focused.final.tapes i=prepared.final.tapes i := by
    rw [ff]
    simp [RecoveryFocus.config,RecoveryFocus.pick,not_exists.mpr hi]
  refine ⟨Composition.joinedReceipt prepared focused,joined,?_,?_,?_⟩
  · change focused.final.heads=_
    rw [ff]
    funext i
    cases hi : RecoveryFocus.pick copySlots i with
    | none => simp only [RecoveryFocus.config,hi,ph]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick copySlots hi
      subst i
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot copySlots (by decide),copyH]
      fin_cases j <;> rfl
  · change focused.final.tapes=_
    funext i
    fin_cases i
    · exact fslot 1
    all_goals first
      | exact (fold 15 (by decide)).trans (pslot 1)
      | exact (fold 23 (by decide)).trans (pslot 2)
      | exact (fold 33 (by decide)).trans (pslot 3)
      | exact fslot 0
      | exact fslot 2
      | exact fslot 3
      | (apply (fold _ (by decide)).trans
         apply (pold _ (by decide)).trans
         exact data_same r inner boundary rank upper record clone packet out unused source _ (by decide) (by decide))
  · change prepared.steps+1+focused.steps=budget r
    rw [ps,fs,cs,copyS]
    rfl

end NearCubicWires.RepairOrdinary.MatrixBucketGatePrepare
