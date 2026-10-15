import Proof.Hierarchy.CompetitorSameBucketRankWorkspace

/-! Actual orientation and rank test for two present copied occurrences.
The left ID must be below U, the right ID at least U, and the left rank
strictly earlier. All three binary comparisons and resets are executed. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketPairCompare
open LocalBitMultitape SignedSortKey RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def compareInput (cap width a b : ℕ) : Fin 4 → List Bool :=
  ![ZeroPadding.pad cap (frame (binary width a)),ZeroPadding.pad cap (frame (binary width b)),
    ZeroPadding.pad cap [false],List.replicate cap false]
def compareOutput (cap width a b : ℕ) : Fin 4 → List Bool :=
  ![ZeroPadding.pad cap (frame (binary width a)),ZeroPadding.pad cap (frame (binary width b)),
    ZeroPadding.pad cap [decide (a≤b)],List.replicate cap false]

theorem compare_ready (cap width a b : ℕ) (ha : a<2^width) (hb : b<2^width) (hc : 2*width+1≤cap) :
    ClockJoin.ReadyRun CompetitorSignedDecision.compareMachine (4*width+4)
      (compareInput cap width a b) (compareOutput cap width a b) := by
  obtain ⟨base,hr,bt,bh,bs⟩ := MatrixUnaryCompare.compare_ready width a b ha hb
  obtain ⟨actual,hh,hf,hs,_⟩ := ZeroPadding.run_config CompetitorSignedDecision.compareMachine (fun _ => cap) _ _ base hr
  have hi : ZeroPadding.config (fun _ => cap)
      (initialConfiguration CompetitorSignedDecision.compareMachine
        ![frame (binary width a),frame (binary width b),[false],List.replicate (2*width+1) false])=
      initialConfiguration CompetitorSignedDecision.compareMachine (compareInput cap width a b) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,initialConfiguration,compareInput,Rewind.Workspace.pad_zeros,max_eq_left hc]
  rw [hi] at hh
  refine ⟨actual,hh,?_,?_,hs.trans_le bs.le⟩
  · rw [hf]
    funext i
    fin_cases i <;> simp [ZeroPadding.config,bt,compareOutput,Rewind.Workspace.pad_zeros,max_eq_left hc]
  · intro i
    rw [hf]
    exact bh i

def leftSlots : Fin 4 → Fin 10 := ![0,1,5,8]
def rightSlots : Fin 4 → Fin 10 := ![0,2,6,8]
def orderSlots : Fin 4 → Fin 10 := ![4,3,7,8]
theorem left_injective : Function.Injective leftSlots := by decide
def leftPick : Fin 10 → Option (Fin 4) := ![some 0,some 1,none,none,none,some 2,none,none,some 3,none]
theorem left_pick (i : Fin 10) : RecoveryFocus.pick leftSlots i=leftPick i := by
  classical
  fin_cases i
  · exact RecoveryFocus.pick_slot leftSlots left_injective 0
  · exact RecoveryFocus.pick_slot leftSlots left_injective 1
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · exact RecoveryFocus.pick_slot leftSlots left_injective 2
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · exact RecoveryFocus.pick_slot leftSlots left_injective 3
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
theorem right_injective : Function.Injective rightSlots := by decide
def rightPick : Fin 10 → Option (Fin 4) := ![some 0,none,some 1,none,none,none,some 2,none,some 3,none]
theorem right_pick (i : Fin 10) : RecoveryFocus.pick rightSlots i=rightPick i := by
  classical
  fin_cases i
  · exact RecoveryFocus.pick_slot rightSlots right_injective 0
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · exact RecoveryFocus.pick_slot rightSlots right_injective 1
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · exact RecoveryFocus.pick_slot rightSlots right_injective 2
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · exact RecoveryFocus.pick_slot rightSlots right_injective 3
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
theorem order_injective : Function.Injective orderSlots := by decide
def orderPick : Fin 10 → Option (Fin 4) := ![none,none,none,some 1,some 0,none,none,some 2,some 3,none]
theorem order_pick (i : Fin 10) : RecoveryFocus.pick orderSlots i=orderPick i := by
  classical
  fin_cases i
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · exact RecoveryFocus.pick_slot orderSlots order_injective 1
  · exact RecoveryFocus.pick_slot orderSlots order_injective 0
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · exact RecoveryFocus.pick_slot orderSlots order_injective 2
  · exact RecoveryFocus.pick_slot orderSlots order_injective 3
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide

noncomputable def left := RecoveryFocus.machine leftSlots CompetitorSignedDecision.compareMachine
noncomputable def right := RecoveryFocus.machine rightSlots CompetitorSignedDecision.compareMachine
noncomputable def order := RecoveryFocus.machine orderSlots CompetitorSignedDecision.compareMachine

def fires (u a b ra rb : ℕ) : Bool := !decide (u≤a) && decide (u≤b) && !decide (rb≤ra)
def data (cap k h u a b ra rb phase : ℕ) : Fin 10 → List Bool :=
  ![ZeroPadding.pad cap (frame (binary k u)),ZeroPadding.pad cap (frame (binary k a)),
    ZeroPadding.pad cap (frame (binary k b)),ZeroPadding.pad cap (frame (binary h ra)),
    ZeroPadding.pad cap (frame (binary h rb)),ZeroPadding.pad cap [if 1≤phase then decide (u≤a) else false],
    ZeroPadding.pad cap [if 2≤phase then decide (u≤b) else false],
    ZeroPadding.pad cap [if 3≤phase then decide (rb≤ra) else false],List.replicate cap false,
    ZeroPadding.pad cap [if 4≤phase then fires u a b ra rb else false]]

theorem left_install (cap k h u a b ra rb : ℕ) : install leftSlots (data cap k h u a b ra rb 0) (compareOutput cap k u a)=data cap k h u a b ra rb 1 := by
  funext i
  simp only [install,left_pick]
  fin_cases i <;> simp [leftPick,data,compareOutput]

theorem left_ready (cap k h u a b ra rb : ℕ) (hu : u<2^k) (ha : a<2^k) (hc : 2*k+1≤cap) :
    ClockJoin.ReadyRun left (4*k+4) (data cap k h u a b ra rb 0) (data cap k h u a b ra rb 1) := by
  have hrun := CompetitorRationalProducts.bounded_focus leftSlots left_injective _ _ _
    (compare_ready cap k u a hu ha hc) (data cap k h u a b ra rb 0) (by intro i; fin_cases i <;> simp [leftSlots,data,compareInput])
  rw [left_install] at hrun
  exact hrun

theorem right_install (cap k h u a b ra rb : ℕ) : install rightSlots (data cap k h u a b ra rb 1) (compareOutput cap k u b)=data cap k h u a b ra rb 2 := by
  funext i
  simp only [install,right_pick]
  fin_cases i <;> simp [rightPick,data,compareOutput]

theorem right_ready (cap k h u a b ra rb : ℕ) (hu : u<2^k) (hb : b<2^k) (hc : 2*k+1≤cap) :
    ClockJoin.ReadyRun right (4*k+4) (data cap k h u a b ra rb 1) (data cap k h u a b ra rb 2) := by
  have hrun := CompetitorRationalProducts.bounded_focus rightSlots right_injective _ _ _
    (compare_ready cap k u b hu hb hc) (data cap k h u a b ra rb 1) (by intro i; fin_cases i <;> simp [rightSlots,data,compareInput])
  rw [right_install] at hrun
  exact hrun

theorem order_install (cap k h u a b ra rb : ℕ) : install orderSlots (data cap k h u a b ra rb 2) (compareOutput cap h rb ra)=data cap k h u a b ra rb 3 := by
  funext i
  simp only [install,order_pick]
  fin_cases i <;> simp [orderPick,data,compareOutput]

theorem order_ready (cap k h u a b ra rb : ℕ) (ha : ra<2^h) (hb : rb<2^h) (hc : 2*h+1≤cap) :
    ClockJoin.ReadyRun order (4*h+4) (data cap k h u a b ra rb 2) (data cap k h u a b ra rb 3) := by
  have hrun := CompetitorRationalProducts.bounded_focus orderSlots order_injective _ _ _
    (compare_ready cap h rb ra hb ha hc) (data cap k h u a b ra rb 2) (by intro i; fin_cases i <;> simp [orderSlots,data,compareInput])
  rw [order_install] at hrun
  exact hrun

def finish : Machine 10 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ bits => some ⟨1,fun i => if i=9 then some (!bits 5 && bits 6 && !bits 7) else none,fun _ => .stay⟩

theorem finish_ready (cap k h u a b ra rb : ℕ) :
    ClockJoin.ReadyRun finish 1 (data cap k h u a b ra rb 3) (data cap k h u a b ra rb 4) := by
  let start := initialConfiguration finish (data cap k h u a b ra rb 3)
  let final : Configuration 10 2 := ⟨1,fun _ => 0,data cap k h u a b ra rb 4⟩
  have h5 : start.scanned 5=decide (u≤a) := by
    change readTapeBit (ZeroPadding.pad cap [decide (u≤a)]) 0=_
    exact ZeroPadding.read_pad cap [decide (u≤a)] 0
  have h6 : start.scanned 6=decide (u≤b) := by
    change readTapeBit (ZeroPadding.pad cap [decide (u≤b)]) 0=_
    exact ZeroPadding.read_pad cap [decide (u≤b)] 0
  have h7 : start.scanned 7=decide (rb≤ra) := by
    change readTapeBit (ZeroPadding.pad cap [decide (rb≤ra)]) 0=_
    exact ZeroPadding.read_pad cap [decide (rb≤ra)] 0
  have hs : step finish start=some final := by
    simp only [step,finish,Option.map_some,Option.some.injEq,h5,h6,h7]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i
      by_cases hi : i=9
      · subst i
        change writeTapeBit (ZeroPadding.pad cap [false]) 0 (fires u a b ra rb)=ZeroPadding.pad cap [fires u a b ra rb]
        exact ZeroPadding.write_pad cap [false] 0 (fires u a b ra rb)
      · simp only [applyAction,hi,ite_false]
        change data cap k h u a b ra rb 3 i=data cap k h u a b ra rb 4 i
        fin_cases i <;> simp_all [data]
  obtain ⟨actual,hr,hf,hsteps⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨actual,hr,congrArg Configuration.tapes hf,by intro i; rw [hf],hsteps.le⟩

noncomputable def tail := Composition.machine order finish
noncomputable def middle := Composition.machine right tail
noncomputable def machine := Composition.machine left middle

theorem pair_ready (cap k h u a b ra rb : ℕ) (hu : u<2^k) (ha : a<2^k) (hb : b<2^k)
    (hra : ra<2^h) (hrb : rb<2^h) (hck : 2*k+1≤cap) (hch : 2*h+1≤cap) :
    ClockJoin.ReadyRun machine (8*k+4*h+16) (data cap k h u a b ra rb 0) (data cap k h u a b ra rb 4) := by
  have htail := ClockJoin.join order finish _ _ _ _ _ (order_ready cap k h u a b ra rb hra hrb hch)
    (finish_ready cap k h u a b ra rb)
  have hmiddle := ClockJoin.join right tail _ _ _ _ _ (right_ready cap k h u a b ra rb hu hb hck) htail
  have hall := ClockJoin.join left middle _ _ _ _ _ (left_ready cap k h u a b ra rb hu ha hck) hmiddle
  have he : (4*k+4)+1+((4*k+4)+1+((4*h+4)+1+1))=8*k+4*h+16 := by omega
  rw [he] at hall
  exact hall

theorem fires_iff (u a b ra rb : ℕ) : fires u a b ra rb=true ↔ a<u ∧ u≤b ∧ ra<rb := by
  simp [fires,Bool.and_eq_true,not_le]
  tauto

end NearCubicWires.RepairOrdinary.CompetitorSameBucketPairCompare
