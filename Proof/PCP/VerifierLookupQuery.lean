import Proof.PCP.VerifierLookupRetainField

/-! The query and its initial ordinal counter are physically produced from
the claimed scan bits and current state. No row or numerical address is input. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupQuery
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def active (phase : Bool) : Fin 4 := if phase then 1 else 0
def base (phase : Bool) : Fin 5 := if phase then 2 else 0
def payload (phase : Bool) : Fin 5 := if phase then 3 else 1
def emit (phase : Bool) (q : Fin 5) (bit zero : Bool) : Action 4 5 :=
  ⟨q,fun i => if i.val=2 then some bit else if i.val=3 then some zero else none,
    fun i => if i=active phase ∨ i.val=2 ∨ i.val=3 then .right else .stay⟩
def raw : Machine 4 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==4
  rule := fun q bits =>
    if q.val=0 then if bits 0 then some (emit false 1 true true) else some ⟨2,fun _=>none,fun _=>.stay⟩
    else if q.val=1 then some (emit false 0 (bits 0) false)
    else if q.val=2 then if bits 1 then some (emit true 3 true true)
      else some ⟨4,fun i=>if i.val=2 ∨ i.val=3 then some false else none,
        fun i=>if i.val=2 ∨ i.val=3 then .right else .stay⟩
    else if q.val=3 then some (emit true 2 (bits 1) false)
    else none

def cfg (phase : Bool) (q : Fin 5) (source other : List Bool) (pos otherPos : ℕ)
    (out zero backing zeroBacking : List Bool) : Configuration 4 5 :=
  ⟨q,fun i=>if i.val=2 then out.length else if i.val=3 then zero.length else
      if i=active phase then pos else otherPos,
    fun i=>if i.val=2 then overlay out backing else if i.val=3 then overlay zero zeroBacking else
      if i=active phase then source else other⟩

theorem apply_emit (phase : Bool) (q next : Fin 5) (source other : List Bool) (pos otherPos : ℕ)
    (out zero backing zeroBacking : List Bool) (bit zb : Bool) :
    applyAction (cfg phase q source other pos otherPos out zero backing zeroBacking) (emit phase next bit zb)=
      cfg phase next source other (pos+1) otherPos (out++[bit]) (zero++[zb]) backing zeroBacking := by
  apply configuration_ext
  · rfl
  · funext i; cases phase <;> fin_cases i <;> simp [applyAction,cfg,emit,active,HeadMove.apply]
  · funext i; cases phase <;> fin_cases i <;> simp [applyAction,cfg,emit,active,overlay_write]

theorem marker_step (phase : Bool) (pre tail other : List Bool) (otherPos : ℕ)
    (out zero backing zeroBacking : List Bool) :
    step raw (cfg phase (base phase) (pre++true::tail) other pre.length otherPos out zero backing zeroBacking)=
      some (cfg phase (payload phase) (pre++true::tail) other (pre.length+1) otherPos
        (out++[true]) (zero++[true]) backing zeroBacking) := by
  have hr : raw.rule (base phase)
      (cfg phase (base phase) (pre++true::tail) other pre.length otherPos out zero backing zeroBacking).scanned=
      some (emit phase (payload phase) true true) := by
    cases phase <;> simp [raw,cfg,base,payload,Configuration.scanned,active,Streaming.read_append]
  change Option.map (applyAction _) (raw.rule (base phase) _) = _
  rw [hr]
  simp only [Option.map_some,Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _ _ _ _ _ _

theorem payload_step (phase : Bool) (pre tail other : List Bool) (otherPos : ℕ)
    (out zero backing zeroBacking : List Bool) (bit : Bool) :
    step raw (cfg phase (payload phase) (pre++bit::tail) other pre.length otherPos out zero backing zeroBacking)=
      some (cfg phase (base phase) (pre++bit::tail) other (pre.length+1) otherPos
        (out++[bit]) (zero++[false]) backing zeroBacking) := by
  have hr : raw.rule (payload phase)
      (cfg phase (payload phase) (pre++bit::tail) other pre.length otherPos out zero backing zeroBacking).scanned=
      some (emit phase (base phase) bit false) := by
    cases phase <;> simp [raw,cfg,base,payload,Configuration.scanned,active,Streaming.read_append]
  change Option.map (applyAction _) (raw.rule (payload phase) _) = _
  rw [hr]
  simp only [Option.map_some,Option.some.injEq]
  exact apply_emit _ _ _ _ _ _ _ _ _ _ _ _ _

theorem copy_prefix (phase : Bool) (bits pre tail other : List Bool) (otherPos : ℕ)
    (out zero backing zeroBacking : List Bool) :
    Timed raw (2*bits.length)
      (cfg phase (base phase) (pre++Streaming.marks bits++tail) other pre.length otherPos out zero backing zeroBacking)
      (cfg phase (base phase) (pre++Streaming.marks bits++tail) other (pre.length+2*bits.length) otherPos
        (out++Streaming.marks bits) (zero++Streaming.marks (List.replicate bits.length false)) backing zeroBacking) := by
  induction bits generalizing pre out zero with
  | nil =>
    simpa [Streaming.marks] using Timed.refl raw
      (cfg phase (base phase) (pre++tail) other pre.length otherPos out zero backing zeroBacking)
  | cons bit bits ih =>
    have h0 := Timed.single (by cases phase <;> rfl : raw.halted (base phase)=false)
      (marker_step phase pre (bit::Streaming.marks bits++tail) other otherPos out zero backing zeroBacking)
    have h1 := Timed.single (by cases phase <;> rfl : raw.halted (payload phase)=false)
      (payload_step phase (pre++[true]) (Streaming.marks bits++tail) other otherPos
        (out++[true]) (zero++[true]) backing zeroBacking bit)
    have htail := ih (pre++[true,bit]) (out++[true,bit]) (zero++[true,false])
    simp only [List.length_append,List.length_cons,List.length_nil,List.append_assoc,
      List.cons_append,List.nil_append,Nat.add_assoc,Nat.zero_add] at h1 htail
    have hj := h0.trans (h1.trans htail)
    have hadd (a : ℕ) : 1+(1+a)=2+a := by omega
    simpa [Streaming.marks,List.replicate_succ,List.append_assoc,Nat.mul_add,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm,hadd] using hj

theorem switch_step (left right : List Bool) (out zero backing zeroBacking : List Bool) :
    step raw (cfg false 0 (frame left) (frame right) (2*left.length) 0 out zero backing zeroBacking)=
      some (cfg true 2 (frame right) (frame left) 0 (2*left.length) out zero backing zeroBacking) := by
  have he : frame left=Streaming.marks left++[false] := by
    simpa only [RepairOrdinary.frame,List.append_nil] using Streaming.frame_append left []
  have hr : readTapeBit (frame left) (2*left.length)=false := by
    rw [he]
    simpa only [Streaming.marks_length] using Streaming.read_append (Streaming.marks left) [] false
  simp [step,raw,cfg,active,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem close_step (left right : List Bool) (out zero backing zeroBacking : List Bool) :
    step raw (cfg true 2 (frame right) (frame left) (2*right.length) (2*left.length) out zero backing zeroBacking)=
      some (cfg true 4 (frame right) (frame left) (2*right.length) (2*left.length)
        (out++[false]) (zero++[false]) backing zeroBacking) := by
  have he : frame right=Streaming.marks right++[false] := by
    simpa only [RepairOrdinary.frame,List.append_nil] using Streaming.frame_append right []
  have hr : readTapeBit (frame right) (2*right.length)=false := by
    rw [he]
    simpa only [Streaming.marks_length] using Streaming.read_append (Streaming.marks right) [] false
  simp [step,raw,cfg,active,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,overlay_write]

def machine : Machine 5 7 := Rewind.machine raw

theorem query_ready (left right backing zeroBacking : List Bool) (cap : ℕ)
    (hb : backing.length≤2*(left.length+right.length)+1)
    (hz : zeroBacking.length≤2*(left.length+right.length)+1)
    (hc : 2*(left.length+right.length)+2≤cap) :
    ReadyRun machine (4*(left.length+right.length)+6)
      ![frame left,frame right,backing,zeroBacking,List.replicate cap false]
      ![frame left,frame right,frame (left++right),
        frame (List.replicate (left.length+right.length) false),List.replicate cap false] := by
  have hframe (bits : List Bool) : Streaming.marks bits++[false]=frame bits := by
    simpa only [RepairOrdinary.frame,List.append_nil] using (Streaming.frame_append bits []).symm
  have hleft := copy_prefix false left [] [false] (frame right) 0 [] [] backing zeroBacking
  have hright := copy_prefix true right [] [false] (frame left) (2*left.length)
    (Streaming.marks left) (Streaming.marks (List.replicate left.length false)) backing zeroBacking
  simp only [List.nil_append,List.length_nil,Nat.zero_add,hframe] at hleft hright
  have hj := (hleft.trans (Timed.single (by rfl : raw.halted (0 : Fin 5)=false)
    (switch_step left right _ _ backing zeroBacking))).trans
    (hright.trans (Timed.single (by rfl : raw.halted (2 : Fin 5)=false)
      (close_step left right _ _ backing zeroBacking)))
  obtain ⟨base,hbase,hbf,hbs⟩ := hj.run (by rfl)
  have hi : cfg false 0 (frame left) (frame right) 0 0 [] [] backing zeroBacking=
      initialConfiguration raw ![frame left,frame right,backing,zeroBacking] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [cfg,active,overlay,initialConfiguration]
  have hi' : cfg false (LookupQuery.base false) (frame left) (frame right) 0 0 [] [] backing zeroBacking=
      initialConfiguration raw ![frame left,frame right,backing,zeroBacking] := hi
  rw [hi'] at hbase
  obtain ⟨r,hr,ht,hrc,hh,hrs,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hbase cap
  have htime : 2*base.steps+2=4*(left.length+right.length)+6 := by rw [hbs]; omega
  rw [htime] at hr
  have hin : Fin.addCases (motive:=fun _ : Fin (4+1) => List Bool)
      (![frame left,frame right,backing,zeroBacking] : Fin 4 → List Bool) (fun _ => List.replicate cap false)=
      (![frame left,frame right,backing,zeroBacking,List.replicate cap false] : Fin 5 → List Bool) := by
    funext i; fin_cases i <;> rfl
  rw [hin] at hr
  have hfit : base.steps≤cap := by rw [hbs]; omega
  refine ⟨r,hr,?_,hh,hrs.trans htime⟩
  funext i; fin_cases i
  · simpa [hbf,cfg,active] using ht 0
  · simpa [hbf,cfg,active] using ht 1
  · have he : (Streaming.marks left++Streaming.marks right)++[false]=frame (left++right) := by rw [←Streaming.marks_append,hframe]
    simpa [hbf,cfg,he,overlay,List.drop_eq_nil_of_le (by simpa using hb)] using ht 2
  · have he : (Streaming.marks (List.replicate left.length false)++Streaming.marks (List.replicate right.length false))++[false]=
        frame (List.replicate (left.length+right.length) false) := by rw [←Streaming.marks_append,←List.replicate_add,hframe]
    simpa [hbf,cfg,he,overlay,List.drop_eq_nil_of_le (by simpa using hz)] using ht 3
  · simpa [max_eq_left hfit] using hrc

end NearCubicWires.RepairSource.VerifierDecoding.LookupQuery
