import Proof.PCP.PCPTriple

/-! Counted physical serialization of equally sized field groups. The actual
constant field-count driver is supplied by the native arity parser; the SAME
shared serializer body consumes every group and restores its work bank. No
new balanced encoder is defined here. -/
namespace NearCubicWires.RepairOrdinary.DecompositionBalancedGroups
open LocalBitMultitape RecoveryExecution PCPSerializerReuse
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stream (groups : List (List (List Bool))) : List Bool :=
  (groups.map FieldList.stream).flatten
def encoded (groups : List (List (List Bool))) : List Bool :=
  FieldList.stream (groups.map (fun fields => (PCPTraversal.code fields).bits))
@[simp] theorem stream_nil : stream []=[] := rfl
@[simp] theorem stream_cons (fields : List (List Bool)) (groups : List (List (List Bool))) :
    stream (fields::groups)=FieldList.stream fields++stream groups := rfl
@[simp] theorem encoded_nil : encoded []=[] := rfl
@[simp] theorem encoded_cons (fields : List (List Bool)) (groups : List (List (List Bool))) :
    encoded (fields::groups)=frame (PCPTraversal.code fields).bits++encoded groups := rfl

noncomputable def machine := RepeatMachine.machine bodyMachine (fun _ _ => true)
noncomputable def cfg (phase : Fin 5) (count capacity : ℕ) (source : List Bool) (pos : ℕ)
    (out : List Bool) (total driver : ℕ) :=
  RepeatMachine.cfg phase (bodyEntry capacity (capacity+1) source pos count out) total driver

private theorem repeat_cfg_eq {t s : ℕ} (phase : Fin 5) (c d : Configuration t s)
    (total head : ℕ) (hh : c.heads=d.heads) (ht : c.tapes=d.tapes) :
    RepeatMachine.cfg phase c total head=RepeatMachine.cfg phase d total head := by
  apply configuration_ext
  · rfl
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

theorem remaining (pre : List Bool) (groups : List (List (List Bool))) (suffix out : List Bool)
    (count capacity total pos : ℕ) (hn : pos+groups.length=total)
    (hcount : ∀ fields∈groups,fields.length=count)
    (hcap : ∀ fields∈groups,PCPTraversal.budget (PCPSerializerMass.mass fields)+1 ≤ capacity) :
    ∃ r,runFrom machine (groups.length*(6*capacity+10)+total+3)
      (cfg 0 count capacity (pre++stream groups++suffix) pre.length out total (pos+1))=some r ∧
      r.final=cfg 3 count capacity (pre++stream groups++suffix) (pre.length+(stream groups).length)
        (out++encoded groups) total 1 ∧
      r.steps ≤ groups.length*(6*capacity+10)+total+3 := by
  induction groups generalizing pre out pos with
  | nil =>
    have hp : pos=total := by simpa only [List.length_nil,Nat.add_zero] using hn
    subst pos
    have h := RepeatMachine.exhaust bodyMachine (fun _ _ => true)
      (bodyEntry capacity (capacity+1) (pre++suffix) pre.length count out) total
    obtain ⟨r,hr,hf,hs⟩ := h.run (by
      simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,?_,?_⟩
    · simpa only [machine,cfg,stream_nil,List.append_nil,List.length_nil,Nat.zero_mul,Nat.zero_add] using hr
    · simpa only [cfg,stream_nil,encoded_nil,List.append_nil,List.length_nil,Nat.add_zero] using hf
    · simp only [List.length_nil,Nat.zero_mul,Nat.zero_add]
      exact hs.le
  | cons fields groups ih =>
    have h3 := hcount fields (by simp)
    obtain ⟨body,hb,bh,bt,bs⟩ := body_repeated_run pre fields (stream groups++suffix) out capacity
      (hcap fields (by simp))
    rw [h3] at hb bh bt
    have hp := RepeatMachine.iteration bodyMachine (fun _ _ => true)
      (bodyEntry capacity (capacity+1) (pre++FieldList.stream fields++(stream groups++suffix)) pre.length count out)
      total pos body (by rfl) (by simp only [List.length_cons] at hn; omega) hb
    have he := repeat_cfg_eq 0 body.final
      (bodyEntry capacity (capacity+1) (pre++FieldList.stream fields++(stream groups++suffix))
        (pre.length+(FieldList.stream fields).length) count (out++frame (PCPTraversal.code fields).bits))
      total (pos+2) bh bt
    change Timed machine (body.steps+2)
      (cfg 0 count capacity (pre++FieldList.stream fields++(stream groups++suffix)) pre.length out total (pos+1))
      (RepeatMachine.cfg 0 body.final total (pos+2)) at hp
    rw [he] at hp
    obtain ⟨tail,ht,tf,ts⟩ := ih (pre++FieldList.stream fields)
      (out++frame (PCPTraversal.code fields).bits) (pos+1)
      (by simp only [List.length_cons] at hn; omega)
      (by intro g hg; exact hcount g (by simp [hg]))
      (by intro g hg; exact hcap g (by simp [hg]))
    have hmid : cfg 0 count capacity ((pre++FieldList.stream fields)++stream groups++suffix)
        (pre++FieldList.stream fields).length (out++frame (PCPTraversal.code fields).bits) total ((pos+1)+1)=
      RepeatMachine.cfg 0 (bodyEntry capacity (capacity+1)
        (pre++FieldList.stream fields++(stream groups++suffix))
        (pre.length+(FieldList.stream fields).length) count (out++frame (PCPTraversal.code fields).bits))
        total (pos+2) := by
      simp only [cfg,List.append_assoc,List.length_append,Nat.add_assoc]
    rw [hmid] at ht
    rcases hp with ⟨space,hp⟩
    obtain ⟨r,hr,hf,hs,_⟩ := hp.followedBy tail ht
    have htime : (body.steps+2)+(groups.length*(6*capacity+10)+total+3) ≤
        (fields::groups).length*(6*capacity+10)+total+3 := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    have hm := runFrom_moreFuel machine _
      ((fields::groups).length*(6*capacity+10)+total+3-
        ((body.steps+2)+(groups.length*(6*capacity+10)+total+3))) _ r hr
    rw [Nat.add_sub_of_le htime] at hm
    refine ⟨r,?_,?_,?_⟩
    · simpa only [stream_cons,List.append_assoc] using hm
    · rw [hf,tf]
      simp only [stream_cons,encoded_cons,List.append_assoc,List.length_append,Nat.add_assoc]
    · rw [hs]
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem loop_run (pre : List Bool) (groups : List (List (List Bool))) (suffix out : List Bool)
    (count capacity : ℕ) (hcount : ∀ fields∈groups,fields.length=count)
    (hcap : ∀ fields∈groups,PCPTraversal.budget (PCPSerializerMass.mass fields)+1 ≤ capacity) :
    ∃ r,runFrom machine (groups.length*(6*capacity+11)+3)
      (cfg 0 count capacity (pre++stream groups++suffix) pre.length out groups.length 1)=some r ∧
      r.final=cfg 3 count capacity (pre++stream groups++suffix) (pre.length+(stream groups).length)
        (out++encoded groups) groups.length 1 ∧
      r.steps ≤ groups.length*(6*capacity+11)+3 := by
  have h := remaining pre groups suffix out count capacity groups.length 0 (by omega) hcount hcap
  have he : groups.length*(6*capacity+10)+groups.length+3=groups.length*(6*capacity+11)+3 := by ring
  simpa only [he,Nat.zero_add] using h

theorem group_mass_le (groups : List (List (List Bool))) (fields : List (List Bool))
    (h : fields∈groups) : PCPSerializerMass.mass fields ≤ (stream groups).length := by
  induction groups with
  | nil => simp at h
  | cons g groups ih =>
    simp only [List.mem_cons] at h
    rcases h with h|h
    · subst fields
      rw [stream_cons,List.length_append,PCPTraversal.stream_mass]
      omega
    · have ht := ih h
      rw [stream_cons,List.length_append]
      omega

theorem global_covers (groups : List (List (List Bool))) (fields : List (List Bool))
    (h : fields∈groups) : PCPTraversal.budget (PCPSerializerMass.mass fields)+1 ≤
      envelope (stream groups).length := envelope_covers _ _ (group_mass_le groups fields h)

end NearCubicWires.RepairOrdinary.DecompositionBalancedGroups
