import Proof.PCP.PCPPRequestNodeEndpoint

/-! One paid streaming loop over native Boolean-node descriptors. The actual unary
field count controls repetition; each field uses the same reusable body. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeLoop
open LocalBitMultitape RecoveryExecution PCPPRequestNodeReuse RepairRepresentation
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable {n : ℕ}

def stream (values : List (BooleanNode n)) : List Bool := values.flatMap PCPPRequestNodeSchema.native
def encoded (values : List (BooleanNode n)) : List Bool :=
  FieldList.stream (values.map (fun node => (ExecutableInterfaces.encodeBooleanNode node).bits))
@[simp] theorem stream_nil : stream ([] : List (BooleanNode n))=[] := rfl
@[simp] theorem stream_cons (node : BooleanNode n) (values : List (BooleanNode n)) :
    stream (node::values)=PCPPRequestNodeSchema.native node++stream values := rfl
@[simp] theorem encoded_nil : encoded ([] : List (BooleanNode n))=[] := rfl
@[simp] theorem encoded_cons (node : BooleanNode n) (values : List (BooleanNode n)) :
    encoded (node::values)=frame (ExecutableInterfaces.encodeBooleanNode node).bits++encoded values := rfl
noncomputable def machine := RepeatMachine.machine bodyMachine (fun _ _ => true)
noncomputable def cfg (phase : Fin 5) (capacity : ℕ) (source : List Bool) (pos : ℕ)
    (out : List Bool) (total driver : ℕ) :=
  RepeatMachine.cfg phase (bodyEntry capacity source pos out) total driver

private theorem repeat_cfg_eq {t s : ℕ} (phase : Fin 5) (c d : Configuration t s)
    (total head : ℕ) (hh : c.heads=d.heads) (ht : c.tapes=d.tapes) :
    RepeatMachine.cfg phase c total head=RepeatMachine.cfg phase d total head := by
  apply configuration_ext
  · rfl
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

private theorem stopped {t s : ℕ} (p : Machine t s)
    (accepted : Fin s → (Fin t → Bool) → Bool) (c : Configuration t s) (total head : ℕ) :
    (RepeatMachine.machine p accepted).halted (RepeatMachine.cfg 3 c total head).control=true := by
  simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode]

theorem remaining (pre : List Bool) (values : List (BooleanNode n)) (suffix out : List Bool)
    (capacity total pos : ℕ) (hn : pos+values.length=total)
    (hcap : ∀ node∈values,PCPPRequestNodeCold.budget node+1 ≤ capacity) :
    ∃ r,runFrom machine (values.length*(6*capacity+14)+total+3)
      (cfg 0 capacity (pre++stream values++suffix) pre.length out total (pos+1))=some r ∧
      r.final=cfg 3 capacity (pre++stream values++suffix) (pre.length+(stream values).length)
        (out++encoded values) total 1 ∧
      r.steps ≤ values.length*(6*capacity+14)+total+3 := by
  induction values generalizing pre out pos with
  | nil =>
    have hp : pos=total := by simpa only [List.length_nil,Nat.add_zero] using hn
    subst pos
    have h := RepeatMachine.exhaust bodyMachine (fun _ _ => true)
      (bodyEntry capacity (pre++suffix) pre.length out) total
    obtain ⟨r,hr,hf,hs⟩ := h.run (stopped _ _ _ _ _)
    refine ⟨r,?_,?_,?_⟩
    · simpa only [machine,cfg,stream_nil,List.append_nil,List.length_nil,Nat.zero_mul,Nat.zero_add] using hr
    · simpa only [cfg,stream_nil,encoded_nil,List.append_nil,List.length_nil,Nat.add_zero] using hf
    · simp only [List.length_nil,Nat.zero_mul,Nat.zero_add]
      exact hs.le
  | cons node values ih =>
    obtain ⟨body,hb,bh,bt,bs⟩ := body_repeated_run pre (stream values++suffix) out node capacity
      (hcap node (by simp))
    have hp := RepeatMachine.iteration bodyMachine (fun _ _ => true)
      (bodyEntry capacity (pre++PCPPRequestNodeSchema.native node++(stream values++suffix)) pre.length out)
      total pos body (by rfl) (by simp only [List.length_cons] at hn; omega) hb
    have he := repeat_cfg_eq 0 body.final
      (bodyEntry capacity (pre++PCPPRequestNodeSchema.native node++(stream values++suffix))
        (pre.length+(PCPPRequestNodeSchema.native node).length) (out++frame (ExecutableInterfaces.encodeBooleanNode node).bits))
      total (pos+2) bh bt
    change Timed machine (body.steps+2)
      (cfg 0 capacity (pre++PCPPRequestNodeSchema.native node++(stream values++suffix)) pre.length out total (pos+1))
      (RepeatMachine.cfg 0 body.final total (pos+2)) at hp
    rw [he] at hp
    obtain ⟨tail,ht,tf,ts⟩ := ih (pre++PCPPRequestNodeSchema.native node)
      (out++frame (ExecutableInterfaces.encodeBooleanNode node).bits) (pos+1)
      (by simp only [List.length_cons] at hn; omega)
      (by intro g hg; exact hcap g (by simp [hg]))
    have hmid : cfg 0 capacity ((pre++PCPPRequestNodeSchema.native node)++stream values++suffix)
        (pre++PCPPRequestNodeSchema.native node).length (out++frame (ExecutableInterfaces.encodeBooleanNode node).bits) total ((pos+1)+1)=
      RepeatMachine.cfg 0 (bodyEntry capacity
        (pre++PCPPRequestNodeSchema.native node++(stream values++suffix))
        (pre.length+(PCPPRequestNodeSchema.native node).length) (out++frame (ExecutableInterfaces.encodeBooleanNode node).bits))
        total (pos+2) := by
      simp only [cfg,List.append_assoc,List.length_append,Nat.add_assoc]
    rw [hmid] at ht
    rcases hp with ⟨space,hp⟩
    obtain ⟨r,hr,hf,hs,_⟩ := hp.followedBy tail ht
    have htime : (body.steps+2)+(values.length*(6*capacity+14)+total+3) ≤
        (node::values).length*(6*capacity+14)+total+3 := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    have hm := runFrom_moreFuel machine _
      ((node::values).length*(6*capacity+14)+total+3-
        ((body.steps+2)+(values.length*(6*capacity+14)+total+3))) _ r hr
    rw [Nat.add_sub_of_le htime] at hm
    refine ⟨r,?_,?_,?_⟩
    · simpa only [stream_cons,List.append_assoc] using hm
    · rw [hf,tf]
      simp only [stream_cons,encoded_cons,List.append_assoc,List.length_append,Nat.add_assoc]
    · rw [hs]
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem loop_run (pre : List Bool) (values : List (BooleanNode n)) (suffix out : List Bool)
    (capacity : ℕ)
    (hcap : ∀ node∈values,PCPPRequestNodeCold.budget node+1 ≤ capacity) :
    ∃ r,runFrom machine (values.length*(6*capacity+15)+3)
      (cfg 0 capacity (pre++stream values++suffix) pre.length out values.length 1)=some r ∧
      r.final=cfg 3 capacity (pre++stream values++suffix) (pre.length+(stream values).length)
        (out++encoded values) values.length 1 ∧
      r.steps ≤ values.length*(6*capacity+15)+3 := by
  have h := remaining pre values suffix out capacity values.length 0 (by omega) hcap
  have he : values.length*(6*capacity+14)+values.length+3=values.length*(6*capacity+15)+3 := by ring
  simpa only [he,Nat.zero_add] using h

end NearCubicWires.RepairOrdinary.PCPPRequestNodeLoop
