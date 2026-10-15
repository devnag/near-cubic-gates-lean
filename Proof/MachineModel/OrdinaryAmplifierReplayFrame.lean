import Proof.MachineModel.GeneratedAmplifierHeader

/-! Frame the exact raw amplifier payload. The arity header is self-framed;
the table is copied under an actual unary length driver, never a data-bit
delimiter. This is the final physical stage of the selected replay wrapper. -/
namespace NearCubicWires.RepairOrdinary.AmplifierReplay.Frame
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 3 8 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==7
  rule := fun q bits =>
    if q.val=0 then some ⟨if bits 0 then 1 else 3,![none,none,some true],![.stay,.stay,.right]⟩
    else if q.val=1 then some ⟨2,![none,none,some (bits 0)],![.right,.stay,.right]⟩
    else if q.val=2 then some ⟨4,![none,none,some true],![.stay,.stay,.right]⟩
    else if q.val=4 then some ⟨0,![none,none,some (bits 0)],![.right,.stay,.right]⟩
    else if q.val=3 then some ⟨5,![none,none,some false],![.right,.stay,.right]⟩
    else if q.val=5 then some (if bits 1 then
      ⟨6,![none,none,some true],![.stay,.stay,.right]⟩
      else ⟨7,![none,none,some false],![.stay,.stay,.right]⟩)
    else if q.val=6 then some ⟨5,![none,none,some (bits 0)],![.right,.right,.right]⟩
    else none

def cfg (q : Fin 8) (source : List Bool) (pos : ℕ) (out : List Bool)
    (count used : ℕ) : Configuration 3 8 :=
  ⟨q,![pos,used+1,out.length],![source,UnaryTemplate.tape count,out]⟩

theorem mark_step (pre tail out : List Bool) (b : Bool) (count used : ℕ) :
    step machine (cfg 0 (pre++b::tail) pre.length out count used)=
      some (cfg (if b then 1 else 3) (pre++b::tail) pre.length (out++[true]) count used) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem bit_step (pre tail out : List Bool) (b : Bool) (count used : ℕ) (q : Fin 8)
    (hq : q=1 ∨ q=4 ∨ q=6) :
    step machine (cfg q (pre++b::tail) pre.length out count used)=
      some (cfg (if q=1 then 2 else if q=4 then 0 else 5)
        (pre++b::tail) (pre.length+1) (out++[b]) count (if q=6 then used+1 else used)) := by
  rcases hq with rfl|rfl|rfl
  all_goals
    simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem data_mark_step (source out : List Bool) (pos count used : ℕ) :
    step machine (cfg 2 source pos out count used)=
      some (cfg 4 source pos (out++[true]) count used) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem header_loop (pre bits tail out : List Bool) (count : ℕ) :
    Timed machine (4*bits.length+2)
      (cfg 0 (pre++frame bits++tail) pre.length out count 0)
      (cfg 5 (pre++frame bits++tail) (pre.length+(frame bits).length)
        (out++Streaming.marks (frame bits)) count 0) := by
  induction bits generalizing pre out with
  | nil =>
    have hs : step machine (cfg 3 (pre++false::tail) pre.length (out++[true]) count 0)=
        some (cfg 5 (pre++false::tail) (pre.length+1) (out++[true,false]) count 0) := by
      simp [step,machine,cfg]
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
      · funext i; fin_cases i
        · rfl
        · rfl
        · simpa [applyAction] using Streaming.write_append (out++[true]) false
    simpa [frame,Streaming.marks] using
      (Timed.single (by rfl : machine.halted (0 : Fin 8)=false) (mark_step pre tail out false count 0)).trans
        (Timed.single (by rfl : machine.halted (3 : Fin 8)=false) hs)
  | cons b bits ih =>
    have hm := mark_step pre (b::frame bits++tail) out true count 0
    have hb := bit_step pre (b::frame bits++tail) (out++[true]) true count 0 1 (Or.inl rfl)
    have hd := data_mark_step (pre++true::b::frame bits++tail) (out++[true,true]) (pre.length+1) count 0
    have he := bit_step (pre++[true]) (frame bits++tail) (out++[true,true,true]) b count 0 4 (Or.inr (Or.inl rfl))
    have ht := ih (pre++[true,b]) (out++[true,true,true,b])
    simp only [↓reduceIte] at hm
    norm_num only at hb he
    simp only [List.append_assoc,List.cons_append,List.nil_append,List.length_append,List.length_singleton] at hm hb hd he ht
    have hh := (Timed.single (by rfl : machine.halted (0 : Fin 8)=false) hm).trans
      ((Timed.single (by rfl : machine.halted (1 : Fin 8)=false) hb).trans
      ((Timed.single (by rfl : machine.halted (2 : Fin 8)=false) hd).trans
      ((Timed.single (by rfl : machine.halted (4 : Fin 8)=false) he).trans ht)))
    have hc : 1+(1+(1+(1+(4*bits.length+2))))=4*(b::bits).length+2 := by simp; omega
    rw [hc] at hh
    convert hh using 1 <;>
      simp [frame,Streaming.marks,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    congr 1
    omega

theorem table_loop (pre bits out : List Bool) (count used : ℕ) (hc : used+bits.length=count) :
    Timed machine (2*bits.length+1)
      (cfg 5 (pre++bits) pre.length out count used)
      (cfg 7 (pre++bits) (pre.length+bits.length) (out++frame bits) count count) := by
  induction bits generalizing pre out used with
  | nil =>
    have hu : used=count := by simpa using hc
    subst used
    have hs : step machine (cfg 5 pre pre.length out count count)=
        some (cfg 7 pre pre.length (out++[false]) count count) := by
      simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape_end]
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
      · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]
    simpa [frame] using Timed.single (by rfl : machine.halted (5 : Fin 8)=false) hs
  | cons b bits ih =>
    have hu : used<count := by simp only [List.length_cons] at hc; omega
    have hm : step machine (cfg 5 (pre++b::bits) pre.length out count used)=
        some (cfg 6 (pre++b::bits) pre.length (out++[true]) count used) := by
      simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape_mark count used hu]
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
      · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]
    have hb := bit_step pre bits (out++[true]) b count used 6 (Or.inr (Or.inr rfl))
    change step machine (cfg 6 (pre++b::bits) pre.length (out++[true]) count used)=
      some (cfg 5 (pre++b::bits) (pre.length+1) ((out++[true])++[b]) count (used+1)) at hb
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hb
    have ht := ih (pre++[b]) (out++[true,b]) (used+1) (by simp only [List.length_cons] at hc; omega)
    simp only [List.append_assoc,List.cons_append,List.nil_append,List.length_append,List.length_singleton] at ht
    have hh := (Timed.single (by rfl : machine.halted (5 : Fin 8)=false) hm).trans
      ((Timed.single (by rfl : machine.halted (6 : Fin 8)=false) hb).trans ht)
    have hc' : 1+(1+(2*bits.length+1))=2*(b::bits).length+1 := by simp; omega
    rw [hc'] at hh
    simpa [frame,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem frame_run (bits table : List Bool) :
    ∃ r,runFrom machine (2*(frame bits++table).length+1)
      (cfg 0 (frame bits++table) 0 [] table.length 0)=some r ∧
      r.final.tapes 2=frame (frame bits++table) ∧
      r.steps=2*(frame bits++table).length+1 := by
  have hh := header_loop [] bits table [] table.length
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hh
  have ht := table_loop (frame bits) table (Streaming.marks (frame bits)) table.length 0 (by omega)
  have he : Streaming.marks (frame bits)++frame table=frame (frame bits++table) :=
    (Streaming.frame_append (frame bits) table).symm
  rw [he] at ht
  have h := hh.trans ht
  have hc : 4*bits.length+2+(2*table.length+1)=2*(frame bits++table).length+1 := by simp; omega
  rw [hc] at h
  obtain ⟨r,hr,hf,hs⟩ := h.run (by rfl)
  exact ⟨r,hr,by rw [hf]; rfl,hs⟩

end NearCubicWires.RepairOrdinary.AmplifierReplay.Frame
