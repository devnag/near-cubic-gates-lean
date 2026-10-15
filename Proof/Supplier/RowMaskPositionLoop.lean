import Proof.Supplier.RowMaskPositionParts

/-! A selected binary address controls the actual cache scan. Each accepted
counter step consumes one N-bit row; the output and occurrence count persist. -/
namespace NearCubicWires.RepairOrdinary.RowMaskPositionLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowMaskPositionParts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 2→ℕ := ![14,5]
noncomputable def programs : (i : Fin 2)→Machine 9 (sizes i)
  | ⟨0,_⟩=>counterMachine
  | ⟨1,_⟩=>skipMachine
  | ⟨n+2,h⟩=>False.elim (by omega)
def next (i : Fin 2) (_ : Fin (sizes i)) (bits : Fin 9→Bool) : Option (Fin 2) :=
  ![if bits 7 then some 1 else none,some 0] i
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
noncomputable def boundary (i : Fin 2) (N w : ℕ) (x : Data) :=
  controlConfig (RecoveryCalls.code sizes i) (cfg (programs i).start N w x)
noncomputable def finished (N w : ℕ) (x : Data) :=
  RecoveryCalls.stopped sizes (heads x) (tapes N w x)

theorem counter_call (N w : ℕ) (x : Data)
    (hb : x.bound+1<2^w) (hc : x.counter<x.bound) :
    ∃ n≤8*w+10,Timed machine n (boundary 0 N w x) (boundary 1 N w (advanced x)) := by
  obtain ⟨r,hr,rf⟩ := counter_run N w x (by omega) (by omega)
  have hn : next 0 r.final.control r.final.scanned=some 1 := by
    rw [rf]
    simp [next,cfg,heads,tapes,advanced,Configuration.scanned,readTapeBit,show x.counter+1≤x.bound by omega]
  obtain ⟨n,hn,h⟩ := call_receipt sizes programs 0 next 0 1 (8*w+9) _ r hr hn
  rw [rf] at h
  refine ⟨n,by omega,?_⟩
  simpa only [machine,boundary,controlConfig,cfg,RecoveryCalls.restarted,programs] using h

theorem counter_stop (N w : ℕ) (x : Data)
    (hb : x.bound+1<2^w) (hc : x.counter=x.bound) :
    ∃ n≤8*w+10,Timed machine n (boundary 0 N w x) (finished N w (advanced x)) := by
  obtain ⟨r,hr,rf⟩ := counter_run N w x (by omega) (by omega)
  have hn : next 0 r.final.control r.final.scanned=none := by
    rw [rf]
    simp [next,cfg,heads,tapes,advanced,Configuration.scanned,readTapeBit,hc]
  obtain ⟨n,hn,h⟩ := stop_receipt sizes programs 0 next 0 (8*w+9) _ r hr hn
  rw [rf] at h
  refine ⟨n,by omega,?_⟩
  simpa only [machine,boundary,finished,controlConfig,cfg,programs] using h

theorem skip_call (N w : ℕ) (x : Data) (pre bits suffix : List Bool)
    (hx : x.source=pre++bits++suffix) (hp : x.pos=pre.length) (hn : bits.length=N) :
    ∃ n≤2*N+5,Timed machine n (boundary 1 N w x) (boundary 0 N w {x with pos:=x.pos+N}) := by
  obtain ⟨r,hr,rf,_⟩ := skip_run N w x pre bits suffix hx hp hn
  obtain ⟨n,hn,h⟩ := call_receipt sizes programs 0 next 1 0 (2*N+4) _ r hr (by rfl)
  rw [rf] at h
  refine ⟨n,by omega,?_⟩
  simpa only [machine,boundary,controlConfig,cfg,RecoveryCalls.restarted,programs] using h

def endpoint (N : ℕ) (x : Data) (remaining : ℕ) : Data :=
  {x with pos:=x.pos+N*remaining,counter:=x.bound+1,flag:=false}

theorem scan_timed (N w : ℕ) (pre : List Bool) (rows : List (List Bool))
    (suffix : List Bool) (x : Data)
    (hx : x.source=pre++rows.flatten++suffix) (hp : x.pos=pre.length)
    (hl : ∀ row∈rows,row.length=N) (hc : x.counter+rows.length=x.bound)
    (hb : x.bound+1<2^w) :
    ∃ n≤rows.length*(2*N+8*w+15)+8*w+10,
      Timed machine n (boundary 0 N w x) (finished N w (endpoint N x rows.length)) := by
  induction rows generalizing pre x with
  | nil =>
    have he : x.counter=x.bound := by simpa using hc
    obtain ⟨n,hn,h⟩ := counter_stop N w x hb he
    refine ⟨n,by simpa using hn,?_⟩
    have hf : advanced x=endpoint N x 0 := by simp [advanced,endpoint,he]
    simpa only [List.length_nil,hf] using h
  | cons row rows ih =>
    have hlen : row.length=N := hl row (by simp)
    have hlt : x.counter<x.bound := by simp only [List.length_cons] at hc; omega
    obtain ⟨a,ha,first⟩ := counter_call N w x hb hlt
    obtain ⟨b,hbtime,second⟩ := skip_call N w (advanced x) pre row (rows.flatten++suffix)
      (by simpa [advanced,List.flatten_cons,List.append_assoc] using hx) hp hlen
    let y : Data := {advanced x with pos:=x.pos+N}
    have hy : y.source=(pre++row)++rows.flatten++suffix := by
      simpa [y,advanced,List.flatten_cons,List.append_assoc] using hx
    have hyp : y.pos=(pre++row).length := by simp [y,hp,hlen]
    have hyc : y.counter+rows.length=y.bound := by
      simp only [y,advanced]
      simp only [List.length_cons] at hc
      omega
    obtain ⟨c,ht,third⟩ := ih (pre++row) y hy hyp
      (by intro r hr; exact hl r (by simp [hr])) hyc hb
    have he : endpoint N y rows.length=endpoint N x (row::rows).length := by
      simp [endpoint,y,advanced,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    rw [he] at third
    have whole := (first.trans second).trans third
    refine ⟨a+b+c,?_,whole⟩
    simp only [List.length_cons,Nat.add_mul,one_mul]
    omega

theorem scan_run (N w : ℕ) (rows : List (List Bool)) (suffix : List Bool) (x : Data)
    (hx : x.source=rows.flatten++suffix) (hp : x.pos=0)
    (hl : ∀ row∈rows,row.length=N) (hc : x.counter=0) (hd : x.bound=rows.length)
    (hb : rows.length+1<2^w) :
    ∃ r,runFrom machine (rows.length*(2*N+8*w+15)+8*w+10)
      (cfg machine.start N w x)=some r ∧
      r.final.heads=heads (endpoint N x rows.length) ∧
      r.final.tapes=tapes N w (endpoint N x rows.length) ∧
      r.steps≤rows.length*(2*N+8*w+15)+8*w+10 := by
  obtain ⟨n,hn,h⟩ := scan_timed N w [] rows suffix x (by simpa using hx) hp hl (by omega) (by omega)
  obtain ⟨r,hr,rf,rs⟩ := h.run (by simp [machine,finished,RecoveryCalls.machine,RecoveryCalls.stopped])
  have more := runFrom_moreFuel machine n (rows.length*(2*N+8*w+15)+8*w+10-n) _ r hr
  rw [Nat.add_sub_of_le hn] at more
  refine ⟨r,?_,?_,?_,rs.le.trans hn⟩
  · exact more
  · rw [rf]; rfl
  · rw [rf]; rfl

end NearCubicWires.RepairOrdinary.RowMaskPositionLoop
