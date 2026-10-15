import Proof.PCP.VerifierLookupNavigationTapes

/-! Fixed lookup entry programs compute flag/table positions by walking the
actual dimension tapes, after paying the code rewind from its retained head. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupNavigation
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 8 → ℕ := ![6,4,3,4,3,4,4,4]
noncomputable def programs : (j : Fin 8) → Machine 5 (sizes j)
  | 0 => reset
  | 1 => walk 0
  | 2 => two
  | 3 => walk 1
  | 4 => two
  | 5 => walk 3
  | 6 => walk 1
  | 7 => walk 1

def next (table : Bool) (j : Fin 8) (_ : Fin (sizes j)) (_ : Fin 5 → Bool) : Option (Fin 8) :=
  if j.val=5 ∧ table=false then none else if h:j.val<7 then some ⟨j.val+1,by omega⟩ else none
noncomputable def machine (table : Bool) := RecoveryCalls.machine sizes programs 0 (next table)

theorem call_phase (table : Bool) (j k : Fin 8) (d e : Store) (fuel : ℕ) (q : Fin (sizes j))
    (r : ExecutionReceipt 5 (sizes j))
    (hr : runFrom (programs j) fuel (cfg (programs j).start d)=some r)
    (hf : r.final=cfg q e) (hn : ∀ c bits,next table j c bits=some k) :
    ∃ time≤fuel+1,Timed (machine table) time
      (cfg (RecoveryCalls.code sizes j (programs j).start) d)
      (cfg (RecoveryCalls.code sizes k (programs k).start) e) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 (next table) j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step sizes programs 0 (next table) j k r.final hh (hn _ _)
  have hj := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at hj
  have hs := runFrom_steps_le (programs j) fuel _ r hr
  exact ⟨r.steps+1,by omega,hj⟩

theorem stop_phase (table : Bool) (j : Fin 8) (d e : Store) (fuel : ℕ) (q : Fin (sizes j))
    (r : ExecutionReceipt 5 (sizes j))
    (hr : runFrom (programs j) fuel (cfg (programs j).start d)=some r)
    (hf : r.final=cfg q e) (hn : ∀ c bits,next table j c bits=none) :
    ∃ time≤fuel+1,Timed (machine table) time
      (cfg (RecoveryCalls.code sizes j (programs j).start) d)
      (cfg (RecoveryCalls.controlCode sizes none) e) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 (next table) j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 (next table) j r.final hh (hn _ _)
  have hj := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at hj
  have hs := runFrom_steps_le (programs j) fuel _ r hr
  exact ⟨r.steps+1,by omega,hj⟩

theorem header_prefix (table : Bool) (d : Store) (hp : d.pos≤2*d.c+1) :
    ∃ time≤3*d.c+3*d.t+3*d.s+17,Timed (machine table) time
      (cfg (machine table).start d)
      (cfg (RecoveryCalls.code sizes 5 (programs 5).start) (positioned d (2*(d.t+d.s+2)))) := by
  let d0 := positioned d 0
  let d1 := positioned d0 (d0.pos+2*d0.t)
  let d2 := positioned d1 (d1.pos+2)
  let d3 := positioned d2 (d2.pos+2*d2.s)
  let d4 := positioned d3 (d3.pos+2)
  obtain ⟨r0,hr0,hf0,_⟩ := reset_run d hp
  obtain ⟨n0,hn0,hp0⟩ := call_phase table 0 1 d d0 _ _ r0 hr0 hf0 (by intro q bits; rfl)
  obtain ⟨r1,hr1,hf1,_⟩ := walk_run 0 d0 d0.t (d0.c+2) rfl
  obtain ⟨n1,hn1,hp1⟩ := call_phase table 1 2 d0 d1 _ _ r1 hr1 hf1 (by intro q bits; rfl)
  obtain ⟨r2,hr2,hf2,_⟩ := two_run d1
  obtain ⟨n2,hn2,hp2⟩ := call_phase table 2 3 d1 d2 _ _ r2 hr2 hf2 (by intro q bits; rfl)
  obtain ⟨r3,hr3,hf3,_⟩ := walk_run 1 d2 d2.s (d2.c+2) rfl
  obtain ⟨n3,hn3,hp3⟩ := call_phase table 3 4 d2 d3 _ _ r3 hr3 hf3 (by intro q bits; rfl)
  obtain ⟨r4,hr4,hf4,_⟩ := two_run d3
  obtain ⟨n4,hn4,hp4⟩ := call_phase table 4 5 d3 d4 _ _ r4 hr4 hf4 (by intro q bits; rfl)
  have h := (((hp0.trans hp1).trans hp2).trans hp3).trans hp4
  have he : d4=positioned d (2*(d.t+d.s+2)) := by
    dsimp only [d4,d3,d2,d1,d0,positioned]
    congr 1
    omega
  rw [he] at h
  refine ⟨(((n0+n1)+n2)+n3)+n4,?_,h⟩
  change n1≤3*d.t+2+1 at hn1
  change n3≤3*d.s+2+1 at hn3
  omega

theorem flags_run (d : Store) (hp : d.pos≤2*d.c+1) :
    ∃ r,runFrom (machine false) (3*d.c+3*d.t+3*d.s+3*d.j+20)
      (cfg (machine false).start d)=some r ∧
      r.final=cfg (RecoveryCalls.controlCode sizes none) (positioned d (2*(d.t+d.s+d.j+2))) ∧
      r.steps≤3*d.c+3*d.t+3*d.s+3*d.j+20 := by
  let e := positioned d (2*(d.t+d.s+2))
  obtain ⟨n0,hn0,hp0⟩ := header_prefix false d hp
  obtain ⟨r1,hr1,hf1,_⟩ := walk_run 3 e e.j 0 (by
    change CompareMachine.word e.j=ZeroPadding.pad 0 (CompareMachine.word e.j)
    simp only [ZeroPadding.pad_zero])
  obtain ⟨n1,hn1,hp1⟩ := stop_phase false 5 e (positioned e (e.pos+2*e.j)) _ _ r1 hr1 hf1 (by intro q bits; rfl)
  have h := hp0.trans hp1
  have he : positioned e (e.pos+2*e.j)=positioned d (2*(d.t+d.s+d.j+2)) := by
    dsimp only [e,positioned]
    congr 1
    omega
  rw [he] at h
  obtain ⟨r,hr,hrf,hrs⟩ := h.run (by simp [machine,RecoveryCalls.machine,cfg])
  have htime : n0+n1≤3*d.c+3*d.t+3*d.s+3*d.j+20 := by change n1≤3*d.j+2+1 at hn1; omega
  have hm := runFrom_moreFuel (machine false) _ ((3*d.c+3*d.t+3*d.s+3*d.j+20)-(n0+n1)) _ r hr
  rw [Nat.add_sub_of_le htime] at hm
  exact ⟨r,hm,hrf,hrs.trans_le htime⟩

theorem table_run (d : Store) (hp : d.pos≤2*d.c+1) :
    ∃ r,runFrom (machine true) (3*d.c+3*d.t+9*d.s+3*d.j+26)
      (cfg (machine true).start d)=some r ∧
      r.final=cfg (RecoveryCalls.controlCode sizes none) (positioned d (2*(d.t+3*d.s+d.j+2))) ∧
      r.steps≤3*d.c+3*d.t+9*d.s+3*d.j+26 := by
  let e := positioned d (2*(d.t+d.s+2))
  let e1 := positioned e (e.pos+2*e.j)
  let e2 := positioned e1 (e1.pos+2*e1.s)
  let e3 := positioned e2 (e2.pos+2*e2.s)
  obtain ⟨n0,hn0,hp0⟩ := header_prefix true d hp
  obtain ⟨r1,hr1,hf1,_⟩ := walk_run 3 e e.j 0 (by
    change CompareMachine.word e.j=ZeroPadding.pad 0 (CompareMachine.word e.j)
    simp only [ZeroPadding.pad_zero])
  obtain ⟨n1,hn1,hp1⟩ := call_phase true 5 6 e e1 _ _ r1 hr1 hf1 (by intro q bits; rfl)
  obtain ⟨r2,hr2,hf2,_⟩ := walk_run 1 e1 e1.s (e1.c+2) rfl
  obtain ⟨n2,hn2,hp2⟩ := call_phase true 6 7 e1 e2 _ _ r2 hr2 hf2 (by intro q bits; rfl)
  obtain ⟨r3,hr3,hf3,_⟩ := walk_run 1 e2 e2.s (e2.c+2) rfl
  obtain ⟨n3,hn3,hp3⟩ := stop_phase true 7 e2 e3 _ _ r3 hr3 hf3 (by intro q bits; rfl)
  have h := ((hp0.trans hp1).trans hp2).trans hp3
  have he : e3=positioned d (2*(d.t+3*d.s+d.j+2)) := by
    dsimp only [e3,e2,e1,e,positioned]
    congr 1
    omega
  rw [he] at h
  obtain ⟨r,hr,hrf,hrs⟩ := h.run (by simp [machine,RecoveryCalls.machine,cfg])
  have htime : (n0+n1)+n2+n3≤3*d.c+3*d.t+9*d.s+3*d.j+26 := by
    change n1≤3*d.j+2+1 at hn1
    change n2≤3*d.s+2+1 at hn2
    change n3≤3*d.s+2+1 at hn3
    omega
  have hm := runFrom_moreFuel (machine true) _ ((3*d.c+3*d.t+9*d.s+3*d.j+26)-((n0+n1)+n2+n3)) _ r hr
  rw [Nat.add_sub_of_le htime] at hm
  exact ⟨r,hm,hrf,hrs.trans_le htime⟩

end NearCubicWires.RepairSource.VerifierDecoding.LookupNavigation
