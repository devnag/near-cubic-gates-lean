import Proof.PCP.VerifierDecodingTableBoundLayout

/-! One ordinary finite program checks the guarded transition-table entry
count. Its only nonzero inputs are the already produced c,t,s counters; it
writes its initial unit values and its final acceptance bit itself. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.TableBoundMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def acceptProgram : Machine 7 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val = 1
  rule := fun q _ => if q.val = 0 then
    some ⟨1,![none,none,none,none,none,none,some true],fun _ => .stay⟩ else none

def acceptInput (c t s p result : ℕ) : Configuration 7 2 :=
  ⟨0,(productOutput c t s p result).heads,(productOutput c t s p result).tapes⟩
def acceptOutput (c t s p result : ℕ) : Configuration 7 2 :=
  ⟨1,(productOutput c t s p result).heads,store c p p t result s true⟩

theorem accept_step (c t s p result : ℕ) :
    step acceptProgram (acceptInput c t s p result) = some (acceptOutput c t s p result) := by
  simp [step,acceptProgram,acceptInput]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,acceptOutput,productOutput]
  · funext i; fin_cases i <;> simp [applyAction,acceptOutput,productOutput,store,writeTapeBit]

def sizes : Fin 5 → ℕ := ![2,11,3,6,2]
def programs : (j : Fin 5) → Machine 7 (sizes j)
  | ⟨0,_⟩ => initProgram
  | ⟨1,_⟩ => powerProgram
  | ⟨2,_⟩ => resetProgram
  | ⟨3,_⟩ => productProgram
  | ⟨4,_⟩ => acceptProgram
  | ⟨n+5,h⟩ => False.elim (by omega)
def next (j : Fin 5) (state : Fin (sizes j)) (_ : Fin 7 → Bool) : Option (Fin 5) :=
  if j.val = 0 then some 1
  else if j.val = 1 then if state.val = 9 then some 2 else none
  else if j.val = 2 then some 3
  else if j.val = 3 then if state.val = 4 then some 4 else none
  else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def budget (c : ℕ) := 10*c*c+14*c+12
noncomputable def succeeded (c t s : ℕ) := RecoveryCalls.stopped sizes
  (acceptOutput c t s (2^t) (2^t*s)).heads (acceptOutput c t s (2^t) (2^t*s)).tapes

def Result (c t s : ℕ) (d : Configuration 7 (Fintype.card (RecoveryCalls.Control sizes))) : Prop :=
  if 2^t*s ≤ c then d = succeeded c t s else d.tapes 6 = [false]

private theorem call (j l : Fin 5) (fuel : ℕ) (c : Configuration 7 (sizes j))
    (r : ExecutionReceipt 7 (sizes j)) (d : Configuration 7 (sizes l))
    (hr : runFrom (programs j) fuel c = some r)
    (hd : d.control = (programs l).start)
    (hh : r.final.heads = d.heads) (ht : r.final.tapes = d.tapes)
    (hn : next j r.final.control r.final.scanned = some l) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes j) c)
      (controlConfig (RecoveryCalls.code sizes l) d) := by
  have hp := prefix_of_run (programs j) fuel c r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp.1⟩
  have hs := RecoveryCalls.return_step sizes programs 0 next j l r.final hp.2 hn
  have he : RecoveryCalls.restarted (programs l) r.final.heads r.final.tapes = d := by
    apply configuration_ext
    · exact hd.symm
    · exact hh
    · exact ht
  rw [he] at hs
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,RecoveryCalls.code,controlConfig]) hs)

private theorem stop (j : Fin 5) (fuel : ℕ) (c : Configuration 7 (sizes j))
    (r : ExecutionReceipt 7 (sizes j)) (hr : runFrom (programs j) fuel c = some r)
    (hn : next j r.final.control r.final.scanned = none) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes j) c)
      (RecoveryCalls.stopped sizes r.final.heads r.final.tapes) := by
  have hp := prefix_of_run (programs j) fuel c r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp.1⟩
  have hs := RecoveryCalls.stop_step sizes programs 0 next j r.final hp.2 hn
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,RecoveryCalls.code,controlConfig]) hs)

private theorem enter (c t s : ℕ) :
    Timed machine 2 (controlConfig (RecoveryCalls.code sizes 0) (initial c t s))
      (controlConfig (RecoveryCalls.code sizes 1) (powerInput c t s)) := by
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl : initProgram.halted (0 : Fin 2) = false) (init_step c t s)).run (by rfl)
  have hp := call 0 1 1 (initial c t s) r (powerInput c t s) hr rfl
    (by simp [hf]) (by simp [hf]) (by rfl)
  simpa only [hs] using hp

private theorem accept (c t s p result : ℕ) :
    Timed machine 2 (controlConfig (RecoveryCalls.code sizes 4) (acceptInput c t s p result))
      (RecoveryCalls.stopped sizes (acceptOutput c t s p result).heads (acceptOutput c t s p result).tapes) := by
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl : acceptProgram.halted (0 : Fin 2) = false)
    (accept_step c t s p result)).run (by rfl)
  have hp := stop 4 1 (acceptInput c t s p result) r hr (by rfl)
  simpa only [hs,hf] using hp

private theorem close_run (c t s time : ℕ) (heads : Fin 7 → ℕ) (tapes : Fin 7 → List Bool)
    (hp : Timed machine time (controlConfig (RecoveryCalls.code sizes 0) (initial c t s))
      (RecoveryCalls.stopped sizes heads tapes)) (hb : time ≤ budget c)
    (hout : Result c t s (RecoveryCalls.stopped sizes heads tapes)) :
    ∃ receipt, runFrom machine (budget c) (controlConfig (RecoveryCalls.code sizes 0) (initial c t s)) = some receipt ∧
      receipt.steps ≤ budget c ∧ Result c t s receipt.final := by
  obtain ⟨r,hr,hf,hs⟩ := hp.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel machine time (budget c-time) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨r,hm,hs.trans_le hb,by simpa only [hf] using hout⟩

/-- Complete table-entry guard, including all oversized dimensions. Each
arithmetic loop is capped by literal c before writing or further iteration. -/
theorem table_bound_run (c t s : ℕ) (hc : 1 ≤ c) (ht : t ≤ c) (hs : s ≤ c) (hspos : 0 < s) :
    ∃ receipt, runFrom machine (budget c) (controlConfig (RecoveryCalls.code sizes 0) (initial c t s)) = some receipt ∧
      receipt.steps ≤ budget c ∧ Result c t s receipt.final := by
  obtain ⟨pr,hpr,hpt,hpf⟩ := power_layout c t s hc ht
  have hpb : t*(8*c+9) ≤ c*(8*c+9) := Nat.mul_le_mul_right _ ht
  by_cases hpower : 2^t ≤ c
  · simp only [if_pos hpower] at hpf
    have hp := call 1 2 _ (powerInput c t s) pr (resetInput c t s (2^t)) hpr rfl
      (by simp [hpf,resetInput]) (by simp [hpf,resetInput]) (by simp [hpf,powerOutput,next])
    obtain ⟨rr,hrr,hrf,hrt⟩ := reset_layout c t s (2^t) hpower
    have hr := call 2 3 _ (resetInput c t s (2^t)) rr (productInput c t s (2^t)) hrr rfl
      (by simp [hrf]) (by simp [hrf]) (by rfl)
    obtain ⟨mr,hmr,hmt,hmf⟩ := product_layout c t s (2^t) hpower hs
    have hmb : s*(2*(2^t)+4) ≤ c*(2*c+4) := Nat.mul_le_mul hs (by omega)
    by_cases hfit : 2^t*s ≤ c
    · simp only [if_pos hfit] at hmf
      have hm := call 3 4 _ (productInput c t s (2^t)) mr (acceptInput c t s (2^t) (2^t*s)) hmr rfl
        (by simp [hmf,acceptInput]) (by simp [hmf,acceptInput]) (by simp [hmf,productOutput,next])
      have hall := (enter c t s).trans (hp.trans (hr.trans (hm.trans (accept c t s (2^t) (2^t*s)))))
      exact close_run c t s _ _ _ hall (by dsimp [budget]; rw [hrt]; nlinarith)
        (by simp [Result,hfit,succeeded])
    · simp only [if_neg hfit] at hmf
      have hm := stop 3 _ (productInput c t s (2^t)) mr hmr (by simp [hmf.1,next])
      have hall := (enter c t s).trans (hp.trans (hr.trans hm))
      exact close_run c t s _ _ _ hall (by dsimp [budget]; rw [hrt]; nlinarith)
        (by simpa [Result,hfit,RecoveryCalls.stopped] using hmf.2)
  · simp only [if_neg hpower] at hpf
    have hfit : ¬2^t*s ≤ c := by
      have hpos : 0 < 2^t := Nat.two_pow_pos t
      nlinarith
    have hp := stop 1 _ (powerInput c t s) pr hpr (by simp [hpf.1,next])
    have hall := (enter c t s).trans hp
    exact close_run c t s _ _ _ hall (by dsimp [budget]; nlinarith)
      (by simpa [Result,hfit,RecoveryCalls.stopped] using hpf.2)

end NearCubicWires.RepairSource.VerifierDecoding.TableBoundMachine
