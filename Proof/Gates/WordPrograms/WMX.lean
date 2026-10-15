import Proof.Wire_3_5.PrimAsmDockW
import Proof.Wire_3_5.FinalPassWordLib

set_option autoImplicit false

namespace NearCubicGates.Close.WordPrograms
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW

/-! ## Bank level: structured programs with machine calls -/

inductive XProg (t : ℕ) where
  | prog (P : Prog t) : XProg t
  | mach {s : ℕ} (M : Machine t s) : XProg t
  | seq (P Q : XProg t) : XProg t
  | ite (i : Fin t) (P Q : XProg t) : XProg t
  | loop (i : Fin t) (P : XProg t) : XProg t

variable {t : ℕ}

/-- The number of control states. -/
def XProg.size : XProg t → ℕ
  | .prog P => P.size
  | @XProg.mach _ s _ => s
  | .seq P Q => P.size + Q.size
  | .ite _ P Q => P.size + Q.size + 1
  | .loop _ P => P.size + 2

/-- **One machine per program.** A machine call compiles to the machine itself. -/
def XProg.compile : (P : XProg t) → Machine t P.size
  | .prog P => P.compile
  | .mach M => M
  | .seq P Q => Composition.machine P.compile Q.compile
  | .ite i P Q => iteMachine i P.compile Q.compile
  | .loop i P => StreamController.machine P.compile i

/-- `XExec P b c n`: the program runs from bank `b` to bank `c` within `n` steps of its machine. -/
inductive XExec : XProg t → Bank t → Bank t → ℕ → Prop where
  | prog {P : Prog t} {b c : Bank t} {n : ℕ} : Exec P b c n → XExec (.prog P) b c n
  | mach {s : ℕ} {M : Machine t s} {b c : Bank t} {n : ℕ} : Step M n b.H b.A c.H c.A → XExec (.mach M) b c n
  | seq {P Q : XProg t} {b c d : Bank t} {n k : ℕ} : XExec P b c n → XExec Q c d k →
      XExec (.seq P Q) b d (n + 1 + k)
  | iteT {i : Fin t} {P Q : XProg t} {b c : Bank t} {n : ℕ} : b.bit i = true → XExec P b c n →
      XExec (.ite i P Q) b c (n + 1)
  | iteF {i : Fin t} {P Q : XProg t} {b c : Bank t} {n : ℕ} : b.bit i = false → XExec Q b c n →
      XExec (.ite i P Q) b c (n + 1)
  | loopF {i : Fin t} {P : XProg t} {b : Bank t} : b.bit i = false → XExec (.loop i P) b b 1
  | loopT {i : Fin t} {P : XProg t} {b c d : Bank t} {n k : ℕ} : b.bit i = true → XExec P b c n →
      XExec (.loop i P) c d k → XExec (.loop i P) b d (n + 2 + k)
  | mono {P : XProg t} {b c : Bank t} {n m : ℕ} : XExec P b c n → n ≤ m → XExec P b c m

/-- **Soundness**: every derivation is a `Step` of the compiled machine. -/
theorem XExec.step {P : XProg t} {b c : Bank t} {n : ℕ} (h : XExec P b c n) :
    Step P.compile n b.H b.A c.H c.A := by
  induction h with
  | prog h => exact h.step
  | mach h => exact h
  | seq _ _ ih1 ih2 => exact Step.seq ih1 ih2
  | @iteT i P Q b c n hb _ ih =>
    exact ite_branch_step i P.compile Q.compile b c n (iteL Q.size) P.compile (by simp [hb])
      (ite_halted_L i _ _) (ite_step_L i _ _) ih
  | @iteF i P Q b c n hb _ ih =>
    exact ite_branch_step i P.compile Q.compile b c n (iteR P.size) Q.compile (by simp [hb])
      (ite_halted_R i _ _) (ite_step_R i _ _) ih
  | @loopF i P b hb =>
    have hs := StreamController.stop_step P.compile i ⟨P.compile.start, b.H, b.A⟩ hb
    have hr := runFrom_step (fuel := 0) (StreamController.machine P.compile i) _ _ _
      (StreamController.test_halted P.compile i) hs (runFrom_zero_of_halted _ _ (StreamController.stop_halted _ _))
    exact ⟨_, hr, rfl, rfl, by simp⟩
  | @loopT i P b c d n k hb _ _ ih1 ih2 =>
    obtain ⟨r1, hr1, hh1, ht1, hs1⟩ := ih1
    obtain ⟨r2, hr2, hh2, ht2, hs2⟩ := ih2
    have henter := StreamController.enter_step P.compile i ⟨P.compile.start, b.H, b.A⟩ hb
    obtain ⟨hbody, hhalt⟩ := StreamController.body_prefix P.compile i n _ r1 hr1
    have hret := StreamController.return_step P.compile i r1.final hhalt
    have t1 := Timed.single (StreamController.test_halted P.compile i) henter
    have t2 : Timed (StreamController.machine P.compile i) r1.steps
        (controlConfig RecordController.code (Composition.restart ⟨P.compile.start, b.H, b.A⟩ P.compile.start))
        (controlConfig RecordController.code r1.final) := ⟨_, hbody⟩
    have t3 := Timed.single (StreamController.body_halted P.compile i r1.final.control) hret
    have e3 : controlConfig (fun _ => RecordController.test P.size) r1.final =
        (⟨(StreamController.machine P.compile i).start, c.H, c.A⟩ : Configuration t (P.size + 2)) := by
      apply configuration_ext
      · rfl
      · exact hh1
      · exact ht1
    rw [e3] at t3
    obtain ⟨sp, hpre⟩ := (t1.trans t2).trans t3
    obtain ⟨joined, hj, hjf, hjs, _⟩ := hpre.followedBy r2 hr2
    have e1 : controlConfig (fun _ => RecordController.test P.size) (⟨P.compile.start, b.H, b.A⟩ :
        Configuration t P.size) = ⟨(StreamController.machine P.compile i).start, b.H, b.A⟩ := rfl
    rw [e1] at hj
    have more := runFrom_moreFuel _ (1 + r1.steps + 1 + k) (n + 2 + k - (1 + r1.steps + 1 + k)) _ joined hj
    rw [show 1 + r1.steps + 1 + k + (n + 2 + k - (1 + r1.steps + 1 + k)) = n + 2 + k by omega] at more
    refine ⟨joined, more, ?_, ?_, by omega⟩
    · rw [hjf]; exact hh2
    · rw [hjf]; exact ht2
  | mono _ hnm ih => exact ih.enlarge hnm

variable {ns nr : ℕ}

inductive WMX (ns nr : ℕ) where
  | wm (P : WM ns nr) : WMX ns nr
  | mach {t s : ℕ} (M : Machine t s) (tmap : Fin t → Fin (ns + 1)) : WMX ns nr
  | seq (P Q : WMX ns nr) : WMX ns nr
  | ifr (r : Fin nr) (P Q : WMX ns nr) : WMX ns nr
  | ifs (i : Fin (ns + 1)) (P Q : WMX ns nr) : WMX ns nr
  | whr (r : Fin nr) (P : WMX ns nr) : WMX ns nr
  | whs (i : Fin (ns + 1)) (P : WMX ns nr) : WMX ns nr

/-- The bank-level program. -/
noncomputable def WMX.toX : WMX ns nr → XProg (ns + 2 + nr)
  | .wm P => .prog P.toProg
  | .mach M tmap => .mach (RecoveryFocus.machine (fun j => sTape (nr := nr) (tmap j)) M)
  | .seq P Q => .seq P.toX Q.toX
  | .ifr r P Q => .ite (rTape r) P.toX Q.toX
  | .ifs i P Q => .ite (sTape i) P.toX Q.toX
  | .whr r P => .loop (rTape r) P.toX
  | .whs i P => .loop (sTape i) P.toX

/-- The number of control states of the compiled machine. -/
noncomputable def WMX.size (P : WMX ns nr) : ℕ := P.toX.size

/-- **One machine per word program.** -/
noncomputable def WMX.compile (P : WMX ns nr) : Machine (ns + 2 + nr) P.size := P.toX.compile

/-- **Big-step semantics** with the costs of the compiled machine. -/
inductive WXExec (cap : ℕ) : WMX ns nr → WState ns nr → WState ns nr → ℕ → Prop where
  | wm {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} : WExec cap P σ τ n → WXExec cap (.wm P) σ τ n
  | mach {t s n : ℕ} {M : Machine t s} {tmap : Fin t → Fin (ns + 1)} (σ : WState ns nr) {hout : Fin t → ℕ}
      {tout : Fin t → List Bool} : Function.Injective tmap →
      Step M n (fun j => σ.sh (tmap j)) (fun j => σ.st (tmap j)) hout tout →
      WXExec cap (.mach M tmap) σ (updS tmap σ hout tout) n
  | seq {P Q : WMX ns nr} {σ τ ρ : WState ns nr} {n k : ℕ} : WXExec cap P σ τ n → WXExec cap Q τ ρ k →
      WXExec cap (.seq P Q) σ ρ (n + 1 + k)
  | ifrT {r : Fin nr} {P Q : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} : σ.val r ≠ 0 → WXExec cap P σ τ n →
      WXExec cap (.ifr r P Q) σ τ (n + 1)
  | ifrF {r : Fin nr} {P Q : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} : σ.val r = 0 → WXExec cap Q σ τ n →
      WXExec cap (.ifr r P Q) σ τ (n + 1)
  | ifsT {i : Fin (ns + 1)} {P Q : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} : wbit σ i = true → WXExec cap P σ τ n →
      WXExec cap (.ifs i P Q) σ τ (n + 1)
  | ifsF {i : Fin (ns + 1)} {P Q : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} : wbit σ i = false →
      WXExec cap Q σ τ n → WXExec cap (.ifs i P Q) σ τ (n + 1)
  | whrF {r : Fin nr} {P : WMX ns nr} {σ : WState ns nr} : σ.val r = 0 → WXExec cap (.whr r P) σ σ 1
  | whrT {r : Fin nr} {P : WMX ns nr} {σ τ ρ : WState ns nr} {n k : ℕ} : σ.val r ≠ 0 → WXExec cap P σ τ n →
      WXExec cap (.whr r P) τ ρ k → WXExec cap (.whr r P) σ ρ (n + 2 + k)
  | whsF {i : Fin (ns + 1)} {P : WMX ns nr} {σ : WState ns nr} : wbit σ i = false → WXExec cap (.whs i P) σ σ 1
  | whsT {i : Fin (ns + 1)} {P : WMX ns nr} {σ τ ρ : WState ns nr} {n k : ℕ} : wbit σ i = true →
      WXExec cap P σ τ n → WXExec cap (.whs i P) τ ρ k → WXExec cap (.whs i P) σ ρ (n + 2 + k)
  | mono {P : WMX ns nr} {σ τ : WState ns nr} {n m : ℕ} : WXExec cap P σ τ n → n ≤ m → WXExec cap P σ τ m

variable (cap : ℕ)

/-- Soundness at the bank level. -/
theorem WXExec.exec {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WXExec cap P σ τ n) :
    XExec P.toX (wenc cap σ) (wenc cap τ) n := by
  induction h with
  | wm h => exact XExec.prog (WExec.exec cap h)
  | mach σ hinj h => exact XExec.mach (dockS cap _ hinj σ h)
  | seq _ _ ih1 ih2 => exact XExec.seq ih1 ih2
  | ifrT hv _ ih => exact XExec.iteT (by rw [wbit_r]; simpa using hv) ih
  | ifrF hv _ ih => exact XExec.iteF (by rw [wbit_r]; simpa using hv) ih
  | ifsT hv _ ih => exact XExec.iteT (by rw [wbit_s]; exact hv) ih
  | ifsF hv _ ih => exact XExec.iteF (by rw [wbit_s]; exact hv) ih
  | whrF hv => exact XExec.loopF (by rw [wbit_r]; simpa using hv)
  | whrT hv _ _ ih1 ih2 => exact XExec.loopT (by rw [wbit_r]; simpa using hv) ih1 ih2
  | whsF hv => exact XExec.loopF (by rw [wbit_s]; exact hv)
  | whsT hv _ _ ih1 ih2 => exact XExec.loopT (by rw [wbit_s]; exact hv) ih1 ih2
  | mono _ hnm ih => exact XExec.mono ih hnm

/-- **Soundness**: every derivation is a `Step` of the ONE compiled machine, on the encoded banks. -/
theorem WXExec.step {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WXExec cap P σ τ n) :
    Step P.compile n (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A :=
  (h.exec cap).step

/-- The encoded heads of a state whose stream heads and registers are all `0` are all `0`. -/
theorem wenc_H_zero (σ : WState ns nr) (hsh : ∀ i, σ.sh i = 0) (hval : ∀ r, σ.val r = 0) :
    (wenc cap σ).H = fun _ => 0 := by
  funext j
  rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [wenc_H_s, hsh]
  · exact wenc_H_c cap σ
  · rw [wenc_H_r, hval]

/-- **Soundness as a plain `run`** from the initial configuration (all heads at `0`): the compiled machine halts
within `n` steps on the encoded tapes of `σ` with the encoded tapes of `τ`. -/
theorem WXExec.run {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WXExec cap P σ τ n)
    (hsh : ∀ i, σ.sh i = 0) (hval : ∀ r, σ.val r = 0) :
    ∃ r : ExecutionReceipt (ns + 2 + nr) P.size, run P.compile n (wenc cap σ).A = some r ∧
      r.final.heads = (wenc cap τ).H ∧ r.final.tapes = (wenc cap τ).A ∧ r.steps ≤ n := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h.step cap
  rw [wenc_H_zero cap σ hsh hval] at hr
  exact ⟨r, hr, hh, ht, hs⟩

/-! ## Rules for consumers -/

theorem WXExec.cast {P : WMX ns nr} {σ τ τ' : WState ns nr} {n n' : ℕ} (h : WXExec cap P σ τ n) (e : τ = τ')
    (hn : n ≤ n') : WXExec cap P σ τ' n' := by
  subst e; exact WXExec.mono h hn

theorem WXExec.ofW {P : WM ns nr} {σ τ τ' : WState ns nr} {n n' : ℕ} (h : WExec cap P σ τ n) (e : τ = τ')
    (hn : n ≤ n') : WXExec cap (.wm P) σ τ' n' :=
  WXExec.cast cap (WXExec.wm h) e hn

/-- Sequencing with the cost stated once. -/
theorem WXExec.seq' {P Q : WMX ns nr} {σ τ ρ : WState ns nr} {n k m : ℕ} (h1 : WXExec cap P σ τ n)
    (h2 : WXExec cap Q τ ρ k) (hm : n + 1 + k ≤ m) : WXExec cap (.seq P Q) σ ρ m :=
  WXExec.mono (WXExec.seq h1 h2) hm

section Upd
variable {t' : ℕ} (tmap : Fin t' → Fin (ns + 1)) (σ : WState ns nr) (hout : Fin t' → ℕ) (tout : Fin t' → List Bool)

theorem updS_st_slot (hinj : Function.Injective tmap) (j : Fin t') : (updS tmap σ hout tout).st (tmap j) = tout j :=
  install_slot tmap hinj σ.st tout j

theorem updS_sh_slot (hinj : Function.Injective tmap) (j : Fin t') : (updS tmap σ hout tout).sh (tmap j) = hout j :=
  dockH_slot tmap hinj σ.sh hout j

theorem updS_st_other (i : Fin (ns + 1)) (hi : ∀ j, tmap j ≠ i) : (updS tmap σ hout tout).st i = σ.st i :=
  install_other tmap σ.st tout i hi

theorem updS_sh_other (i : Fin (ns + 1)) (hi : ∀ j, tmap j ≠ i) : (updS tmap σ hout tout).sh i = σ.sh i :=
  dockH_other tmap σ.sh hout i hi

@[simp] theorem updS_val : (updS tmap σ hout tout).val = σ.val := rfl

@[simp] theorem updS_cell : (updS tmap σ hout tout).cell = σ.cell := rfl

/-- `updS` is characterized by its slots and its frame. -/
theorem updS_eq (hinj : Function.Injective tmap) (τ : WState ns nr) (hst : ∀ j, τ.st (tmap j) = tout j)
    (hsh : ∀ j, τ.sh (tmap j) = hout j) (hout' : ∀ i, (∀ j, tmap j ≠ i) → τ.st i = σ.st i ∧ τ.sh i = σ.sh i)
    (hval : τ.val = σ.val) (hcell : τ.cell = σ.cell) : updS tmap σ hout tout = τ := by
  classical
  apply WState.eq
  · funext i
    by_cases h : ∃ j, tmap j = i
    · obtain ⟨j, rfl⟩ := h
      rw [updS_sh_slot tmap σ hout tout hinj, hsh]
    · have h' : ∀ j, tmap j ≠ i := fun j hj => h ⟨j, hj⟩
      rw [updS_sh_other tmap σ hout tout i h', (hout' i h').2]
  · funext i
    by_cases h : ∃ j, tmap j = i
    · obtain ⟨j, rfl⟩ := h
      rw [updS_st_slot tmap σ hout tout hinj, hst]
    · have h' : ∀ j, tmap j ≠ i := fun j hj => h ⟨j, hj⟩
      rw [updS_st_other tmap σ hout tout i h', (hout' i h').1]
  · exact hval.symm
  · exact hcell.symm

end Upd

theorem WXExec.mach_of {t' s n : ℕ} {M : Machine t' s} {tmap : Fin t' → Fin (ns + 1)} (hinj : Function.Injective tmap)
    {σ τ : WState ns nr} {hout : Fin t' → ℕ} {tout : Fin t' → List Bool}
    (h : Step M n (fun j => σ.sh (tmap j)) (fun j => σ.st (tmap j)) hout tout)
    (hst : ∀ j, τ.st (tmap j) = tout j) (hsh : ∀ j, τ.sh (tmap j) = hout j)
    (hout' : ∀ i, (∀ j, tmap j ≠ i) → τ.st i = σ.st i ∧ τ.sh i = σ.sh i)
    (hval : τ.val = σ.val) (hcell : τ.cell = σ.cell) : WXExec cap (.mach M tmap) σ τ n := by
  have e := updS_eq tmap σ hout tout hinj τ hst hsh hout' hval hcell
  rw [← e]
  exact WXExec.mach σ hinj h

noncomputable def WMX.machZ {t' s : ℕ} (M : Machine t' s) (tmap : Fin t' → Fin (ns + 1)) (L : Fin (ns + 1)) :
    WMX ns nr :=
  .mach (MaskedReset.machine M (fun _ => true)) (Fin.addCases tmap (fun _ : Fin 1 => L))

theorem addCases_inj {t' : ℕ} (tmap : Fin t' → Fin (ns + 1)) (hinj : Function.Injective tmap) (L : Fin (ns + 1))
    (hL : ∀ j, tmap j ≠ L) : Function.Injective (Fin.addCases (motive := fun _ => Fin (ns + 1)) tmap
      (fun _ : Fin 1 => L)) := by
  intro a b
  refine Fin.addCases (fun a' => ?_) (fun a' => ?_) a <;> refine Fin.addCases (fun b' => ?_) (fun b' => ?_) b <;>
    intro hab
  · simp only [Fin.addCases_left] at hab
    rw [hinj hab]
  · simp only [Fin.addCases_left, Fin.addCases_right] at hab
    exact absurd hab (hL a')
  · simp only [Fin.addCases_left, Fin.addCases_right] at hab
    exact absurd hab.symm (hL b')
  · rw [Fin.eq_zero a', Fin.eq_zero b']

theorem WXExec.machZ {t' s n lcap : ℕ} {M : Machine t' s} {tmap : Fin t' → Fin (ns + 1)} {L : Fin (ns + 1)}
    (hinj : Function.Injective tmap) (hL : ∀ j, tmap j ≠ L) {σ τ : WState ns nr} {hout : Fin t' → ℕ}
    {tout : Fin t' → List Bool} (h : Step M n (fun _ => 0) (fun j => σ.st (tmap j)) hout tout)
    (h0 : ∀ j, σ.sh (tmap j) = 0) (hLst : σ.st L = List.replicate lcap false) (hLsh : σ.sh L = 0) (hn : n ≤ lcap)
    (hst : ∀ j, τ.st (tmap j) = tout j) (hsh : ∀ j, τ.sh (tmap j) = 0)
    (hout' : ∀ i, (∀ j, tmap j ≠ i) → τ.st i = σ.st i ∧ τ.sh i = σ.sh i)
    (hval : τ.val = σ.val) (hcell : τ.cell = σ.cell) : WXExec cap (WMX.machZ M tmap L) σ τ (2 * n + 2) := by
  have hm := h.mask (cap := lcap) (fun _ => true) (fun _ _ => rfl) hn
  have hinj' := addCases_inj tmap hinj L hL
  refine WXExec.mach_of cap hinj' (hout := Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0))
    (tout := Fin.addCases tout (fun _ : Fin 1 => List.replicate lcap false)) ?_ ?_ ?_ ?_ hval hcell
  · refine Step.congr_in hm ?_ ?_
    · funext x
      refine Fin.addCases (fun j => ?_) (fun j => ?_) x
      · simp only [Fin.addCases_left, h0]
      · simp only [Fin.addCases_right, hLsh]
    · funext x
      refine Fin.addCases (fun j => ?_) (fun j => ?_) x
      · simp only [Fin.addCases_left]
      · simp only [Fin.addCases_right, hLst]
  · intro x
    refine Fin.addCases (fun j => ?_) (fun j => ?_) x
    · simp only [Fin.addCases_left, hst]
    · simp only [Fin.addCases_right]
      rw [(hout' L (fun j' => hL j')).1, hLst]
  · intro x
    refine Fin.addCases (fun j => ?_) (fun j => ?_) x
    · simp only [Fin.addCases_left, hsh]
    · simp only [Fin.addCases_right]
      rw [(hout' L (fun j' => hL j')).2, hLsh]
  · intro i hi
    exact hout' i (fun j hj => hi (Fin.castAdd 1 j) (by simp only [Fin.addCases_left]; exact hj))

structure Docked {t' : ℕ} (tmap : Fin t' → Fin (ns + 1)) (σ τ : WState ns nr) (hout : Fin t' → ℕ)
    (tout : Fin t' → List Bool) : Prop where
  st : ∀ j, τ.st (tmap j) = tout j
  sh : ∀ j, τ.sh (tmap j) = hout j
  other : ∀ i, (∀ j, tmap j ≠ i) → τ.st i = σ.st i ∧ τ.sh i = σ.sh i
  val : τ.val = σ.val
  cell : τ.cell = σ.cell

theorem docked_updS {t' : ℕ} (tmap : Fin t' → Fin (ns + 1)) (hinj : Function.Injective tmap) (σ : WState ns nr)
    (hout : Fin t' → ℕ) (tout : Fin t' → List Bool) : Docked tmap σ (updS tmap σ hout tout) hout tout :=
  ⟨updS_st_slot tmap σ hout tout hinj, updS_sh_slot tmap σ hout tout hinj,
    fun i hi => ⟨updS_st_other tmap σ hout tout i hi, updS_sh_other tmap σ hout tout i hi⟩, rfl, rfl⟩

/-- **The `mach` rule, existential form** (for donors whose run theorem pins only some output tapes). -/
theorem WXExec.mach_ex {t' s n : ℕ} {M : Machine t' s} {tmap : Fin t' → Fin (ns + 1)} (hinj : Function.Injective tmap)
    (σ : WState ns nr) {hout : Fin t' → ℕ} {tout : Fin t' → List Bool}
    (h : Step M n (fun j => σ.sh (tmap j)) (fun j => σ.st (tmap j)) hout tout) :
    ∃ τ, WXExec cap (.mach M tmap) σ τ n ∧ Docked tmap σ τ hout tout :=
  ⟨_, WXExec.mach σ hinj h, docked_updS tmap hinj σ hout tout⟩

theorem WXExec.mach_run {t' s n : ℕ} {M : Machine t' s} {tmap : Fin t' → Fin (ns + 1)}
    (hinj : Function.Injective tmap) (σ : WState ns nr) (h0 : ∀ j, σ.sh (tmap j) = 0) {r : ExecutionReceipt t' s}
    (hr : LocalBitMultitape.run M n (fun j => σ.st (tmap j)) = some r) :
    ∃ τ, WXExec cap (.mach M tmap) σ τ n ∧ Docked tmap σ τ r.final.heads r.final.tapes := by
  refine WXExec.mach_ex cap hinj σ (Step.of_run (r := r) ?_ rfl rfl)
  have e : (fun j => σ.sh (tmap j)) = fun _ => 0 := funext h0
  rw [e]
  exact hr

theorem WXExec.machZ_ex {t' s n lcap : ℕ} {M : Machine t' s} {tmap : Fin t' → Fin (ns + 1)} {L : Fin (ns + 1)}
    (hinj : Function.Injective tmap) (hL : ∀ j, tmap j ≠ L) (σ : WState ns nr) {hout : Fin t' → ℕ}
    {tout : Fin t' → List Bool} (h : Step M n (fun _ => 0) (fun j => σ.st (tmap j)) hout tout)
    (h0 : ∀ j, σ.sh (tmap j) = 0) (hLst : σ.st L = List.replicate lcap false) (hLsh : σ.sh L = 0) (hn : n ≤ lcap) :
    ∃ τ, WXExec cap (WMX.machZ M tmap L) σ τ (2 * n + 2) ∧ Docked tmap σ τ (fun _ => 0) tout := by
  have hd := docked_updS tmap hinj σ (fun _ => 0) tout
  exact ⟨_, WXExec.machZ cap hinj hL h h0 hLst hLsh hn hd.st hd.sh hd.other hd.val hd.cell, hd⟩

theorem WXExec.machZ_run {t' s n lcap : ℕ} {M : Machine t' s} {tmap : Fin t' → Fin (ns + 1)} {L : Fin (ns + 1)}
    (hinj : Function.Injective tmap) (hL : ∀ j, tmap j ≠ L) (σ : WState ns nr) {r : ExecutionReceipt t' s}
    (hr : LocalBitMultitape.run M n (fun j => σ.st (tmap j)) = some r)
    (h0 : ∀ j, σ.sh (tmap j) = 0) (hLst : σ.st L = List.replicate lcap false) (hLsh : σ.sh L = 0) (hn : n ≤ lcap) :
    ∃ τ, WXExec cap (WMX.machZ M tmap L) σ τ (2 * n + 2) ∧ Docked tmap σ τ (fun _ => 0) r.final.tapes :=
  WXExec.machZ_ex cap hinj hL σ (Step.of_run (r := r) hr rfl rfl) h0 hLst hLsh hn

/-! ### Single instructions as `WMX` atoms -/

def WMX.skip : WMX ns nr := .wm .skip
def WMX.inc (r : Fin nr) : WMX ns nr := .wm (.inc r)
def WMX.dec (r : Fin nr) : WMX ns nr := .wm (.dec r)
def WMX.fwd (i : Fin (ns + 1)) : WMX ns nr := .wm (.fwd i)
def WMX.bwd (i : Fin (ns + 1)) : WMX ns nr := .wm (.bwd i)
def WMX.wr (i : Fin (ns + 1)) (b : Bool) : WMX ns nr := .wm (.wr i b)
def WMX.setc (v : Bool) : WMX ns nr := .wm (.setc v)

theorem WXExec.skip (σ : WState ns nr) : WXExec cap WMX.skip σ σ 0 := WXExec.wm (WExec.skip σ)

theorem WXExec.inc (r : Fin nr) (σ : WState ns nr) (h : σ.val r < cap) :
    WXExec cap (WMX.inc r) σ (σ.setv r (σ.val r + 1)) 3 := WXExec.wm (WExec.inc r σ h)

theorem WXExec.dec (r : Fin nr) (σ : WState ns nr) (h : σ.val r ≤ cap) :
    WXExec cap (WMX.dec r) σ (σ.setv r (σ.val r - 1)) 1 := WXExec.wm (WExec.dec r σ h)

theorem WXExec.fwd (i : Fin (ns + 1)) (σ : WState ns nr) : WXExec cap (WMX.fwd i) σ (σ.seth i (σ.sh i + 1)) 1 :=
  WXExec.wm (WExec.fwd i σ)

theorem WXExec.bwd (i : Fin (ns + 1)) (σ : WState ns nr) : WXExec cap (WMX.bwd i) σ (σ.seth i (σ.sh i - 1)) 1 :=
  WXExec.wm (WExec.bwd i σ)

theorem WXExec.wr (i : Fin (ns + 1)) (b : Bool) (σ : WState ns nr) :
    WXExec cap (WMX.wr i b) σ (σ.sets i (writeTapeBit (σ.st i) (σ.sh i) b)) 1 := WXExec.wm (WExec.wr i b σ)

theorem WXExec.setc (v : Bool) (σ : WState ns nr) : WXExec cap (WMX.setc v) σ (σ.setc v) 1 :=
  WXExec.wm (WExec.setc v σ)

end NearCubicGates.Close.WordPrograms
