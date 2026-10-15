import Proof.PCP.ProjectionDimensionPower

/-! A raw unary driver is copied to a sentinel-terminated reusable template.
The optional successor and both false sentinels are physically written. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.DimensionTemplate
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw (extra : Bool) : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bits => if q.val=0 then some ⟨1,![none,some false],![.stay,.right]⟩
    else if q.val=1 then some (if bits 0 then ⟨1,![none,some true],![.right,.right]⟩
      else ⟨2,![none,if extra then some true else none],![.stay,if extra then .right else .stay]⟩)
    else if q.val=2 then some ⟨3,![none,some false],![.stay,.stay]⟩ else none

def cfg (q : Fin 4) (n pos : ℕ) (out : List Bool) : Configuration 2 4 :=
  ⟨q,![pos,out.length],![List.replicate n true,out]⟩

theorem copy_step (extra : Bool) (n pos : ℕ) (out : List Bool) (hp : pos<n) :
    step (raw extra) (cfg 1 n pos out)=some (cfg 1 n (pos+1) (out++[true])) := by
  simp [step,raw,cfg,Configuration.scanned,ClockUnaryProduct.read_unary,hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem end_step (extra : Bool) (n : ℕ) (out : List Bool) :
    step (raw extra) (cfg 1 n n out)=some (cfg 2 n n (out++List.replicate extra.toNat true)) := by
  cases extra <;> simp [step,raw,cfg,Configuration.scanned,ClockUnaryProduct.read_unary]
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,Streaming.write_append])

theorem loop (extra : Bool) (n pos k : ℕ) (out : List Bool) (hk : pos+k=n) :
    Timed (raw extra) (k+1) (cfg 1 n pos out)
      (cfg 2 n n (out++List.replicate (k+extra.toNat) true)) := by
  induction k generalizing pos out with
  | zero =>
    have hp : pos=n := by omega
    subst pos
    simpa using Timed.single (by rfl : (raw extra).halted (1 : Fin 4)=false) (end_step extra n out)
  | succ k ih =>
    have ht := ih (pos+1) (out++[true]) (by omega)
    have ho : (out++[true])++List.replicate (k+extra.toNat) true=
        out++List.replicate (k+1+extra.toNat) true := by
      have he : k+1+extra.toNat=(k+extra.toNat)+1 := by omega
      simp [he,List.replicate_succ,List.append_assoc]
    rw [ho] at ht
    simpa [Nat.add_assoc] using Timed.step (by rfl)
      (copy_step extra n pos out (by omega)) ht

def final (extra : Bool) (n : ℕ) : Configuration 2 4 :=
  ⟨3,![n,n+extra.toNat+1],![List.replicate n true,UnaryTemplate.tape (n+extra.toNat)]⟩

theorem raw_run (extra : Bool) (n : ℕ) :
    ∃ r,run (raw extra) (n+3) ![List.replicate n true,[]]=some r ∧
      r.final=final extra n ∧ r.steps=n+3 := by
  have hb : step (raw extra) (cfg 0 n 0 [])=some (cfg 1 n 0 [false]) := by
    simp [step,raw,cfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have ht := loop extra n 0 n [false] (by omega)
  have hf : step (raw extra) (cfg 2 n n ([false]++List.replicate (n+extra.toNat) true))=
      some (final extra n) := by
    simp [step,raw,cfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,final]
    · funext i; fin_cases i
      · rfl
      · simpa [applyAction,final,UnaryTemplate.tape] using
          Streaming.write_append (false::List.replicate (n+extra.toNat) true) false
  have h := (Timed.single (by rfl : (raw extra).halted (0 : Fin 4)=false) hb).trans
    (ht.trans (Timed.single (by rfl : (raw extra).halted (2 : Fin 4)=false) hf))
  obtain ⟨r,hr,hfinal,hsteps⟩ := h.run (by rfl)
  have hi : cfg 0 n 0 []=initialConfiguration (raw extra) ![List.replicate n true,[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  have htime : 1+(n+1+1)=n+3 := by omega
  rw [hi,htime] at hr
  rw [htime] at hsteps
  exact ⟨r,hr,hfinal,hsteps⟩

def machine (extra : Bool) := Rewind.machine (raw extra)
def input (n : ℕ) : Fin 3 → List Bool := ![List.replicate n true,[],[]]
def output (extra : Bool) (n : ℕ) : Fin 3 → List Bool :=
  ![List.replicate n true,UnaryTemplate.tape (n+extra.toNat),List.replicate (n+3) false]

theorem ready (extra : Bool) (n : ℕ) :
    ClockJoin.ReadyRun (machine extra) (2*n+8) (input n) (output extra n) := by
  obtain ⟨base,hb,hf,hs⟩ := raw_run extra n
  obtain ⟨r,hr,ht,hcount,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace (raw extra) _ _ base hb 0
  have hi : (Fin.addCases (motive := fun _ : Fin (2+1) => List Bool)
      ![List.replicate n true,[]] (fun _ : Fin 1 => []))=input n := by
    funext i; fin_cases i <;> rfl
  change run (machine extra) (2*base.steps+2)
    (Fin.addCases (motive := fun _ : Fin (2+1) => List Bool)
      ![List.replicate n true,[]] (fun _ : Fin 1 => []))=some r at hr
  rw [hi] at hr
  have he : 2*base.steps+2=2*n+8 := by omega
  rw [he] at hr
  refine ⟨r,hr,?_,hh,by omega⟩
  funext i
  fin_cases i
  · simpa [output,hf,final] using ht 0
  · simpa [output,hf,final] using ht 1
  · simpa [output,hs] using hcount

end NearCubicWires.RepairSource.ProjectionNormalization.DimensionTemplate
