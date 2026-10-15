import Proof.MachineModel.OrdinaryMatrixMaskAndReturn

/-! The literal row-wise AND consumes a retained padded mask and one row
of the unweighted left matrix. It returns the mask and width sentinel for
the next row while both global source/output cursors continue streaming. -/
namespace NearCubicWires.RepairOrdinary.MatrixMaskAndRow
open LocalBitMultitape RecoveryExecution
open MatrixMaskAndReturn (cfg)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def values (pairs : List (Bool×Bool)) := pairs.map (fun x => x.1 && x.2)
def copy : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ scan => if scan 0 then
    some ⟨0,![none,none,none,some (scan 1 && scan 2)],fun _ => .right⟩
    else some ⟨1,fun _ => none,fun _ => .stay⟩
def machine := Composition.machine copy MatrixMaskAndReturn.machine

theorem emit_step (a b : Bool) (mpre mtail pre tail out : List Bool) (count : ℕ) (hc : mpre.length<count) :
    step copy (cfg 0 count (mpre.length+1) mpre.length (mpre++a::mtail) (pre++b::tail) pre.length out)=
      some (cfg 0 count (mpre.length+2) (mpre.length+1) (mpre++a::mtail) (pre++b::tail) (pre.length+1) (out++[a && b])) := by
  simp [step,copy,cfg,Configuration.scanned,UnaryTemplate.tape_mark count mpre.length hc,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem stop_step (count : ℕ) (mask source out : List Bool) (pos : ℕ) :
    step copy (cfg 0 count (count+1) count mask source pos out)=
      some (cfg 1 count (count+1) count mask source pos out) := by
  simp [step,copy,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem copy_prefix (pairs : List (Bool×Bool)) (mpre pre suffix out : List Bool) (count : ℕ)
    (hc : mpre.length+pairs.length=count) :
    Timed copy (pairs.length+1)
      (cfg 0 count (mpre.length+1) mpre.length (mpre++pairs.map Prod.fst)
        (pre++pairs.map Prod.snd++suffix) pre.length out)
      (cfg 1 count (count+1) count (mpre++pairs.map Prod.fst)
        (pre++pairs.map Prod.snd++suffix) (pre.length+pairs.length) (out++values pairs)) := by
  induction pairs generalizing mpre pre out with
  | nil =>
    have hm : mpre.length=count := by simpa using hc
    simpa [hm,values] using Timed.single (by rfl) (stop_step count mpre (pre++suffix) out pre.length)
  | cons pair pairs ih =>
    have hs := Timed.single (by rfl) (emit_step pair.1 pair.2 mpre (pairs.map Prod.fst)
      pre (pairs.map Prod.snd++suffix) out count (by simp only [List.length_cons] at hc; omega))
    have ht := ih (mpre++[pair.1]) (pre++[pair.2]) (out++[pair.1 && pair.2])
      (by simp only [List.length_append,List.length_cons,List.length_nil] at hc ⊢; omega)
    have ht' : Timed copy (pairs.length+1)
        (cfg 0 count (mpre.length+2) (mpre.length+1) (mpre++pair.1::pairs.map Prod.fst)
          (pre++pair.2::(pairs.map Prod.snd++suffix)) (pre.length+1) (out++[pair.1 && pair.2]))
        (cfg 1 count (count+1) count (mpre++pair.1::pairs.map Prod.fst)
          (pre++pair.2::(pairs.map Prod.snd++suffix)) ((pre++[pair.2]).length+pairs.length)
          ((out++[pair.1 && pair.2])++values pairs)) := by
      simpa [List.append_assoc,Nat.add_assoc] using ht
    have hh := hs.trans ht'
    simpa [values,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem pairs_run (pairs : List (Bool×Bool)) (pre suffix out : List Bool) : ∃ actual,
    runFrom machine (2*pairs.length+4)
      (cfg machine.start pairs.length 1 0 (pairs.map Prod.fst) (pre++pairs.map Prod.snd++suffix) pre.length out)=some actual ∧
    actual.final=cfg 4 pairs.length 1 0 (pairs.map Prod.fst) (pre++pairs.map Prod.snd++suffix)
      (pre.length+pairs.length) (out++values pairs) ∧ actual.steps=2*pairs.length+4 := by
  obtain ⟨first,hfirst,ff,fs⟩ := (copy_prefix pairs [] pre suffix out pairs.length (by simp)).run (by rfl)
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hfirst ff
  obtain ⟨last,hl,lf,ls⟩ := MatrixMaskAndReturn.reset_run pairs.length (pairs.map Prod.fst)
    (pre++pairs.map Prod.snd++suffix) (out++values pairs) (pre.length+pairs.length)
  have hi : Composition.restart first.final MatrixMaskAndReturn.machine.start=
      cfg 0 pairs.length (pairs.length+1) pairs.length (pairs.map Prod.fst) (pre++pairs.map Prod.snd++suffix)
        (pre.length+pairs.length) (out++values pairs) := by rw [ff]; rfl
  rw [←hi] at hl
  have hj := Composition.run_join copy MatrixMaskAndReturn.machine _ _ _ first last hfirst hl
  have hc : pairs.length+1+1+(pairs.length+2)=2*pairs.length+4 := by omega
  rw [hc] at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_⟩
  · change Composition.rightConfig 2 last.final=_
    rw [lf]
    rfl
  · change first.steps+1+last.steps=_
    omega

theorem row_run (mask bits pre suffix out : List Bool) (hlen : mask.length=bits.length) : ∃ actual,
    runFrom machine (2*bits.length+4)
      (cfg machine.start bits.length 1 0 mask (pre++bits++suffix) pre.length out)=some actual ∧
    actual.final=cfg 4 bits.length 1 0 mask (pre++bits++suffix) (pre.length+bits.length)
      (out++values (mask.zip bits)) ∧ actual.steps=2*bits.length+4 := by
  obtain ⟨actual,ha,hf,hs⟩ := pairs_run (mask.zip bits) pre suffix out
  have hm := List.map_fst_zip (l₁ := mask) (l₂ := bits) hlen.le
  have hb := List.map_snd_zip (l₁ := mask) (l₂ := bits) hlen.ge
  have hl : (mask.zip bits).length=bits.length := by simp [hlen]
  rw [hm,hb,hl] at ha hf
  rw [hl] at hs
  exact ⟨actual,ha,hf,hs⟩

end NearCubicWires.RepairOrdinary.MatrixMaskAndRow
