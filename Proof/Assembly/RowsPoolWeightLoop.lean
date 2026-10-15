import Proof.Assembly.RowsPoolWeightBody

/-! The original arity driver traverses every native weight and every
physical live-mask coordinate once. The output has the same arity; live
weights are replaced by zero, never deleted. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolWeight
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairRepresentation
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Item:=ℤ×Bool
def word (xs : List Item):=xs.flatMap (fun x=>intWord x.1)
def mask (xs : List Item):=xs.map Prod.snd
def emitted (xs : List Item):=xs.flatMap (fun x=>intWord (transformed x.2 x.1))
def saved (xs : List Item) (backing : List Bool):=
  xs.foldl (fun bs x=>DecompositionSource.Fields.saved x.1 bs) backing
noncomputable def loop:=RepeatMachine.machine body (fun _ _=>true)
noncomputable def cfg (phase : Fin 5) (source : List Bool) (pos : ℕ)
    (backing out membership : List Bool) (mpos total driver : ℕ):=
  RepeatMachine.cfg phase (⟨body.start,heads pos mpos out,data source backing out membership⟩) total driver

theorem remaining (xs : List Item) (pre tail backing out mpre mtail : List Bool)
    (total pos : ℕ) (hn : pos+xs.length=total) :
    ∃ time≤(word xs).length+14*xs.length+total+3,Timed loop time
      (cfg 0 (pre++word xs++tail) pre.length backing out (mpre++mask xs++mtail) mpre.length total (pos+1))
      (cfg 3 (pre++word xs++tail) (pre.length+(word xs).length) (saved xs backing)
        (out++emitted xs) (mpre++mask xs++mtail) (mpre.length+xs.length) total 1):=by
  induction xs generalizing pre backing out mpre pos with
  | nil=>
    have he:pos=total:=by simpa using hn
    subst pos
    refine ⟨total+3,by simp [word],?_⟩
    simpa [cfg,loop,word,mask,emitted,saved] using RepeatMachine.exhaust body (fun _ _=>true)
      (⟨body.start,heads pre.length mpre.length out,data (pre++tail) backing out (mpre++mtail)⟩) total
  | cons x xs ih=>
    obtain ⟨r,hr,rh,rt,rs⟩:=body_run pre (word xs++tail) backing out mpre (mask xs++mtail) x.1 x.2
    have one:=RepeatMachine.iteration body (fun _ _=>true)
      ⟨body.start,heads pre.length mpre.length out,
        data (pre++intWord x.1++(word xs++tail)) backing out (mpre++x.2::(mask xs++mtail))⟩
      total pos r rfl (by simp only [List.length_cons] at hn;omega) hr
    simp only [↓reduceIte] at one
    rw [RowOccurrenceLoop.cfg_eq 0 r.final
      (⟨body.start,heads (pre.length+(intWord x.1).length) (mpre.length+1)
        (out++intWord (transformed x.2 x.1)),
        data (pre++intWord x.1++(word xs++tail)) (DecompositionSource.Fields.saved x.1 backing)
          (out++intWord (transformed x.2 x.1)) (mpre++x.2::(mask xs++mtail))⟩)
      total (pos+2) rh rt] at one
    obtain ⟨t,ht,rest⟩:=ih (pre++intWord x.1) (DecompositionSource.Fields.saved x.1 backing)
      (out++intWord (transformed x.2 x.1)) (mpre++[x.2]) (pos+1)
      (by simp only [List.length_cons] at hn;omega)
    have hp:(pre++intWord x.1).length=pre.length+(intWord x.1).length:=List.length_append
    have hm:(mpre++[x.2]).length=mpre.length+1:=by simp
    simp only [cfg,List.append_assoc,List.singleton_append,hp,hm,show pos+1+1=pos+2 by omega] at rest
    simp only [List.append_assoc,List.cons_append] at one rest
    have all:=one.trans rest
    refine ⟨r.steps+2+t,?_,?_⟩
    · rw [body_budget] at rs
      simp only [word,List.flatMap_cons,List.length_append,List.length_cons] at ht ⊢
      omega
    · simpa only [loop,cfg,word,mask,emitted,saved,List.flatMap_cons,List.map_cons,List.foldl_cons,
        List.length_append,List.length_cons,List.append_assoc,List.cons_append,Nat.add_assoc,
        Nat.add_comm 1 xs.length] using all

def loopBudget (xs : List Item):=(word xs).length+15*xs.length+3

theorem weights_run (xs : List Item) (pre tail backing out mpre mtail : List Bool) :
    ∃ r,runFrom loop (loopBudget xs)
      (cfg 0 (pre++word xs++tail) pre.length backing out (mpre++mask xs++mtail) mpre.length xs.length 1)=some r ∧
      r.final=cfg 3 (pre++word xs++tail) (pre.length+(word xs).length) (saved xs backing)
        (out++emitted xs) (mpre++mask xs++mtail) (mpre.length+xs.length) xs.length 1 ∧
      r.steps≤loopBudget xs:=by
  obtain ⟨t,ht,h⟩:=remaining xs pre tail backing out mpre mtail xs.length 0 (by omega)
  obtain ⟨r,hr,hf,hs⟩:=h.run (by simp [loop,cfg,RepeatMachine.machine,RepeatMachine.cfg,
    controlConfig,RepeatMachine.phaseCode])
  have hb:t≤loopBudget xs:=by unfold loopBudget;omega
  have more:=runFrom_moreFuel loop t (loopBudget xs-t) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,hf,hs.le.trans hb⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsPoolWeight
