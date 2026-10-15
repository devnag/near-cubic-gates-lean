import Proof.Amplification.RecoveryCompactMaterialize

/-! The real materializer retains all336 source/marker tapes below its reset
log. This lets the enclosing all-code call consume both original raw banks
and the already prepared marker with the same valuation word. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCompact
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def below (a : Fin 493→List Bool) (i : Fin 336) := a (i.castAdd 157)
theorem put_below (a : Fin 493→List Bool) (dst : Fin 493) (word : List Bool) (reset : Nat)
    (hd : 336 ≤ dst.val) : below (put a dst word reset)=below a := by
  funext i
  have hdst : i.castAdd 157≠dst := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd] at hv
    omega
  have hreset : i.castAdd 157≠(336 : Fin 493) := by
    intro he
    have hv := congrArg Fin.val he
    change i.val=336 at hv
    omega
  simp only [below,put,Function.update_of_ne hreset,Function.update_of_ne hdst]

theorem stage_below (bits word innerBits outerBits : List Bool) (n m : Nat) (a : Fin 493→List Bool) :
    below (stage34 bits word innerBits outerBits n m a)=below a := by
  unfold stage34 stage33 stage32 stage31 stage30 stage29 stage28 stage27 stage26 stage25 stage24 stage23 stage22 stage21 stage20 stage19 stage18 stage17 stage16 stage15 stage14 stage13 stage12 stage11 stage10 stage9 stage8 stage7 stage6 stage5 stage4 stage3 stage2 stage1 stage0
  rw [put_below _ 428 _ _ (by decide),
    put_below _ 359 _ _ (by decide),
    put_below _ 491 _ _ (by decide),
    put_below _ 489 _ _ (by decide),
    put_below _ 406 _ _ (by decide),
    put_below _ 443 _ _ (by decide),
    put_below _ 374 _ _ (by decide),
    put_below _ 437 _ _ (by decide),
    put_below _ 368 _ _ (by decide),
    put_below _ 480 _ _ (by decide),
    put_below _ 464 _ _ (by decide),
    put_below _ 456 _ _ (by decide),
    put_below _ 395 _ _ (by decide),
    put_below _ 387 _ _ (by decide),
    put_below _ 459 _ _ (by decide),
    put_below _ 455 _ _ (by decide),
    put_below _ 475 _ _ (by decide),
    put_below _ 390 _ _ (by decide),
    put_below _ 386 _ _ (by decide),
    put_below _ 435 _ _ (by decide),
    put_below _ 366 _ _ (by decide),
    put_below _ 492 _ _ (by decide),
    put_below _ 483 _ _ (by decide),
    put_below _ 482 _ _ (by decide),
    put_below _ 467 _ _ (by decide),
    put_below _ 466 _ _ (by decide),
    put_below _ 445 _ _ (by decide),
    put_below _ 444 _ _ (by decide),
    put_below _ 407 _ _ (by decide),
    put_below _ 398 _ _ (by decide),
    put_below _ 397 _ _ (by decide),
    put_below _ 376 _ _ (by decide),
    put_below _ 375 _ _ (by decide),
    put_below _ 338 _ _ (by decide)]

theorem finish_below (a : Fin 493→List Bool) : below (finishTapes a)=below a := by
  funext i
  have hn : i.castAdd 157≠(404 : Fin 493) ∧ i.castAdd 157≠(473 : Fin 493) := by
    simp only [ne_eq,Fin.ext_iff,Fin.val_castAdd]
    change i.val≠404 ∧ i.val≠473
    omega
  simp only [below,finishTapes,Function.update_of_ne hn.2,Function.update_of_ne hn.1]

theorem retained (bits word innerBits outerBits : List Bool) (n m : Nat)
    (a : Fin 338→List Bool) (i : Fin 336) :
    finishTapes (stage34 bits word innerBits outerBits n m (bankInput a)) (i.castAdd 157)=a (i.castAdd 2) := by
  have h := (finish_below (stage34 bits word innerBits outerBits n m (bankInput a))).trans
    (stage_below bits word innerBits outerBits n m (bankInput a))
  have hi := congrFun h i
  have he : i.castAdd 157=(i.castAdd 2).castAdd 155 := Fin.ext rfl
  simpa only [below,he,bankInput,Fin.addCases_left] using hi

end NearCubicWires.RepairOrdinary.RecoveryColdCompact
