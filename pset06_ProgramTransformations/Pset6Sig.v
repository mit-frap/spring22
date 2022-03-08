Require Export Frap.Frap.
From Coq Require Export NArith.
From Coq Require Export Program.Equality.

Arguments N.add : simpl nomatch.
Arguments N.sub : simpl nomatch.
Arguments N.mul : simpl nomatch.
Arguments N.div : simpl nomatch.
Arguments N.shiftl : simpl nomatch.
Arguments N.shiftr : simpl nomatch.

(*|
Totals below don't sum up to 100%!  This is because this pset is a
chose-your-own-adventure assignment, so you can pick what to do.  Here is the
complete rubric, which choice points indicated by `==`::

    1    Axiom opt_binop_fold_test1
    8    Axiom opt_binop_fold_sound
    7    Axiom eval_deterministic
         = Arith (23 points)
           == Precompute
   16         Axiom opt_binop_precompute_sound
    2         Axiom opt_arith_precompute_test1
    2         Axiom opt_arith_precompute_test2
           == Log
   16         Axiom opt_binop_log2_sound
    2         Axiom opt_arith_log2_test1
    2         Axiom opt_arith_log2_test2
           == Bitwise
   16         Axiom opt_binop_bitwise_sound
    2         Axiom opt_arith_bitwise_test1
    2         Axiom opt_arith_bitwise_test2
    4    Axiom opt_arith_fold_test1
   10    Axiom opt_arith_sound
    2    Axiom opt_unskip_test1
    2    Axiom opt_unskip_test2
   16    Axiom opt_unskip_sound
         = Eval (32 points)
           == ConstProp
    8         Axiom opt_arith_constprop_sound
    2         Axiom opt_constprop_test1
    2         Axiom opt_constprop_test2
   18         Axiom opt_constprop_sound
           == Unroll
    6         Parameter eval_read_only
    2         Axiom opt_unroll_test1
    2         Axiom opt_unroll_test2
   20         Axiom opt_unroll_sound
         -- Total 100
|*)

Module Type S.
  Inductive BinopName : Set :=
    LogAnd : BinopName
  | Eq : BinopName
  | ShiftLeft : BinopName
  | ShiftRight : BinopName
  | Times : BinopName
  | Divide : BinopName
  | Plus : BinopName
  | Minus : BinopName
  | Modulo : BinopName.

  Inductive expr : Set :=
    Const : nat -> expr
  | Var : var -> expr
  | Binop : BinopName -> expr -> expr -> expr.

  Inductive cmd : Set :=
    Skip : cmd
  | Assign : var -> expr -> cmd
  | AssignCall : var -> var -> expr -> expr -> cmd
  | Sequence : cmd -> cmd -> cmd
  | If : expr -> cmd -> cmd -> cmd
  | While : expr -> cmd -> cmd.

  Declare Scope expr.
  Delimit Scope expr with expr.

  Coercion Const : nat >-> expr.
  Coercion Var : var >-> expr.

  Infix "&" := (Binop LogAnd) (at level 80) : expr.
  Infix "==" := (Binop Eq) (at level 70) : expr.
  Infix ">>" := (Binop ShiftRight) (at level 60) : expr.
  Infix "<<" := (Binop ShiftLeft) (at level 60) : expr.
  Infix "+" := (Binop Plus) (at level 50, left associativity) : expr.
  Infix "-" := (Binop Minus) (at level 50, left associativity) : expr.
  Infix "*" := (Binop Times) (at level 40, left associativity) : expr.
  Infix "/" := (Binop Divide) (at level 40, left associativity) : expr.
  Infix "mod" := (Binop Modulo) (at level 40) : expr.

  Notation "x <- e" :=
    (Assign x e%expr)
      (at level 75).
  Notation "x <- 'call1' f e1" :=
    (AssignCall x f e1%expr (Const 0))
      (at level 75, f at level 0, e1 at level 0).
  Notation "x <- 'call2' f e1 e2" :=
    (AssignCall x f e1%expr e2%expr)
      (at level 75, f at level 0, e1 at level 0, e2 at level 0).
  Infix ";;" :=
    Sequence (at level 76).
  Notation "'when' e 'then' then_ 'else' else_ 'done'" :=
    (If e%expr then_ else_)
      (at level 75, e at level 0).
  Notation "'while' e 'loop' body 'done'" :=
    (While e%expr body)
      (at level 75).

  Example Times3Plus1Body :=
    ("n" <- "n" * 3 + 1).

  Example FactBody :=
    ("f" <- 1;;
     while "n" loop
       "f" <- "f" * "n";;
       "n" <- "n" - 1
     done).

  Example FactRecBody :=
    (when "n" == 1 then
       "f" <- 1
     else
       "f" <- call1 "fact_r" ("n" - 1);;
       "f" <- "f" * "n"
     done).

  Example FactTailRecBody :=
    (when "n" == 1 then
       "f" <- "acc"
     else
       "f" <- call2 "fact_tr" ("n" - 1) ("acc" * "n")
     done).

  Example CollatzBody :=
    (when ("start" == 1) then
       Skip
     else when ("start" mod 2 == 0) then
            "start" <- "start" / 2
          else
            (* `call1 f arg` is short for `call2 f arg 0` *)
            "start" <- call1 "times3plus1" ("start" + 0)
          done;;
          "flight" <- call2 "collatz" "start" ("flight" + 1)
     done).

  Notation TimesThreePlus1_signature := (("n", ""), "n", Times3Plus1Body).
  Notation Fact_signature := (("n", ""), "f", FactBody).
  Notation FactRec_signature := (("n", ""), "f", FactRecBody).
  Notation FactTailRec_signature := (("n", "acc"), "f", FactTailRecBody).
  Notation Collatz_signature := (("start", "flight"), "flight", CollatzBody).

  Notation Collatz_env :=
  ($0
    $+ ("collatz", Collatz_signature)
    $+ ("times3plus1", TimesThreePlus1_signature)).

  Notation Fact_env :=
    ($0
      $+ ("fact", Fact_signature)
      $+ ("fact_r", FactRec_signature)
      $+ ("fact_tr", FactTailRec_signature)).

  Parameter interp_binop : BinopName -> nat -> nat -> nat.

  Definition valuation := fmap var nat.
  Parameter interp_arith : expr -> valuation -> nat.

  Definition environment := fmap string ((var * var) * var * cmd).

  Inductive eval (phi: environment): valuation -> cmd -> valuation -> Prop :=
  | EvalSkip: forall v,
      eval phi v Skip v
  | EvalAssign: forall v x e a,
      interp_arith e v = a ->
      eval phi v (Assign x e) (v $+ (x, a))
  | EvalAssignCall: forall x f e1 e2 x1 x2 y body a1 a2 a v v',
      phi $? f = Some ((x1, x2), y, body) ->
      interp_arith e1 v = a1 ->
      interp_arith e2 v = a2 ->
      eval phi ($0 $+ (x1, a1) $+ (x2, a2)) body v' ->
      v' $? y = Some a ->
      eval phi v (AssignCall x f e1 e2) (v $+ (x, a))
  | EvalSequence: forall v c1 v1 c2 v2,
      eval phi v c1 v1 ->
      eval phi v1 c2 v2 ->
      eval phi v (Sequence c1 c2) v2
  | EvalIfTrue: forall v e thn els v' c,
      interp_arith e v = c ->
      c <> 0 ->
      eval phi v thn v' ->
      eval phi v (If e thn els) v'
  | EvalIfFalse: forall v e thn els v',
      interp_arith e v = 0 ->
      eval phi v els v' ->
      eval phi v (If e thn els) v'
  | EvalWhileTrue: forall v e body v' v'' c,
      interp_arith e v = c ->
      c <> 0 ->
      eval phi v body v' ->
      eval phi v' (While e body) v'' ->
      eval phi v (While e body) v''
  | EvalWhileFalse: forall v e body,
      interp_arith e v = 0 ->
      eval phi v (While e body) v.

  (*[6%]*)
  Axiom eval_deterministic : forall phi c v0 v1 v2,
      eval phi v0 c v1 ->
      eval phi v0 c v2 ->
      v1 = v2.  
  
  Definition eval_returns phi v cmd outVar result :=
    exists v', eval phi v cmd v' /\ v' $? outVar = Some result.

  Axiom TwoPlusTwoIsFour :
    eval_returns $0 $0 ("out" <- 2 + 2) "out" 4.
  Axiom EvalVars :
    eval_returns $0 $0 ("x" <- 1 + 1;; "x" <- "x" + "x" + "y") "x" 4.
  Axiom EvalSimpleArith :
    eval_returns $0 $0 ("out" <- (((14 >> 1) + 8 / 4 / 2) * (7 - 2) << 1) + 2 == 82) "out" 1.
  Axiom EvalTimes3Plus1 : forall n : nat,
      eval_returns $0 ($0 $+ ("n", n)) Times3Plus1Body "n" (3 * n + 1).
  Axiom EvalFact6 : exists v : valuation,
      eval $0 ($0 $+ ("n", 3)) FactBody v /\ v $? "f" = Some 6.
  Axiom EvalFactRec6 : exists v : valuation,
      eval Fact_env ($0 $+ ("n", 3)) FactRecBody v /\ v $? "f" = Some 6.
  Axiom EvalFactTailRec6 : exists v : valuation,
      eval Fact_env ($0 $+ ("n", 3) $+ ("acc", 1)) FactTailRecBody v /\
      v $? "f" = Some 6.
  Axiom collatz_result : exists v : valuation,
      eval Collatz_env ($0 $+ ("flight", 0) $+ ("start", 10)) CollatzBody v /\
      v $? "flight" = Some 6.

  Parameter opt_binop_fold : BinopName -> expr -> expr -> expr.
  (*[1%]*) Axiom opt_binop_fold_test1 : opt_binop_fold Plus "x" 0 = "x".

  (*[8%]*) Axiom opt_binop_fold_sound :
    forall (b : BinopName) (e1 e2 : expr) (v : valuation),
      interp_arith (opt_binop_fold b e1 e2) v =
      interp_binop b (interp_arith e1 v) (interp_arith e2 v).

  Parameter opt_binop_precompute : BinopName -> expr -> expr -> expr.
  (*[Arith/Precompute:16%]*) Axiom opt_binop_precompute_sound :
    forall (b : BinopName) (e1 e2 : expr) (v : valuation),
      interp_arith (opt_binop_precompute b e1 e2) v =
      interp_binop b (interp_arith e1 v) (interp_arith e2 v).

  Parameter opt_binop_log2 : BinopName -> expr -> expr -> expr.
  (*[Arith/Log:16%]*) Axiom opt_binop_log2_sound :
    forall (b : BinopName) (e1 e2 : expr) (v : valuation),
      interp_arith (opt_binop_log2 b e1 e2) v =
      interp_binop b (interp_arith e1 v) (interp_arith e2 v).

  Parameter opt_binop_bitwise : BinopName -> expr -> expr -> expr.
  (*[Arith/Bitwise:16%]*) Axiom opt_binop_bitwise_sound :
    forall (b : BinopName) (e1 e2 : expr) (v : valuation),
      interp_arith (opt_binop_bitwise b e1 e2) v =
      interp_binop b (interp_arith e1 v) (interp_arith e2 v).

  Parameter opt_arith : expr -> expr.

  (*[4%]*) Axiom opt_arith_fold_test1 :
    opt_arith (1 + "z" * ("y" * ("x" * (0 + 0 / 1))))%expr =
    (1)%expr.
  (*[Arith/Precompute:2%]*) Axiom opt_arith_precompute_test1:
    opt_arith (("x" + (3 - 3)) / (0 + 1) + ("y" + "y" * 0))%expr =
    ("x" + "y")%expr.
  (*[Arith/Precompute:2%]*) Axiom opt_arith_precompute_test2 :
    opt_arith ((("y" / ("x" * 0 + 7 / 1)) mod (12 - 5)) / (2 * 3))%expr =
    (("y" / 7) mod 7 / 6)%expr.
  (*[Arith/Log:2%]*) Axiom opt_arith_log2_test1 :
    opt_arith (("y" * 8) mod 8 / 4)%expr =
    (("y" << 3 & 7) >> 2)%expr.
  (*[Arith/Log:2%]*) Axiom opt_arith_log2_test2 :
    opt_arith (("y" * 1 + (4 + 0)) mod 9 / 3)%expr =
    (("y" + 4) mod 9 / 3)%expr.
  (*[Arith/Bitwise:2%]*) Axiom opt_arith_bitwise_test1 :
    opt_arith ("y" * 13)%expr =
    ("y" + (("y" << 2) + ("y" << 3)))%expr.
  (*[Arith/Bitwise:2%]*) Axiom opt_arith_bitwise_test2 :
    opt_arith ("y" * (3 + 0))%expr =
    ("y" + ("y" << 1))%expr.

  (*[10%]*) Axiom opt_arith_sound :
    forall (e : expr) (v : valuation),
      interp_arith (opt_arith e) v = interp_arith e v.

  Parameter opt_unskip : cmd -> cmd.

  (*[2%]*) Axiom opt_unskip_test1 :
    opt_unskip (Skip;; (Skip;; Skip);; (Skip;; Skip;; Skip)) =
    Skip.
  (*[2%]*) Axiom opt_unskip_test2 :
    opt_unskip (when 0 then (Skip;; Skip) else Skip done;;
                while 0 loop Skip;; Skip done;; Skip) =
    (when 0 then Skip else Skip done;; while 0 loop Skip done).

  (*[16%]*) Axiom opt_unskip_sound :
    forall (phi : environment) (c : cmd) (v v' : valuation),
      eval phi v c v' -> eval phi v (opt_unskip c) v'.

  Parameter opt_arith_constprop : expr -> valuation -> expr.

  (*[Eval/ConstProp:8%]*) Axiom opt_arith_constprop_sound :
    forall (e : expr) (v consts : fmap var nat),
      consts $<= v ->
      interp_arith (opt_arith_constprop e consts) v = interp_arith e v.

  Parameter opt_constprop : cmd -> cmd.

  (*[Eval/ConstProp:2%]*) Axiom opt_constprop_test1 :
    opt_constprop FactBody = FactBody.
  (*[Eval/ConstProp:2%]*) Axiom opt_constprop_test2 :
    opt_constprop ("x" <- 7;; "y" <- "x";;
                   when "x" mod "w" then
                     "z" <- "x";; "t" <- "z";; while "t" loop "t" <- "t" - 1 done
                   else
                     "z" <- "u" + "x";; "t" <- "z"
                   done;;
                   "r" <- "z") =
   ("x" <- 7;; "y" <- 7;;
    when 7 mod "w" then
      "z" <- 7;; "t" <- 7;; while "t" loop "t" <- "t" - 1 done
    else
      "z" <- "u" + 7;; "t" <- "z"
    done;;
    "r" <- "z").

  (*[Eval/ConstProp:18%]*) Axiom opt_constprop_sound :
    forall (phi : environment) (c : cmd) (v v' : valuation),
      eval phi v c v' -> eval phi v (opt_constprop c) v'.

  Parameter read_only : forall (c: cmd) (x0: var), bool.

  (*[Eval/Unroll:6%]*)
  Parameter eval_read_only: forall {phi v v' x c},
      eval phi v c v' ->
      read_only c x = true ->
      v' $? x = v $? x.

  Parameter opt_unroll : cmd -> cmd.

  (*[Eval/Unroll:2%]*) Axiom opt_unroll_test1 :
    opt_unroll CollatzBody = CollatzBody.
  (*[Eval/Unroll:2%]*) Axiom opt_unroll_test2 :
    opt_unroll FactBody <> FactBody.

  (*[Eval/Unroll:20%]*) Axiom opt_unroll_sound :
    forall (phi : environment) (c : cmd) (v v' : valuation),
      eval phi v c v' -> eval phi v (opt_unroll c) v'.
End S.

Global Arguments Nat.modulo !_ !_ /.
Global Arguments Nat.div !_ !_.
Global Arguments Nat.log2 !_ /.

(*|
TIPS: A few things that might be helpful keep in mind as you work on Pset 6
===========================================================================
 *)

(*|

Throughout the pset, think carefully on what you want to be doing induction on: commands, or proofs of `eval`?  In many cases both are possible, but not always: theorems that require reasoning about equivalences between loops will typically not be provable by induction on a command.

---

Do not assume that all lemmas are directly provable as stated: you will often need intermediate lemmas.  For example, for `eval_deterministic`, you will likely want to prove a variant with premises reordered to get a stronger induction hypothesis.  For `opt_constprop_sound`, you'll want to make a generalized version with an arbitrary `consts` set instead of `$0`.

---

Automation can help with many of the proofs in this pset.  The tactics `eval_intro` and `eval_elim` may be convenient building blocks to use in your own tactics.

To detect an arbitrary match from Ltac, use `match ?x with _ => _ end`:
|*)

Ltac cases_any :=
  match goal with
  | [ |- context[match ?x with _ => _ end] ] => cases x
  end.

Goal (forall x y z: bool, x || y || z || true = true).
Proof.
  unfold orb.
  simplify; repeat cases_any; eauto.
Qed.

(*|
---

Coq's standard library contains many lemmas — you do not need to prove
everything from first principles!  Among other lemmas, our solution uses the
following, which get automatically picked up by `simplify`.
|*)

Local Hint Rewrite Nat.mul_0_r Nat.div_1_r Nat.add_0_r.
Local Hint Rewrite <- Nat.ones_equiv.
Local Hint Rewrite Nat.mul_1_r Nat.shiftl_mul_pow2 Nat.shiftr_div_pow2 Nat.land_ones.

(*|

As always, use `Search` to find relevant lemmas.

---

Beware of issues with operator precedence:
- `(n - 1) mod 2` is not the same as `n - 1 mod 2`.
 *)


(*|
HINTS: A few hints to help you if you get stuck on certain 
       problems in Pset 6.
       Beware! Don't read further if you don't want spoilers!
=============================================================
|*)

Module Hints (I: S). Import I.









































(* 
HINT 1: Constant propagation
============================

You will have an easier time if you define a function to test for constants, like so:

Definition as_const (e: expr) : option nat :=
  match e with
  | Const n => Some n
  | _ => None
  end.

Otherwise, goals will get very large.
*)









































(*|
HINT 2: Constant propagation
============================

In the proof of `opt_constprop_sound`, or more likely the strengthened version of it, you will probably find the following lemma useful:


Lemma includes_remove_add (consts v: valuation) x n:
  consts $<= v ->
  consts $- x $<= v $+ (x, n).
Proof.
  simplify; apply includes_intro; simplify.
  cases (x ==v k); subst; simplify; try equality.
  eauto using includes_lookup.
Qed.
|*)








































                     
(*|
HINT 3: Loop unrolling
======================

In the implementation of `read_only`, you can use `if x ==v x0 then true else false` to get a Boolean indicating whether two variables are equal.
|*)









































(*|
HINT 4: Loop unrolling
======================

Programs in this section can get pretty big — consider adding intermediate definitions and proving lemmas about them.  For example, I used this:
 *)
                     
Definition loop1 x body :=
  body;; x <- x - 1.

Lemma opt_unroll_decr : forall {phi v v' x body n},
    eval phi v (loop1 x body) v' ->
    read_only body x = true ->
    v $? x = Some n ->
    v' $? x = Some (n - 1).
Abort.
                     
(*|
The key difficulty in this problem is connecting the unrolled loop body to the original loop body.  Because of the way `EvalWhileTrue` and `EvalWhileFalse` are defined, regular induction gives you two cases: one where the loop exits immediately and one where it runs `n + 1` times.

Instead, you want to think about three cases: the loops exits immediately, the loop runs a single time, and the loop runs `n + 2` times.  The key is to make a lemma that mentions both of these cases at once.  Let's look at a concrete example:
|*)

Fixpoint even (n: nat) :=
  match n with
  | 0 => True
  | 1 => False
  | S (S n) => even n
  end.

Lemma even_sum : forall x y, even x -> even y -> even (x + y).
Proof.
  induct x; simplify.
  - assumption.
  - cases x.
    + equality.
    + simpl.

(*|
This proof is stuck: intuitively, IH steps one step forward, and we want to take two steps at once.
|*)

Abort.

(*|
The trick is to generalize the lemma to assert two "levels":
|*)

Lemma even_sum : forall x y,
    (even x -> even y -> even (x + y)) /\
    (even (S x) -> even y -> even (S x + y)).
Proof.
  induct x.
  - simplify; cases y; first_order.
  - simplify; firstorder.
Qed.

(*|
What does that mean for this pset?  Chances are you'll probably come up with a lemma that looks like this at some point:
|*)

Lemma opt_unroll_template_sound : forall phi v v' x body n,
    n mod 2 = 0 ->
    v $? x = Some n ->
    read_only body x = true ->
    eval phi v (while x loop (loop1 x body) done) v' ->
    eval phi v (while x loop (loop1 x body);; (loop1 x body) done) v'.
Abort.

(*|
… but it won't work by induction.  No, what you need is this, which *will* work by induction:
|*)

Lemma opt_unroll_template_mx_sound : forall phi v v' x body n,
    v $? x = Some n ->
    read_only body x = true ->
    eval phi v (while x loop (loop1 x body) done) v' ->
    eval phi v (if n mod 2 ==n 0 then
                while x loop (loop1 x body);; (loop1 x body) done
              else
                (loop1 x body);;
                while x loop (loop1 x body);; (loop1 x body) done) v'.
Abort.

(*|
One last trick: this form with an `if` is essentially a partially evaluated version of the full loop-unrolling template, with the “fixup” phase at the beginning.  In other words, you can prove the following theorem:
|*)

Lemma opt_unroll_eqn {phi v v' body x}:
  let n := match v $? x with Some n => n | None => 0 end in
  eval phi v (if n mod 2 ==n 0 then
              while x loop (loop1 x body);; (loop1 x body) done
            else
              (loop1 x body);;
              while x loop (loop1 x body);; (loop1 x body) done) v' ->
  eval phi v (when (x mod 2) then loop1 x body else Skip done;;
            while x loop (loop1 x body);; (loop1 x body) done) v'.
Abort.

End Hints.
