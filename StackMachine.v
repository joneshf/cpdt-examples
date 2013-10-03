(* Standard set of imports. *)
Add LoadPath "~/programming/coq/cpdt/src".
Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.

(* An ADT *)
Inductive binop : Set := Plus | Times.
Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Times => mult
  end.

(*
Sugar for:
Definition binopDenote : binop -> nat -> nat -> nat := fun (b: binop) =>
  match b with
    | Plus => plus
    | Times => mult
  end.

Or, without the types:
Definition binopDenote := fun b =>
  match b with
    | Plus => plus
    | Times => mult
  end.
*)

(* Fixpoint denotes recursive data type. *)
Fixpoint expDenote (e: exp) : nat :=
  match e with
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.

(* We want to eval some things in order to test we have the right definitions. *)
Eval simpl in expDenote (Const 42).
Eval simpl in expDenote (Binop Plus (Const 2) (Const 2)).
Eval simpl in expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

(* The actual language. *)
Inductive instr : Set :=
(* Push Const on the stack. *)
| iConst : nat -> instr
(* Pop two Const's apply the Binop and push on the stack. *)
| iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.
Definition instrDenote (i : instr) (s: stack) : option stack :=
  match i with
    (* Push it on the stack. *)
    | iConst n => Some (n :: s)
    | iBinop b =>
      match s with
        (* Apply the operator. *)
        | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
        (* Stack underflow. *)
        | _ => None
      end
  end.
Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
    (* No more instructions. *)
    | nil => Some s
    | i :: p' =>
      (* Apply the instruction. *)
      match instrDenote i s with
        (* Stack underflow. *)
        | None => None
        | Some s' => progDenote p' s'
      end
  end.

(* Compiler. *)
Fixpoint compile (e : exp) : prog :=
  match e with
    | Const n => iConst n :: nil
    | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
  end.

(* Test the compiler. *)
Eval simpl in compile (Const 42).
Eval simpl in compile (Binop Plus (Const 2) (Const 2)).
Eval simpl in compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

Eval simpl in progDenote (compile (Const 42)) nil.
Eval simpl in progDenote (compile (Binop Plus (Const 2) (Const 2))) nil.
Eval simpl in progDenote (compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))) nil.

(* Proving correctness. *)
Theorem compile_correct : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).

(* Our first attempt seems too hard, for what reason?
Let's try something else. *)
Abort.

Lemma compile_correct' : forall e p s, progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).

(* Let's try the induction tactic. *)
induction e.

(* Use the intros tactic, whatever that is. *)
intros.
(* This seems to lift forall variables into a free state? *)

(* Let's unfold the functions in our goal. *)
unfold compile.
unfold expDenote.
(* We only need to unfold the LHS progDenote, why? *)
unfold progDenote at 1.
(* Now we can remove some of the cruft, since we know the first arg to progDenote *)
simpl.
(* Now fold it back up. *)
fold progDenote.
(* It's trivial now. *)
reflexivity.

(* On to the next one. *)
intros.
unfold compile.
fold compile.
unfold expDenote.
fold expDenote.
(* Near as I can tell, this folding/unfolding is equivalent to simpl. *)

(* The LHS almost looks like IHe2, we jus need to change the parens. *)
(* Need associative law for lists. *)
Check app_assoc_reverse.
(* We can also search like in hoogle. *)
SearchRewrite ((_ ++ _) ++ _).
rewrite app_assoc_reverse.
(* Now we can rewrite it as the hypothesis. *)
rewrite IHe2.
(* If we do that again, we can get IHe1. *)
rewrite app_assoc_reverse.
rewrite IHe1.
(* We're practically done. *)
unfold progDenote at 1.
simpl.
fold progDenote.
reflexivity.

(* But this was messy.  We can do better with coq. *)
Abort.

Lemma compile_correct' : forall e s p, progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
  induction e; crush.
Qed.

(* Now we can actually prove our theorem. *)
Theorem compile_correct : forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
  intros.
  (* We need to use the lemma we constructed, and it almost looks like it, just need a rewrite. *)
  Check app_nil_end.
  (* Have to state exactly what to rewrite. *)
  rewrite (app_nil_end (compile e)).
  (* Use our lemma. *)
  rewrite compile_correct'.
  (* Let's skip a step and let coq handle the nitty. *)
  reflexivity.
Qed.