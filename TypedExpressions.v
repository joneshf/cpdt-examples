(* Standard imports. *)
Add LoadPath "~/programming/coq/cpdt/src".
Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.

(* Defining our own stuff. *)
Inductive type : Set := Nat | Bool.

(* Typed binary ops. *)
(* This is an indexed type family. Whatever that means. *)
Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
(* Make TEq polymorphic. *)
| TEq : forall t, tbinop t t Bool
| TLt : tbinop Nat Nat Bool.
(* Apparently that just means that types are enforced. *)

(* Typed expresssions. *)
Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

(* Convert object types into meta types. *)
Definition typeDenote (t: type) : Set :=
  match t with
    | Nat => nat
    | Bool => bool
  end.

(* Convert object binops to meta binops. *)
Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
: typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
    | TPlus => plus
    | TTimes => mult
    | TEq Nat => beq_nat
    | TEq Bool => eqb
    | TLt => leb
  end.

