Require Import Strings.String.
Local Open Scope string_scope.

Inductive Val :=
|undecl: Val
|unassign: Val
|num: nat -> Val
|boolean: bool -> Val.
.
Coercion num: nat >-> Val.
Coercion boolean: bool >-> Val. 

Scheme Equality for Val.
Definition Env := string -> Val
Definition env : Env := fun x => .

Definition update (env : Env) (str : string) (v : Val) : Env :=
  fun str' =>
    if(string_dec str str')
.

Inductive AExp :=
| avar: string -> AExp
| anum: nat -> AExp
| aplus: AExp -> AExp -> AExp
| asub: AExp -> AExp -> AExp
| amul: AExp -> AExp -> AExp
| adiv: AExp -> AExp -> AExp
| amod: AExp -> AExp -> AExp.

Coercion anum : nat >-> AExp.
Coercion avar : string >-> AExp.
Notation "A +' B" := (aplus A B) (at level 48).
Notation "A -' B" := (asub A B) (at level 48).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 46).
Notation "A %' B" := (amod A B) (at level 46).

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bvar : string -> BExp
| blessthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bgreaterthan: AExp -> AExp -> BExp
| bor : BExp -> BExp -> BExp.

Coercion bvar: string >-> BExp.
Notation "A <=' B" := (blessthan A B) (at level 53).
Notation "A >=' B" := (bgreaterthan A B) (at level 53).
Notation "` A " := (bnot A) (at level 40).
Notation "A &&' B" := (band A B) (at level 55).
Notation "A ||' B" := (bor A B) (at level 55).

Inductive Stmt :=
| def_nat : string -> AExp ->Stmt
| def_bool : string -> BExp ->Stmt
| assignment : string -> AExp -> Stmt
| bassignment : string -> BExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| For : Stmt -> BExp -> Stmt -> Stmt ->Stmt
| forcontent : BExp -> Stmt -> Stmt -> Stmt.

Notation "X ::= A" := (assignment X A ) (at level 50).
Notation "X :b:= A" := (bassignment X A ) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 92).
Notation "'If' ( C ) 'then' { A } 'else' { B } 'end'" := (ifthenelse C A B) (at level 59).
Notation "'If' ( C ) 'then' { A } 'end'" := (ifthen C A) (at level 59).
Notation "'while'' ( A ) { B } " := (while A B) (at level 91).
Notation "'for' ( A ; B ; C ) { D }" := (For A B C D) (at level 91).
Notation "'int' A := B" := (def_nat A B)(at level 50).
Notation "'boolean' A := B" := (def_bool A B)(at level 50).
Reserved Notation "S -{ sigma }->  sigma'" (at level 60).
